module

public import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.Timmesfeld.Bridge.Asc72NoPolar
public import CFSG.Timmesfeld.Bridge.Asc72ThirdKind

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

@[expose] def StrongConclusion (G : Type*) [Group G] (D : Set G) : Prop :=
  Conclusion G D ∧
    (CFSG.BenderSuzuki.IsBenderGroup G ∨ (Subgroup.center G = ⊥ ∧ commutator G ≠ ⊤))

@[expose] def SmallerHolds (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nat.card K < n → ∀ E : Set K, Setup K E →
    (∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected E →
    StrongConclusion K E

@[expose] def WreathInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
    ∀ M : Subgroup G, IsMinimalNormal M → ¬ IsSimpleGroup M →
      ∃ f n : ℕ, 2 ≤ f ∧ (n = 3 ∨ n = 4) ∧ Nonempty (G ≃* L2Wreath f n)

@[expose] def ThirdKindExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
    Subgroup.center G = ⊥ → (∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K) →
    SmallerHolds (Nat.card G) →
    ∀ u ∈ D, ∀ w ∈ D, ∀ v ∈ D, IsTriangle D u w v → IsThirdKind u w v → ¬ Reach D u w →
      u * v ∉ D → False

theorem commutator_ne_top_of_l2Wreath {K : Type*} [Group K] {f n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* L2Wreath f n) : commutator K ≠ ⊤ := by
  intro htop
  set φ : K →* ℤˣ :=
    Equiv.Perm.sign.comp ((SemidirectProduct.rightHom).comp e.toMonoidHom) with hφ
  have hker : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [htop] at hker
  set σ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  obtain ⟨k, hk⟩ := e.surjective (SemidirectProduct.inr σ)
  have h1 : φ k = 1 := hker (Subgroup.mem_top k)
  rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hk,
    SemidirectProduct.rightHom_inr, Equiv.Perm.sign_swap (by simp [Fin.ext_iff])] at h1
  exact absurd h1 (by decide)

theorem top_eq_bot_of_isSolvable_of_commutator_eq_top {K : Type*} [Group K]
    (hsol : Group.IsSolvable K) (htop : commutator K = ⊤) : (⊤ : Subgroup K) = ⊥ := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def K).mp hsol
  have hall : ∀ m, derivedSeries K m = ⊤ := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  rw [← hall n, hn]

theorem eq_of_commute_of_odd {G : Type*} [Group G] {D : Set G} (hD : IsOddTransp D)
    {M : Subgroup G} [M.Normal] {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (hc : Commute (QuotientGroup.mk' M u) (QuotientGroup.mk' M v))
    (hodd : Odd (orderOf (u * v))) : QuotientGroup.mk' M u = QuotientGroup.mk' M v := by
  have hsq : (QuotientGroup.mk' M (u * v)) ^ 2 = 1 := by
    rw [map_mul, ← commute_iff_mul_sq_eq_one]
    · exact hc
    · rw [← map_mul, hD.mul_self_eq_one hu, map_one]
    · rw [← map_mul, hD.mul_self_eq_one hv, map_one]
  have hdvd : orderOf (QuotientGroup.mk' M (u * v)) ∣ orderOf (u * v) := orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' M (u * v)) ∣ 2 ^ 1 := by
    rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf (QuotientGroup.mk' M (u * v)) = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases i with _ | i
    · simpa using hi
    · have := Odd.of_dvd_nat hodd hdvd
      rw [hi, pow_succ] at this
      exact absurd this (by simp [Nat.not_odd_iff_even])
  rw [orderOf_eq_one_iff, map_mul, mul_eq_one_iff_eq_inv] at h1
  rw [h1, ← map_inv, hD.inv_eq hv]

theorem commute_of_commute_of_ne {G : Type*} [Group G] {D : Set G} (hD : IsOddTransp D)
    {M : Subgroup G} [M.Normal] {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (hne : QuotientGroup.mk' M u ≠ QuotientGroup.mk' M v)
    (hc : Commute (QuotientGroup.mk' M u) (QuotientGroup.mk' M v)) : Commute u v := by
  by_contra h
  have hodd : Odd (orderOf (u * v)) := by
    rcases hD.2 u hu v hv with h2 | ho
    · exfalso
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2
      · have hmul : u * v = 1 := by
          have := pow_orderOf_eq_one (u * v)
          rwa [h1, pow_one] at this
        have hinv : u⁻¹ = v := inv_eq_of_mul_eq_one_right hmul
        rw [hD.inv_eq hu] at hinv
        exact h (by rw [hinv])
      · have hsq : (u * v) * (u * v) = 1 := by
          rw [← pow_two, ← h2]; exact pow_orderOf_eq_one _
        have hinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right hsq
        rw [mul_inv_rev, hD.inv_eq hu, hD.inv_eq hv] at hinv
        exact h hinv.symm
    · exact ho
  exact hne (eq_of_commute_of_odd hD hu hv hc hodd)

theorem commutator_le_of_index_eq_two {G : Type*} [Group G] {M : Subgroup G} (h : M.index = 2) :
    commutator G ≤ M := by
  have : M.Normal := Subgroup.normal_of_index_eq_two h
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hsq : ∀ x : G ⧸ M, x * x = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mul_self_mem_of_index_two h g
  refine ⟨⟨fun a b => ?_⟩⟩
  have h1 := hsq (a * b)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right (hsq b), inv_eq_of_mul_eq_one_right (hsq a)]

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem strongConclusion_of_reduced (hT : ThirdKindExclusion) (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hdisc : Disconnected D)
    (hZ : Subgroup.center G = ⊥) (hnorm : ∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K)
    (hIH : SmallerHolds (Nat.card G)) : StrongConclusion G D := by
  by_cases hnp : Moufang.NoPolar D
  · have hB := isBenderGroup_of_noPolar hS hrad hdisc hnp
    exact ⟨Or.inl hB, Or.inl hB⟩
  · exfalso
    simp only [Moufang.NoPolar, not_forall] at hnp
    obtain ⟨u, hu, v, hv, hc, hne, hnot⟩ := hnp
    obtain ⟨w, hw, huw, htri, h3⟩ := exists_thirdKind hS hdisc hnorm hu hv hne hc hnot
    exact hT G D hS hrad hdisc hZ hnorm hIH u hu w hw v hv htri h3 huw hnot

omit [Finite G] in
theorem center_le_centralizer (M : Subgroup G) :
    Subgroup.center G ≤ Subgroup.centralizer (M : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro m _
  exact (Subgroup.mem_center_iff.mp hz m)

theorem strongConclusion_of_smaller (hW : WreathInput) (hT : ThirdKindExclusion) (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hdisc : Disconnected D)
    (hIH : SmallerHolds (Nat.card G)) : StrongConclusion G D := by
  obtain ⟨M, hM⟩ := exists_minimalNormal hS
  have := hM.1
  have hC := centralizer_eq_bot_of_minimal hS hrad hM
  have hZ : Subgroup.center G = ⊥ := le_bot_iff.mp (hC ▸ center_le_centralizer M)
  by_cases hMs : IsSimpleGroup M
  · rcases simple_minimal_cases hS hrad hM hMs with hDM | ⟨hdisj, hcong⟩
    ·
      have hMtop := hS.eq_top_of_subset M hDM
      refine strongConclusion_of_reduced hT hS hrad hdisc hZ (fun K hK => ?_) hIH
      rcases hM.2.2 K hK (hMtop ▸ le_top) with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ hMtop ▸ le_top)
    · by_cases hidx : 2 < M.index
      ·
        have hAS : AlmostSimpleCase G D :=
          ⟨M, hM.1, hM, fun N hN => eq_of_minimal hS hrad hM hN, hMs, hC, hidx,
            widthOne_of_disjoint hS hdisj hcong,
            fun u hu => isOddTranspClass_conjSet hS hrad hM hMs hu⟩
        refine ⟨Or.inr (Or.inr hAS), Or.inr ⟨hZ, fun htop => ?_⟩⟩
        have h1 : ∀ d ∈ D, QuotientGroup.mk' M d ≠ 1 := fun d hd h =>
          hdisj d hd ((QuotientGroup.eq_one_iff d).mp h)
        have hSQ := hS.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M) h1
        have hsol : Group.IsSolvable (G ⧸ M) := hSQ.isSolvable_of_forall_commute (by
          rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
          rcases hS.oddT.commute_or_odd hu hv with hc | hodd
          · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
            exact hcong u hu v hv hc
          · exact eq_of_commute_of_odd hS.oddT hu hv huv hodd)
        have hmap : (commutator G).map (QuotientGroup.mk' M) = commutator (G ⧸ M) := by
          rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M),
            commutator_def]
        have hQtop : commutator (G ⧸ M) = ⊤ := by
          rw [← hmap, htop, ← MonoidHom.range_eq_map,
            MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M)]
        have hbot := top_eq_bot_of_isSolvable_of_commutator_eq_top hsol hQtop
        have hMtop : M = ⊤ := by
          rw [eq_top_iff]
          intro g _
          have : (g : G ⧸ M) = 1 := by
            have := Subgroup.mem_top (g : G ⧸ M)
            rw [hbot, Subgroup.mem_bot] at this
            exact this
          exact (QuotientGroup.eq_one_iff g).mp this
        rw [hMtop, Subgroup.index_top] at hidx
        omega
      ·
        have hMne : M ≠ ⊤ := by
          intro h
          obtain ⟨d, hd⟩ := hS.nonempty
          exact hdisj d hd (h ▸ Subgroup.mem_top d)
        have hidx2 : M.index = 2 := by
          have := Subgroup.one_lt_index_of_ne_top hMne
          omega
        have hGM := commutator_le_of_index_eq_two hidx2
        refine strongConclusion_of_reduced hT hS hrad hdisc hZ (fun K hK => ?_) hIH
        rcases hM.2.2 (K ⊓ M) inferInstance inf_le_right with h | h
        · left
          rw [eq_bot_iff, ← hC]
          intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          exact (Subgroup.commute_of_normal_of_disjoint K M hK hM.1 (disjoint_iff.mpr h) k m hk
            hm).eq.symm
        · exact Or.inr (hGM.trans (inf_eq_right.mp h))
  · obtain ⟨f, n, hf, hn, ⟨e⟩⟩ := hW G D hS hrad hdisc M hM hMs
    have hn2 : 2 ≤ n := by omega
    exact ⟨Or.inr (Or.inl ⟨f, n, hf, hn, ⟨e⟩⟩), Or.inr ⟨hZ, commutator_ne_top_of_l2Wreath hn2 e⟩⟩

theorem strongConclusion_of_inputs (hW : WreathInput) (hT : ThirdKindExclusion) :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
      (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
      StrongConclusion G D := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G = n →
      Setup G D → (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
      Disconnected D → StrongConclusion G D from
    fun G _ _ D => key _ G D rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ D hn hS hrad hdisc
  exact strongConclusion_of_smaller hW hT hS hrad hdisc
    (fun K _ _ hK E hSK hradK hdiscK => ih _ (hn ▸ hK) K E rfl hSK hradK hdiscK)

theorem theoremOne_of_inputs (hW : WreathInput) (hT : ThirdKindExclusion) : TheoremOne := by
  intro G _ _ D hclass hinv hodd hgen hrad hH
  have hS : Setup G D := ⟨hclass, ⟨hinv, hodd⟩, hgen⟩
  exact (strongConclusion_of_inputs hW hT G D hS hrad (disconnected_of_exists_subgroup hS hH)).1

end CFSG.Timmesfeld.Bridge.Asc72
