module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pDefs
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.K22p

open Subgroup

structure Good (p : ℕ) (M : Type) [Group M] [Finite M] (σ : MulAut M) : Prop where
  isKGroup : CFSG.Open.IsKGroup M
  not_dvd_three : ¬ 3 ∣ Nat.card M
  pow_three : σ ^ 3 = 1
  fixesSylow : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → FixesSylow σ q

variable {M : Type} [Group M] [Finite M]

instance instActorAction (σ : MulAut M) : MulDistribMulAction (Subgroup.zpowers σ) M :=
  MulDistribMulAction.compHom M (Subgroup.subtype (Subgroup.zpowers σ))

abbrev commAct (σ : MulAut M) : Subgroup M :=
  CFSG.commutatorAction (A := Subgroup.zpowers σ) (G := M)

theorem zpowers_self_eq_top (σ : MulAut M) :
    Subgroup.zpowers (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, Subtype.ext hk⟩

theorem pow_mem_commSub (τ : MulAut M) (n : ℕ) (g : M) :
    g⁻¹ * (τ ^ n) g ∈ commSub τ := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      have key : g⁻¹ * (τ ^ (n + 1)) g =
          (g⁻¹ * τ g) * ((τ g)⁻¹ * (τ ^ n) (τ g)) := by
        rw [pow_succ, MulAut.mul_apply]
        group
      rw [key]
      have hgen : g⁻¹ * τ g ∈ commSub τ :=
        Subgroup.subset_closure (show g⁻¹ * τ g ∈ Set.range (fun x : M => x⁻¹ * τ x) from ⟨g, rfl⟩)
      exact Subgroup.mul_mem _ hgen (ih (τ g))

theorem zpow_mem_commSub (τ : MulAut M) (k : ℤ) (g : M) :
    g⁻¹ * (τ ^ k) g ∈ commSub τ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact pow_mem_commSub τ n g
  · have hfix : (τ ^ n) ((τ ^ (-(n : ℤ))) g) = g := by
      have hone : τ ^ n * τ ^ (-(n : ℤ)) = (1 : MulAut M) := by
        rw [← zpow_natCast, ← zpow_add]
        simp
      rw [← MulAut.mul_apply, hone, MulAut.one_apply]
    have key : g⁻¹ * (τ ^ (-(n : ℤ))) g =
        (((τ ^ (-(n : ℤ))) g)⁻¹ * (τ ^ n) ((τ ^ (-(n : ℤ))) g))⁻¹ := by
      rw [hfix]
      group
    rw [key]
    exact Subgroup.inv_mem _ (pow_mem_commSub τ n ((τ ^ (-(n : ℤ))) g))

theorem commutatorAction_eq_commSub {A : Type} [Group A] [MulDistribMulAction A M]
    (a₀ : A) (hgen : Subgroup.zpowers a₀ = ⊤) (τ : MulAut M)
    (hsmul : ∀ x : M, a₀ • x = τ x) :
    CFSG.commutatorAction (A := A) (G := M) = commSub τ := by
  apply le_antisymm
  · rw [CFSG.commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := commSub τ)).mpr ?_
    rintro x ⟨a, g, rfl⟩
    have ha : a ∈ Subgroup.zpowers a₀ := by rw [hgen]; trivial
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hto : MulDistribMulAction.toMulAut A M a₀ = τ := MulEquiv.ext hsmul
    have hpow : a • g = (τ ^ k) g := by
      rw [← hk]
      calc (a₀ ^ k) • g
          = (MulDistribMulAction.toMulAut A M (a₀ ^ k)) g := by
              rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
        _ = (τ ^ k) g := by rw [map_zpow, hto]
    rw [hpow]
    exact zpow_mem_commSub τ k g
  · rw [commSub]
    refine (Subgroup.closure_le (K := CFSG.commutatorAction (A := A) (G := M))).mpr ?_
    rintro _ ⟨g, rfl⟩
    rw [CFSG.commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨a₀, g, by rw [hsmul]⟩

theorem commAct_eq_commSub (σ : MulAut M) : commAct σ = commSub σ :=
  commutatorAction_eq_commSub ⟨σ, Subgroup.mem_zpowers σ⟩ (zpowers_self_eq_top σ) σ
    (fun _ => rfl)

theorem commAct_normal (σ : MulAut M) : (commAct σ).Normal :=
  CFSG.commutatorAction_normal (A := Subgroup.zpowers σ) (G := M)

theorem commAct_isInvariant (σ : MulAut M) :
    IsInvariant (Subgroup.zpowers σ) M (commAct σ) :=
  CFSG.commutatorAction_isInvariant (A := Subgroup.zpowers σ) (G := M)

theorem commAct_invariant (σ : MulAut M) {x : M} (hx : x ∈ commAct σ) :
    σ x ∈ commAct σ := by
  have := ((commAct_isInvariant σ).invariant ⟨σ, Subgroup.mem_zpowers σ⟩ x).mp hx
  simpa using this

theorem map_eq_of_pointwise_invariant (σ : MulAut M) (L : Subgroup M)
    (h : ∀ x ∈ L, σ x ∈ L) : L.map σ.toMonoidHom = L := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact h
  · rw [Subgroup.card_map_of_injective σ.injective]

theorem commAct_map_eq (σ : MulAut M) :
    (commAct σ).map σ.toMonoidHom = commAct σ :=
  map_eq_of_pointwise_invariant σ (commAct σ) (fun _ hx => commAct_invariant σ hx)

theorem restrictedAutomorphism_pow_apply (σ : MulAut M) (L : Subgroup M)
    (hL : L.map σ.toMonoidHom = L) (n : ℕ) (l : L) :
    (((CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ L hL) ^ n) l : M) =
      (σ ^ n) (l : M) := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply,
        ih (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ L hL l),
        CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_apply]
      rw [← MulAut.mul_apply, ← pow_succ]

theorem good_restrict {p : ℕ} {σ : MulAut M} (hGood : Good p M σ) {L : Subgroup M} [L.Normal]
    (hLinv : ∀ x ∈ L, σ x ∈ L) :
    Good p L (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ L
      (map_eq_of_pointwise_invariant σ L hLinv)) := by
  let hL := map_eq_of_pointwise_invariant σ L hLinv
  let τ : MulAut L := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ L hL
  change Good p L τ
  refine ⟨hGood.isKGroup.subgroup L, ?_, ?_, ?_⟩
  · exact fun h => hGood.not_dvd_three (h.trans (Subgroup.card_subgroup_dvd_card L))
  · apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [restrictedAutomorphism_pow_apply σ L hL 3 l, hGood.pow_three]
    rfl
  · intro q hq hq2 hqp
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q, hQfix⟩ : ∃ Q : Sylow q M, ∀ x ∈ (Q : Subgroup M), σ x = x :=
      hGood.fixesSylow q hq hq2 hqp
    obtain ⟨Q', hQ'⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_sylow_inf_normal Q L
    refine ⟨Q', ?_⟩
    intro y hy
    apply Subtype.ext
    rw [CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_apply]
    have hyQ : (y : M) ∈ (Q : Subgroup M) := by
      have hmem : (y : M) ∈ (Q' : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem L.subtype hy
      rw [hQ'] at hmem
      exact hmem.1
    exact hQfix _ hyQ

theorem commSub_commAct_restrict_eq_top (σ : MulAut M) (hσ : σ ^ 3 = 1)
    (h3 : ¬ 3 ∣ Nat.card M) :
    commSub (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ (commAct σ)
      (commAct_map_eq σ)) = ⊤ := by
  let a₀ : Subgroup.zpowers σ := ⟨σ, Subgroup.mem_zpowers σ⟩
  let τ : MulAut (commAct σ) :=
    CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism σ (commAct σ) (commAct_map_eq σ)
  letI : MulDistribMulAction (Subgroup.zpowers σ) (commAct σ) :=
    CFSG.SignalizerFunctor.Helpers.invariantSubgroupAction (commAct σ)
      (fun a x hx => (commAct_isInvariant σ).invariant a x |>.mp hx)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers σ)) (Nat.card M) := by
    have hA : Nat.card (Subgroup.zpowers σ) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hσ
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr h3 |>.coprime_dvd_left hA
  have hcomp : CFSG.commutatorAction (A := Subgroup.zpowers σ) (G := commAct σ) = commSub τ :=
    commutatorAction_eq_commSub (A := Subgroup.zpowers σ) a₀ (zpowers_self_eq_top σ) τ
      (fun l => by
        apply Subtype.ext
        rw [CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_apply]
        change a₀ • (l : M) = σ (l : M)
        rfl)
  have hmap : (CFSG.commutatorAction (A := Subgroup.zpowers σ) (G := commAct σ)).map
      (commAct σ).subtype = commAct σ := by
    have h1 := CFSG.commutatorAction_map_subtype_eq_commutatorAction₂
      (A := Subgroup.zpowers σ) (G := M)
    have h2 := CFSG.commutatorAction₂_eq_commutatorAction_of_coprime
      (A := Subgroup.zpowers σ) (G := M) hcop
    rw [h1, h2]
  have htop : (commSub τ).map (commAct σ).subtype = commAct σ := hcomp ▸ hmap
  have hcard : Nat.card (commSub τ) = Nat.card (commAct σ) := by
    rw [← Subgroup.card_map_of_injective (commAct σ).subtype_injective, htop]
  exact Subgroup.eq_top_of_card_eq (H := commSub τ) hcard

abbrev quotientAutomorphism (σ : MulAut M) (N : Subgroup M) [N.Normal]
    (h : N.map σ.toMonoidHom = N) : MulAut (M ⧸ N) :=
  QuotientGroup.congr N N σ h

theorem quotientAutomorphism_pow_three (σ : MulAut M) (N : Subgroup M) [N.Normal]
    (h : N.map σ.toMonoidHom = N) (hσ : σ ^ 3 = 1) :
    quotientAutomorphism σ N h ^ 3 = 1 := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hpow : ∀ n : ℕ, ∀ z : M,
        (quotientAutomorphism σ N h ^ n) (QuotientGroup.mk' N z) =
          QuotientGroup.mk' N ((σ ^ n) z) := by
      intro n
      induction n with
      | zero => intro z; simp
      | succ n ih =>
        intro z
        rw [pow_succ, MulAut.mul_apply,
          show quotientAutomorphism σ N h (QuotientGroup.mk' N z) = QuotientGroup.mk' N (σ z)
            from QuotientGroup.congr_mk' N N σ h z, ih (σ z)]
        rw [← MulAut.mul_apply, ← pow_succ]
    change (quotientAutomorphism σ N h ^ 3) (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N x
    rw [hpow 3 x, hσ]
    rfl

theorem quotient_commSub_eq (σ : MulAut M) (N : Subgroup M) [N.Normal]
    (h : N.map σ.toMonoidHom = N) :
    commSub (quotientAutomorphism σ N h) = (commSub σ).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · rw [commSub]
    refine (Subgroup.closure_le (K := (commSub σ).map (QuotientGroup.mk' N))).mpr ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x⁻¹ * σ x ∈ commSub σ :=
      Subgroup.subset_closure (show x⁻¹ * σ x ∈ Set.range (fun z : M => z⁻¹ * σ z) from ⟨x, rfl⟩)
    have hmem : (QuotientGroup.mk' N) (x⁻¹ * σ x) ∈ (commSub σ).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hx
    rwa [map_mul, map_inv, show (QuotientGroup.mk' N) (σ x) =
      quotientAutomorphism σ N h (QuotientGroup.mk' N x) from
      (QuotientGroup.congr_mk' N N σ h x).symm] at hmem
  · rw [Subgroup.map_le_iff_le_comap, commSub]
    refine (Subgroup.closure_le (K := Subgroup.comap (QuotientGroup.mk' N)
      (commSub (quotientAutomorphism σ N h)))).mpr ?_
    rintro _ ⟨w, rfl⟩
    change (QuotientGroup.mk' N) (w⁻¹ * σ w) ∈ commSub (quotientAutomorphism σ N h)
    rw [map_mul, map_inv, show (QuotientGroup.mk' N) (σ w) =
      quotientAutomorphism σ N h (QuotientGroup.mk' N w) from
      (QuotientGroup.congr_mk' N N σ h w).symm]
    exact Subgroup.subset_closure (show (QuotientGroup.mk' N w)⁻¹ *
      quotientAutomorphism σ N h (QuotientGroup.mk' N w) ∈
      Set.range (fun z => z⁻¹ * quotientAutomorphism σ N h z) from
      ⟨QuotientGroup.mk' N w, rfl⟩)

theorem quotient_good {p : ℕ} {σ : MulAut M} (hGood : Good p M σ) (N : Subgroup M) [N.Normal]
    (hNinv : ∀ x ∈ N, σ x ∈ N) :
    Good p (M ⧸ N) (quotientAutomorphism σ N (map_eq_of_pointwise_invariant σ N hNinv)) := by
  let hmap := map_eq_of_pointwise_invariant σ N hNinv
  let φ := quotientAutomorphism σ N hmap
  change Good p (M ⧸ N) φ
  refine ⟨hGood.isKGroup.quotient N, ?_, ?_, ?_⟩
  · intro h
    rw [← Subgroup.index_eq_card] at h
    exact hGood.not_dvd_three (h.trans N.index_dvd_card)
  · exact quotientAutomorphism_pow_three σ N hmap hGood.pow_three
  · intro q hq hq2 hqp
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q, hQfix⟩ : ∃ Q : Sylow q M, ∀ x ∈ (Q : Subgroup M), σ x = x :=
      hGood.fixesSylow q hq hq2 hqp
    refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective N), ?_⟩
    intro y hy
    rw [Sylow.coe_mapSurjective] at hy
    obtain ⟨x, hxQ, rfl⟩ := hy
    rw [show φ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (σ x) from
      QuotientGroup.congr_mk' N N σ hmap x, hQfix x hxQ]

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.K22p
