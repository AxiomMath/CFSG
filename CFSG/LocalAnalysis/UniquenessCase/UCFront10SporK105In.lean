module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup

variable {X : Type} [Group X] [Finite X]

@[expose] def K105In (H T : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, T ≤ Y → Y ≤ H → Group.IsSolvable ↥Y → ¬ 3 ∣ Nat.card ↥Y → Y ≤ T

omit [Finite X] in
theorem K105In.mono {H H' T : Subgroup X} (h : K105In H T) (hH : H' ≤ H) : K105In H' T :=
  fun Y hTY hYH => h Y hTY (hYH.trans hH)

theorem k105SporAt_of_k105In {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ]
    {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) (h : K105In ⊤ S₀)
    (e : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ) : K105SporAt s := by
  refine k105SporAt_of_index hS₀ (fun Z hSZ hZs m hm => ?_) e
  by_cases h3 : 3 ∣ m
  · exact Or.inr h3
  · left
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S₀)).1 hS₀.2.1
    have h3Z : ¬ 3 ∣ Nat.card ↥Z := by
      rw [hm, hk]
      intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h' | h'
      · exact h3 h'
      · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h'
        omega
    have hZS : Z = S₀ := le_antisymm (h Z hSZ le_top hZs h3Z) hSZ
    rw [hZS] at hm
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [one_mul]; exact hm.symm)

omit [Finite X] in
theorem k105In_of_quotient {C T : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTC : T ≤ C)
    (N : Subgroup ↥C) [N.Normal] (hNT : N.map C.subtype ≤ T) {L : Type} [Group L] [Finite L]
    (e : ↥C ⧸ N ≃* L)
    (hL : ∀ S H : Subgroup L, IsSylowTwoOf S ⊤ → S ≤ H → Group.IsSolvable ↥H →
      ¬ 3 ∣ Nat.card ↥H → H ≤ S) :
    K105In C T := by
  intro Y hTY hYC hYs hY3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hYs
  let φ : ↥C →* L := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hS : IsSylowTwoOf ((T.subgroupOf C).map φ) ⊤ := by
    refine ⟨le_top, (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm).map φ, ?_⟩
    change ¬ 2 ∣ ((T.subgroupOf C).map φ).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    intro h2
    apply hT.2.2
    change 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h2.trans ((Subgroup.index_map_dvd _ hφ).trans (Subgroup.relIndex_dvd_index_of_le hTC))
  have hYC' : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv
  have hle : (Y.subgroupOf C).map φ ≤ (T.subgroupOf C).map φ := by
    refine hL _ _ hS (Subgroup.map_mono fun x hx => hTY hx) ?_ ?_
    · have : Group.IsSolvable ↥(Y.subgroupOf C) :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYC).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hYC).symm.surjective
      exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective (Y.subgroupOf C))
    · intro h3
      apply hY3
      rw [← hYC']
      exact h3.trans (Subgroup.card_map_dvd _ _)
  intro y hy
  have hyC : y ∈ C := hYC hy
  have hmem : φ ⟨y, hyC⟩ ∈ (Y.subgroupOf C).map φ := ⟨⟨y, hyC⟩, hy, rfl⟩
  obtain ⟨t, ht, hte⟩ := hle hmem
  have hq : (QuotientGroup.mk t : ↥C ⧸ N) = QuotientGroup.mk ⟨y, hyC⟩ := e.injective hte
  have hN : t⁻¹ * ⟨y, hyC⟩ ∈ N := QuotientGroup.eq.1 hq
  have hNX : ((t⁻¹ * ⟨y, hyC⟩ : ↥C) : X) ∈ T := hNT ⟨_, hN, rfl⟩
  have htT : (t : X) ∈ T := ht
  have hyt : y = (t : X) * ((t⁻¹ * ⟨y, hyC⟩ : ↥C) : X) := by simp
  rw [hyt]
  exact T.mul_mem htT hNX

theorem k105In_normalizer_of_card_le_four {T V : Subgroup X} (hT : IsSylowTwoOf T ⊤) {z : X}
    (hzT : T ≤ centralizer {z}) (hzV : z ∈ V) (hV : Nat.card V ≤ 4)
    (hC : K105In (centralizer {z}) T) :
    K105In (normalizer (V : Set X)) T := by
  intro Y hTY hYN hYs hY3
  have := hYs
  have hKT : centralizer (V : Set X) ⊓ Y ≤ T := by
    have hsub : T ⊔ (centralizer (V : Set X) ⊓ Y) ≤ Y := sup_le hTY inf_le_right
    refine le_sup_right.trans (hC _ le_sup_left (sup_le hzT ?_) ?_ ?_)
    · exact inf_le_left.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzV))
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hsub)
    · exact fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le hsub))
  let ψ : ↥Y →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  have hker : ψ.ker = (centralizer (V : Set X)).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker]
    rfl
  have hidx : (centralizer (V : Set X)).relIndex Y ∣ 24 := by
    have h1 := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective ψ)
    rw [hker, ← Subgroup.index, ← Subgroup.relIndex] at h1
    have hinj : Function.Injective (MulAut.toPerm ↥V) :=
      fun a b h => MulEquiv.toEquiv_injective h
    refine h1.trans ((Subgroup.card_dvd_of_injective _ hinj).trans ?_)
    rw [Nat.card_perm]
    exact (Nat.factorial_dvd_factorial hV).trans (by decide)
  have hidx3 : ¬ 3 ∣ (centralizer (V : Set X)).relIndex Y := fun h =>
    hY3 (h.trans (Subgroup.index_dvd_card _))
  have hidx8 : (centralizer (V : Set X)).relIndex Y ∣ 8 :=
    Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hidx3).symm
      (hidx : (centralizer (V : Set X)).relIndex Y ∣ 8 * 3)
  have e1 := Subgroup.relIndex_mul_card (centralizer (V : Set X)) Y
  have e2 := Subgroup.relIndex_mul_card T Y
  rw [inf_of_le_left hTY] at e2
  obtain ⟨u, hu⟩ := Subgroup.card_dvd_of_le hKT
  have hj : T.relIndex Y ∣ 8 := by
    have hpos : 0 < Nat.card ↥(centralizer (V : Set X) ⊓ Y) := Nat.card_pos
    have he : (centralizer (V : Set X)).relIndex Y = T.relIndex Y * u := by
      have he' := e1.trans e2.symm
      rw [hu] at he'
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [he']
      ring
    exact (Dvd.intro u he.symm).trans hidx8
  have hjodd : ¬ 2 ∣ T.relIndex Y := fun h => hT.2.2 (by
    have h' := h.trans (Subgroup.relIndex_dvd_index_of_le hTY)
    rwa [← Subgroup.relIndex_top_right] at h')
  have hj1 : T.relIndex Y = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show T.relIndex Y ∣ 2 ^ 3 from hj)
    rcases k with _ | k
    · simpa using hk
    · exact (hjodd (by rw [hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k))).elim
  exact Subgroup.relIndex_eq_one.1 hj1

theorem normalizer_le_centralizer_of_le {P Q : Subgroup X} {z : X} (hP : IsPGroup 2 ↥P)
    (hQP : Q ≤ P) (hCQ : centralizer (Q : Set X) ≤ Q)
    (hZQ : ∀ x ∈ Q, x ∈ centralizer (Q : Set X) → x = 1 ∨ x = z) :
    normalizer (P : Set X) ≤ centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  have hZ : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x = 1 ∨ x = z := by
    intro x hxP hx
    have hxc : x ∈ centralizer (Q : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => hx y (hQP hy)
    exact hZQ x (hCQ hxc) hxc
  by_cases hPb : P = ⊥
  · have hQb : Q = ⊥ := le_bot_iff.1 (hPb ▸ hQP)
    have hgc : g ∈ centralizer (Q : Set X) := Subgroup.mem_centralizer_iff.2 fun h hh => by
      have h1 : h = 1 := by
        rw [hQb] at hh
        exact Subgroup.mem_bot.1 hh
      rw [h1, one_mul, mul_one]
    have hgQ := hCQ hgc
    rw [hQb] at hgQ
    rw [Subgroup.mem_bot.1 hgQ]
    exact one_mem _
  · have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPb
    have : Nontrivial ↥(center ↥P) := hP.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(center ↥P))
    have hcP : ((c : ↥P) : X) ∈ P := (c : ↥P).2
    have hcZ : ∀ y ∈ P, y * ((c : ↥P) : X) = ((c : ↥P) : X) * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨y, hy⟩)
    have hcz : ((c : ↥P) : X) = z := by
      rcases hZ _ hcP hcZ with h | h
      · exact absurd (show c = 1 from Subtype.ext (Subtype.ext h)) hc1
      · exact h
    have hzP : z ∈ P := hcz ▸ hcP
    have hzZ : ∀ y ∈ P, y * z = z * y := by
      intro y hy
      rw [← hcz]
      exact hcZ y hy
    have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext (hcz.trans h)))
    have hgzP : g * z * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hg z).1 hzP
    have hgzZ : ∀ y ∈ P, y * (g * z * g⁻¹) = (g * z * g⁻¹) * y := by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ P := by
        refine (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)).2 ?_
        have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [e]
        exact hy
      have hc := hzZ _ hy'
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = (g * z * g⁻¹) * y := by group
    rcases hZ _ hgzP hgzZ with h | h
    · exact absurd (by simpa using h) hz1
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]

omit [Finite X] in
theorem le_thompsonJ_of_rank {T Q : Subgroup X} {m : ℕ} (hQT : Q ≤ T)
    (hrank : ∀ A : Subgroup X, A ≤ T → CFSG.Open.IsElemAbelian 2 A → Nat.card A ≤ 2 ^ m)
    (hgen : Q ≤ ⨆ (A : Subgroup X) (_ : A ≤ Q ∧ CFSG.Open.IsElemAbelian 2 A ∧
      Nat.card A = 2 ^ m), A) :
    Q ≤ CFSG.Quasithin.thompsonJ T := by
  refine hgen.trans (iSup₂_le fun A hA => ?_)
  obtain ⟨hAQ, hAe, hAc⟩ := hA
  refine le_iSup₂_of_le A ⟨hAQ.trans hQT, hAe, fun B hBT hB => ?_⟩ le_rfl
  rw [hAc]
  exact hrank B hBT hB

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
