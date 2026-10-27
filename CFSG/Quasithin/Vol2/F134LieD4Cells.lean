module

public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent

public section

namespace CFSG.Quasithin.F134.LieD4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

section SL2

open Matrix

variable {L : Type*} [Field L]

theorem coe_uSL_mul_WSL (s : L) :
    ((uSL s * WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![-s, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_WSL]
  simp

theorem coe_uSL_mul_WSL_pow_three (h2 : (2 : L) = 0) {s : L} (hs : s ^ 3 + s + 1 = 0) :
    (((uSL s * WSL) ^ 3 : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      !![s + 1, s ^ 2 + 1; s ^ 2 + 1, s] := by
  rw [pow_succ, pow_succ, pow_one, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_uSL_mul_WSL]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-1 : L) * hs + s * h2
  · linear_combination (-1 : L) * h2
  · linear_combination (-s ^ 2) * h2

theorem uSL_mul_WSL_pow_nine (h2 : (2 : L) = 0) {s : L} (hs : s ^ 3 + s + 1 = 0) :
    (uSL s * WSL : SL2 L) ^ 9 = 1 := by
  have e : (uSL s * WSL : SL2 L) ^ 9 = ((uSL s * WSL) ^ 3) ^ 3 := by rw [← pow_mul]
  rw [e]
  ext i j
  rw [pow_succ, pow_succ, pow_one, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_uSL_mul_WSL_pow_three h2 hs]
  simp only [Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (3 * s ^ 2 + 2 * s + 4) * hs + (s ^ 2 - 1) * h2
  · linear_combination (s ^ 3 + 5 * s + 2) * hs + (s ^ 2 - 2 * s) * h2
  · linear_combination (s ^ 3 + 5 * s + 2) * hs + (s ^ 2 - 2 * s) * h2
  · linear_combination (3 * s ^ 2 + s + 4) * hs + (-s ^ 2 - s - 2) * h2

theorem orderOf_uSL_mul_WSL (h2 : (2 : L) = 0) {s : L} (hs : s ^ 3 + s + 1 = 0) :
    orderOf (uSL s * WSL : SL2 L) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime_pow (p := 3) (n := 1) (fun h => ?_) (uSL_mul_WSL_pow_nine h2 hs)
  have h1 := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L) 0 1) h
  simp only [pow_one, coe_uSL_mul_WSL_pow_three h2 hs] at h1
  simp at h1
  exact one_ne_zero (by linear_combination hs - s * h1 : (1 : L) = 0)

theorem exists_cube_add_add_one_eq_zero [Finite L] (h2 : (2 : L) = 0) (hL : Nat.card L = 8) :
    ∃ s : L, s ^ 3 + s + 1 = 0 := by
  classical
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : L, s₀ ≠ 0 ∧ s₀ ≠ 1 := by
    by_contra hcon
    have hsub : (Finset.univ : Finset L) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · have : x = 1 := by
          by_contra hx1
          exact hcon ⟨x, hx, hx1⟩
        simp [this]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hL] at this
    have h2' := Finset.card_le_two (a := (0 : L)) (b := 1)
    omega
  have h7 : s₀ ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one s₀ hs₀.1
    rwa [← Nat.card_eq_fintype_card, hL] at this
  have hprod : (s₀ - 1) * ((s₀ ^ 3 + s₀ + 1) * (s₀ ^ 3 + s₀ ^ 2 + 1)) = 0 := by
    linear_combination h7 + (s₀ ^ 4 - s₀ ^ 3) * h2
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd (sub_eq_zero.1 h) hs₀.2
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨s₀, h⟩
  · refine ⟨s₀⁻¹, ?_⟩
    have hs : s₀ ≠ 0 := hs₀.1
    field_simp
    linear_combination h

end SL2

theorem false_of_orderOf_eq_nine {G : Type*} [Group G] [Finite G] {M P : Subgroup G}
    (hPM : P ≤ M) (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) {m : ℕ}
    (hM : Nat.card M = 9 * m) (hm : ¬ 3 ∣ m) {g : G} (hg : g ∈ M) (hg9 : orderOf g = 9) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' : Nat.card (P.subgroupOf M) = 9 := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  have hidx : (P.subgroupOf M).index = m := by
    have := (P.subgroupOf M).card_mul_index
    rw [hP', hM] at this
    omega
  have hPp : IsPGroup 3 (P.subgroupOf M) := IsPGroup.of_card (n := 2) (by rw [hP']; norm_num)
  set S₀ : Sylow 3 M := hPp.toSylow (by rw [hidx]; exact hm) with hS₀
  have hg' : orderOf (⟨g, hg⟩ : M) = 9 := by rw [Subgroup.orderOf_mk, hg9]
  have hZ : IsPGroup 3 (Subgroup.zpowers (⟨g, hg⟩ : M)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg']; norm_num)
  obtain ⟨S, hS⟩ := hZ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M S S₀
  have hmem : c * ⟨g, hg⟩ * c⁻¹ ∈ P.subgroupOf M := by
    have h1 : MulAut.conj c • (⟨g, hg⟩ : M) ∈ MulAut.conj c • (S : Subgroup M) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hS (Subgroup.mem_zpowers _))
    rw [← Sylow.coe_subgroup_smul, hc, hS₀, IsPGroup.toSylow_coe] at h1
    exact h1
  have h3 : (c * ⟨g, hg⟩ * c⁻¹) ^ 3 = 1 :=
    Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.1 hmem))
  rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h3
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg'] at this
  norm_num at this




section Cells

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem eq_one_or_eq_of_mem_foldedParabolicWeylGroup_singleton
    {b : Fin t.foldedTag.rank}
    {w : WeylGroup t.tag} (hw : w ∈ foldedParabolicWeylGroup t {b}) :
    w = 1 ∨ w = t.orbitReflection b := by
  rw [foldedParabolicWeylGroup, Set.image_singleton, Subgroup.mem_closure_singleton] at hw
  obtain ⟨k, rfl⟩ := hw
  have h2 : t.orbitReflection b ^ (2 : ℤ) = 1 := by
    rw [zpow_two, t.orbitReflection_mul_self]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    have e : k = 2 * (k / 2) := by omega
    rw [e, zpow_mul, h2, one_zpow]
  · right
    have e : k = 2 * (k / 2) + 1 := by omega
    rw [e, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem graphFixedRootBruhatCell_one :
    graphFixedRootBruhatCell t K σ 1 = (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := by
  ext x
  rw [mem_graphFixedRootBruhatCell, canonicalRep_one]
  constructor
  · rintro ⟨b, hb, b', hb', rfl⟩
    rw [mul_one]
    exact mul_mem hb hb'
  · intro hx
    exact ⟨x, hx, 1, one_mem _, by rw [mul_one, mul_one]⟩

section Cells'


theorem mem_graphFixedParabolic_singleton_iff (hσ : Function.Surjective σ)
    {b : Fin t.foldedTag.rank} {g : ModGL t.tag K} :
    g ∈ graphFixedParabolic t K σ {b} ↔ g ∈ graphFixedRootBorel t K σ ∨
      ∃ c ∈ graphFixedRootBorel t K σ,
        ∃ u ∈ graphFixedInversionUnipotent t K σ (t.orbitReflection b),
          c * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u = g := by
  constructor
  · intro hg
    obtain ⟨w, hw, hgw⟩ := graphFixedParabolic_subset_cells hσ {b} hg
    rcases eq_one_or_eq_of_mem_foldedParabolicWeylGroup_singleton hw with rfl | rfl
    · left
      rw [graphFixedRootBruhatCell_one] at hgw
      exact hgw
    · right
      obtain ⟨⟨c, u⟩, ⟨hc, hu⟩, rfl⟩ :=
        (bijOn_graphFixedRootBruhatCell hσ (t.orbitReflection_mem b)).2.2 hgw
      exact ⟨c, hc, u, hu, rfl⟩
  · rintro (hg | ⟨c, hc, u, hu, rfl⟩)
    · exact graphFixedRootBorel_le_graphFixedParabolic t K σ {b} hg
    · refine mul_mem (mul_mem (graphFixedRootBorel_le_graphFixedParabolic t K σ {b} hc) ?_) ?_
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨b, rfl, rfl⟩)
      · exact graphFixedRootBorel_le_graphFixedParabolic t K σ {b}
          (graphFixedPosUnipotent_le_graphFixedRootBorel
            (graphFixedInversionUnipotent_le_graphFixedPosUnipotent _ hu))

theorem eq_and_eq_of_mul_canonicalRep_mul_eq (hσ : Function.Surjective σ)
    {b : Fin t.foldedTag.rank} {c c' u u' : ModGL t.tag K} (hc : c ∈ graphFixedRootBorel t K σ)
    (hc' : c' ∈ graphFixedRootBorel t K σ)
    (hu : u ∈ graphFixedInversionUnipotent t K σ (t.orbitReflection b))
    (hu' : u' ∈ graphFixedInversionUnipotent t K σ (t.orbitReflection b))
    (h : c * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u =
      c' * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u') :
    c = c' ∧ u = u' :=
  Prod.ext_iff.1 ((bijOn_graphFixedRootBruhatCell hσ (t.orbitReflection_mem b)).2.1
    (Set.mk_mem_prod hc hu) (Set.mk_mem_prod hc' hu') h)

theorem mul_canonicalRep_mul_not_mem (hσ : Function.Surjective σ) {b : Fin t.foldedTag.rank}
    {c u : ModGL t.tag K} (hc : c ∈ graphFixedRootBorel t K σ)
    (hu : u ∈ graphFixedInversionUnipotent t K σ (t.orbitReflection b)) :
    c * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u ∉
      graphFixedRootBorel t K σ := by
  intro hB
  have h1 : c * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u ∈
      graphFixedRootBruhatCell t K σ (t.orbitReflection b) :=
    (bijOn_graphFixedRootBruhatCell hσ (t.orbitReflection_mem b)).1 (Set.mk_mem_prod hc hu)
  have h2 : c * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u ∈
      graphFixedRootBruhatCell t K σ 1 := by
    rw [graphFixedRootBruhatCell_one]
    exact hB
  exact Set.disjoint_left.1 (disjoint_graphFixedRootBruhatCell (t.orbitReflection_ne_one b)) h1 h2


theorem card_graphFixedParabolic_singleton [Finite K] (hσ : Function.Surjective σ)
    (b : Fin t.foldedTag.rank) :
    Nat.card (graphFixedParabolic t K σ {b}) = Nat.card (graphFixedRootBorel t K σ) *
      (1 + Nat.card (graphFixedInversionUnipotent t K σ (t.orbitReflection b))) := by
  classical
  have : Finite (ModGL t.tag K) := finite_modGL
  let f : graphFixedRootBorel t K σ ⊕ (graphFixedRootBorel t K σ ×
      graphFixedInversionUnipotent t K σ (t.orbitReflection b)) →
      graphFixedParabolic t K σ {b} := fun x => match x with
    | .inl c => ⟨c, (mem_graphFixedParabolic_singleton_iff hσ).2 (Or.inl c.2)⟩
    | .inr p => ⟨p.1 * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * p.2,
        (mem_graphFixedParabolic_singleton_iff hσ).2 (Or.inr ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩)⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro (c | ⟨c, u⟩) (c' | ⟨c', u'⟩) h <;> simp only [f, Subtype.mk.injEq] at h
      · rw [Subtype.ext h]
      · exact absurd (h ▸ c.2) (mul_canonicalRep_mul_not_mem hσ c'.2 u'.2)
      · exact absurd (h ▸ c'.2) (mul_canonicalRep_mul_not_mem hσ c.2 u.2)
      · obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_canonicalRep_mul_eq hσ c.2 c'.2 u.2 u'.2 h
        rw [Subtype.ext h1, Subtype.ext h2]
    · rintro ⟨g, hg⟩
      rcases (mem_graphFixedParabolic_singleton_iff hσ).1 hg with hg | ⟨c, hc, u, hu, rfl⟩
      · exact ⟨.inl ⟨g, hg⟩, rfl⟩
      · exact ⟨.inr (⟨c, hc⟩, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, Nat.card_prod]
  ring

theorem card_inf_mul_le_card [Finite K] (hσ : Function.Surjective σ) {b : Fin t.foldedTag.rank}
    {H : Subgroup (ModGL t.tag K)} (hUH : graphFixedPosUnipotent t K σ ≤ H)
    (hHP : H ≤ graphFixedParabolic t K σ {b}) (hHB : ¬ H ≤ graphFixedRootBorel t K σ) :
    Nat.card (H ⊓ graphFixedRootBorel t K σ : Subgroup (ModGL t.tag K)) *
      (1 + Nat.card (graphFixedInversionUnipotent t K σ (t.orbitReflection b))) ≤
        Nat.card H := by
  classical
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨h, hh, hhB⟩ := Set.not_subset.1 hHB
  obtain ⟨c₀, hc₀, u₀, hu₀, rfl⟩ :=
    ((mem_graphFixedParabolic_singleton_iff hσ).1 (hHP hh)).resolve_left hhB
  have hXH : ∀ u ∈ graphFixedInversionUnipotent t K σ (t.orbitReflection b), u ∈ H :=
    fun u hu => hUH (graphFixedInversionUnipotent_le_graphFixedPosUnipotent _ hu)
  have key : ∀ z u : ModGL t.tag K,
      z * (c₀ * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u₀) * (u₀⁻¹ * u) =
        z * c₀ * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u :=
    fun z u => by group
  let f : (H ⊓ graphFixedRootBorel t K σ : Subgroup (ModGL t.tag K)) ×
      Option (graphFixedInversionUnipotent t K σ (t.orbitReflection b)) → H := fun p =>
    match p.2 with
    | none => ⟨p.1, p.1.2.1⟩
    | some u => ⟨p.1 * (c₀ * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * u₀) *
        (u₀⁻¹ * u), mul_mem (mul_mem p.1.2.1 hh) (mul_mem (inv_mem (hXH _ hu₀)) (hXH _ u.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨z, _ | u⟩ ⟨z', _ | u'⟩ h <;> simp only [f, Subtype.mk.injEq] at h
    · rw [Subtype.ext h]
    · rw [key] at h
      exact absurd (h ▸ z.2.2) (mul_canonicalRep_mul_not_mem hσ (mul_mem z'.2.2 hc₀) u'.2)
    · rw [key] at h
      exact absurd (h ▸ z'.2.2) (mul_canonicalRep_mul_not_mem hσ (mul_mem z.2.2 hc₀) u.2)
    · rw [key, key] at h
      obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_canonicalRep_mul_eq hσ (mul_mem z.2.2 hc₀)
        (mul_mem z'.2.2 hc₀) u.2 u'.2 h
      rw [Subtype.ext (mul_right_cancel h1), Subtype.ext h2]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Finite.card_option] at this
  linarith

theorem le_or_relIndex_eq [Finite K] (hσ : Function.Surjective σ) {b : Fin t.foldedTag.rank}
    {H : Subgroup (ModGL t.tag K)} (hUH : graphFixedPosUnipotent t K σ ≤ H)
    (hHP : H ≤ graphFixedParabolic t K σ {b}) :
    H ≤ graphFixedRootBorel t K σ ∨ (graphFixedRootBorel t K σ).relIndex H =
      1 + Nat.card (graphFixedInversionUnipotent t K σ (t.orbitReflection b)) := by
  have : Finite (ModGL t.tag K) := finite_modGL
  by_cases hHB : H ≤ graphFixedRootBorel t K σ
  · exact Or.inl hHB
  right
  have h1 := card_inf_mul_le_card hσ hUH hHP hHB
  have h2 := Subgroup.relIndex_mul_card (graphFixedRootBorel t K σ) H
  have h3 := Subgroup.relIndex_mul_card (graphFixedRootBorel t K σ)
    (graphFixedParabolic t K σ {b})
  rw [inf_eq_left.2 (graphFixedRootBorel_le_graphFixedParabolic t K σ {b}),
    card_graphFixedParabolic_singleton hσ b] at h3
  have hB0 : 0 < Nat.card (graphFixedRootBorel t K σ) := Nat.card_pos
  have h3' : (graphFixedRootBorel t K σ).relIndex (graphFixedParabolic t K σ {b}) =
      1 + Nat.card (graphFixedInversionUnipotent t K σ (t.orbitReflection b)) :=
    Nat.eq_of_mul_eq_mul_right hB0 (by rw [h3, mul_comm])
  have h4 := Subgroup.relIndex_le_of_le_right hHP (by rw [h3']; omega)
  rw [inf_comm] at h2
  have hI0 : 0 < Nat.card (H ⊓ graphFixedRootBorel t K σ : Subgroup (ModGL t.tag K)) :=
    Nat.card_pos
  have h5 : 1 + Nat.card (graphFixedInversionUnipotent t K σ (t.orbitReflection b)) ≤
      (graphFixedRootBorel t K σ).relIndex H := by
    rw [← h2, mul_comm] at h1
    exact Nat.le_of_mul_le_mul_right h1 hI0
  omega

end Cells'

end Cells

section Borel


variable {t : TwistTag} {K : Type} [Field K] [Finite K] {σ : K →+* K}

theorem eq_one_of_mem_graphFixedRootBorel_of_pow_three [CharP K 2]
    (hσ : Function.Surjective σ) (hK : (Nat.card K - 1) % 3 = 1) {x : ModGL t.tag K}
    (hx : x ∈ graphFixedRootBorel t K σ) (h3 : x ^ 3 = 1) : x = 1 := by
  have hU := pow_card_sub_one_mem_graphFixedPosUnipotent hσ hx
  have hpow : x ^ (Nat.card K - 1) = x := by
    rw [← Nat.div_add_mod (Nat.card K - 1) 3, hK, pow_add, pow_mul, h3, one_pow, one_mul,
      pow_one]
  rw [hpow] at hU
  have hP : IsPGroup 2 (graphFixedPosUnipotent t K σ) :=
    (isPGroup_posUnipotent 2 t.tag).to_le inf_le_left
  obtain ⟨k, hk⟩ := hP ⟨x, hU⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h1
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem not_three_dvd_card_graphFixedRootBorel [CharP K 2] (hσ : Function.Surjective σ)
    (hK : (Nat.card K - 1) % 3 = 1) : ¬ 3 ∣ Nat.card (graphFixedRootBorel t K σ) := by
  have : Finite (ModGL t.tag K) := finite_modGL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have h1 : (x : ModGL t.tag K) = 1 :=
    eq_one_of_mem_graphFixedRootBorel_of_pow_three hσ hK x.2
      (by rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one])
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  norm_num at hx

theorem exists_orderOf_eq_nine_mem_graphFixedParabolic [CharP K 2] (b : Fin t.foldedTag.rank)
    (hb : Nat.card (orbitField t K σ b) = 8) :
    ∃ g ∈ graphFixedParabolic t K σ {b}, orderOf g = 9 := by
  obtain ⟨R, hRu, -, -, hRW, hN, -, -, hker, -⟩ := exceptional_fixed_rank_one_central_image t K σ b
  have h2 : (2 : orbitField t K σ b) = 0 := Subtype.ext (by
    change (2 : K) = 0
    exact CharTwo.two_eq_zero)
  obtain ⟨s, hs⟩ := exists_cube_add_add_one_eq_zero h2 hb
  have hinj : Function.Injective R := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl, hgl⟩ := hker g hg
    have hl1 : (l : orbitField t K σ b) = 1 := by
      have h0 : ((l : orbitField t K σ b) - 1) ^ 2 = 0 := by
        linear_combination hl + (1 - (l : orbitField t K σ b)) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.1 h0)
    refine Subtype.ext ?_
    rw [hgl, hl1, one_smul]
    rfl
  refine ⟨R (uSL s * WSL), ?_, ?_⟩
  · rw [map_mul, hRu, hRW, hN]
    exact mul_mem (graphFixedRootBorel_le_graphFixedParabolic t K σ {b}
      (graphFixedPosUnipotent_le_graphFixedRootBorel (orbitX_mem_graphFixedPosUnipotent t σ b s)))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨b, rfl, rfl⟩))
  · rw [orderOf_injective R hinj, orderOf_uSL_mul_WSL h2 hs]

end Borel

theorem card_sub_one_mod_three {K : Type} {n : ℕ} (hn : Odd n) (hK : Nat.card K = (2 ^ n) ^ 3) :
    (Nat.card K - 1) % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h : (2 ^ (2 * m + 1)) ^ 3 % 3 = 2 := by
    rw [← pow_mul, show (2 * m + 1) * 3 = 2 * (3 * m + 1) + 1 by ring, pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ (2 ^ (2 * m + 1)) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  rw [hK]
  omega

section Triality


variable {K : Type} [Field K]

theorem card_graphFixedInversionUnipotent_D4 (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n))
    (b : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom
      (TwistTag.D4.orbitReflection b)) = (2 ^ n) ^ (TwistTag.D4.orbit b).card := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedInversionUnipotent σ.surjective
    (CFSG.Timmesfeld.ExceptionalOrders.card_orbitField Nat.prime_two hn hK hσc)
    (TwistTag.D4.orbitReflection_mem b), length_orbitReflection]

theorem even_and_le_graphFixedRootBorel [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n))
    {Q H P : Subgroup (ModGL TwistTag.D4.tag K)}
    (hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q)
    (hQC : Q ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hQ : Q ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hHQ : H ≤ Q)
    (hUH : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ H)
    (hH : Nat.card H = 9 * Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    (hPH : P ≤ H) (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    Even n ∧ H ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra h
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hP
    norm_num at hP
  have hQJ := (fixed_Borel_overgroup_classification TwistTag.D4 K σ Q hBQ hQC).1
  obtain ⟨b, hJb⟩ : ∃ b : Fin TwistTag.D4.foldedTag.rank,
      {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈ Q} ⊆
        {b} := by
    obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.foldedTag.rank,
        canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∉ Q := by
      by_contra h
      have hJ : {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection a) ∈ Q} = Set.univ :=
        Set.eq_univ_of_forall fun a => by
          by_contra ha
          exact h ⟨a, ha⟩
      apply hQ
      rw [hQJ, hJ]
      exact (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.2
    have ha2 : a.val < 2 := a.2
    refine ⟨⟨1 - a.val, by change 1 - a.val < 2; omega⟩, fun j hj => ?_⟩
    have hja : j ≠ a := fun e => ha (e ▸ hj)
    have hj2 : j.val < 2 := j.2
    rw [Set.mem_singleton_iff, Fin.ext_iff]
    rw [Ne, Fin.ext_iff] at hja
    change j.val = 1 - a.val
    omega
  have hHb : H ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {b} :=
    hHQ.trans (hQJ.le.trans (((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 _ {b}).2
      hJb))
  have hUrel : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).relIndex H = 9 := by
    have h := Subgroup.relIndex_mul_card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hBdvd : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex H ∣ 9 :=
    hUrel ▸ Subgroup.relIndex_dvd_of_le_left H graphFixedPosUnipotent_le_graphFixedRootBorel
  rcases le_or_relIndex_eq hσ hUH hHb with hHB | hrel
  ·
    refine ⟨?_, hHB⟩
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exact absurd (eq_one_of_mem_graphFixedRootBorel_of_pow_three hσ
        (card_sub_one_mod_three ho hK) (hHB (hPH hx₀)) (hexp x₀ hx₀)) hx₀1
  · exfalso
    rw [hrel, card_graphFixedInversionUnipotent_D4 σ hn hK hσc b] at hBdvd
    have hd : (TwistTag.D4.orbit b).card = 3 ∨ (TwistTag.D4.orbit b).card = 1 := by
      have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
          (TwistTag.D4.orbit c).card = 3 ∨ (TwistTag.D4.orbit c).card = 1 := by decide
      exact this b
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show 1 + (2 ^ n) ^ (TwistTag.D4.orbit b).card ∣ 3 ^ 2 by norm_num; exact hBdvd)
    rw [← pow_mul] at hie
    have hpos : 0 < 2 ^ (n * (TwistTag.D4.orbit b).card) := by positivity
    have hcases : 2 ^ (n * (TwistTag.D4.orbit b).card) = 2 ^ 1 ∨
        2 ^ (n * (TwistTag.D4.orbit b).card) = 2 ^ 3 := by
      interval_cases i <;> simp at hie <;> omega
    have hodd : Odd n := by
      rcases hcases with h | h <;>
        have h' := Nat.pow_right_injective (le_refl 2) h <;>
        rcases hd with hd | hd <;> rw [hd] at h' <;>
        exact Nat.odd_iff.2 (by omega)
    have hB3 := not_three_dvd_card_graphFixedRootBorel (t := TwistTag.D4) hσ
      (card_sub_one_mod_three hodd hK)
    have hPb := card_graphFixedParabolic_singleton hσ b
    rw [card_graphFixedInversionUnipotent_D4 σ hn hK hσc b, ← pow_mul] at hPb
    have hPdvd : 9 ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b}) :=
      hP ▸ Subgroup.card_dvd_of_le (hPH.trans hHb)
    rcases hcases with h | h
    ·
      rw [h] at hPb
      rw [hPb] at hPdvd
      have h9 : 3 * 3 ∣ Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) * 3 := by
        simpa using hPdvd
      exact hB3 (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h9)
    ·
      have hLb : Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) = 8 := by
        rw [CFSG.Timmesfeld.ExceptionalOrders.card_orbitField Nat.prime_two hn hK hσc,
          ← pow_mul, h]
        norm_num
      obtain ⟨g, hg, hg9⟩ := exists_orderOf_eq_nine_mem_graphFixedParabolic b hLb
      rw [h] at hPb
      exact false_of_orderOf_eq_nine (hPH.trans hHb) hP hexp
        (by rw [hPb]; norm_num; ring) hB3 hg hg9

end Triality

end CFSG.Quasithin.F134.LieD4
