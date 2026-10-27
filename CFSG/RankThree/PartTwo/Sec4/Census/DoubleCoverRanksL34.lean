module

public import CFSG.RankThree.PartTwo.Census.TransitiveLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.KFacts.L34CenterProof
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace DoubleCoverRanksTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement IsMulCommutative

section SL

variable {K : Type} [Field K]

@[expose] def uSL (a b : K) : SpecialLinearGroup (Fin 3) K := rootElt 0 2 a * rootElt 1 2 b

theorem uSL_mul (a b c d : K) : uSL a b * uSL c d = uSL (a + c) (b + d) := by
  have h : rootElt (1 : Fin 3) 2 b * rootElt 0 2 c = rootElt 0 2 c * rootElt 1 2 b :=
    rootElt_mul_comm (by decide) (by decide) b c
  simp only [uSL, rootElt_add, mul_assoc]
  rw [← mul_assoc (rootElt 1 2 b), h]
  simp only [mul_assoc]

theorem uSL_zero : uSL (0 : K) 0 = 1 := by
  rw [uSL, rootElt_zero, rootElt_zero, mul_one]

theorem uSL_zero_right (a : K) : uSL a 0 = rootElt 0 2 a := by
  rw [uSL, rootElt_zero, mul_one]

theorem uSL_apply_zero_two (a b : K) : (uSL a b : Matrix (Fin 3) (Fin 3) K) 0 2 = a := by
  simp [uSL, coe_rootElt_of_ne, Matrix.mul_apply, Fin.sum_univ_three, transvection,
    Matrix.single_apply, Matrix.one_apply]

theorem uSL_apply_one_two (a b : K) : (uSL a b : Matrix (Fin 3) (Fin 3) K) 1 2 = b := by
  simp [uSL, coe_rootElt_of_ne, Matrix.mul_apply, transvection, Matrix.single_apply,
    Matrix.one_apply]

theorem eq_zero_of_uSL_mem_center {a b : K}
    (h : uSL a b ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : a = 0 ∧ b = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h1 := congrFun (congrFun hr 0) 2
  have h2 := congrFun (congrFun hr 1) 2
  rw [uSL_apply_zero_two] at h1
  rw [uSL_apply_one_two] at h2
  simp only [scalar_apply, diagonal_apply] at h1 h2
  exact ⟨h1.symm.trans (ite_eq_right (by decide)), h2.symm.trans (ite_eq_right (by decide))⟩

theorem diagElt_conj_uSL (s : Fin 3 → K) (hs : ∏ i, s i = 1) (a b : K) :
    diagElt s hs * uSL a b * (diagElt s hs)⁻¹ = uSL (s 0 * (s 2)⁻¹ * a) (s 1 * (s 2)⁻¹ * b) := by
  rw [uSL, uSL, show diagElt s hs * (rootElt 0 2 a * rootElt 1 2 b) * (diagElt s hs)⁻¹ =
      (diagElt s hs * rootElt 0 2 a * (diagElt s hs)⁻¹) *
        (diagElt s hs * rootElt 1 2 b * (diagElt s hs)⁻¹) by group,
    diagElt_conj_rootElt, diagElt_conj_rootElt]

theorem lower_conj_uSL (c a b : K) :
    rootElt 1 0 c * uSL a b * (rootElt 1 0 c)⁻¹ = uSL a (c * a + b) := by
  have h1 : rootElt (1 : Fin 3) 0 c * rootElt 0 2 a * (rootElt 1 0 c)⁻¹ =
      rootElt 1 2 (c * a) * rootElt 0 2 a := by
    have h := commutatorElement_rootElt (K := K) (n := 3) (i := 1) (j := 0) (l := 2)
      (by decide) (by decide) (by decide) c a
    rw [commutatorElement_def] at h
    rw [← h]
    group
  have h2 : rootElt (1 : Fin 3) 0 c * rootElt 1 2 b * (rootElt 1 0 c)⁻¹ = rootElt 1 2 b := by
    rw [rootElt_mul_comm (K := K) (i := (1 : Fin 3)) (j := 0) (k := 1) (l := 2) (by decide)
      (by decide), mul_inv_cancel_right]
  have h3 : rootElt (1 : Fin 3) 2 (c * a) * rootElt 0 2 a =
      rootElt 0 2 a * rootElt 1 2 (c * a) :=
    rootElt_mul_comm (by decide) (by decide) _ _
  rw [uSL, uSL, show rootElt 1 0 c * (rootElt 0 2 a * rootElt 1 2 b) * (rootElt 1 0 c)⁻¹ =
      (rootElt 1 0 c * rootElt 0 2 a * (rootElt 1 0 c)⁻¹) *
        (rootElt 1 0 c * rootElt 1 2 b * (rootElt 1 0 c)⁻¹) by group, h1, h2, h3,
    rootElt_add, mul_assoc]

theorem upper_conj_uSL (c a b : K) :
    rootElt 0 1 c * uSL a b * (rootElt 0 1 c)⁻¹ = uSL (a + c * b) b := by
  have h1 : rootElt (0 : Fin 3) 1 c * rootElt 0 2 a * (rootElt 0 1 c)⁻¹ = rootElt 0 2 a := by
    rw [rootElt_mul_comm (K := K) (i := (0 : Fin 3)) (j := 1) (k := 0) (l := 2) (by decide)
      (by decide), mul_inv_cancel_right]
  have h2 : rootElt (0 : Fin 3) 1 c * rootElt 1 2 b * (rootElt 0 1 c)⁻¹ =
      rootElt 0 2 (c * b) * rootElt 1 2 b := by
    have h := commutatorElement_rootElt (K := K) (n := 3) (i := 0) (j := 1) (l := 2)
      (by decide) (by decide) (by decide) c b
    rw [commutatorElement_def] at h
    rw [← h]
    group
  rw [uSL, uSL, show rootElt 0 1 c * (rootElt 0 2 a * rootElt 1 2 b) * (rootElt 0 1 c)⁻¹ =
      (rootElt 0 1 c * rootElt 0 2 a * (rootElt 0 1 c)⁻¹) *
        (rootElt 0 1 c * rootElt 1 2 b * (rootElt 0 1 c)⁻¹) by group, h1, h2, rootElt_add,
    mul_assoc]

theorem exists_conj_uSL [CharP K 2] {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 3) K, g * uSL 1 0 * g⁻¹ = uSL a b := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    refine ⟨rootElt 0 1 b⁻¹ * rootElt 1 0 b, ?_⟩
    rw [_root_.mul_inv_rev, show rootElt 0 1 b⁻¹ * rootElt 1 0 b * uSL 1 0 *
        ((rootElt 1 0 b)⁻¹ * (rootElt 0 1 b⁻¹)⁻¹) =
        rootElt 0 1 b⁻¹ * (rootElt 1 0 b * uSL 1 0 * (rootElt 1 0 b)⁻¹) *
          (rootElt 0 1 b⁻¹)⁻¹ by group, lower_conj_uSL, upper_conj_uSL, ha, mul_one, add_zero,
      inv_mul_cancel₀ hb, CharTwo.add_self_eq_zero]
  · have hs : ∏ i, (![a, a⁻¹, 1] : Fin 3 → K) i = 1 := by
      simp [Fin.prod_univ_three, ha]
    refine ⟨rootElt 1 0 (b * a⁻¹) * diagElt _ hs, ?_⟩
    rw [_root_.mul_inv_rev, show rootElt 1 0 (b * a⁻¹) * diagElt _ hs * uSL 1 0 *
        ((diagElt _ hs)⁻¹ * (rootElt 1 0 (b * a⁻¹))⁻¹) =
        rootElt 1 0 (b * a⁻¹) * (diagElt _ hs * uSL 1 0 * (diagElt _ hs)⁻¹) *
          (rootElt 1 0 (b * a⁻¹))⁻¹ by group, diagElt_conj_uSL, lower_conj_uSL]
    simp [ha]

end SL

section Proj

variable (K : Type) [Field K]

@[expose] noncomputable def toProjSL : SpecialLinearGroup (Fin 3) K →* projSL 3 K :=
  SpecialLinearGroup.toPGL.codRestrict (projSL 3 K) fun g => by
    rw [CFSG.RankThree.PartTwo.KFacts.L34.projSL_eq_range_toPGL]
    exact ⟨g, rfl⟩

variable {K}

theorem toProjSL_surjective : Function.Surjective (toProjSL K) := by
  rintro ⟨x, hx⟩
  rw [CFSG.RankThree.PartTwo.KFacts.L34.projSL_eq_range_toPGL] at hx
  obtain ⟨g, rfl⟩ := hx
  exact ⟨g, rfl⟩

theorem toProjSL_eq_one_iff {g : SpecialLinearGroup (Fin 3) K} :
    toProjSL K g = 1 ↔ g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  rw [← SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

@[expose] noncomputable def uHom : Multiplicative (K × K) →* projSL 3 K where
  toFun v := toProjSL K (uSL (Multiplicative.toAdd v).1 (Multiplicative.toAdd v).2)
  map_one' := by simp [uSL_zero]
  map_mul' v w := by simp [← map_mul, uSL_mul]

theorem uHom_apply (v : Multiplicative (K × K)) :
    uHom v = toProjSL K (uSL (Multiplicative.toAdd v).1 (Multiplicative.toAdd v).2) :=
  rfl

theorem uHom_injective : Function.Injective (uHom (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [MonoidHom.mem_ker, uHom_apply, toProjSL_eq_one_iff] at hv
  obtain ⟨h1, h2⟩ := eq_zero_of_uSL_mem_center hv
  rw [Subgroup.mem_bot]
  exact Multiplicative.toAdd.injective (Prod.ext h1 h2)

theorem card_range_uHom : Nat.card (uHom (K := K)).range = Nat.card K * Nat.card K := by
  rw [← Nat.card_congr (MonoidHom.ofInjective uHom_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod]

theorem sq_eq_one_of_mem_range_uHom [CharP K 2] {x : projSL 3 K} (hx : x ∈ (uHom (K := K)).range) :
    x ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [← map_pow]
  have hv : v ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)
  rw [hv, map_one]

theorem exists_conj_of_mem_range_uHom [CharP K 2] {x : projSL 3 K}
    (hx : x ∈ (uHom (K := K)).range) (hx1 : x ≠ 1) :
    ∃ g : projSL 3 K, g * uHom (Multiplicative.ofAdd ((1 : K), (0 : K))) * g⁻¹ = x := by
  obtain ⟨v, rfl⟩ := hx
  have hab : (Multiplicative.toAdd v).1 ≠ 0 ∨ (Multiplicative.toAdd v).2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx1
    have hv : v = 1 := Multiplicative.toAdd.injective (Prod.ext h.1 h.2)
    rw [hv, map_one]
  obtain ⟨g, hg⟩ := exists_conj_uSL hab
  refine ⟨toProjSL K g, ?_⟩
  rw [uHom_apply, uHom_apply, ← map_inv, ← map_mul, ← map_mul, toAdd_ofAdd, hg]

@[expose] noncomputable def rootHom : Multiplicative K →* projSL 3 K :=
  (toProjSL K).comp
    { toFun := fun a => rootElt 0 2 (Multiplicative.toAdd a)
      map_one' := rootElt_zero 0 2
      map_mul' := fun _ _ => rootElt_add 0 2 _ _ }

theorem rootHom_apply (a : Multiplicative K) :
    rootHom a = toProjSL K (rootElt 0 2 (Multiplicative.toAdd a)) :=
  rfl

theorem rootHom_mem_range_uHom (a : Multiplicative K) :
    rootHom a ∈ (uHom (K := K)).range :=
  ⟨Multiplicative.ofAdd (Multiplicative.toAdd a, 0), by
    rw [uHom_apply, rootHom_apply, toAdd_ofAdd, uSL_zero_right]⟩

theorem card_range_rootHom : Nat.card (rootHom (K := K)).range = Nat.card K := by
  have hinj : Function.Injective (rootHom (K := K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, rootHom_apply, ← uSL_zero_right, toProjSL_eq_one_iff] at ha
    rw [Subgroup.mem_bot]
    exact Multiplicative.toAdd.injective (eq_zero_of_uSL_mem_center ha).1
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr Multiplicative.toAdd]

end Proj

section Lift

variable {K : Type} [Field K] {J : Type} [Group J] {φ : J →* projSL 3 K}
  (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center J)
include hφ hker

theorem commute_lift_rootHom {y y' : J} (hy : φ y ∈ (rootHom (K := K)).range)
    (hy' : φ y' ∈ (rootHom (K := K)).range) : y * y' = y' * y := by
  obtain ⟨a, ha⟩ := hy
  obtain ⟨b, hb⟩ := hy'
  obtain ⟨p, hp⟩ := hφ (toProjSL K (rootElt 0 1 (Multiplicative.toAdd b)))
  obtain ⟨q, hq⟩ := hφ (toProjSL K (rootElt 1 2 (1 : K)))
  refine TransitiveLift.commute_of_map_eq_commutatorElement hker (p := p) (q := q) ?_ ?_ ?_
  · rw [← ha, hp, rootHom_apply, Commute, SemiconjBy, ← map_mul, ← map_mul,
      rootElt_mul_comm (K := K) (i := (0 : Fin 3)) (j := 2) (k := 0) (l := 1) (by decide)
        (by decide)]
  · rw [← ha, hq, rootHom_apply, Commute, SemiconjBy, ← map_mul, ← map_mul,
      rootElt_mul_comm (K := K) (i := (0 : Fin 3)) (j := 2) (k := 1) (l := 2) (by decide)
        (by decide)]
  · rw [← hb, map_commutatorElement, hp, hq, rootHom_apply, ← map_commutatorElement,
      commutatorElement_rootElt (K := K) (n := 3) (i := 0) (j := 1) (l := 2) (by decide)
        (by decide) (by decide), mul_one]

variable [CharP K 2] (hK : 3 ≤ Nat.card K)
include hK

theorem exists_sq_eq_sq_E {y : J} (hy : φ y ∈ (uHom (K := K)).range) :
    ∃ c : J, φ c = 1 ∧ y ^ 2 = c ^ 2 := by
  refine TransitiveLift.exists_sq_eq_sq hφ hker (fun x hx => sq_eq_one_of_mem_range_uHom hx) ?_
    (fun x hx hx1 => exists_conj_of_mem_range_uHom hx hx1) hy
  rw [card_range_uHom]
  nlinarith

theorem exists_commutator_eq_sq_E {y y' : J} (hy : φ y ∈ (uHom (K := K)).range)
    (hy' : φ y' ∈ (uHom (K := K)).range) : ∃ c : J, φ c = 1 ∧ ⁅y, y'⁆ = c ^ 2 := by
  refine TransitiveLift.exists_commutator_eq_sq hφ hker
    (fun x hx => sq_eq_one_of_mem_range_uHom hx) ?_
    (fun x hx hx1 => exists_conj_of_mem_range_uHom hx hx1) hy hy'
  rw [card_range_uHom]
  nlinarith

end Lift

section Center

variable {K : Type} [Field K] [CharP K 2] {J : Type} [Group J] [Finite J]
  {φ : J →* projSL 3 K} (hφ : Function.Surjective φ) (hker : φ.ker = Subgroup.center J)
include hφ hker

theorem four_le_pRank_of_involutions (hK : Nat.card K = 4) {z₁ z₂ : J}
    (hz₁ : z₁ ∈ Subgroup.center J) (hz₂ : z₂ ∈ Subgroup.center J) (h₁ : z₁ ^ 2 = 1)
    (h₂ : z₂ ^ 2 = 1) (h₁₁ : z₁ ≠ 1) (h₂₁ : z₂ ≠ 1) (h₁₂ : z₁ ≠ z₂) : 4 ≤ CFSG.pRank 2 J := by
  have hk : φ.ker ≤ Subgroup.center J := hker.le
  have hmem : ∀ z ∈ Subgroup.center J, φ z = 1 := fun z hz => by
    rw [← MonoidHom.mem_ker, hker]; exact hz
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hφ hk
    (W := (rootHom (K := K)).range) (fun y y' hy hy' => commute_lift_rootHom hφ hk hy hy')
    (fun y hy => by
      obtain ⟨a, ha⟩ := hy
      exact exists_sq_eq_sq_E hφ hk (by omega) (ha ▸ rootHom_mem_range_uHom a))
  have hΩ : 3 ≤ Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := by
    classical
    have := Fintype.ofFinite {c : J // φ c = 1 ∧ c ^ 2 = 1}
    rw [Nat.card_eq_fintype_card]
    have hs : ({⟨1, map_one φ, one_pow 2⟩, ⟨z₁, hmem z₁ hz₁, h₁⟩, ⟨z₂, hmem z₂ hz₂, h₂⟩} :
        Finset {c : J // φ c = 1 ∧ c ^ 2 = 1}).card = 3 := by
      refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
      · exact fun h => h₁₁ (congrArg Subtype.val h).symm
      · exact fun h => h₂₁ (congrArg Subtype.val h).symm
      · exact fun h => h₁₂ (congrArg Subtype.val h)
    calc (3 : ℕ) = _ := hs.symm
      _ ≤ _ := Finset.card_le_univ _
  rw [card_range_rootHom, hK] at hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hr4 : 4 ≤ r := by
    by_contra h
    push Not at h
    have : 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact TransitiveLift.le_pRank_of_card hA (k := 4) (by
    rw [hr]; exact Nat.pow_le_pow_right (by norm_num) hr4)

theorem five_le_pRank_of_sq_eq_one (hK : Nat.card K = 4) [Nontrivial (Subgroup.center J)]
    (hZ : ∀ z ∈ Subgroup.center J, z ^ 2 = 1) : 5 ≤ CFSG.pRank 2 J := by
  have hk : φ.ker ≤ Subgroup.center J := hker.le
  have hsq1 : ∀ c, φ c = 1 → c ^ 2 = 1 := fun c hc => hZ c (hk hc)
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hφ hk
    (W := (uHom (K := K)).range)
    (fun y y' hy hy' => by
      obtain ⟨c, hc, h⟩ := exists_commutator_eq_sq_E hφ hk (by omega) hy hy'
      rw [hsq1 c hc, commutatorElement_eq_one_iff_mul_comm] at h
      exact h)
    (fun y hy => exists_sq_eq_sq_E hφ hk (by omega) hy)
  have hΩ : Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} = Nat.card (Subgroup.center J) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨c.1, hk c.2.1⟩
        invFun := fun c => ⟨c.1, ?_, hZ c.1 c.2⟩
        left_inv := fun c => rfl
        right_inv := fun c => rfl }
    rw [← MonoidHom.mem_ker, hker]
    exact c.2
  have h2 : 2 ≤ Nat.card (Subgroup.center J) := Finite.one_lt_card
  rw [card_range_uHom, hK, hΩ] at hcard
  exact TransitiveLift.le_pRank_of_card hA (k := 5) (by rw [hcard]; omega)

end Center

theorem isCyclic_card_four {Z : Type*} [CommGroup Z] [Finite Z] (hexp : ∀ y : Z, y ^ 4 = 1)
    (huniq : ∀ a b : Z, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b) {z : Z}
    (hz : z ^ 2 ≠ 1) : IsCyclic Z ∧ Nat.card Z = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf z = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := z) (by simpa using hz)
      (by simpa using hexp z)
    simpa using h
  have hz4 : (z ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hexp z
  have hmem : ∀ y : Z, y ∈ Subgroup.zpowers z := by
    intro y
    have hy4 : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hexp y
    by_cases hy2 : y ^ 2 = 1
    · by_cases hy1 : y = 1
      · rw [hy1]; exact Subgroup.one_mem _
      · rw [huniq y (z ^ 2) hy2 hz4 hy1 hz]
        exact Subgroup.npow_mem_zpowers z 2
    · have hyz : y ^ 2 = z ^ 2 := huniq _ _ hy4 hz4 hy2 hz
      have hw : (y * z⁻¹) ^ 2 = 1 := by rw [mul_pow, hyz, inv_pow, mul_inv_cancel]
      have hy : y = y * z⁻¹ * z := by rw [inv_mul_cancel_right]
      by_cases hw1 : y * z⁻¹ = 1
      · rw [hy, hw1, one_mul]; exact Subgroup.mem_zpowers z
      · rw [hy, huniq _ (z ^ 2) hw hz4 hw1 hz]
        exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers z 2) (Subgroup.mem_zpowers z)
  have htop : Subgroup.zpowers z = ⊤ := eq_top_iff.mpr fun y _ => hmem y
  have hcard : Nat.card Z = 4 := by
    rw [← Subgroup.card_top, ← htop, Nat.card_zpowers, hord]
  exact ⟨isCyclic_of_orderOf_eq_card z (by rw [hord, hcard]), hcard⟩

theorem pow_four_eq_one_of_mem_center
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J)
    (hZ2 : IsPGroup 2 (Subgroup.center J))
    (e : J ⧸ Subgroup.center J ≃* projSL 3 (GaloisField 2 2)) {z : J}
    (hz : z ∈ Subgroup.center J) : z ^ 4 = 1 := by
  have : Group.IsPerfect J := hJ
  set q := QuotientGroup.mk' (Subgroup.center J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker ≤ Subgroup.center J := (QuotientGroup.ker_mk' _).le
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hk
  have hzk : z ∈ q.ker := by rw [QuotientGroup.ker_mk']; exact hz
  rw [← hmap] at hzk
  obtain ⟨m, hm, rfl⟩ := hzk
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four _
    (CFSG.RankThree.PartTwo.KFacts.L34Center.blueprint_lieModel_of_models
      (CFSG.RankThree.PartTwo.KFacts.KS44.lieModel_of_mulEquiv_projSL e))
  let eM' := (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.trans eM
  have h12 : (⟨m, hm⟩ : CFSG.RankThree.PerfectCover.hopfMultiplier _) ^ 12 = 1 := by
    apply eM'.injective
    rw [map_pow, map_one]
    generalize eM' ⟨m, hm⟩ = x
    revert x
    decide
  have h12z : (CFSG.RankThree.PerfectCover.hopfLift q hq hk m) ^ 12 = 1 := by
    rw [← map_pow]
    have := congrArg Subtype.val h12
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [this, map_one]
  obtain ⟨k, hk2⟩ := hZ2 ⟨_, hz⟩
  have hk2' : (CFSG.RankThree.PerfectCover.hopfLift q hq hk m) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk2
    simpa using this
  set w := CFSG.RankThree.PerfectCover.hopfLift q hq hk m
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk2')
  have hj12 : 2 ^ j ∣ 12 := hj ▸ orderOf_dvd_of_pow_eq_one h12z
  have hj2 : j ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ∣ 12 := (Nat.pow_dvd_pow 2 h).trans hj12
    norm_num at this
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ (Nat.pow_dvd_pow 2 hj2))

theorem psl34_center :
    ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
      CFSG.pRank 2 J = 3 → IsCyclic (Subgroup.center J) ∧ Nat.card (Subgroup.center J) = 4 := by
  intro J _ _ ⟨hq, hZ2, hZnt, ⟨e⟩⟩ hr
  have hK : Nat.card (GaloisField 2 2) = 4 :=
    CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two
  let φ : J →* projSL 3 (GaloisField 2 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  by_cases hA : ∃ z₁ ∈ Subgroup.center J, ∃ z₂ ∈ Subgroup.center J, z₁ ^ 2 = 1 ∧ z₂ ^ 2 = 1 ∧
      z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₁ ≠ z₂
  · obtain ⟨z₁, hz₁, z₂, hz₂, h₁, h₂, h₁₁, h₂₁, h₁₂⟩ := hA
    have := four_le_pRank_of_involutions hφ hker hK hz₁ hz₂ h₁ h₂ h₁₁ h₂₁ h₁₂
    omega
  by_cases hB : ∀ z ∈ Subgroup.center J, z ^ 2 = 1
  · have := five_le_pRank_of_sq_eq_one hφ hker hK hB
    omega
  push Not at hA hB
  obtain ⟨z, hz, hz2⟩ := hB
  refine isCyclic_card_four (Z := Subgroup.center J) (fun y => Subtype.ext ?_) ?_
    (z := ⟨z, hz⟩) (fun h => hz2 (congrArg Subtype.val h))
  · exact pow_four_eq_one_of_mem_center hq.1 hZ2 e y.2
  · intro a b ha hb ha1 hb1
    exact Subtype.ext (hA a a.2 b b.2 (congrArg Subtype.val ha) (congrArg Subtype.val hb)
      (fun h => ha1 (Subtype.ext h)) (fun h => hb1 (Subtype.ext h)))

end DoubleCoverRanksTwo

end CFSG.RankThree.PartTwo.Sec4.Census
