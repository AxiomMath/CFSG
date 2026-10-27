module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.LocalAnalysis.WeakClosure81.SevenFour
import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Timmesfeld.Bridge.Asc72Triangle
import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Unitary QuadraticMap

@[expose] def orthTriangleInvariant {K : Type} [Field K] (Q₀ : QuadraticForm K (Fin 4 → K))
    (x y z : Fin 4 → K) : K :=
  polar Q₀ x y ^ 2 + polar Q₀ y z ^ 2 + polar Q₀ z x ^ 2 +
    polar Q₀ x y * polar Q₀ y z * polar Q₀ z x

@[expose] def orthTriangleVec {K : Type} [Field K] (Q₀ : QuadraticForm K (Fin 4 → K))
    (x y z : Fin 4 → K) : Fin 4 → K :=
  (polar Q₀ x y)⁻¹ • (polar Q₀ y z • x + polar Q₀ z x • y) + z

@[expose] def triangleProduct {K F : Type} [Field F] (σ : F ≃+* F)
    (a : (Fin 4 → K) → (Fin 4 → F)) (x y z : Fin 4 → K) : F :=
  herm σ (a x) (a y) * herm σ (a y) (a z) * herm σ (a z) (a x)

theorem orthTriangleVec_spec {K : Type} [Field K] [CharP K 2] {Q₀ : QuadraticForm K (Fin 4 → K)}
    {x y z : Fin 4 → K} (hx : Q₀ x = 1) (hy : Q₀ y = 1) (hz : Q₀ z = 1)
    (hβ₁ : polar Q₀ x y ≠ 0) :
    polar Q₀ (orthTriangleVec Q₀ x y z) x = 0 ∧ polar Q₀ (orthTriangleVec Q₀ x y z) y = 0 ∧
      polar Q₀ (orthTriangleVec Q₀ x y z) z = 0 ∧
      Q₀ (orthTriangleVec Q₀ x y z) * polar Q₀ x y ^ 2 = orthTriangleInvariant Q₀ x y z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hself : ∀ v, polar Q₀ v v = 0 := fun v => by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hinv : (polar Q₀ x y)⁻¹ * polar Q₀ x y = 1 := inv_mul_cancel₀ hβ₁
  have hyx : polar Q₀ y x = polar Q₀ x y := polar_comm _ _ _
  have hzy : polar Q₀ z y = polar Q₀ y z := polar_comm _ _ _
  have hxz : polar Q₀ x z = polar Q₀ z x := polar_comm _ _ _
  simp only [orthTriangleVec, orthTriangleInvariant, polar_add_left, polar_smul_left,
    polar_smul_right, smul_eq_mul, hself, hyx, hzy, hxz,
    QuadraticMap.map_add Q₀, QuadraticMap.map_smul, hx, hy, hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination polar Q₀ z x * hinv + polar Q₀ z x * h2
  · linear_combination polar Q₀ y z * hinv + polar Q₀ y z * h2
  · linear_combination (polar Q₀ x y)⁻¹ * polar Q₀ y z * polar Q₀ z x * h2
  · linear_combination ((polar Q₀ x y)⁻¹ * polar Q₀ x y + 1) *
        (polar Q₀ y z ^ 2 + polar Q₀ z x ^ 2 + polar Q₀ x y * polar Q₀ y z * polar Q₀ z x) * hinv +
      (polar Q₀ x y)⁻¹ * polar Q₀ x y ^ 2 * polar Q₀ y z * polar Q₀ z x * h2

theorem exists_orthogonal_of_orthTriangleInvariant_ne_zero {K : Type} [Field K] [Finite K]
    [CharP K 2] {Q₀ : QuadraticForm K (Fin 4 → K)} {x y z : Fin 4 → K} (hx : Q₀ x = 1)
    (hy : Q₀ y = 1) (hz : Q₀ z = 1) (hβ₁ : polar Q₀ x y ≠ 0)
    (hg : orthTriangleInvariant Q₀ x y z ≠ 0) :
    ∃ w : Fin 4 → K, Q₀ w = 1 ∧ polar Q₀ w x = 0 ∧ polar Q₀ w y = 0 ∧ polar Q₀ w z = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := orthTriangleVec_spec hx hy hz hβ₁
  have hQw : Q₀ (orthTriangleVec Q₀ x y z) ≠ 0 := fun h => hg (by rw [← h4, h, zero_mul])
  obtain ⟨s, hs⟩ := surjective_frobenius K 2 (Q₀ (orthTriangleVec Q₀ x y z))
  rw [frobenius_def] at hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hQw (by rw [← hs]; ring)
  refine ⟨s⁻¹ • orthTriangleVec Q₀ x y z, ?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_smul, ← hs, smul_eq_mul]
    field_simp
  · rw [polar_smul_left, h1, smul_zero]
  · rw [polar_smul_left, h2, smul_zero]
  · rw [polar_smul_left, h3, smul_zero]

theorem exists_shift_orthTriangleInvariant_ne_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    {Q₀ : QuadraticForm K (Fin 4 → K)} (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hK4 : 4 ≤ Nat.card K) {x y z : Fin 4 → K} (hx : Q₀ x = 1) (hy : Q₀ y = 1) (hz : Q₀ z = 1)
    (hβ₁ : polar Q₀ x y ≠ 0) (hβ₂ : polar Q₀ y z ≠ 0) (hβ₃ : polar Q₀ z x ≠ 0)
    (hind : z ∉ Submodule.span K {x, y}) (hg : orthTriangleInvariant Q₀ x y z = 0) :
    ∃ z' : Fin 4 → K, Q₀ z' = 1 ∧ polar Q₀ z' x ≠ 0 ∧ polar Q₀ z' y ≠ 0 ∧
      polar Q₀ z' z ≠ 0 ∧ orthTriangleInvariant Q₀ x y z' ≠ 0 ∧
      orthTriangleInvariant Q₀ y z z' ≠ 0 ∧ orthTriangleInvariant Q₀ z x z' ≠ 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hinv : (polar Q₀ x y)⁻¹ * polar Q₀ x y = 1 := inv_mul_cancel₀ hβ₁
  have hs : polar Q₀ x y + polar Q₀ y z + polar Q₀ z x ≠ 0 := by
    intro hs
    have e : orthTriangleInvariant Q₀ x y z = polar Q₀ x y * polar Q₀ y z * polar Q₀ z x := by
      unfold orthTriangleInvariant
      linear_combination (polar Q₀ x y + polar Q₀ y z + polar Q₀ z x) * hs -
        (polar Q₀ x y * polar Q₀ y z + polar Q₀ y z * polar Q₀ z x +
          polar Q₀ z x * polar Q₀ x y) * h2
    rw [hg] at e
    exact mul_ne_zero (mul_ne_zero hβ₁ hβ₂) hβ₃ e.symm
  obtain ⟨t, ht0, ht1, ht2, ht3⟩ : ∃ t : K, t ≠ 0 ∧ t ^ 2 ≠ polar Q₀ x y ∧
      t ^ 2 ≠ polar Q₀ y z ∧ t ^ 2 ≠ polar Q₀ z x := by
    by_contra! h
    have hcov : ∀ u : K, u = 0 ∨ u = polar Q₀ x y ∨ u = polar Q₀ y z ∨ u = polar Q₀ z x := by
      intro u
      obtain ⟨r, hr⟩ := surjective_frobenius K 2 u
      rw [frobenius_def] at hr
      by_cases hu : u = 0
      · exact Or.inl hu
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hu (by rw [← hr]; ring)
      by_cases k1 : r ^ 2 = polar Q₀ x y
      · exact Or.inr (Or.inl (hr.symm.trans k1))
      by_cases k2 : r ^ 2 = polar Q₀ y z
      · exact Or.inr (Or.inr (Or.inl (hr.symm.trans k2)))
      exact Or.inr (Or.inr (Or.inr (hr.symm.trans (h r hr0 k1 k2))))
    have hcard : ∀ p q : K, (∀ u : K, u = 0 ∨ u = p ∨ u = q) → False := by
      intro p q hu
      let _ := Fintype.ofFinite K
      have hle : Fintype.card K ≤ 3 := by
        rw [← Finset.card_univ]
        calc (Finset.univ : Finset K).card ≤ ({0, p, q} : Finset K).card :=
              Finset.card_le_card fun u _ => by
                rcases hu u with h | h | h <;> simp [h]
          _ ≤ 3 := Finset.card_le_three
      rw [Nat.card_eq_fintype_card] at hK4
      omega
    rcases hcov (polar Q₀ x y + polar Q₀ y z + polar Q₀ z x) with h0 | h0 | h0 | h0
    · exact hs h0
    · have e : polar Q₀ y z = polar Q₀ z x := CharTwo.add_eq_zero.1 (by linear_combination h0)
      exact hcard (polar Q₀ x y) (polar Q₀ y z) fun u => by
        rcases hcov u with k | k | k | k
        exacts [Or.inl k, Or.inr (Or.inl k), Or.inr (Or.inr k), Or.inr (Or.inr (k.trans e.symm))]
    · have e : polar Q₀ x y = polar Q₀ z x := CharTwo.add_eq_zero.1 (by linear_combination h0)
      exact hcard (polar Q₀ x y) (polar Q₀ y z) fun u => by
        rcases hcov u with k | k | k | k
        exacts [Or.inl k, Or.inr (Or.inl k), Or.inr (Or.inr k), Or.inr (Or.inl (k.trans e.symm))]
    · have e : polar Q₀ x y = polar Q₀ y z := CharTwo.add_eq_zero.1 (by linear_combination h0)
      exact hcard (polar Q₀ x y) (polar Q₀ z x) fun u => by
        rcases hcov u with k | k | k | k
        exacts [Or.inl k, Or.inr (Or.inl k), Or.inr (Or.inl (k.trans e.symm)), Or.inr (Or.inr k)]
  obtain ⟨u₀, hu₀x, hu₀y, -⟩ :=
    PartFour.exists_polar_eq_map_eq_of_polar_ne_zero hQ₀ (by simp) hβ₁ t t 0
  obtain ⟨v, hvx, hvy, hzv⟩ : ∃ v, polar Q₀ v x = 0 ∧ polar Q₀ v y = 0 ∧ polar Q₀ z v ≠ 0 := by
    by_contra! h
    obtain ⟨α, β, hαβ⟩ := PartFour.exists_eq_smul_add_smul_of_forall_polar_eq_zero hQ₀ h
    exact hind (Submodule.mem_span_pair.2 ⟨α, β, hαβ.symm⟩)
  have hvz : polar Q₀ v z ≠ 0 := by rwa [polar_comm]
  obtain ⟨u₁, hu₁x, hu₁y, hu₁z⟩ :
      ∃ u₁, polar Q₀ u₁ x = t ∧ polar Q₀ u₁ y = t ∧ polar Q₀ u₁ z = t := by
    refine ⟨u₀ + ((t - polar Q₀ u₀ z) / polar Q₀ v z) • v, ?_, ?_, ?_⟩
    · rw [polar_add_left, polar_smul_left, hvx, smul_zero, add_zero, hu₀x]
    · rw [polar_add_left, polar_smul_left, hvy, smul_zero, add_zero, hu₀y]
    · rw [polar_add_left, polar_smul_left, smul_eq_mul, div_mul_cancel₀ _ hvz]
      ring
  obtain ⟨w, hwx, hwy, hwz, hQw, hp⟩ : ∃ w, polar Q₀ w x = 0 ∧ polar Q₀ w y = 0 ∧
      polar Q₀ w z = 0 ∧ Q₀ w = 0 ∧ polar Q₀ u₁ w ≠ 0 := by
    obtain ⟨hwx, hwy, hwz, hw⟩ := orthTriangleVec_spec hx hy hz hβ₁
    refine ⟨_, hwx, hwy, hwz, ?_, ?_⟩
    · rw [hg] at hw
      exact (mul_eq_zero.1 hw).resolve_right (pow_ne_zero 2 hβ₁)
    · intro h0
      have e : polar Q₀ u₁ (orthTriangleVec Q₀ x y z) * polar Q₀ x y =
          t * (polar Q₀ x y + polar Q₀ y z + polar Q₀ z x) := by
        simp only [orthTriangleVec, polar_add_right, polar_smul_right, smul_eq_mul, hu₁x, hu₁y,
          hu₁z]
        linear_combination (polar Q₀ y z * t + polar Q₀ z x * t) * hinv
      rw [h0, zero_mul] at e
      exact mul_ne_zero ht0 hs e.symm
  obtain ⟨z', hz', hz'x, hz'y, hz'z⟩ : ∃ z', Q₀ z' = 1 ∧ polar Q₀ z' x = t ∧
      polar Q₀ z' y = t ∧ polar Q₀ z' z = t := by
    refine ⟨u₁ + ((1 - Q₀ u₁) / polar Q₀ u₁ w) • w, ?_, ?_, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q₀, QuadraticMap.map_smul, hQw, smul_zero, add_zero,
        polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hp]
      ring
    · rw [polar_add_left, polar_smul_left, hwx, smul_zero, add_zero, hu₁x]
    · rw [polar_add_left, polar_smul_left, hwy, smul_zero, add_zero, hu₁y]
    · rw [polar_add_left, polar_smul_left, hwz, smul_zero, add_zero, hu₁z]
  have hxz' : polar Q₀ x z' = t := by rw [polar_comm]; exact hz'x
  have hyz' : polar Q₀ y z' = t := by rw [polar_comm]; exact hz'y
  have hzz' : polar Q₀ z z' = t := by rw [polar_comm]; exact hz'z
  refine ⟨z', hz', by rw [hz'x]; exact ht0, by rw [hz'y]; exact ht0, by rw [hz'z]; exact ht0,
    ?_, ?_, ?_⟩
  · have e : orthTriangleInvariant Q₀ x y z' = polar Q₀ x y * (polar Q₀ x y + t ^ 2) := by
      unfold orthTriangleInvariant
      rw [hyz', hz'x]
      linear_combination t ^ 2 * h2
    rw [e]
    exact mul_ne_zero hβ₁ fun h => ht1 (CharTwo.add_eq_zero.1 h).symm
  · have e : orthTriangleInvariant Q₀ y z z' = polar Q₀ y z * (polar Q₀ y z + t ^ 2) := by
      unfold orthTriangleInvariant
      rw [hzz', hz'y]
      linear_combination t ^ 2 * h2
    rw [e]
    exact mul_ne_zero hβ₂ fun h => ht2 (CharTwo.add_eq_zero.1 h).symm
  · have e : orthTriangleInvariant Q₀ z x z' = polar Q₀ z x * (polar Q₀ z x + t ^ 2) := by
      unfold orthTriangleInvariant
      rw [hxz', hz'z]
      linear_combination t ^ 2 * h2
    rw [e]
    exact mul_ne_zero hβ₃ fun h => ht3 (CharTwo.add_eq_zero.1 h).symm

theorem triangleProduct_fixed_of_orthogonal {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    (hinv : ∀ c, σ (σ c) = c) {a b c d : Fin 4 → F}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hc : herm σ c c = 0)
    (hd : herm σ d d = 0) (hd0 : d ≠ 0)
    (hda : herm σ d a = 0) (hdb : herm σ d b = 0) (hdc : herm σ d c = 0) :
    σ (herm σ a b * herm σ b c * herm σ c a) = herm σ a b * herm σ b c * herm σ c a := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdep : ¬ LinearIndependent F ![a, b, c, d] := by
    intro hli
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp)
    refine hd0 (eq_zero_of_herm σ fun y => ?_)
    have hle : Submodule.span F (Set.range ![a, b, c, d]) ≤ LinearMap.ker (hermL σ d) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [hda, hdb, hdc, hd]
    have hy : y ∈ Submodule.span F (Set.range ![a, b, c, d]) := by
      rw [htop]
      exact Submodule.mem_top
    simpa using hle hy
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hrel : g 0 • a + g 1 • b + g 2 • c + g 3 • d = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have e0 := congrArg (herm σ a) hrel
  have e1 := congrArg (herm σ b) hrel
  have e2 := congrArg (herm σ c) hrel
  simp only [herm_add_right, herm_smul_right, herm_zero_right, ha, hb, hc,
    herm_eq_zero_comm σ hinv hda, herm_eq_zero_comm σ hinv hdb, herm_eq_zero_comm σ hinv hdc,
    mul_zero, add_zero, zero_add] at e0 e1 e2
  have hdet : herm σ a b * herm σ b c * herm σ c a +
      herm σ b a * herm σ c b * herm σ a c = 0 := by
    have k0 : (herm σ a b * herm σ b c * herm σ c a +
        herm σ b a * herm σ c b * herm σ a c) * g 0 = 0 := by
      linear_combination (-(herm σ b c * herm σ c b)) * e0 + (herm σ a c * herm σ c b) * e1 +
        (herm σ a b * herm σ b c) * e2
    have k1 : (herm σ a b * herm σ b c * herm σ c a +
        herm σ b a * herm σ c b * herm σ a c) * g 1 = 0 := by
      linear_combination (herm σ b c * herm σ c a) * e0 - (herm σ c a * herm σ a c) * e1 +
        (herm σ a c * herm σ b a) * e2
    have k2 : (herm σ a b * herm σ b c * herm σ c a +
        herm σ b a * herm σ c b * herm σ a c) * g 2 = 0 := by
      linear_combination (herm σ b a * herm σ c b) * e0 + (herm σ a b * herm σ c a) * e1 -
        (herm σ a b * herm σ b a) * e2
    by_contra hD
    have h00 : g 0 = 0 := (mul_eq_zero.1 k0).resolve_left hD
    have h01 : g 1 = 0 := (mul_eq_zero.1 k1).resolve_left hD
    have h02 : g 2 = 0 := (mul_eq_zero.1 k2).resolve_left hD
    have h03 : g 3 ≠ 0 := by
      intro h03
      apply hi
      fin_cases i
      exacts [h00, h01, h02, h03]
    simp only [h00, h01, h02, zero_smul, zero_add] at hrel
    exact hd0 ((smul_eq_zero.1 hrel).resolve_left h03)
  rw [herm_conj σ hinv a b, herm_conj σ hinv b c, herm_conj σ hinv c a] at hdet
  rw [map_mul, map_mul]
  linear_combination hdet - herm σ a b * herm σ b c * herm σ c a * h2

theorem triangleProduct_cone {K F : Type} [Field F] {σ : F ≃+* F} (hinv : ∀ c, σ (σ c) = c)
    (a : (Fin 4 → K) → (Fin 4 → F)) (x y z z' : Fin 4 → K) :
    triangleProduct σ a x y z *
        (σ (herm σ (a x) (a z')) * herm σ (a x) (a z')) *
        (σ (herm σ (a y) (a z')) * herm σ (a y) (a z')) *
        (σ (herm σ (a z) (a z')) * herm σ (a z) (a z')) =
      triangleProduct σ a x y z' * triangleProduct σ a y z z' *
        triangleProduct σ a z x z' := by
  simp only [triangleProduct, ← herm_conj σ hinv]
  ring

theorem triangle_fixed {K F : Type} [Field K] [Finite K] [CharP K 2] [Field F] [CharP F 2]
    {σ : F ≃+* F} (hinv : ∀ c, σ (σ c) = c) {Q₀ : QuadraticForm K (Fin 4 → K)}
    (hK4 : 4 ≤ Nat.card K) (hQ₀ : Q₀.polarBilin.Nondegenerate) {a : (Fin 4 → K) → (Fin 4 → F)}
    (hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧ herm σ (a y) (a y) = 0)
    (hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → (herm σ (a x) (a y) = 0 ↔ polar Q₀ x y = 0))
    {x y z : Fin 4 → K} (hx : Q₀ x = 1) (hy : Q₀ y = 1) (hz : Q₀ z = 1) :
    σ (triangleProduct σ a x y z) = triangleProduct σ a x y z := by
  classical
  have key : ∀ {x y z : Fin 4 → K}, Q₀ x = 1 → Q₀ y = 1 → Q₀ z = 1 →
      (∃ w, Q₀ w = 1 ∧ polar Q₀ w x = 0 ∧ polar Q₀ w y = 0 ∧ polar Q₀ w z = 0) →
      σ (triangleProduct σ a x y z) = triangleProduct σ a x y z := by
    rintro x y z hx hy hz ⟨w, hw, hwx, hwy, hwz⟩
    obtain ⟨hw0, hww⟩ := hA1 w hw
    exact triangleProduct_fixed_of_orthogonal hinv (hA1 x hx).2 (hA1 y hy).2 (hA1 z hz).2 hww hw0
      ((hA2 w hw x hx).2 hwx) ((hA2 w hw y hy).2 hwy) ((hA2 w hw z hz).2 hwz)
  by_cases h1 : polar Q₀ x y = 0
  · simp [triangleProduct, (hA2 x hx y hy).2 h1]
  by_cases h2 : polar Q₀ y z = 0
  · simp [triangleProduct, (hA2 y hy z hz).2 h2]
  by_cases h3 : polar Q₀ z x = 0
  · simp [triangleProduct, (hA2 z hz x hx).2 h3]
  rcases eq_or_ne (orthTriangleInvariant Q₀ x y z) 0 with hg | hg
  swap
  · exact key hx hy hz (exists_orthogonal_of_orthTriangleInvariant_ne_zero hx hy hz h1 hg)
  by_cases hspan : z ∈ Submodule.span K {x, y}
  · obtain ⟨w, hwx, hwy, hw⟩ :=
      PartFour.exists_polar_eq_map_eq_of_polar_ne_zero hQ₀ (by simp) h1 0 0 1
    refine key hx hy hz ⟨w, hw, hwx, hwy, ?_⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hspan
    simp [polar_add_right, polar_smul_right, hwx, hwy]
  obtain ⟨z', hz', hz'x, hz'y, hz'z, hg1, hg2, hg3⟩ :=
    exists_shift_orthTriangleInvariant_ne_zero hQ₀ hK4 hx hy hz h1 h2 h3 hspan hg
  have k1 := key hx hy hz' (exists_orthogonal_of_orthTriangleInvariant_ne_zero hx hy hz' h1 hg1)
  have k2 := key hy hz hz' (exists_orthogonal_of_orthTriangleInvariant_ne_zero hy hz hz' h2 hg2)
  have k3 := key hz hx hz' (exists_orthogonal_of_orthTriangleInvariant_ne_zero hz hx hz' h3 hg3)
  have hN : ∀ {u : Fin 4 → K}, Q₀ u = 1 → polar Q₀ z' u ≠ 0 →
      σ (herm σ (a u) (a z')) * herm σ (a u) (a z') ≠ 0 := by
    intro u hu hne
    have h0 : herm σ (a u) (a z') ≠ 0 := fun h =>
      hne (by rw [polar_comm]; exact (hA2 u hu z' hz').1 h)
    exact mul_ne_zero ((map_ne_zero σ).2 h0) h0
  have hP0 := mul_ne_zero (mul_ne_zero (hN hx hz'x) (hN hy hz'y)) (hN hz hz'z)
  have hcone := triangleProduct_cone hinv a x y z z'
  have hσcone := congrArg σ hcone
  simp only [map_mul, k1, k2, k3, hinv] at hσcone
  have hdiff : (σ (triangleProduct σ a x y z) - triangleProduct σ a x y z) *
      ((σ (herm σ (a x) (a z')) * herm σ (a x) (a z')) *
        (σ (herm σ (a y) (a z')) * herm σ (a y) (a z')) *
        (σ (herm σ (a z) (a z')) * herm σ (a z) (a z'))) = 0 := by
    linear_combination hσcone - hcone
  exact sub_eq_zero.1 ((mul_eq_zero.1 hdiff).resolve_right hP0)

end CFSG.OddTranspositions.PartThree

end
