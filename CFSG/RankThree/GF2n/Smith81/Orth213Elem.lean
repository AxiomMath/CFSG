module

public import CFSG.RankThree.GF2n.Smith81.Orth213Stmts
public import CFSG.RankThree.GF2n.Smith81.Orth28Eps
public import CFSG.RankThree.GF2n.Smith81.Orth212C4Root

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)

namespace Orth213

theorem concl_of_sq {G : Type} [Group G] [Finite G]
    {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z x y : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h : (x * y) ^ 2 = 1 ∨ IsConj z ((x * y) ^ 2)) : Orth213Concl z x y := by
  rcases h with h | h
  · have hd : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact ⟨Or.inr (Or.inr (by rw [h1]; exact odd_one)), fun h4 => by omega⟩
    · exact ⟨Or.inl h2, fun h4 => by omega⟩
  · have hc1 : (x * y) ^ 2 ≠ 1 := ne_one_of_isConj_Z hz1 h
    have hc2 : (x * y) ^ 2 * (x * y) ^ 2 = 1 := mul_self_eq_one_of_isConj_Z H hz h
    have h4 : (x * y) ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]; exact hc2
    have hd : orderOf (x * y) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hnd : ¬ orderOf (x * y) ∣ 2 := fun hd2 => hc1 (orderOf_dvd_iff_pow_eq_one.mp hd2)
    have hle : orderOf (x * y) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < orderOf (x * y) := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have h4' : orderOf (x * y) = 4 := by
      interval_cases hh : orderOf (x * y)
      · exact absurd (by norm_num) hnd
      · exact absurd (by norm_num) hnd
      · exact absurd hd (by norm_num)
      · rfl
    exact ⟨Or.inr (Or.inl h4'), fun _ => h⟩

section Tensor

variable {K : Type} [Field K] {ι : Type}

theorem pure_or_zero_E (qU : QuadraticForm K (ι → K)) (g : Matrix (Fin 2) (Fin 2) K)
    {p : (ι → K) × (ι → K)} (hp : PairTypeA qU p) :
    p + orthTensor g id p = 0 ∨ PairTypeA qU (p + orthTensor g id p) := by
  obtain ⟨c₁, c₂, u, hc, hu, hqu, rfl⟩ := hp
  set a : K := c₁ + (g 0 0 * c₁ + g 0 1 * c₂) with ha
  set b : K := c₂ + (g 1 0 * c₁ + g 1 1 * c₂) with hb
  have e : (c₁ • u, c₂ • u) + orthTensor g id (c₁ • u, c₂ • u) = (a • u, b • u) := by
    simp only [orthTensor, id, Prod.mk_add_mk, smul_smul, ha, hb, add_smul, smul_add]
  rw [e]
  by_cases hab : a = 0 ∧ b = 0
  · left
    rw [hab.1, hab.2, zero_smul]
    rfl
  · right
    refine ⟨a, b, u, ?_, hu, hqu, rfl⟩
    by_contra hcon
    push Not at hcon
    exact hab hcon

theorem pure_or_zero_A [CharP K 2] (qU : QuadraticForm K (ι → K)) {u' w' : ι → K}
    (hu' : qU u' = 0) (hw' : qU w' = 0) (huw : QuadraticMap.polar qU u' w' = 0)
    {p : (ι → K) × (ι → K)} (hp : PairTypeA qU p) :
    p + orthTensor 1 ⇑(eichler qU u' w') p = 0 ∨
      PairTypeA qU (p + orthTensor 1 ⇑(eichler qU u' w') p) := by
  obtain ⟨c₁, c₂, u, hc, hu, hqu, rfl⟩ := hp
  set s : ι → K := u + eichler qU u' w' u with hs
  have hsing : qU s = 0 := by
    have h1 := CFSG.ClassicalGroups.Orthogonal.eichler_apply (Q := qU) hu' huw u
    have h2 : s = QuadraticMap.polar qU u u' • w' + (-(QuadraticMap.polar qU u w')) • u' := by
      have h3 : s = (2 : K) • u + QuadraticMap.polar qU u u' • w' +
          (-(QuadraticMap.polar qU u w')) • u' := by
        rw [hs, h1, hw', zero_mul, add_zero]
        module
      rw [h3, CharTwo.two_eq_zero, zero_smul, zero_add]
    have hwu : QuadraticMap.polar qU w' u' = 0 := by rw [QuadraticMap.polar_comm, huw]
    rw [h2, orth212C4_qU_add_smul qU hw' hu', hwu, mul_zero]
  have e : (c₁ • u, c₂ • u) + orthTensor 1 ⇑(eichler qU u' w') (c₁ • u, c₂ • u) =
      (c₁ • s, c₂ • s) := by
    have h1 : orthTensor (1 : Matrix (Fin 2) (Fin 2) K) ⇑(eichler qU u' w') (c₁ • u, c₂ • u) =
        (eichler qU u' w' (c₁ • u), eichler qU u' w' (c₂ • u)) := by
      simp [orthTensor, Matrix.one_apply]
    rw [h1]
    simp only [hs, map_smul, Prod.mk_add_mk, smul_add]
  rw [e]
  by_cases hs0 : s = 0
  · left
    rw [hs0, smul_zero, smul_zero]
    rfl
  · right
    exact ⟨c₁, c₂, s, hc, hs0, hsing, rfl⟩

end Tensor

end Orth213

open Orth213

theorem orth213Elem_of (h24 : Smith24ActStatement)
    (hK : OrthClassStatement) : Orth213ElemStatement := by
  intro G _ _ M Q Z B hc z hz hz1 x y hxM hyM hxz hyz hcase
  have H := hc.ctx.hyp
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have key : ∀ x y : G, x ∈ M → y ∈ M → IsConj z x → IsConj z y → x ∈ Q → y ∉ Q →
      (x * y) ^ 2 = 1 ∨ IsConj z ((x * y) ^ 2) := by
    intro x y hxM hyM hxz hyz hxQ hyQ
    obtain ⟨g, hg⟩ := isConj_iff.mp hyz
    have hsy : Sit M Q Z (conjSubgroup g Z) y := by
      have := Sit.of_conj H hz hz1 (g := g) (by rw [hg]; exact hyM) (by rw [hg]; exact hyQ)
      rwa [hg] at this
    have h12 := smith_1_12 hsy
    have hy2 : y * y = 1 := mul_self_eq_one_of_isConj_Z H hz hyz
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hx2 : x * x = 1 := mul_self_eq_one_of_isConj_Z H hz hxz
    have hceq : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [hyinv, pow_two]; group
    have hx'Q : y * x * y⁻¹ ∈ Q := conj_mem_Q H hyM hxQ
    have hcQ : x * (y * x * y⁻¹) ∈ Q := Q.mul_mem hxQ hx'Q
    rw [hceq]
    by_cases hxZ : x ∈ Z
    · left
      rw [hsy.x_cent h12 x hxZ]
      exact hx2
    · have hpA := (C.hF.root z hz hz1 x hxQ hxZ).mp hxz
      have fin : ∀ {g' : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)},
          ActsAsTensor Q Z C.M₀ C.φ y g' o →
          (C.φ (C.M₀.π x) + orthTensor g' o (C.φ (C.M₀.π x)) = 0 ∨
            PairTypeA C.qU (C.φ (C.M₀.π x) + orthTensor g' o (C.φ (C.M₀.π x)))) →
          x * (y * x * y⁻¹) = 1 ∨ IsConj z (x * (y * x * y⁻¹)) := by
        intro g' o hact hor
        have hφc : C.φ (C.M₀.π (x * (y * x * y⁻¹))) =
            C.φ (C.M₀.π x) + orthTensor g' o (C.φ (C.M₀.π x)) := by
          rw [C.M₀.π_mul x hxQ _ hx'Q, map_add, hact x hxQ]
        rcases hor with h0 | hpa
        · have h0' : C.M₀.π (x * (y * x * y⁻¹)) = 0 := by
            rw [← C.φ.map_eq_zero_iff, hφc]
            exact h0
          have hcZ : x * (y * x * y⁻¹) ∈ Z := (C.M₀.π_ker _ hcQ).mp h0'
          by_cases h1 : x * (y * x * y⁻¹) = 1
          · exact Or.inl h1
          · obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hcZ h1
            exact Or.inr (isConj_iff.mpr ⟨m, hm⟩)
        · have hcZ : x * (y * x * y⁻¹) ∉ Z := by
            intro hcZ
            have h0 : C.M₀.π (x * (y * x * y⁻¹)) = 0 := (C.M₀.π_ker _ hcQ).mpr hcZ
            apply OrthEps.pairTypeA_ne_zero hpa
            rw [← hφc, h0, map_zero]
          exact Or.inr ((C.hF.root z hz hz1 _ hcQ hcZ).mpr (hφc ▸ hpa))
      rcases hK G M Q Z B hc C _ y hsy with ⟨g', -, -, -, hact⟩ | ⟨u', w', hu', hw', huw, -, hact⟩
      · exact fin hact (pure_or_zero_E C.qU g' hpA)
      · exact fin hact (pure_or_zero_A C.qU hu' hw' huw hpA)
  by_cases hxyQ : x * y ∈ Q
  · apply concl_of_sq H hz hz1
    have hc2 : (x * y) ^ 2 ∈ Z := sq_mem_Z H hxyQ
    by_cases h1 : (x * y) ^ 2 = 1
    · exact Or.inl h1
    · obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hc2 h1
      exact Or.inr (isConj_iff.mpr ⟨m, hm⟩)
  · apply concl_of_sq H hz hz1
    rcases hcase with hxQ | hyQ | hxyQ'
    · have hyQ : y ∉ Q := fun hy => hxyQ (Q.mul_mem hxQ hy)
      exact key x y hxM hyM hxz hyz hxQ hyQ
    · have hxQ : x ∉ Q := fun hx => hxyQ (Q.mul_mem hx hyQ)
      have h := key y x hyM hxM hyz hxz hyQ hxQ
      have e : (x * y) ^ 2 = x * (y * x) ^ 2 * x⁻¹ := by simp only [pow_two]; group
      rw [e]
      rcases h with h | h
      · left
        rw [h]
        group
      · right
        exact h.trans (isConj_iff.mpr ⟨x, rfl⟩)
    · exact absurd hxyQ' hxyQ

end CFSG.RankThree.GF2n.Smith81
