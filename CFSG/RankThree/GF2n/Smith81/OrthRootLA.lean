module

public import CFSG.RankThree.GF2n.Smith81.OrthModel
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.OrthogonalInvolutions (mem_commSpace one_le_finrank_commSpace omegaGroup
  mem_omegaGroup dicksonHom dicksonHom_apply)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_apply_self)
open scoped commutatorElement

section Pure

variable {K : Type} [Field K] [CharP K 2] {ι : Type}

theorem pure_of_smul_add_eq_zero (p : (ι → K) × (ι → K)) {s t : K}
    (h : s • p.1 + t • p.2 = 0) (hst : s ≠ 0 ∨ t ≠ 0) :
    ∃ (c : Fin 2 → K) (u : ι → K), p = (c 0 • u, c 1 • u) := by
  rcases hst with hs | ht
  · refine ⟨![-t / s, 1], p.2, Prod.ext ?_ ?_⟩
    · have h' : s • p.1 = -(t • p.2) := eq_neg_of_add_eq_zero_left h
      calc p.1 = s⁻¹ • (s • p.1) := (inv_smul_smul₀ hs p.1).symm
        _ = s⁻¹ • (-(t • p.2)) := by rw [h']
        _ = (-t / s) • p.2 := by
          rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv]
          congr 1
          ring
    · simp
  · refine ⟨![1, -s / t], p.1, Prod.ext ?_ ?_⟩
    · simp
    · have h' : t • p.2 = -(s • p.1) := eq_neg_of_add_eq_zero_right h
      calc p.2 = t⁻¹ • (t • p.2) := (inv_smul_smul₀ ht p.2).symm
        _ = t⁻¹ • (-(s • p.1)) := by rw [h']
        _ = (-s / t) • p.1 := by
          rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv]
          congr 1
          ring

theorem pure_iff_exists_fix (p : (ι → K) × (ι → K)) :
    (∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ g ≠ 1 ∧ orthTensor g id p = p) ↔
      ∃ (c : Fin 2 → K) (u : ι → K), p = (c 0 • u, c 1 • u) := by
  constructor
  · rintro ⟨g, -, hne, hfix⟩
    have h1 : g 0 0 • p.1 + g 0 1 • p.2 = p.1 := congrArg Prod.fst hfix
    have h2 : g 1 0 • p.1 + g 1 1 • p.2 = p.2 := congrArg Prod.snd hfix
    by_contra hpure
    have key : ∀ s t : K, s • p.1 + t • p.2 = 0 → s = 0 ∧ t = 0 := by
      intro s t hst
      by_contra hc
      exact hpure (pure_of_smul_add_eq_zero p hst (not_and_or.mp hc))
    obtain ⟨a00, a01⟩ := key (g 0 0 - 1) (g 0 1) (by linear_combination (norm := module) h1)
    obtain ⟨a10, a11⟩ := key (g 1 0) (g 1 1 - 1) (by linear_combination (norm := module) h2)
    apply hne
    have e00 : g 0 0 = 1 := sub_eq_zero.mp a00
    have e11 : g 1 1 = 1 := sub_eq_zero.mp a11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e11, a01, a10]
  · rintro ⟨c, u, rfl⟩
    by_cases hc : c 0 = 0 ∧ c 1 = 0
    · refine ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; norm_num, ?_, ?_⟩
      · intro h
        have h01 := congrFun (congrFun h 0) 1
        simp at h01
      · simp [orthTensor, hc.1, hc.2]
    · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have e0 : (1 + c 0 * c 1) * c 0 + c 0 ^ 2 * c 1 = c 0 := by
        linear_combination (c 0 ^ 2 * c 1) * h2
      have e1 : c 1 ^ 2 * c 0 + (1 + c 0 * c 1) * c 1 = c 1 := by
        linear_combination (c 0 * c 1 ^ 2) * h2
      refine ⟨!![1 + c 0 * c 1, c 0 ^ 2; c 1 ^ 2, 1 + c 0 * c 1], ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        linear_combination (c 0 * c 1) * h2
      · intro h
        by_cases h0 : c 0 = 0
        · have h10 := congrFun (congrFun h 1) 0
          have h1 : c 1 = 0 := by simpa [h0] using h10
          exact hc ⟨h0, h1⟩
        · have h01 := congrFun (congrFun h 0) 1
          exact h0 (by simpa using h01)
      · refine Prod.ext ?_ ?_
        · show (1 + c 0 * c 1) • (c 0 • u) + c 0 ^ 2 • (c 1 • u) = c 0 • u
          linear_combination (norm := module) e0 • u
        · show c 1 ^ 2 • (c 0 • u) + (1 + c 0 * c 1) • (c 1 • u) = c 1 • u
          linear_combination (norm := module) e1 • u

end Pure

section Dickson

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]

theorem polarBilin_nondegenerate_of_hnd {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v : ι → K, (∀ w, QuadraticMap.polar qU v w = 0) → v = 0) :
    (QuadraticMap.polarBilin qU).Nondegenerate := by
  refine ⟨fun v hv => hnd v (fun w => ?_), fun v hv => hnd v (fun w => ?_)⟩
  · have h := hv w
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  · have h := hv w
    rw [QuadraticMap.polarBilin_apply_apply] at h
    rw [QuadraticMap.polar_comm qU v w]
    exact h

end Dickson

end CFSG.RankThree.GF2n.Smith81
