module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.SectionRank.ClassicalEven

variable {f : ℕ} {K : Type} [Field K]

@[expose] def u4TorusEntries : (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* (Fin 4 → Kˣ) where
  toFun d := ![(d 0 : Kˣ), (d 1 : Kˣ), (d 2 : Kˣ), ((d 0 : Kˣ) * (d 1 : Kˣ) * (d 2 : Kˣ))⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' := by
    intro d e
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem torusDiag_u4TorusEntries_mem (d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) :
    torusDiag (u4TorusEntries d) ∈ StatedSU 4 (2 ^ f) K := by
  refine torusDiag_mem_SU (by positivity) ?_ ?_
  · rw [Fin.prod_univ_four]
    simp [u4TorusEntries]
  · rw [← map_pow]
    have hd : d ^ (2 ^ f + 1) = 1 := by
      funext i
      apply Subtype.ext
      simpa [Pi.pow_apply] using (mem_rootsOfUnity (2 ^ f + 1) (d i : Kˣ)).mp (d i).2
    rw [hd, map_one]

@[expose] noncomputable def u4TorusHom :
    (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* StatedProj (StatedSU 4 (2 ^ f) K) :=
  (projH _).comp ((torusDiag.comp u4TorusEntries).codRestrict _ torusDiag_u4TorusEntries_mem)

theorem u4TorusHom_injective (hf : 1 ≤ f) : Function.Injective (u4TorusHom (f := f) (K := K)) := by
  refine (injective_iff_map_eq_one (u4TorusHom (f := f) (K := K))).mpr ?_
  intro d hd
  have hd' : projH (StatedSU 4 (2 ^ f) K)
      ⟨torusDiag (u4TorusEntries d), torusDiag_u4TorusEntries_mem d⟩ = 1 := by
    simpa [u4TorusHom] using hd
  have hmem : (⟨torusDiag (u4TorusEntries d), torusDiag_u4TorusEntries_mem d⟩ :
      StatedSU 4 (2 ^ f) K) ∈
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K) :=
    (QuotientGroup.eq_one_iff _).mp hd'
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have heq : u4TorusEntries d = fun _ => c := by
    apply torusDiag_injective
    rw [← scalar_eq_torusDiag]
    exact hc.symm
  have h0 : (d 0 : Kˣ) = c := by
    simpa [u4TorusEntries] using congrFun heq 0
  have h1 : (d 1 : Kˣ) = c := by
    simpa [u4TorusEntries] using congrFun heq 1
  have h2 : (d 2 : Kˣ) = c := by
    simpa [u4TorusEntries] using congrFun heq 2
  have h3 : c = (c * c * c)⁻¹ := by
    have h := congrFun heq 3
    simp [u4TorusEntries] at h
    rw [h0, h1, h2] at h
    exact h.symm
  have hc4 : c ^ 4 = 1 := by
    have h4 : c * (c * c * c) = 1 := by
      have h := congrArg (fun x : Kˣ => x * (c * c * c)) h3
      rw [inv_mul_cancel] at h
      exact h
    calc c ^ 4 = c ^ 3 * c := by rw [pow_succ]
      _ = (c * c * c) * c := by rw [pow_three']
      _ = c * (c * c * c) := by rw [mul_comm (c * c * c) c]
      _ = 1 := h4
  have hcQ : c ^ (2 ^ f + 1) = 1 := by
    rw [← h0]
    exact (mem_rootsOfUnity (2 ^ f + 1) (d 0 : Kˣ)).mp (d 0).2
  have hgcd : Nat.gcd 4 (2 ^ f + 1) = 1 := by
    have heven : Even (2 ^ f) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega : f ≠ 0)
    have hodd : Odd (2 ^ f + 1) := heven.add_one
    have hcop : Nat.Coprime 4 (2 ^ f + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num)]
      exact hodd.coprime_two_left
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hc1 : c = 1 := by
    have h : c ^ Nat.gcd 4 (2 ^ f + 1) = 1 :=
      (pow_gcd_eq_one (a := c) (m := 4) (n := 2 ^ f + 1)).mpr ⟨hc4, hcQ⟩
    simpa [hgcd] using h
  funext i
  fin_cases i
  · exact Subtype.ext (h0.trans hc1)
  · exact Subtype.ext (h1.trans hc1)
  · exact Subtype.ext (h2.trans hc1)

theorem uFieldAut_u4TorusHom (h : UnitaryFieldData 2 f K) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2)
    (d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) :
    uFieldAut h (n := 4) (by norm_num) σ (u4TorusHom d) = u4TorusHom (d ^ 2) := by
  change uFieldAut h (n := 4) (by norm_num) σ
      (projH (StatedSU 4 (2 ^ f) K)
        ⟨torusDiag (u4TorusEntries d), torusDiag_u4TorusEntries_mem d⟩) =
    projH (StatedSU 4 (2 ^ f) K)
      ⟨torusDiag (u4TorusEntries (d ^ 2)), torusDiag_u4TorusEntries_mem (d ^ 2)⟩
  rw [uFieldAut_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_glAut, coe_torusDiag, Matrix.diagonal_map (map_zero σ), coe_torusDiag]
  apply congrArg Matrix.diagonal
  funext i
  rw [hσ, map_pow, Pi.pow_apply]
  simp [Units.val_pow_eq_pow_val]

theorem uFieldAut_pow_u4TorusHom (h : UnitaryFieldData 2 f K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) (j : ℕ) (d : Fin 3 → rootsOfUnity (2 ^ f + 1) K) :
    (uFieldAut h (n := 4) (by norm_num) σ ^ j) (u4TorusHom d) = u4TorusHom (d ^ 2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmul : uFieldAut h (n := 4) (by norm_num) σ ^ (j + 1) =
        uFieldAut h (n := 4) (by norm_num) σ *
          uFieldAut h (n := 4) (by norm_num) σ ^ j := pow_succ' _ _
    rw [hmul, MulAut.mul_apply, ih, uFieldAut_u4TorusHom h hσ]
    have hpow : (d ^ 2 ^ j) ^ 2 = d ^ 2 ^ (j + 1) := by
      rw [← pow_mul, pow_succ]
    rw [hpow]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
