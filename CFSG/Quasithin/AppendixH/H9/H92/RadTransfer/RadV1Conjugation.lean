module

public import CFSG.Quasithin.AppendixH.H9.H92.RadCard
public import CFSG.Quasithin.AppendixH.H9.H92.RadHyperplane
public import CFSG.Quasithin.AppendixH.H9.H92.RadTransfer.RadMatConjugation

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

private theorem conjAut_map_of_conj_eq {V : Type*} [CommGroup V] {G : Type*} [Group G]
    (φ : G →* MulAut V) (ψ : G →* G) (t : MulAut V) (h : ∀ x, t * φ x * t⁻¹ = φ (ψ x))
    (A : Subgroup G) : conjAut t (A.map φ) = (A.map ψ).map φ := by
  unfold conjAut
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, h]

private theorem conjAut_map_hom_apply {V : Type*} [CommGroup V] {G : Type*} [Group G]
    (φ : G →* MulAut V) (g : G) (A : Subgroup G) :
    conjAut (φ g) (A.map φ) = (A.map (MulAut.conj g).toMonoidHom).map φ :=
  conjAut_map_of_conj_eq φ (MulAut.conj g).toMonoidHom (φ g)
    (fun x => by simp [MulAut.conj_apply, map_mul, map_inv]) A

theorem conjAut_pairActN_map_radMat {n : ℕ} {D₁ D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (B : GL (Fin n) (ZMod 2))
    (hB : ∀ x, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ D₂ ↔ x ∈ D₁) :
    conjAut (pairActN n B) ((RadMat n D₁).map (pairActN n)) =
      (RadMat n D₂).map (pairActN n) :=
  (conjAut_map_hom_apply (pairActN n) B (RadMat n D₁)).trans
    (congrArg (Subgroup.map (pairActN n)) (map_conj_radMat B hB))

theorem dualGLn_mem_radMat {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {C : GL (Fin n) (ZMod 2)} (hC : C ∈ RadMat n D) : dualGLn n C ∈ RadMat n (dotPerp n D) := by
  have hinv : C⁻¹ = C := inv_eq_of_mul_eq_one_right ((radMat_comm_sq D).2 C hC)
  rw [mem_radMat_iff_sub_mem_radNil, dualGLn_val, hinv]
  have h := transpose_mem_radNil n D _ ((mem_radMat_iff_sub_mem_radNil C).1 hC)
  rwa [Matrix.transpose_sub, Matrix.transpose_one] at h

theorem map_dualHomN_radMat {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (RadMat n D).map (dualHomN n) = RadMat n (dotPerp n D) := by
  apply le_antisymm
  · rintro _ ⟨C, hC, rfl⟩
    exact dualGLn_mem_radMat hC
  · intro C hC
    have h := dualGLn_mem_radMat hC
    rw [dotPerp_dotPerp] at h
    exact ⟨dualGLn n C, h, dualGLn_dualGLn C⟩

theorem conjAut_swapN_map_radMat {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    conjAut (swapN n) ((RadMat n D).map (pairActN n)) =
      (RadMat n (dotPerp n D)).map (pairActN n) := by
  have h : ∀ C : GL (Fin n) (ZMod 2),
      swapN n * pairActN n C * (swapN n)⁻¹ = pairActN n (dualHomN n C) := by
    intro C
    rw [swapN_mul_pairActN, mul_assoc, swapN_inv, swapN_mul_self, mul_one]
    rfl
  exact (conjAut_map_of_conj_eq (pairActN n) (dualHomN n) (swapN n) h (RadMat n D)).trans
    (congrArg (Subgroup.map (pairActN n)) (map_dualHomN_radMat D))

end CFSG.ASVolI.ChH
