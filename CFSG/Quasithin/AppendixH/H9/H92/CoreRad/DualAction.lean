module

public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.FixedVectors
public import CFSG.Quasithin.AppendixH.H9.H92.RadHyperplane

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

private theorem dualHomN_mulVec_mem {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {s : GL (Fin n) (ZMod 2)} (hs : s ∈ stabMat n D) {b : Fin n → ZMod 2}
    (hb : b ∈ dotPerp n D) :
    ((dualHomN n s : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b ∈
      dotPerp n D := by
  intro d hd
  have hd' : ((s⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ d ∈ D :=
    ((stabMat n D).inv_mem hs d).mpr hd
  have h := Matrix.dotProduct_transpose_mulVec
    ((s⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) d b
  rw [dotProduct_comm]
  exact h.trans (hb _ hd')

theorem dualHomN_mem_stabMat {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {s : GL (Fin n) (ZMod 2)} (hs : s ∈ stabMat n D) :
    dualHomN n s ∈ stabMat n (dotPerp n D) := by
  intro b
  constructor
  · intro hb'
    have h := dualHomN_mulVec_mem ((stabMat n D).inv_mem hs) hb'
    rw [map_inv, GL_inv_mulVec_mulVec] at h
    exact h
  · exact dualHomN_mulVec_mem hs

theorem normal_two_subgroup_le_radMat {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (K : Subgroup (GL (Fin n) (ZMod 2))) (hK2 : IsPGroup 2 K) (hKD : K ≤ stabMat n D)
    (hKn : ∀ s ∈ stabMat n D, ∀ k ∈ K, s * k * s⁻¹ ∈ K) : K ≤ RadMat n D := by
  intro k hk
  refine mem_radMat_iff_sub_mem_and_fix.mpr
    ⟨fun x => ?_, normal_two_subgroup_fixes_subspace D K hK2 hKD hKn k hk⟩
  have hK'2 : IsPGroup 2 (K.map (dualHomN n)) := hK2.map (dualHomN n)
  have hK'D : K.map (dualHomN n) ≤ stabMat n (dotPerp n D) := by
    rintro _ ⟨k', hk', rfl⟩
    exact dualHomN_mem_stabMat (hKD hk')
  have hK'n : ∀ s ∈ stabMat n (dotPerp n D), ∀ k ∈ K.map (dualHomN n),
      s * k * s⁻¹ ∈ K.map (dualHomN n) := by
    rintro s hs _ ⟨k', hk', rfl⟩
    have hs' : dualHomN n s ∈ stabMat n D := by
      have h := dualHomN_mem_stabMat hs
      rwa [dotPerp_dotPerp] at h
    refine ⟨dualHomN n s * k' * (dualHomN n s)⁻¹, hKn _ hs' k' hk', ?_⟩
    rw [map_mul, map_mul, map_inv]
    show dualGLn n (dualGLn n s) * _ * (dualGLn n (dualGLn n s))⁻¹ = _
    rw [dualGLn_dualGLn]
  have key := normal_two_subgroup_fixes_subspace (dotPerp n D) (K.map (dualHomN n)) hK'2 hK'D
    hK'n
  have hmem : ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x ∈ dotPerp n (dotPerp n D) := by
    intro b hb
    have hkT : (k : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ b = b := by
      have h := key (dualHomN n k⁻¹) ⟨k⁻¹, K.inv_mem hk, rfl⟩ b hb
      have e : ((dualHomN n k⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
          (k : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
        show (((k⁻¹)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = _
        rw [inv_inv]
      rwa [e] at h
    calc (((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x) ⬝ᵥ b
        = b ⬝ᵥ (((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x) := dotProduct_comm _ _
      _ = x ⬝ᵥ (((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b) :=
          (Matrix.dotProduct_transpose_mulVec _ _ _).symm
      _ = 0 := by
          rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, hkT,
            Matrix.one_mulVec, sub_self, dotProduct_zero]
  rwa [dotPerp_dotPerp] at hmem

end CFSG.ASVolI.ChH
