module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private theorem torPSp_col_eq_zero {n : ℕ} {F : Type} [Field F]
    {r : TauCeti.GLSymplecticFin.RootSubgroupIndex n} {γ : Fin n → ℤ}
    (hr : Symplectic.stdVec r = Symplectic.toStd n γ) {h : CFSG.Open.StatedSp n F}
    (hh : h ∈ Subgroup.normalizer (Symplectic.rootGroup n F γ : Set (CFSG.Open.StatedSp n F)))
    {a b : Fin n ⊕ Fin n} (hEab : Symplectic.SpExtras.E F r = Matrix.single a b 1)
    {r' : Fin n ⊕ Fin n} (hne : r' ≠ a) :
    Symplectic.SpExtras.mat n F h r' a = 0 := by
  obtain ⟨χ, hχ⟩ := PsiDiag.Symp.conj_elt_eq_of_mem_normalizer hr hh
  have hHH : Symplectic.SpExtras.mat n F h * Symplectic.SpExtras.mat n F h⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hE : Symplectic.SpExtras.mat n F h * Symplectic.SpExtras.E F r *
      Symplectic.SpExtras.mat n F h⁻¹ = χ • Symplectic.SpExtras.E F r := by
    have h1 := congrArg (Symplectic.SpExtras.mat n F) (hχ 1)
    rw [map_mul, map_mul, Symplectic.SpExtras.mat_elt, Symplectic.SpExtras.mat_elt, one_smul,
      mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH] at h1
    exact add_left_cancel h1
  have hME : Symplectic.SpExtras.mat n F h * Symplectic.SpExtras.E F r =
      χ • (Symplectic.SpExtras.E F r * Symplectic.SpExtras.mat n F h) := by
    have h2 := congrArg (fun M => M * Symplectic.SpExtras.mat n F h) hE
    rw [Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, Matrix.smul_mul] at h2
    exact h2
  have h3 := congrFun (congrFun hME r') b
  rw [hEab] at h3
  simp only [Matrix.mul_single_apply_same, Matrix.smul_apply,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ hne, smul_eq_mul, mul_one, mul_zero] at h3
  exact h3

theorem ggTorus_apply_eq_zero_PSp (n : ℕ) (F : Type) [Field F]
    {h : ↥(CFSG.Open.StatedSp n F)} (hh : h ∈ ggTorus (Symplectic.rootDatum n F))
    {i j : Fin n ⊕ Fin n} (hij : i ≠ j) :
    ((h : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j = 0 := by
  rw [← Symplectic.SpExtras.mat_apply h]
  rcases j with k | k
  · obtain ⟨γ, hγ, hγeq⟩ :=
      CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec (n := n)
        (TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong k)
    have hr : Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong k) =
        Symplectic.toStd n γ := hγeq.symm
    have hN : h ∈ Subgroup.normalizer
        (Symplectic.rootGroup n F γ : Set (CFSG.Open.StatedSp n F)) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh γ hγ
    exact torPSp_col_eq_zero hr hN rfl hij
  · obtain ⟨γ, hγ, hγeq⟩ :=
      CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec (n := n)
        (TauCeti.GLSymplecticFin.RootSubgroupIndex.negativeLong k)
    have hr : Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.negativeLong k) =
        Symplectic.toStd n γ := hγeq.symm
    have hN : h ∈ Subgroup.normalizer
        (Symplectic.rootGroup n F γ : Set (CFSG.Open.StatedSp n F)) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh γ hγ
    exact torPSp_col_eq_zero hr hN rfl hij

end CFSG.StandardType.ClassicalPosition
