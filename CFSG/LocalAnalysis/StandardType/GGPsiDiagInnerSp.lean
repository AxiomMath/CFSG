module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LieType.Steinberg.Classical.Symplectic
public import CFSG.LieType.Steinberg.PartBAssembly
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  TauCeti.GLSymplecticFin CFSG.Assembly.LowTwoRank

namespace PsiDiag.Symp

variable {n : ℕ} {F : Type} [Field F]

theorem conj_elt_eq_of_mem_normalizer {γ : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) {h : StatedSp n F}
    (hh : h ∈ Subgroup.normalizer (rootGroup n F γ : Set (StatedSp n F))) :
    ∃ χ : F, ∀ c : F, h * elt r c * h⁻¹ = elt r (χ * c) := by
  obtain ⟨χ, hχ⟩ := (mem_rootGroup_iff hr).mp
    ((Subgroup.mem_normalizer_iff.mp hh _).mp (elt_mem_rootGroup hr (1 : F)))
  refine ⟨χ, fun c => ?_⟩
  have hHH : mat n F h * mat n F h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hE : mat n F h * E F r * mat n F h⁻¹ = χ • E F r := by
    have h1 := congrArg (mat n F) hχ
    rw [map_mul, map_mul, mat_elt, mat_elt, one_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, hHH] at h1
    exact add_left_cancel h1
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH,
    Matrix.mul_smul, Matrix.smul_mul, hE, smul_smul, mul_comm]

theorem ggTorus_conj_x (γ : Fin n → ℤ) (hγ : γ ∈ (rootDatum n F).roots)
    (h : StatedSp n F) (hh : h ∈ ggTorus (rootDatum n F)) :
    ∃ χ : F, ∀ c, h * CFSG.LieType.Steinberg.Sp.x n F γ c * h⁻¹ =
      CFSG.LieType.Steinberg.Sp.x n F γ (χ * c) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  have hN : h ∈ Subgroup.normalizer (rootGroup n F γ : Set (StatedSp n F)) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh γ hγ
  obtain ⟨χ, hχ⟩ := conj_elt_eq_of_mem_normalizer hr hN
  exact ⟨χ, fun c => by
    rw [CFSG.LieType.Steinberg.Sp.x_eq hr, CFSG.LieType.Steinberg.Sp.x_eq hr, hχ]⟩

theorem cartanC_eq_B : cartanC n = CartanMatrix.B n := by
  ext i j
  simp only [cartanC, CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

theorem det_cartanC (hn : 1 ≤ n) : (cartanC n).det = 2 ^ 1 := by
  rw [cartanC_eq_B, CartanMatrix.B_det (by omega), pow_one]

theorem exists_mem_centralizer [Finite F] [CharP F 2] (hn : 2 ≤ n) {G : Type*} [Group G]
    (ψ : StatedSp n F →* G) (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {c : G}
    (hc : GGPsiInnerDiag (rootDatum n F) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  have hE := CFSG.LieType.Steinberg.Sp.chevalleyExtras hn O CFSG.LieType.Steinberg.Sp.commC
    (CFSG.LieType.Steinberg.Sp.commutatorFormula O)
  exact exists_mem_centralizer_of_ggPsiInnerDiag hE rfl (isCTGroupDatum n F).iSup_eq_top
    (det_cartanC (by omega)) (fun i h hh => ggTorus_conj_x _ (single_mem_roots i) h hh) ψ
    hker hc

end PsiDiag.Symp

section Genuine

theorem ggPsiDiagInner_PSp :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .PSp n f).K →* G) (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU .PSp n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  intro G _ _ n f ψ G₀ hpres c _ hc
  obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker hc

end Genuine

end CFSG.StandardType
