module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.PartBAssembly
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LieType.Steinberg.Classical.SpinFrame

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame

namespace PsiDiag.SpinP

variable {n : ℕ} {K : Type} [Field K]

theorem coe_x_eq (hn : 3 ≤ n) {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    ∃ N : CliffordAlgebra (quadPlus n K), ∀ c : K,
      ((SpinPlus.x n K hn γ c : spinGroup (quadPlus n K)) : CliffordAlgebra (quadPlus n K)) =
        1 + c • N := by
  obtain ⟨i, j, hij, s, t, he⟩ := PlusCT.exists_toStdD_eq_of_mem_rootsD (by omega) hγ
  refine ⟨(repSign i j s t : K) • (CliffordAlgebra.ι (quadPlus n K) ((plusFrame n K hn).vec i s) *
    CliffordAlgebra.ι (quadPlus n K) ((plusFrame n K hn).vec j t)), fun c => ?_⟩
  rw [SpinPlus.x, rootElt_eq _ hij he, HypFrame.coe_longRoot, smul_smul, mul_comm]

theorem det_cartanD (hn : 2 ≤ n) : (cartanD n).det = 2 ^ 2 := by
  rw [cartanD_eq, CartanMatrix.D_det hn]
  norm_num

theorem exists_mem_centralizer [Finite K] [CharP K 2] (hn : 3 ≤ n) {G : Type*} [Group G]
    (ψ : spinGroup (quadPlus n K) →* G)
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) {c : G}
    (hc : GGPsiInnerDiag (plusDatum n K hn) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (plusDatum n K hn).isFiniteType
    (Dv := (plusDatum n K hn).divisible) rfl
  have hE := SpinPlus.chevalleyExtras hn O SpinPlus.commC (SpinPlus.commutatorFormula hn O)
  refine exists_mem_centralizer_of_ggPsiInnerDiag hE rfl (plusDatum_iSup_eq_top n K hn)
    (det_cartanD (by omega)) (fun i h hh => ?_) ψ hker hc
  obtain ⟨N, hN⟩ := coe_x_eq (K := K) hn (single_mem_roots (D := plusDatum n K hn) i)
  refine conj_eq_of_affine (spinGroup (quadPlus n K)).subtype Subtype.val_injective
    ((hE.param _ (single_mem_roots i)).1) hN ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots i)

end PsiDiag.SpinP

section Genuine

theorem ggPsiDiagInner_POmegaPlus :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .POmegaPlus n f).K →* G)
      (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ →
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  intro G _ _ n f
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    intro ψ G₀ hpres c _ hc
    obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    exact PsiDiag.SpinP.exists_mem_centralizer (K := GaloisField 2 f) hn ψ hker hc
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ G₀ hpres
    exact absurd hpres.1.2 (by decide)

end Genuine

end CFSG.StandardType
