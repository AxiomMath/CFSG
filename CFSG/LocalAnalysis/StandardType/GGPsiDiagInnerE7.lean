module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

namespace PsiDiag.Minu


theorem conj_xm_eq_of_mem_normalizer {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*)
    [Field k] {γ : Fin τ.rank → ℤ} {h : hV.minGroup k}
    (hh : h ∈ Subgroup.normalizer (hV.rootGroup k γ : Set (hV.minGroup k))) :
    ∃ χ : k, ∀ c, h * hV.xm k γ c * h⁻¹ = hV.xm k γ (χ * c) := by
  obtain ⟨χ, hχ⟩ := (hV.mem_rootGroup k).mp
    ((Subgroup.mem_normalizer_iff.mp hh _).mp (hV.xm_mem_rootGroup k γ 1))
  have hHH : hV.endo k h * hV.endo k h⁻¹ = 1 := hV.endo_mul_inv k h
  have hE : hV.endo k h * D.rootOp k γ * hV.endo k h⁻¹ = χ • D.rootOp k γ := by
    have h1 := congrArg (hV.endo k) hχ
    rw [hV.endo_mul, hV.endo_mul, hV.endo_xm, hV.endo_xm, one_smul, mul_add, add_mul, mul_one,
      hHH] at h1
    exact (add_left_cancel h1).symm
  refine ⟨χ, fun c => hV.endo_injective k ?_⟩
  rw [hV.endo_mul, hV.endo_mul, hV.endo_xm, hV.endo_xm, mul_add, add_mul, mul_one, hHH,
    mul_smul_comm, smul_mul_assoc, hE, smul_smul, mul_comm]

theorem exists_mem_centralizer_E7 {k : Type} [Field k] [Finite k] [CharP k 2] {G : Type*}
    [Group G] (ψ : ↥(e7Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup k)) {c : G}
    (hc : GGPsiInnerDiag (e7Datum k) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨O⟩ := e7_nonempty_commOrder k
  have hE := (e7Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E7 k
    posDef_cartan_E7 neighbour_E7 O).2
  refine exists_mem_centralizer_of_ggPsiInnerDiag hE rfl (e7Datum_isCTGroupDatum k).iSup_eq_top
    (a := 1) (by rw [pow_one]; exact CFSG.LieType.Chevalley.det_cartan_E7)
    (fun i h hh => conj_xm_eq_of_mem_normalizer e7Data_valid k ?_) ψ hker hc
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots i)

end PsiDiag.Minu

section Genuine

theorem ggPsiDiagInner_E7 :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .E7 n f).K →* G) (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU .E7 n f).D .E7 n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU .E7 n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  intro G _ _ n f ψ G₀ hpres c _ hc
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hker hc

end Genuine

end CFSG.StandardType
