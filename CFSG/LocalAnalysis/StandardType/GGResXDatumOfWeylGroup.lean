module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumSurj
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResXDatum_of_weylReflectionGroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNoTr : GGNoTransvection p Bs) (hW : GGWeylReflectionGroup p (ggAutomizer X Bs))
    (hG2 : ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer X Bs)) : GGResXDatum p Bs X := by
  classical
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have hind : ∀ φ ∈ ggAutomizer X Bs, φ ∈ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  have key : ∀ {n : ℕ} (e : Fin n ≃ ι) (M₀ : CoxeterMatrix (Fin n))
      (C₀ : Matrix (Fin n) (Fin n) ℤ), M = M₀.reindex e → GGIntCartan M₀ C₀ →
      (∀ i j, i ≠ j → C₀ i j = 0 ∨ C₀ i j = -1 ∨ C₀ i j = -2) →
      SecFiveRootRefl.CartanTree C₀ → GGResXDatum p Bs X := by
    intro n e M₀ C₀ hMe hC₀ hent hT
    haveI : Fintype ι := Fintype.ofEquiv _ e
    have hC : GGIntCartan M (Matrix.reindex e e C₀) := hMe ▸ hC₀.reindex e
    obtain ⟨h, α, hα, hrefl, hpair⟩ := SecFiveRootRefl.exists_cartan_pairing_of_iso hp2 hNoTr hC
      (SecFiveRootRefl.entries_reindex e hent) (hT.reindex e) f hf hind ιV
    have hlin : ∀ i w, ggLin (p := p) ιV ((f (M.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
        w = w - α i w • h i :=
      fun i w => by rw [hrefl i]; exact Module.reflection_apply w (hα i)
    exact ⟨ι, inferInstance, inferInstance, M, Matrix.reindex e e C₀, V, inferInstance,
      inferInstance, ιV, fun i => ((f (M.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs), h, α,
      hM, hC, hlin, hf, hpair, ⟨f, fun i => rfl⟩,
      ggAutomizer_eq_closure_of_surj f.toMonoidHom f.surjective fun i => rfl⟩
  have hM' := hM
  rcases hM' with ⟨n, e, hn, hMA | ⟨hn2, hMB⟩ | ⟨hn4, hMD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hMG⟩
  · exact key e _ _ hMA (ggIntCartan_A n) (SecFiveRootRefl.entries_A n)
      (SecFiveRootRefl.cartanTree_A n hn)
  · exact key e _ _ hMB (ggIntCartan_B n) (SecFiveRootRefl.entries_B n)
      (SecFiveRootRefl.cartanTree_B n hn)
  · exact key e _ _ hMD (ggIntCartan_D n) (SecFiveRootRefl.entries_D n)
      (SecFiveRootRefl.cartanTree_D n hn4)
  · exact key e _ _ hE6 ggIntCartan_E₆ (SecFiveRootRefl.entries_E 6)
      (SecFiveRootRefl.cartanTree_E 6 (by norm_num))
  · exact key e _ _ hE7 ggIntCartan_E₇ (SecFiveRootRefl.entries_E 7)
      (SecFiveRootRefl.cartanTree_E 7 (by norm_num))
  · exact key e _ _ hE8 ggIntCartan_E₈ (SecFiveRootRefl.entries_E 8)
      (SecFiveRootRefl.cartanTree_E 8 (by norm_num))
  · exact key e _ _ hF4 ggIntCartan_F₄ SecFiveRootRefl.entries_F₄ SecFiveRootRefl.cartanTree_F₄
  · exfalso
    subst hMG
    exact hG2 (GGWeylOfType.of_reindex ⟨f, hf⟩)

end CFSG.StandardType

end
