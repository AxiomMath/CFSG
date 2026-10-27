module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumAllAux
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BstarCentralLeaf
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumHAut
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumNorm
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_stab_datum_all {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (hSh : M.Shape)
    {lab : LargeEvenLabel} (hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab))
    (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter) :
    ∃ (ι : Additive ↥(ggGamma L hBsN).range ≃+ (M.V ⧸ Submodule.span (ZMod 3) {M.xV}))
      (φ : M.Λ → MulAut ↥(ggGamma L hBsN).range)
      (h : M.Λ → M.V ⧸ Submodule.span (ZMod 3) {M.xV})
      (α : M.Λ → Module.Dual (ZMod 3) (M.V ⧸ Submodule.span (ZMod 3) {M.xV})),
      (∀ b : ↥Bs, ι (Additive.ofMul (⟨ggGamma L hBsN b, b, rfl⟩ : ↥(ggGamma L hBsN).range)) =
          Submodule.Quotient.mk (M.model (Additive.ofMul b))) ∧
        (∀ i j, α i (h j) = ((M.cartan i j : ℤ) : ZMod 3)) ∧
        (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
        ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
          Subgroup.closure (Set.range φ) ∧
        (Submodule.span (ZMod 3) (Set.range h) = ⊤ ∨
          ∀ v, (∀ i, α i v = 0) → v = 0) ∧
        Nat.card ↥(Subgroup.closure (Set.range fun i => ggLin (p := 3) ι (φ i))) ≤
          Nat.card ↥(ggAutomizer L Bs) := by
  obtain ⟨ι, φ, h, α, hι, hpair, hlin, hdisj, hφeq⟩ := ggQ2s08x1p_descent hS hBsN M
  refine ⟨ι, φ, h, α, hι, hpair, hlin, ?_, hdisj, ?_⟩
  · have hZ := ggQ2s08_bstar_centralizes_center hS hInn hCen
    have hP : ∀ b ∈ Bs, (∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), (b : G) = l * c) →
        (b : G) ∈ (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
      rcases hSh with hF | hA | hB | hC | hD
      · exact fun b hb _ => ggQ2s08x1p_inner_of_cover hS hBsN M hF.2.2.2 b hb
      · intro b hb hbl
        exact Subgroup.mem_sup_left
          (Subgroup.mem_inf.mpr ⟨hb, hOut hS hInn hmark hlab M hA hMW b hb hbl⟩)
      · exact fun b hb _ => ggQ2s08x1p_inner_of_cover hS hBsN M hB.2.2.2 b hb
      · exact ggQ2s08x1p_inner_of_not_mem hS hC.1
      · exact fun b hb _ => ggQ2s08x1p_inner_of_cover hS hBsN M
          (by rw [hD.2.2]; exact top_sup_eq _) b hb
    have hle := ggQ2s08x1p_hAut_le_of_norm hS hBsN M
      (fun l hl => ggQ2s08x1p_norm hS hBsN hZ hP l hl)
    have hφ : φ = ggQ2s08x1p_psi hS hBsN M := funext hφeq
    subst hφ
    refine le_antisymm hle ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ggQ2s08x1p_psi_mem hS hBsN M i
  · simpa only [hφeq] using ggQ2s08x1p_hcard hS hBsN M ι

end CFSG.StandardType

end
