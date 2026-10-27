module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS2FramePlane
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModelEven
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
import CFSG.ClassicalInvolution.Models.TwistedPairs

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_apply frobQ_frobQ)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2Model)

private theorem ggF4QGeFourBond_S2_spinMinus8 {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaMinus 4 f).K →* G) (hφ : Function.Injective φ) :
    GGF4QGeFourBond .S2 f hf
      ((ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single (1 : Fin 3) 1)).map φ)
      ((ggRootLevi (ggU .POmegaMinus 4 f).D (Pi.single (2 : Fin 3) 1)).map φ) := by
  obtain ⟨W, hW, hle⟩ := CFSG.ClassicalInvolution.WeakCT.unitaryB2BlockStandardPair_minusDatum_even
    (F := GaloisField 2 f) (K := GaloisField 2 (2 * f)) (GaloisField.card 2 f (by omega))
    (card_galoisField_two_mul 2 f hf) (frobQ_frobQ 2 f hf) (frobQ_apply 2 f) (minusCoeffs_irr 2 f)
    (n := 4) (by norm_num) (i := 1) (j := 2) rfl rfl
  refine ⟨W.map φ, TwistedB2Model.StandardPair.map hW φ hφ, ?_⟩
  rw [← Subgroup.map_sup]
  exact Subgroup.map_mono hle

theorem ggF4QGeFourRk2_bond_of_tableBPosImage_POmegaMinus {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f X) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    CoxeterMatrix.F₄ i j = 4 →
      GGF4QGeFourBond .S2 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)) ∨
        GGF4QGeFourBond .S2 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs)) := by
  intro hl
  by_cases hij : i = j
  · subst hij
    have h1 : CoxeterMatrix.F₄ i i = 1 := CoxeterMatrix.F₄.diagonal i
    omega
  obtain ⟨ψ, hker, -, hpos'⟩ := hpos
  obtain ⟨ν, u, c, d, -, -, -, h4, hSi, hSj⟩ :=
    exists_simplePair_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hAind hpres hXA (by omega) hpos' w
      hij hi hj
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (n := 4) le_rfl
      (minusCoeffs_irr 2 f)).le
  have hψ' : Function.Injective ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) :=
    (MulAut.conj (ψ (ν u))).injective.comp hψ
  have hbond := ggF4QGeFourBond_S2_spinMinus8 (by omega) _ hψ'
  rw [hSi, hSj]
  rcases h4 hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr hbond
  · exact Or.inl hbond

end CFSG.StandardType

end
