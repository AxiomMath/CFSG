module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowOFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpCartan
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpan
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_bFrame {S : ℕ → LargeEvenLabel → Prop}
    (hF : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs L →
        ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), ∃ k : ℕ, 3 ≤ k ∧
          Nat.card ↥(ggGamma L hN).range = p ^ k ∧
          GGWeylFrame p (ggGamma L hN).range (CoxeterMatrix.B k)) :
    GGExcReflTBWeylDatumQFourOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  obtain ⟨k, hk3, hcard, hF'⟩ := hF G p B Bs x L D J hHyp hL hNL
  have hW : GGWeylOfType p (CoxeterMatrix.B k) (ggAutomizer L Bs) :=
    ggWeylOfType_of_frame hp hp2 hBs hSC hNT hNL hZ hF'
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  obtain ⟨hno6, hpar, hdepth⟩ := ggCartanC_pathTree (k := k) ⟨0, by omega⟩ rfl
  have hdet : (((CartanMatrix.C k).det : ℤ) : ZMod p) ≠ 0 := by
    rw [CartanMatrix.C_det (by omega : 0 < k)]
    have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
      haveI : Fact p.Prime := ⟨hp⟩
      exact_mod_cast zmod_two_ne_zero hp2
    exact h2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hNL
  have hV : Module.finrank (ZMod p) V = k + 1 := by
    haveI : Module.Finite (ZMod p) V := by
      haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
      exact Module.Finite.of_finite
    haveI : Fact p.Prime := ⟨hp⟩
    have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
        Nat.card_zmod]
    have hpow : p ^ Module.finrank (ZMod p) V = p ^ (k + 1) := by
      rw [← hcardV, ← hmul, hcard, pow_succ]
    exact Nat.pow_right_injective hp.two_le hpow
  have hk : k ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have := ggReflSpan_card_le_finrank_of_weylOfType hp2 hNT (ggIntCartan_C k) hno6
      (ggPathPar k) ⟨0, by omega⟩ (fun i => i.1) hpar hdepth hdet hW ιV
    simpa using this
  haveI : Fact p.Prime := ⟨hp⟩
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT (M := CoxeterMatrix.B k)
    (Or.inl ⟨k, Equiv.refl _, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩) (by simpa using hk3)
    (ggIntCartan_C k) hno6 (ggPathPar k) ⟨0, by omega⟩ (fun i => i.1) hpar hdepth hW ιV
    (Or.inl (by omega))

theorem ggExcReflTBWeylDatumQFourOn_rowR5O1 :
    GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5O1 p lab :=
  ggExcReflTBWeylDatumQFourOn_of_bFrame fun _ _ _ _ _ _ _ _ _ _ hHyp hL hN =>
    ggO1Row_frame hHyp hL hN

end CFSG.StandardType

end
