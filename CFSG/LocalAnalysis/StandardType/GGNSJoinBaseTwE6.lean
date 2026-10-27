module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Rank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGStdSubExist

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

theorem nsTwE6Bad_card_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) :
    Nat.card ↥Bs ≤ p ^ 7 := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
  obtain ⟨Φ, _T, _w, h⟩ := ggTwE6Bad_model hHyp hL hN
  have hp3 : p = 3 := by
    obtain ⟨-, _, _, hraw⟩ := hL
    obtain ⟨_, _, _, _, _, _, _, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP.2.1
  have hγ : Nat.card (ggGamma L hN).range ≤ 3 ^ 6 :=
    calc Nat.card (ggGamma L hN).range ≤ Nat.card (Multiplicative (Fin 6 → ZMod 3)) :=
          Nat.card_le_card_of_injective Φ h.injective
      _ = 3 ^ 6 := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  calc Nat.card ↥Bs = Nat.card (ggGamma L hN).range * p := hmul.symm
    _ ≤ 3 ^ 6 * p := Nat.mul_le_mul_right p hγ
    _ = p ^ 7 := by rw [hp3]; norm_num

theorem nsTwE6Plus_card_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L) :
    Nat.card ↥Bs ≤ p ^ 7 := by
  obtain ⟨hp, hBs, -, -, -⟩ := hHyp.1.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData hBs
  have h7 : Module.finrank (ZMod p) V ≤ 7 := ggTwE6Row_finrank_le_seven hHyp hL ιV
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  exact Nat.pow_le_pow_right hp.pos h7

theorem nsBaseFrame_twE6
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L ∨
      GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL := by
  have hE6 : GGIsWeylMatrixE (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)) := by
    refine Or.inl ⟨Equiv.refl _, ?_⟩
    apply CoxeterMatrix.ext
    ext i j
    rw [CoxeterMatrix.reindex_apply]
    simp
  refine ⟨Fin 6, inferInstance, CoxeterMatrix.E₆, Or.inr hE6, ?_, ?_, by simp⟩
  · rcases hL with hL | hL
    · exact ggTwE6Bad_weylOfType hHyp hL
    · exact ggTwE6Row_weylOfType hHyp hL
  · rw [Fintype.card_fin]
    rcases hL with hL | hL
    · exact nsTwE6Bad_card_le hHyp hL
    · exact nsTwE6Plus_card_le hHyp hL

theorem nsBaseFrame_twE6_of_cfg
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L ∨
      GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer L Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL :=
  nsBaseFrame_twE6 hcfg.1.1 hL

end NSJoin

end CFSG.StandardType

end
