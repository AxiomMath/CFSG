module

public import CFSG.Sporadic.MI301Three.Class
public import CFSG.Sporadic.MI301Three.Elem
public import CFSG.Sporadic.MI301Three.ElemCo1
public import CFSG.Sporadic.MI301Three.RowI
public import CFSG.Sporadic.MI301Three.RowK
public import CFSG.Sporadic.MI301.LeechFix
public import CFSG.Sporadic.MI301.RowMax
public import CFSG.Sporadic.MI301.Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeAGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public section

namespace CFSG.Sporadic.MI301Three

open CFSG.Blueprint CFSG.Open CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301 Subgroup

section Leech

variable {G : Type} [Group G] [Finite G] {t ζ : G}

private theorem exists_i301ARowCfg_leech (h : GMSLeechCentralizer t) (L : LeechSystem t)
    (hζt : ζ ∈ centralizer ({t} : Set G)) (hζ3 : orderOf ζ = 3)
    (hy : IsConj TabMThreeALeech.c0 (L.φ ⟨ζ, hζt⟩))
    (hIeq : rowIOf 3 ζ = centralizer ({ζ} : Set G)) (hI : RowI .m3 3 (rowIOf 3 ζ))
    (hOut : ∀ σ : MulAut G, ∃ g : G, σ = MulAut.conj g)
    (hrk : GLATwoLocalRank 3 NativeSporadic.Co1 < 6) :
    ∃ B₁ : Subgroup G, I301ARowCfg .m3 (leechQ t) B₁ ζ := by
  obtain ⟨hQe, hQc⟩ := MI301.leech_hR h
  obtain ⟨E, hE, hEc, hyE⟩ := exists_elemAbelian_mem_of_isConj_c0 hy
  obtain ⟨B₁, hBt, hB, hBc, hζB⟩ := exists_elemAbelian_lift_leech L hQc hζt hζ3 hE hEc hyE
  have hodd : Odd (orderOf ζ) := by
    rw [hζ3]
    exact ⟨1, rfl⟩
  have hfix : (co1Fix (L.φ ⟨ζ, hζt⟩)).ncard = 2 ^ 12 := TabMThreeALeech.ncard_fix_threeB hy
  have hK : rowKOf 3 ζ (leechQ t) =
      GLAPLayer 3 (centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) := by
    unfold rowKOf
    rw [hIeq, MI301.normalizer_leechQ h]
  have hKt : RowK .m3 3 (rowKOf 3 ζ (leechQ t)) := by
    rw [hK]
    exact isTypeWithCenter_rowK_leech L hQc hζt hζ3 hy
  have hR0 : Nat.card (rowR0Of ζ (leechQ t)) = 2 ^ 13 :=
    (MI301.card_rowR0_leech L hζt hodd).trans (by rw [hfix]; norm_num)
  have hc : centerOf (rowR0Of ζ (leechQ t)) = zpowers t :=
    MI301.centerOf_rowR0_leech L hζt hodd
  have hK6 : rowKOf 3 ζ (leechQ t) = GLAPLayer 3 (centralizer ({ζ} : Set G) ⊓
      centralizer (centerOf (rowR0Of ζ (leechQ t)) : Set G)) := by
    rw [hc, zpowers_eq_closure, centralizer_closure, hK]
  have hR0t := MI301.isExtraSpec2_rowR0_leech L hζt hodd (by rw [hfix]; norm_num)
  have hζ1 : ζ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hζ3
    exact absurd hζ3 (by norm_num)
  exact ⟨B₁,
    { hR := ⟨hQe, hQc⟩
      hB := ⟨hB, hBc⟩
      hBN := hBt.trans (MI301.normalizer_leechQ h).ge
      hd := ⟨hζB, hζ1⟩
      hI := hI
      hK := hKt
      hR0 := hR0
      hR0t := Or.inl hR0t
      hK6 := Or.inr hK6
      hNL := fun h5 => absurd h5 (by decide)
      hMax := MI301.hMax_leech h Nat.prime_three (by norm_num) hrk hOut hB hBc
        hBt }⟩

end Leech

section MGriess

theorem i301ARow_m3 : I301ARow .m3 := by
  have hG : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO :=
    CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  have hB3 : TabBThreeACard := tabBThreeACard_thm
  obtain ⟨hζ3, hinv, h23, -⟩ := TabMThreeA.zetaM_spec hB3 hG
  obtain ⟨t, htD, htc, htB⟩ :=
    TabMThreeA.exists_twoB_mem_range_yMc hG (TabMThreeA.ker_yMc_le hG)
  rw [← TabMThreeA.centralizer_zetaM_eq_range hB3 hG] at htD
  have htζ := mem_centralizer_singleton_iff.1 htD
  have hζt : TabMThreeA.zetaM hG ∈ centralizer ({t} : Set MGriess) :=
    mem_centralizer_singleton_iff.2 htζ.symm
  have h : GMSLeechCentralizer t := GMSLeechCentralizer.of_isConj gmsLeechCentralizer_xGriess htB
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness h
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hrk4 : GLATwoLocalRank 3 NativeSporadic.Co1 ≤ 4 :=
    H1017.i1016Co1Fact_holds NativeSporadic.Co1 ⟨.sporadic .Co1, rfl, ⟨b⟩⟩
  obtain ⟨hIeq, hI⟩ := rowI_zetaM hB3 hG
  obtain ⟨B₁, hcfg⟩ := exists_i301ARowCfg_leech h L hζt hζ3
    (isConj_c0_of_zeta hζ3 hinv h23 htc htζ htB L hζt) hIeq hI
    MI301.mGriess_mulAut_eq_conj (hrk4.trans_lt (by norm_num))
  exact i301ARow_of_model (row := .m3) MGriess MI301.nonempty_mGriess_equiv_sporadicM hcfg

end MGriess

end CFSG.Sporadic.MI301Three

end
