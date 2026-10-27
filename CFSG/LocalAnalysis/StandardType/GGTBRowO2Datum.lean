module

public import CFSG.LocalAnalysis.StandardType.GGTBRowO2Frame
public import CFSG.LocalAnalysis.StandardType.GGTBRowDCartan
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpCartan
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpan
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggO2Row_datum_of_frame {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {k : ℕ} (hk3 : 3 ≤ k)
    (hcard : Nat.card ↥(ggGamma L hN).range = p ^ k) {M : CoxeterMatrix (Fin k)}
    (hM : GGIsWeylMatrix M) {C : Matrix (Fin k) (Fin k) ℤ} (hC : GGIntCartan M C)
    (hno6 : ∀ i j, M i j ≠ 6) (par : Fin k → Fin k) (root : Fin k)
    (hpar : ∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → (par i).1 < i.1) (hdet : ((C.det : ℤ) : ZMod p) ≠ 0)
    (hF : GGWeylFrame p (ggGamma L hN).range M) :
    Nonempty (GGExcReflTBWeylDatum p Bs L J) := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  have hW : GGWeylOfType p M (ggAutomizer L Bs) :=
    ggWeylOfType_of_frame hp hp2 hBs hSC hNT hN hZ hF
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
  have hV : Module.finrank (ZMod p) V = k + 1 := by
    haveI : Module.Finite (ZMod p) V := by
      haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
      exact Module.Finite.of_finite
    have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
        Nat.card_zmod]
    have hpow : p ^ Module.finrank (ZMod p) V = p ^ (k + 1) := by
      rw [← hcardV, ← hmul, hcard, pow_succ]
    exact Nat.pow_right_injective hp.two_le hpow
  have hk : k ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) := by
    have := ggReflSpan_card_le_finrank_of_weylOfType hp2 hNT hC hno6 par root (fun i => i.1)
      hpar hdepth hdet hW ιV
    simpa using this
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT hM (by simpa using hk3) hC hno6 par root
    (fun i => i.1) hpar hdepth hW ιV (Or.inl (by omega))

theorem ggO2Row_recipe_dbFrame
    {m n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n + 1) (hme : Even m) (hm : 4 ≤ m)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusDBFrameW p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ m) hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus (by omega) b c hbc),
    ggO2Row_dbFrameW_of_evenSignedPermEltSC (kP := fun k => k = m + 1) hp hp2 (fun _ h => h) hZ
      hcp (fun k hk => by omega)
      (ggOrthEvenTorusInput_holds.2 K m p b c hm hme hbc hp (by rw [hK]; exact hpn))⟩

theorem ggO2Row_labelAll_dbFrame
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTBRowR5O2 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusDBFrameW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, ho, hpn⟩ := h
  subst htag
  dsimp only at h4 ho hpn hlab
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨j, hj⟩ := ho
    exact ggO2Row_recipe_dbFrame hp hlab.1 hpn ⟨j, by omega⟩ (by omega) hQ

theorem ggO2Row_labelAllGuard_dbFrame
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTBRowR5O2 p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusDBFrameW p r R I) :=
  nbrC_labelAll_guard (ggO2Row_labelAll_dbFrame hp hlab h)

theorem ggO2Row_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ k : ℕ, 4 ≤ k ∧ Nat.card ↥(ggGamma L hN).range = p ^ k ∧
      (GGWeylFrame p (ggGamma L hN).range (ggCoxeterMatrixD k) ∨
        GGWeylFrame p (ggGamma L hN).range (CoxeterMatrix.B k)) := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab)
    (fun lab hlab hs => ggO2Row_labelAllGuard_dbFrame hp hlab hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  exact hT L (ggQuotHom θ) _ (ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3)

theorem ggExcReflTBWeylDatumQFourOn_rowR5O2 :
    GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab := by
  intro G _ _ p B Bs x L D J hHyp _ _ hL _
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  obtain ⟨k, hk4, hcard, hF | hF⟩ := ggO2Row_frame hHyp hL hNL
  · obtain ⟨hno6, hpar, hdepth⟩ := ggCartanD_forkTree hk4 ⟨0, by omega⟩ rfl
    exact ggO2Row_datum_of_frame hHyp hNL (by omega) hcard
      (Or.inl ⟨k, Equiv.refl _, by omega, Or.inr (Or.inr ⟨hk4,
        (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm⟩)⟩)
      (ggIntCartan_D k) hno6 (ggDForkPar k) ⟨0, by omega⟩ hpar hdepth
      (ggCartanD_det_ne_zero hp2 (by omega)) hF
  · obtain ⟨hno6, hpar, hdepth⟩ := ggCartanC_pathTree (k := k) ⟨0, by omega⟩ rfl
    have hdet : (((CartanMatrix.C k).det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.C_det (by omega : 0 < k)]
      exact_mod_cast zmod_two_ne_zero hp2
    exact ggO2Row_datum_of_frame hHyp hNL (by omega) hcard
      (Or.inl ⟨k, Equiv.refl _, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩)
      (ggIntCartan_C k) hno6 (ggPathPar k) ⟨0, by omega⟩ hpar hdepth hdet hF

end CFSG.StandardType

end
