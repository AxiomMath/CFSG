module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFramePSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameProd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameMod
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.F918C6
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_case9_frame (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hΔ : Concl1617 D ⊥ V hV L A g Δ) (h9 : Case168_9 D ⊥ V hV L) :
    ∃ Z : Subgroup (MulAut (Vtil ⊥ V hV)),
      Z ≤ oddBar D.M ⊥ V hV ∧ Nat.card ↥Z = 7 ∧
      (∀ y ∈ oddBar D.M ⊥ V hV, (∀ z ∈ Z, y * z = z * y) → y ∈ Z) ∧
      (∀ x ∈ Mbar D.M ⊥ V hV, Z.map (MulAut.conj x).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ l ∈ lBar ⊥ V hV L, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ wTil ⊥ V hV L, z w ∈ wTil ⊥ V hV L) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ wTil ⊥ V hV L, z w ≠ w) ∧
      (∀ x ∈ Mbar D.M ⊥ V hV, (wTil ⊥ V hV L).map x.toMonoidHom = wTil ⊥ V hV L →
        (lBar ⊥ V hV L).map (MulAut.conj x).toMonoidHom = lBar ⊥ V hV L) := by
  have hS : Setting16 D ⊥ V L := hC.setting
  obtain ⟨hn, hle, hi, hs, -, -, h910⟩ := hΔ
  have hΔeq : Δ = wConj D.M ⊥ V hV L := h910 (Or.inl h9)
  obtain ⟨⟨e₀⟩, hL3, hs15, -, -⟩ := h9
  have e : ↥(Fstar (Mbar D.M ⊥ V hV)) ≃*
      (Multiplicative (ZMod 7) × ↥(lBar ⊥ V hV L) × ↥(lBar ⊥ V hV L)) := e₀
  have hM : D.M ≤ normalizer (V : Set G) := hS.hyp16.hyp125.normalizer_eq.ge
  have hL : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  have hcj : imgTil ⊥ V hV '' Δ =
      conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (barSub ⊥ V hV L)) := by
    rw [hΔeq]
    exact s16c167_imgTil_wConj hV hM L
  obtain ⟨hn2, -, hsup⟩ := s16c167_imgTil_decomp hV hn hle hi hs
  rw [hcj] at hn2 hsup
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)
  have hSC := s16c167_isPSL_simpleCentreless hL
  have hperf := s16c167_isPSL_isPerfect hL
  have hout := s16c167_isPSL_outer_solvable hL
  have hev := s16c167_isPSL_even_card hL
  have hOutF : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(Fstar (Mbar D.M ⊥ V hV))) :=
    s16c167_frame_outer_cyclic_square_solvable hSC hperf hout e
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hS.hyp151.le
  have hLF : lBar ⊥ V hV L ≤ Fstar (Mbar D.M ⊥ V hV) :=
    s16c167_frame_le_of_perfect hFX hLX hFn hself hOutF hperf
  obtain ⟨hOle, hOn, hOodd⟩ := s16c167_frame_relPPrimeCore_facts (Mbar D.M ⊥ V hV)
  have hZcard : Nat.card ↥((Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
      (Fstar (Mbar D.M ⊥ V hV)).subtype) = 7 := by
    rw [s16c167_frame_centerF_card hSC.center e, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hZconj := s16c167_frame_centerF_conj (X := Mbar D.M ⊥ V hV)
    (F := Fstar (Mbar D.M ⊥ V hV)) hFn
  have hZX : (Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
      (Fstar (Mbar D.M ⊥ V hV)).subtype ≤ Mbar D.M ⊥ V hV := fun z hz =>
    hFX ((s16c167_frame_mem_centerF.1 hz).1)
  have hZn : ∀ x ∈ Mbar D.M ⊥ V hV, ∀ z ∈ (Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
      (Fstar (Mbar D.M ⊥ V hV)).subtype,
      x * z * x⁻¹ ∈ (Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
        (Fstar (Mbar D.M ⊥ V hV)).subtype := by
    intro x hx z hz
    rw [← hZconj x hx]
    exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hz
  obtain ⟨hcs, hci⟩ := s16c167_frame_center_sup_commutator hperf hSC.center e
  have hOF := s16c167_frame_odd_inf_le_centerF hFX hOn hOodd
    (fun N hN hodd => s16c167_frame_odd_normal_le_center hSC.simple hev e hN hodd)
  refine ⟨(Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map (Fstar (Mbar D.M ⊥ V hV)).subtype,
    s16c167_frame_le_relPPrimeCore hZX hZn (by rw [hZcard]; decide), hZcard,
    s16c167_frame_centralizer_le_centerF hFX hOle hFn hOn hself hOF hcs hci, hZconj,
    ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    exact (s16c167_frame_mem_centerF.1 hz).2 l (hLF hl)
  · intro z hz w hw
    refine commSub_top_stable151b (X := barSub ⊥ V hV L) (g := z) (fun x hx => ?_) w hw
    have h1 : x * z = z * x := ((s16c167_frame_mem_centerF.1 hz).2 x (hLF hx)).symm
    have h2 : z * x * z⁻¹ = x := by rw [← h1]; group
    rw [h2]
    exact hx
  · exact s16c167_frame_faithful_of_conj_sup (p := 7) (by norm_num) hZcard hZconj hsup
  · intro x hx hstab
    exact s16c167_normalizes_of_stab hcls hn2 (barSub ⊥ V hV L)
      ⟨1, (Mbar D.M ⊥ V hV).one_mem, by ext y; simp⟩ x hx hstab

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
