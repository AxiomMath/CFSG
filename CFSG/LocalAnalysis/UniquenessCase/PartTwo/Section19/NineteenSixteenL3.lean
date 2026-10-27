module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TransvectionModelCompat
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalIdentification
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLSpFourFinal
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316Small
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316Narrow
public import CFSG.RankThree.PartTwo.Sec19.F194Item316X
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenOutcomeFive
public import CFSG.CGT.Foote82.T66.MC2Arith
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Main
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAlt
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthCent
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthTwoPart
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SpSmall
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.HardMathSupport.Curtis.Coordinator.PLType
open CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certificates


variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
  {r : ℕ} {Y N Dsub H S : Subgroup G}

omit [Finite G] in
private theorem bar2_equiv_alt_of_isAltNaturalType {n : ℕ}
    (h : CFSG.RankThree.PartTwo.IsAltNaturalType Dsub n) :
    Nonempty (Bar2 Dsub ≃* alternatingGroup (Fin n)) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

omit [Finite G] in
private theorem bar2_equiv_omegaMinus_of_isOmegaMinusType {m : ℕ}
    (h : CFSG.RankThree.PartTwo.IsOmegaMinusType Dsub m) :
    Nonempty (Bar2 Dsub ≃* ↥(omegaMinusTwo m)) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

omit [Finite G] in
private theorem bar2_equiv_alt_of_isA7FourType
    (h : CFSG.RankThree.PartTwo.IsA7FourType Dsub) :
    Nonempty (Bar2 Dsub ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨⟨α, hα, hker⟩, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

omit [Finite G] in
private theorem isOmegaMinus_bar2_of_isOmegaMinusType {m : ℕ}
    (h : CFSG.RankThree.PartTwo.IsOmegaMinusType Dsub m) :
    IsOmegaMinus (Bar2 Dsub) (2 * (m + 1)) 1 := by
  obtain ⟨e⟩ := bar2_equiv_omegaMinus_of_isOmegaMinusType h
  refine ⟨⟨m + 1, by ring⟩, ZMod 2, inferInstance, inferInstance, 1, 1, by norm_num, ?_, ?_⟩
  · exact CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
  · show Nonempty (Bar2 Dsub ≃* StatedProj (StatedOmega (StatedQuadMinus
      ((2 * (m + 1)) / 2) (ZMod 2) 1 1)))
    rw [Nat.mul_div_cancel_left (m + 1) (by norm_num)]
    exact ⟨e.trans ((MulEquiv.subgroupCongr
        (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega m)).trans
      (CFSG.HardMathSupport.Cooperstein.StructureLie.statedProjEquiv
        (StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1))).symm)⟩

omit [Finite G] in
private theorem isOmegaPlus_bar2_of_isAltNaturalType_eight
    (h : CFSG.RankThree.PartTwo.IsAltNaturalType Dsub 8) :
    IsOmegaPlus (Bar2 Dsub) 6 1 := by
  obtain ⟨e⟩ := bar2_equiv_alt_of_isAltNaturalType h
  refine ⟨⟨3, by ring⟩, ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
  show Nonempty (Bar2 Dsub ≃* StatedProj (StatedOmega (StatedQuadPlus (6 / 2)
    (ZMod 2))))
  rw [show (6 / 2 : ℕ) = 3 by norm_num]
  let eqp : ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) ≃* alternatingGroup (Fin 8) :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8
  exact ⟨e.trans (eqp.symm.trans
    (CFSG.HardMathSupport.Cooperstein.StructureLie.statedProjEquiv
      (StatedOmega (StatedQuadPlus 3 (ZMod 2)))).symm)⟩

private theorem isNontrivialParabolic_alt_six_of_sfour
    {P : Subgroup (alternatingGroup (Fin 6))} (e : ↥P ≃* Equiv.Perm (Fin 4)) :
    IsNontrivialParabolic (alternatingGroup (Fin 6)) P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardP : Nat.card ↥P = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hPne : P ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top, hA6card] at hcardP
    omega
  let T0 : Sylow 2 ↥P := default
  have hT0card : Nat.card (T0 : Subgroup ↥P) = 8 := by
    rw [Sylow.card_eq_multiplicity, hcardP]
    decide +kernel
  let Tsub : Subgroup (alternatingGroup (Fin 6)) := (T0 : Subgroup ↥P).map P.subtype
  have hTsubcard : Nat.card Tsub = 8 := by
    change Nat.card (Subgroup.map P.subtype (T0 : Subgroup ↥P)) = 8
    rw [Subgroup.card_map_of_injective P.subtype_injective, hT0card]
  have hTsubP : IsPGroup 2 Tsub := (T0.isPGroup').map P.subtype
  have hTsuble : Tsub ≤ P := by
    change Subgroup.map P.subtype (T0 : Subgroup ↥P) ≤ P
    exact Subgroup.map_subtype_le _
  have hidx : Tsub.index = 45 := by
    have h := Subgroup.card_mul_index Tsub
    rw [hTsubcard, hA6card] at h
    omega
  have hodd : ¬ 2 ∣ Tsub.index := by rw [hidx]; decide
  let T : Sylow 2 (alternatingGroup (Fin 6)) := hTsubP.toSylow hodd
  have hTcoe : (T : Subgroup (alternatingGroup (Fin 6))) = Tsub :=
    IsPGroup.toSylow_coe hTsubP hodd
  obtain ⟨S0, hS0⟩ := CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_six
  have hNT : Subgroup.normalizer ((T : Subgroup (alternatingGroup (Fin 6))) :
      Set (alternatingGroup (Fin 6))) = Tsub :=
    (CFSG.LieType.SteinbergBR.OddSylow.normalizer_eq_of_one S0 hS0 T).trans hTcoe
  refine ⟨⟨T, ?_⟩, hPne, T, ?_⟩
  · change Subgroup.normalizer (((T : Subgroup (alternatingGroup (Fin 6))) :
      Set (alternatingGroup (Fin 6)))) ≤ P
    rw [hNT]
    exact hTsuble
  · change Subgroup.normalizer (((T : Subgroup (alternatingGroup (Fin 6))) :
      Set (alternatingGroup (Fin 6)))) < P
    rw [hNT]
    exact lt_of_le_of_ne hTsuble (by
      intro hPQ
      have hcard : Nat.card Tsub = Nat.card ↥P := by rw [hPQ]
      omega)

omit [Finite G] in
private theorem not_alt_of_isOrthogonalTwo {n : ℕ}
    (hO : CFSG.AGLEmbedding.IsOrthogonalTwo ↥(CFSG.AGLEmbedding.barM H Dsub))
    (hn : 5 ≤ n) (hA : IsAlt ↥(CFSG.AGLEmbedding.barM H Dsub) n)
    (h5 : n ≠ 5) (h6 : n ≠ 6) (h8 : n ≠ 8) : False := by
  obtain ⟨eA⟩ := hA
  rcases hO with ⟨d, ⟨m, q, hq, hcase⟩, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩
  · rcases hcase with hcase | hcase | ⟨-, hcase⟩
    · exact ((altTypeExcl_holds n hn).1 m d ⟨q, hq, Or.inl hcase⟩).elim (eA.symm.trans e)
    · exact ((altTypeExcl_holds n hn).1 m d ⟨q, hq, Or.inr hcase⟩).elim (eA.symm.trans e)
    · exact ((altTypeExcl_holds n hn).2.1 d ⟨q, hq, hcase⟩).elim (eA.symm.trans e)
  · have hk5 : 5 ≤ k := by rcases hk with rfl | rfl | rfl <;> norm_num
    have hnk : n = k :=
      (altTypeExcl_holds n hn).2.2 k hk5 ⟨eA.symm.trans e⟩
    rcases hk with rfl | rfl | rfl
    · exact h5 hnk
    · exact h6 hnk
    · exact h8 hnk

private theorem inClassXBlock_of_odd_alt {n : ℕ}
    (hshort : CFSG.QuasithinUnique.IsShort2 Dsub) (hn : Odd n)
    (h : CFSG.RankThree.PartTwo.IsAltNaturalType Dsub n) :
    CFSG.AGLEmbedding.InClassXBlock Dsub := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact (CFSG.RankThree.PartTwo.Sec19.false_of_isAltNaturalType_one
      (CFSG.RankThree.PartTwo.IsShort2.isShort hshort) h).elim
  · refine ⟨hshort, Or.inr ⟨k, hk, ?_⟩⟩
    exact CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.isAltType_of_isAltNaturalType
      (⟨k, rfl⟩ : Odd (2 * k + 1)) h

private theorem p19_16_4_of_model
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h3 : CFSG.AGLEmbedding.NineThreeThree H S Dsub) {m : ℕ} {ε : Bool}
    (hm : m = 3 ∨ m = 4) (hΩ : IsOmegaEps2 (Bar2 Dsub) ε m)
    (hcard : Nat.card (CFSG.AGLEmbedding.blockPL H S Dsub) =
      if m = 3 then 720 else 1451520) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := ctx19_14_isKGroup h
  have hhyp := ctx19_14_asc81bHyp h h11
  have hK := ctx19_14_isWeakSBlock h h11
  have ht := h3.2.2.2
  have hQV := CFSG.HardMathSupport.Cooperstein.StructureLie.commutator_pCore_le_blockV
    hX hhyp hK ht
  have hZ := CFSG.HardMathSupport.Cooperstein.StructureLie.centre_barM_trivial
    hX hhyp hK ht hQV
  obtain ⟨W, _, _, _, Hc, tt, e, hmodel, hirr, hblock⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_transvectionModel_compat
      (M := H) (S := S) (L := Dsub) hX hhyp hK h3 hZ
  let eb := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.barMEquiv hK.le hK.inf_twoCore
  let e' : Bar2 Dsub ≃* ↥⁅Hc, Hc⁆ := eb.trans e
  have hYmap : (barOfInter D.M Dsub).map e'.toMonoidHom =
      (Subgroup.centralizer ({tt} : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))).subgroupOf
        ⁅Hc, Hc⁆ := by
    have h1 : (barOfInter D.M Dsub).map eb.toMonoidHom =
        (CFSG.AGLEmbedding.blockPL H S Dsub).subgroupOf (CFSG.AGLEmbedding.barM H Dsub) := by
      rw [ctx19_14_barOfInter_eq h h11]
      exact CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.map_starIm_barMEquiv
        hK.le hK.inf_twoCore (Subgroup.normalizer (S : Set G))
    calc (barOfInter D.M Dsub).map e'.toMonoidHom
        = ((barOfInter D.M Dsub).map eb.toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_map]
          rfl
      _ = ((CFSG.AGLEmbedding.blockPL H S Dsub).subgroupOf
            (CFSG.AGLEmbedding.barM H Dsub)).map e.toMonoidHom := by rw [h1]
      _ = _ := hblock
  have hcardY : Nat.card (barOfInter D.M Dsub) = if m = 3 then 720 else 1451520 := by
    have hYeq : Nat.card (barOfInter D.M Dsub) =
        Nat.card (CFSG.AGLEmbedding.blockPL H S Dsub) := by
      rw [← Subgroup.card_map_of_injective (f := eb.toMonoidHom) eb.injective]
      have hle : CFSG.AGLEmbedding.blockPL H S Dsub ≤ CFSG.AGLEmbedding.barM H Dsub := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        exact Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).2)
      have h1 : (barOfInter D.M Dsub).map eb.toMonoidHom =
          (CFSG.AGLEmbedding.blockPL H S Dsub).subgroupOf (CFSG.AGLEmbedding.barM H Dsub) := by
        rw [ctx19_14_barOfInter_eq h h11]
        exact CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.map_starIm_barMEquiv
          hK.le hK.inf_twoCore (Subgroup.normalizer (S : Set G))
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hYeq, hcard]
  have hcent :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.isCentralizerOfTransvectionIn_of_model
      hmodel hirr e' (barOfInter D.M Dsub) hYmap hcardY
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, Or.inl ⟨ε, hΩ, hcent⟩⟩)))

private theorem p19_16_5_of_alt_six
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (hshape : BlockShape ↥(CFSG.AGLEmbedding.barM H Dsub)
      ↥(CFSG.AGLEmbedding.blockPL H S Dsub))
    (e6 : Bar2 Dsub ≃* alternatingGroup (Fin 6)) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := ctx19_14_isWeakSBlock h h11
  let eb := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.barMEquiv hK.le hK.inf_twoCore
  let e6X : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* alternatingGroup (Fin 6) := eb.symm.trans e6
  have hP : Nonempty (↥(CFSG.AGLEmbedding.blockPL H S Dsub) ≃* Equiv.Perm (Fin 4)) :=
    conj_alt_six altTypeExcl_holds hshape e6X
  obtain ⟨eP'⟩ := hP
  have hqOpen : CFSG.Open.IsQuasisimple (Bar2 Dsub) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eb hK.component.2.2
  have hcenter : Subgroup.center (Bar2 Dsub) = ⊥ :=
    CFSG.Quasithin.H13.Lem8.center_eq_bot_of_mulEquiv e6
      (CFSG.Quasithin.H13.Lem8.center_alternatingGroup_eq_bot (by norm_num))
  obtain ⟨eInf⟩ := uc22p21k_barInf_equiv_of_center_bot hqOpen hcenter
  have hList : List19_16_5 (BarInf Dsub) := Or.inr (Or.inl ⟨eInf.trans e6⟩)
  have hle : CFSG.AGLEmbedding.blockPL H S Dsub ≤ CFSG.AGLEmbedding.barM H Dsub := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).2)
  let PX : Subgroup ↥(CFSG.AGLEmbedding.barM H Dsub) :=
    (CFSG.AGLEmbedding.blockPL H S Dsub).subgroupOf (CFSG.AGLEmbedding.barM H Dsub)
  have ePX : ↥PX ≃* ↥(CFSG.AGLEmbedding.blockPL H S Dsub) :=
    Subgroup.subgroupOfEquivOfLe hle
  let PA : Subgroup (alternatingGroup (Fin 6)) := PX.map e6X.toMonoidHom
  have ePA : ↥PA ≃* Equiv.Perm (Fin 4) :=
    (Subgroup.equivMapOfInjective PX e6X.toMonoidHom e6X.injective).symm.trans
      (ePX.trans eP')
  have hparA : IsNontrivialParabolic (alternatingGroup (Fin 6)) PA :=
    isNontrivialParabolic_alt_six_of_sfour ePA
  have hparX : IsNontrivialParabolic ↥(CFSG.AGLEmbedding.barM H Dsub) PX := by
    obtain ⟨-, hne, T, hlt⟩ := hparA
    have h' := isNontrivialParabolic_map e6X.symm hne T hlt
    simpa [PA, PX, Subgroup.map_map] using h'
  have hparB : IsNontrivialParabolic (Bar2 Dsub) (barOfInter D.M Dsub) := by
    obtain ⟨-, hne, T, hlt⟩ := hparX
    have h' := isNontrivialParabolic_map eb.symm hne T hlt
    have h1 : (barOfInter D.M Dsub).map eb.toMonoidHom = PX := by
      rw [ctx19_14_barOfInter_eq h h11]
      exact CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.map_starIm_barMEquiv
        hK.le hK.inf_twoCore (Subgroup.normalizer (S : Set G))
    have hPXeq : PX.map eb.symm.toMonoidHom = barOfInter D.M Dsub := by
      rw [← h1, Subgroup.map_map]
      rw [show eb.symm.toMonoidHom.comp eb.toMonoidHom =
        MonoidHom.id (Bar2 Dsub) by
        ext x
        simp]
      rw [Subgroup.map_id]
    rw [hPXeq] at h'
    exact h'
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hList, hparB⟩)))

omit [Finite G] in
private theorem card_blockPL_of_alt_eight
    (hshape : BlockShape ↥(CFSG.AGLEmbedding.barM H Dsub)
      ↥(CFSG.AGLEmbedding.blockPL H S Dsub))
    (e8 : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* alternatingGroup (Fin 8)) :
    Nat.card ↥(CFSG.AGLEmbedding.blockPL H S Dsub) = 720 := by
  have hfac8 : (Nat.card (alternatingGroup (Fin 8))).factorization 2 = 6 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide +kernel
  rcases conj_alt altTypeExcl_holds hshape (n := 8) (by norm_num) e8 with
    ⟨h6, -⟩ | ⟨k, hk, hS⟩ | hP
  · omega
  · obtain ⟨eS⟩ := hS
    have hk6 : k * (k - 1) = 6 := by rw [← hk, hfac8]
    have hk3 : k = 3 := by
      have := eq_of_mul_pred_eq (m := 3) (by norm_num) (by simpa using hk6)
      exact this
    subst hk3
    rw [Nat.card_congr eS.toEquiv,
      CFSG.HardMathSupport.RichardWeiss.Proving.PLType.card_statedSp_two_two]
  · obtain ⟨eP⟩ := hP
    rw [Nat.card_congr eP.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num

omit [Finite G] in
private theorem card_blockPL_of_omegaMinus_two
    (hshape : BlockShape ↥(CFSG.AGLEmbedding.barM H Dsub)
      ↥(CFSG.AGLEmbedding.blockPL H S Dsub))
    (e2 : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* ↥(omegaMinusTwo 2)) :
    Nat.card ↥(CFSG.AGLEmbedding.blockPL H S Dsub) = 720 := by
  have hX : Nat.card ↥(CFSG.AGLEmbedding.barM H Dsub) = 25920 := by
    rw [Nat.card_congr e2.toEquiv, CFSG.CGT.Foote82.MC2.card_omegaMinusTwo_two]
  rcases hshape with ⟨⟨eA6⟩, -⟩ | ⟨k, hk, hS⟩ | ⟨m, hm, eAm, hP⟩
  · have h360 : Nat.card ↥(CFSG.AGLEmbedding.barM H Dsub) = 360 := by
      rw [Nat.card_congr eA6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num
    omega
  · obtain ⟨eP⟩ := hS
    have hfac : (Nat.card ↥(CFSG.AGLEmbedding.barM H Dsub)).factorization 2 = 6 := by
      rw [hX]
      decide +kernel
    have hk6 : k * (k - 1) = 6 := by rw [← hk, hfac]
    have hk3 : k = 3 := by
      have := eq_of_mul_pred_eq (m := 3) (by norm_num) (by simpa using hk6)
      exact this
    subst hk3
    rw [Nat.card_congr eP.toEquiv,
      CFSG.HardMathSupport.RichardWeiss.Proving.PLType.card_statedSp_two_two]
  · obtain ⟨eAm⟩ := eAm
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hAcard : Nat.card (alternatingGroup (Fin m)) = Nat.card ↥(omegaMinusTwo 2) := by
      rw [← Nat.card_congr eAm.toEquiv, Nat.card_congr e2.toEquiv]
    have hfac : m.factorial / 2 = Nat.card ↥(omegaMinusTwo 2) := by
      rw [← hAcard, nat_card_alternatingGroup, Nat.card_fin]
    exact (CFSG.CGT.Foote82.MC2.factorial_div_two_ne_card_omegaMinusTwo
      (m := 2) (Or.inl rfl) hfac).elim

omit [Finite G] in
private theorem card_blockPL_of_omegaMinus_three
    (hshape : BlockShape ↥(CFSG.AGLEmbedding.barM H Dsub)
      ↥(CFSG.AGLEmbedding.blockPL H S Dsub))
    (e3 : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* ↥(omegaMinusTwo 3)) :
    Nat.card ↥(CFSG.AGLEmbedding.blockPL H S Dsub) = 1451520 := by
  have hX : Nat.card ↥(CFSG.AGLEmbedding.barM H Dsub) = 197406720 := by
    rw [Nat.card_congr e3.toEquiv, CFSG.CGT.Foote82.MC2.card_omegaMinusTwo_three]
  rcases hshape with ⟨⟨eA6⟩, -⟩ | ⟨k, hk, hS⟩ | ⟨m, hm, eAm, hP⟩
  · have h360 : Nat.card ↥(CFSG.AGLEmbedding.barM H Dsub) = 360 := by
      rw [Nat.card_congr eA6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num
    omega
  · obtain ⟨eP⟩ := hS
    have hfac : (Nat.card ↥(CFSG.AGLEmbedding.barM H Dsub)).factorization 2 = 12 := by
      rw [hX]
      decide +kernel
    have hk12 : k * (k - 1) = 12 := by rw [← hk, hfac]
    have hk4 : k = 4 := by
      have := eq_of_mul_pred_eq (m := 4) (by norm_num) (by simpa using hk12)
      exact this
    subst hk4
    rw [Nat.card_congr eP.toEquiv,
      CFSG.RankThree.PartTwo.Late.KFParSp6.card_stated_three]
  · obtain ⟨eAm⟩ := eAm
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hAcard : Nat.card (alternatingGroup (Fin m)) = Nat.card ↥(omegaMinusTwo 3) := by
      rw [← Nat.card_congr eAm.toEquiv, Nat.card_congr e3.toEquiv]
    have hfac : m.factorial / 2 = Nat.card ↥(omegaMinusTwo 3) := by
      rw [← hAcard, nat_card_alternatingGroup, Nat.card_fin]
    exact (CFSG.CGT.Foote82.MC2.factorial_div_two_ne_card_omegaMinusTwo
      (m := 3) (Or.inr rfl) hfac).elim

theorem p19_16_of_nineThreeThree
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h3 : CFSG.AGLEmbedding.NineThreeThree H S Dsub)
    (hL : CFSG.RankThree.PartTwo.IsTypeScriptL Dsub) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := ctx19_14_isKGroup h
  have hhyp := ctx19_14_asc81bHyp h h11
  have hK := ctx19_14_isWeakSBlock h h11
  have ht := h3.2.2.2
  have hQV := CFSG.HardMathSupport.Cooperstein.StructureLie.commutator_pCore_le_blockV
    hX hhyp hK ht
  have hZ := CFSG.HardMathSupport.Cooperstein.StructureLie.centre_barM_trivial
    hX hhyp hK ht hQV
  have hshape : BlockShape ↥(CFSG.AGLEmbedding.barM H Dsub)
      ↥(CFSG.AGLEmbedding.blockPL H S Dsub) :=
    block_shape OrthCent.orthTransvectionCent_holds
      CFSG.HardMathSupport.RichardWeiss.Proving.PLType.symTransvectionCent_holds
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.spFourTransvectionCent_holds
      orthTwoPart_holds hX hhyp hK h3 hZ
  let eb := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.barMEquiv hK.le hK.inf_twoCore
  have hqOpen : CFSG.Open.IsQuasisimple (Bar2 Dsub) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eb hK.component.2.2
  have hq : CFSG.IsQuasisimple (Bar2 Dsub) :=
    CFSG.RankThree.PartTwo.Sec19.Item194Proof.isQuasisimple_of_open hqOpen
  have hMmax : CFSG.IsMaximalTwoLocal N :=
    CFSG.LocalAnalysis.RankThreeUC.isMaximalTwoLocal_of_rankThreeIsMaxTwoLocal h.hN.1.1
  rcases hL with ⟨n, hLin⟩ | ⟨n, hAlt⟩ | ⟨m, hPlus⟩ | ⟨m, hMinus⟩ | hA6 | hA7
  ·
    have hn0 : n ≠ 0 := CFSG.RankThree.PartTwo.Sec19.ne_zero_of_isLin2Type hLin
    exact (ctx19_14_not_inClassXBlock h h15
      ⟨h3.1, Or.inl ⟨n, Nat.one_le_iff_ne_zero.mpr hn0, hLin⟩⟩).elim
  ·
    rcases Nat.even_or_odd n with hev | hodd
    ·
      have hmem := CFSG.RankThree.PartTwo.Sec19.Narrow316.mem_of_isAltNaturalType_of_even
        h.ctx.h1910.1 hMmax h.hD.1.1.le hq hAlt hev
      obtain ⟨eBar⟩ := bar2_equiv_alt_of_isAltNaturalType hAlt
      have eX : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* alternatingGroup (Fin n) :=
        eb.symm.trans eBar
      have hAltX : IsAlt ↥(CFSG.AGLEmbedding.barM H Dsub) n := ⟨eX⟩
      rcases hmem with rfl | rfl | rfl
      · exact p19_16_5_of_alt_six h h11 hshape eBar
      · have hcard := card_blockPL_of_alt_eight hshape eX
        have hΩ : IsOmegaEps2 (Bar2 Dsub) true 3 := by
          simpa [IsOmegaEps2] using
            isOmegaPlus_bar2_of_isAltNaturalType_eight (h := hAlt) (Dsub := Dsub)
        exact p19_16_4_of_model h h11 h3 (Or.inl rfl) hΩ (by simpa using hcard)
      · exact (not_alt_of_isOrthogonalTwo h3.2.1 (n := 10) (by norm_num) hAltX
          (by norm_num) (by norm_num) (by norm_num)).elim
    ·
      exact (ctx19_14_not_inClassXBlock h h15
        (inClassXBlock_of_odd_alt h3.1 hodd hAlt)).elim
  ·
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · have hm2 : m ≤ 2 := by omega
      exact (CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.false_of_isOmegaPlusType_le_two
        (CFSG.RankThree.PartTwo.IsShort2.isShort h3.1) hm2 hPlus).elim
    · rcases Nat.lt_or_ge m 4 with hm3 | hm4
      · obtain rfl : m = 3 := by omega
        have hAlt8 :=
          CFSG.RankThree.PartTwo.Sec19.isAltNaturalType_eight_of_isOmegaPlusType_three hPlus
        obtain ⟨e8⟩ := bar2_equiv_alt_of_isAltNaturalType hAlt8
        have hcard := card_blockPL_of_alt_eight hshape (eb.symm.trans e8)
        have hΩ : IsOmegaEps2 (Bar2 Dsub) true 3 := by
          simpa [IsOmegaEps2] using
            isOmegaPlus_bar2_of_isAltNaturalType_eight (h := hAlt8) (Dsub := Dsub)
        exact p19_16_4_of_model h h11 h3 (Or.inl rfl) hΩ (by simpa using hcard)
      · have hm := CFSG.RankThree.PartTwo.Sec19.Narrow316.lt_four_of_isOmegaPlusType
          h.ctx.h1910.1 hMmax h.hD.1.1.le hPlus
        omega
  ·
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · rcases Nat.lt_or_ge m 1 with h0 | h1
      · obtain rfl : m = 0 := by omega
        have h3alt := CFSG.RankThree.PartTwo.Sec19.isAltNaturalType_three_of_isOmegaMinusType_zero
          hMinus
        exact (ctx19_14_not_inClassXBlock h h15
          (inClassXBlock_of_odd_alt h3.1 ⟨1, by norm_num⟩ h3alt)).elim
      · obtain rfl : m = 1 := by omega
        have h5alt := CFSG.RankThree.PartTwo.Sec19.isAltNaturalType_five_of_isOmegaMinusType_one
          hMinus
        exact (ctx19_14_not_inClassXBlock h h15
          (inClassXBlock_of_odd_alt h3.1 ⟨2, by norm_num⟩ h5alt)).elim
    · have hm4 := CFSG.RankThree.PartTwo.Sec19.Narrow316.lt_four_of_isOmegaMinusType
        h.ctx.h1910.1 hMmax h.hD.1.1.le hMinus
      rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
      · obtain ⟨e2⟩ := bar2_equiv_omegaMinus_of_isOmegaMinusType hMinus
        have eX : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* ↥(omegaMinusTwo 2) :=
          eb.symm.trans e2
        have hcard := card_blockPL_of_omegaMinus_two hshape eX
        have hΩ : IsOmegaEps2 (Bar2 Dsub) false 3 := by
          simpa [IsOmegaEps2] using isOmegaMinus_bar2_of_isOmegaMinusType hMinus (m := 2)
        exact p19_16_4_of_model h h11 h3 (Or.inl rfl) hΩ (by simpa using hcard)
      · obtain ⟨e3⟩ := bar2_equiv_omegaMinus_of_isOmegaMinusType hMinus
        have eX : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* ↥(omegaMinusTwo 3) :=
          eb.symm.trans e3
        have hcard := card_blockPL_of_omegaMinus_three hshape eX
        have hΩ : IsOmegaEps2 (Bar2 Dsub) false 4 := by
          simpa [IsOmegaEps2] using isOmegaMinus_bar2_of_isOmegaMinusType hMinus (m := 3)
        exact p19_16_4_of_model h h11 h3 (Or.inr rfl) hΩ (by simpa using hcard)
  ·
    obtain ⟨⟨α, hα, hpc_le, hkercard⟩, -⟩ := hA6
    let φ : Bar2 Dsub →* alternatingGroup (Fin 6) :=
      QuotientGroup.lift (CFSG.pCore 2 ↥Dsub) α hpc_le
    have hφsurj : Function.Surjective φ := by
      intro y
      obtain ⟨x, rfl⟩ := hα y
      refine ⟨QuotientGroup.mk x, ?_⟩
      change (QuotientGroup.lift (CFSG.pCore 2 ↥Dsub) α hpc_le)
        (QuotientGroup.mk x) = _
      rw [QuotientGroup.lift_mk]
    let s : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2,
        Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    have hs : s ≠ 1 := by
      intro h1
      have h2 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2 :
          Equiv.Perm (Fin 6)) 0 = (1 : Equiv.Perm (Fin 6)) 0 :=
        congrArg (fun x : alternatingGroup (Fin 6) => (x : Equiv.Perm (Fin 6)) 0) h1
      revert h2
      decide
    have hφne : ∃ k, φ k ≠ 1 := by
      obtain ⟨k, hk⟩ := hφsurj s
      exact ⟨k, by rw [hk]; exact hs⟩
    have hker_le : φ.ker ≤ Subgroup.center (Bar2 Dsub) :=
      CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hφne
    have hne : φ.ker ≠ ⊥ := by
      intro hbot
      have hle : α.ker ≤ CFSG.pCore 2 ↥Dsub := by
        intro x hx
        have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub) x ∈ φ.ker := by
          rw [MonoidHom.mem_ker]
          change φ (QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub) x) = 1
          change (QuotientGroup.lift (CFSG.pCore 2 ↥Dsub) α hpc_le)
            (QuotientGroup.mk x) = 1
          rw [QuotientGroup.lift_mk]
          exact hx
        rw [hbot, Subgroup.mem_bot] at hxbar
        exact (QuotientGroup.eq_one_iff x).mp hxbar
      have hcardeq : Nat.card α.ker = Nat.card (CFSG.pCore 2 ↥Dsub) := by
        rw [le_antisymm hle hpc_le]
      rw [hcardeq] at hkercard
      have hpos : 0 < Nat.card (CFSG.pCore 2 ↥Dsub) := Nat.card_pos
      omega
    have hcenter_ne : Subgroup.center (Bar2 Dsub) ≠ ⊥ := by
      intro hbot
      exact hne (le_bot_iff.mp (hker_le.trans (le_of_eq hbot)))
    exact (hcenter_ne (CFSG.Quasithin.H13.Lem8.center_eq_bot_of_mulEquiv eb hZ)).elim
  ·
    obtain ⟨eBar⟩ := bar2_equiv_alt_of_isA7FourType hA7
    have eX : ↥(CFSG.AGLEmbedding.barM H Dsub) ≃* alternatingGroup (Fin 7) :=
      eb.symm.trans eBar
    exact (not_alt_of_isOrthogonalTwo h3.2.1 (n := 7) (by norm_num) ⟨eX⟩
      (by norm_num) (by norm_num) (by norm_num)).elim

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
