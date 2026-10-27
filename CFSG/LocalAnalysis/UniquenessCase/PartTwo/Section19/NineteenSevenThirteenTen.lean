module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alpha
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiNe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_7_SingleComponent : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y N : Subgroup (MulAut W),
      IsIrrOn Y ⊤ ⊥ → Opp 3 Y = N → (IsAlt ↥N 5 ∨ IsU3 ↥N 2) →
      (∃ t : MulAut W, t ∈ Y ∧ orderOf t = 2 ∧
        E3.mQuot (⊤ : Subgroup W) (fixV (Subgroup.zpowers t)) ≤ 3) →
      CFSG.Open.pRank 5 Y ≤ 1

structure Setting19_7 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop where
  ctx : Ctx19_1 D V₀ V p L K
  not_gt : ¬ MBarGT D.M V₀ V 3
  l_ne : barSub V₀ V hV L ≠ ⊥
  k_ne : barSub V₀ V hV K ≠ ⊥
  l_alt : IsAlt ↥(barSub V₀ V hV L) 5
  k_alt : IsAlt ↥(barSub V₀ V hV K) 5
  comm : ⁅barSub V₀ V hV L, barSub V₀ V hV K⁆ = ⊥
  opp3 : Opp 3 (Mbar D.M V₀ V hV) = barSub V₀ V hV L ⊔ barSub V₀ V hV K
  opp5 : Opp 5 (Mbar D.M V₀ V hV) = barSub V₀ V hV L ⊔ barSub V₀ V hV K
  omega : IsOmegaPlus ↥(barSub V₀ V hV L ⊔ barSub V₀ V hV K) 4 2
  conj : ∃ g ∈ Mbar D.M V₀ V hV,
    barSub V₀ V hV K = (barSub V₀ V hV L).map (MulAut.conj g).toMonoidHom
  five_dvd : 5 ∣ Nat.card (F11.CTilde D.M V₀ V)

theorem nineteen_seven_barSub_ne_bot (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hV : IsElemAbelian 2 V) (h2 : R19_2At D V₀ V p L K h) (h5 : R19_5At D V₀ V p L K h)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (hgap : Gap19_7_SingleComponent)
    (hm : ¬ MBarGT D.M V₀ V 3) :
    barSub V₀ V hV L ≠ ⊥ ∧ barSub V₀ V hV K ≠ ⊥ := by
  have hp := h.hyp.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hLm : L ∈ calC D.M := S17.calLp_subset_calC D p h.hyp.hL
  have hLst : L ≤ stabTil V₀ V := hLm.1.le.trans hMs
  have hKst : K ≤ stabTil V₀ V := h.hK.1.le.trans hMs
  have h2' : Opp 3 D.M = L ⊔ K := h2
  have hV0 : V₀ ≠ ⊥ := by
    intro hbot
    have hbig : 1 < mSub V₀ := h.hyp.big
    have h1 : mSub V₀ = 0 := by rw [hbot]; exact rk_bot
    omega
  have hgap_case : ∀ N : Subgroup (MulAut (Vtil V₀ V hV)),
      Opp 3 (Mbar D.M V₀ V hV) = N →
      (IsAlt ↥N 5 ∨ IsU3 ↥N 2) → False := by
    intro N hopp hshape
    have hirr := s15_semi_isIrrOn_Mbar h.hyp.hyp125 hV0
    have hinv := nineteen_seven_exists_involution D h hV h5 hx h61 hm
    have hle := hgap (Vtil V₀ V hV) (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (Mbar D.M V₀ V hV) N hirr hopp hshape hinv
    have h2le := nineteen_seven_two_le_pRank_mbar D h hV h5 hx h61
    omega
  have hboth : barSub V₀ V hV L = ⊥ → barSub V₀ V hV K = ⊥ → False := by
    intro hLbot hKbot
    have hLC : L ≤ F11.CTilde D.M V₀ V :=
      (barSub_eq_bot_iff hV hp.le_normalizer hp.le_normalizer₀ hLm.1.le).1 hLbot
    have hKC : K ≤ F11.CTilde D.M V₀ V :=
      (barSub_eq_bot_iff hV hp.le_normalizer hp.le_normalizer₀ h.hK.1.le).1 hKbot
    have h1 : CFSG.Open.pRank 5 (L ⊔ K) ≤ CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) :=
      CFSG.SectionRank.pRank_mono (by norm_num) (sup_le hLC hKC)
    have h2le := nineteen_seven_pRank_cTilde_le_one D h h5 h61
    have h3 := nineteen_seven_two_le_pRank_sup D h
    omega
  constructor
  · intro hLbot
    by_cases hKbot : barSub V₀ V hV K = ⊥
    · exact hboth hLbot hKbot
    · refine hgap_case (barSub V₀ V hV K) ?_ ?_
      · have hh : barSub V₀ V hV (Opp 3 D.M) = Opp 3 (Mbar D.M V₀ V hV) :=
          close16_barSub_opp hMs
        rw [h2', s16c7_barSub_sup V₀ V hV hLst hKst] at hh
        simpa [hLbot] using hh.symm
      · exact Or.inl (S18.isAlt_barSub_of_isAlt_bar2 h.hyp.hyp125 h.hK hKbot h.hKshape)
  · intro hKbot
    by_cases hLbot : barSub V₀ V hV L = ⊥
    · exact hboth hLbot hKbot
    · refine hgap_case (barSub V₀ V hV L) ?_ ?_
      · have hh : barSub V₀ V hV (Opp 3 D.M) = Opp 3 (Mbar D.M V₀ V hV) :=
          close16_barSub_opp hMs
        rw [h2', s16c7_barSub_sup V₀ V hV hLst hKst] at hh
        simpa [hKbot] using hh.symm
      · rcases h.shape with hL2 | hL3
        · exact Or.inl (S18.isAlt_barSub_of_isAlt_bar2 h.hyp.hyp125 hLm hLbot
            (S17.isAlt_five_of_isL2_two hL2))
        · have hsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_shape (Or.inr hL3)
          obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h.hyp.hyp125 hLm hLbot hsimple
          exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hL3)

theorem nineteen_seven_thirteen_ten (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hV : IsElemAbelian 2 V) (h2 : R19_2At D V₀ V p L K h) (h5 : R19_5At D V₀ V p L K h)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h1310 : Inputs1719.W4Thm13_10) (hgap : Gap19_7_SingleComponent)
    (hm : ¬ MBarGT D.M V₀ V 3) :
    Setting19_7 D V₀ V p L K hV ∧
      (commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L)) (barSub V₀ V hV K) = ⊥ ∨
        NatOmegaPlus (barSub V₀ V hV L ⊔ barSub V₀ V hV K) ⊤ ⊥ 4 2) := by
  obtain ⟨hLne, hKne⟩ := nineteen_seven_barSub_ne_bot D h hV h2 h5 hx h61 hgap hm
  have hp := h.hyp.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hLm : L ∈ calC D.M := S17.calLp_subset_calC D p h.hyp.hL
  have hLst : L ≤ stabTil V₀ V := hLm.1.le.trans hMs
  have hKst : K ≤ stabTil V₀ V := h.hK.1.le.trans hMs
  have h2' : Opp 3 D.M = L ⊔ K := h2
  have hKalt : IsAlt ↥(barSub V₀ V hV K) 5 :=
    S18.isAlt_barSub_of_isAlt_bar2 h.hyp.hyp125 h.hK hKne h.hKshape
  have hcomm_le : ⁅L, K⁆ ≤ pCoreOf 2 D.M :=
    (calC_commutator_le_of_ne hLm h.hK h.hne.symm).trans
      (inf_le_left.trans (uc22p22r_pCoreOf_le_of_isSubnormal hLm.1))
  have hcomm : ⁅barSub V₀ V hV L, barSub V₀ V hV K⁆ = ⊥ := by
    have hbotM : barSub V₀ V hV ⁅L, K⁆ = ⊥ :=
      le_bot_iff.1 (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp.hyp125 ▸
        barSub_mono V₀ V hV hcomm_le)
    exact le_bot_iff.1 (hbotM ▸ S18.commutator_barSub_le hV hLst hKst)
  have hcompL : IsComponentOf (barSub V₀ V hV L) (Mbar D.M V₀ V hV) :=
    barSub_mem_compBar_of_ne_bot h.hyp.hyp125 hLm hLne
  have hcompK : IsComponentOf (barSub V₀ V hV K) (Mbar D.M V₀ V hV) :=
    barSub_mem_compBar_of_ne_bot h.hyp.hyp125 h.hK hKne
  have hLperfect : ⁅barSub V₀ V hV L, barSub V₀ V hV L⁆ = barSub V₀ V hV L :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hcompL.2.2.1)
  have hLneK : barSub V₀ V hV L ≠ barSub V₀ V hV K := by
    intro heq
    have h1 : ⁅barSub V₀ V hV L, barSub V₀ V hV L⁆ = ⊥ := by
      rw [← heq] at hcomm
      exact hcomm
    rw [hLperfect] at h1
    exact hLne h1
  have hMbar_ne : Mbar D.M V₀ V hV ≠ ⊥ := by
    intro hbot
    exact hLne (le_bot_iff.1 (hbot ▸ barSub_mono V₀ V hV hLm.1.le))
  have hopp3 : Opp 3 (Mbar D.M V₀ V hV) =
      barSub V₀ V hV L ⊔ barSub V₀ V hV K := by
    have hh : barSub V₀ V hV (Opp 3 D.M) = Opp 3 (Mbar D.M V₀ V hV) :=
      close16_barSub_opp hMs
    rw [h2', s16c7_barSub_sup V₀ V hV hLst hKst] at hh
    exact hh.symm
  have hLalt_or : IsAlt ↥(barSub V₀ V hV L) 5 ∨
      LieModel ↥(barSub V₀ V hV L) .PSU 3 2 2 := by
    rcases h.shape with hL2 | hL3
    · exact Or.inl (S18.isAlt_barSub_of_isAlt_bar2 h.hyp.hyp125 hLm hLne
        (S17.isAlt_five_of_isL2_two hL2))
    · have hsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_shape (Or.inr hL3)
      obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h.hyp.hyp125 hLm hLne hsimple
      exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hL3)
  have hout := h1310 (Vtil V₀ V hV) (s15_Infra_vtil_sq_eq_one V₀ V hV)
    (Mbar D.M V₀ V hV) (barSub V₀ V hV L) (barSub V₀ V hV K)
    (CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple (isKGroup_mbar D hV hMs))
    (fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp.hyp125 hP hN h2)
    (TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h.hyp.hyp125 hMbar_ne)
    hcompL hcompK hLneK
    (nineteen_seven_exists_involution D h hV h5 hx h61 hm)
    hopp3 hKalt hLalt_or
  obtain ⟨homega, hopp5, hconj, hcase⟩ := hout
  have hLalt : IsAlt ↥(barSub V₀ V hV L) 5 := by
    rcases hLalt_or with h | h
    · exact h
    · exfalso
      obtain ⟨g, -, hconjg⟩ := hconj
      have hcardK : Nat.card ↥(barSub V₀ V hV K) = 60 := by
        obtain ⟨e⟩ := hKalt
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      have hcardL : Nat.card ↥(barSub V₀ V hV L) = 62400 := by
        have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel
            ↥(barSub V₀ V hV L) .PSU 3 2 2 :=
          CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
        have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.1 rfl
        rw [h1]
        decide
      have hcard_eq : Nat.card ↥(barSub V₀ V hV K) =
          Nat.card ↥(barSub V₀ V hV L) := by
        rw [hconjg]
        exact Subgroup.card_map_of_injective (MulAut.conj g).injective
      omega
  have hcomm_el : ∀ a ∈ barSub V₀ V hV L, ∀ b ∈ barSub V₀ V hV K, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ha) b hb).symm
  have hcenterL : Subgroup.center ↥(barSub V₀ V hV L) = ⊥ := by
    obtain ⟨e⟩ := hLalt
    rw [eq_bot_iff]
    intro x hx
    have hx' : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
    rw [alternatingGroup.center_eq_bot (by norm_num), Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hx', map_one])
  have hi : barSub V₀ V hV L ⊓ barSub V₀ V hV K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxK⟩ := Subgroup.mem_inf.1 hx
    have hxc : (⟨x, hxL⟩ : ↥(barSub V₀ V hV L)) ∈
        Subgroup.center ↥(barSub V₀ V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : (y : MulAut (Vtil V₀ V hV)) ∈
          Subgroup.centralizer ((barSub V₀ V hV K) : Set _) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) y.2
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy x hxK).symm
    rw [hcenterL, Subgroup.mem_bot] at hxc
    exact Subtype.ext_iff.mp hxc
  have hA5xA5 : S17.IsA5xA5 ↥(barSub V₀ V hV L ⊔ barSub V₀ V hV K) := by
    obtain ⟨eL⟩ := hLalt
    obtain ⟨eK⟩ := hKalt
    exact ⟨((CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcomm_el hi).symm).trans
      (MulEquiv.prodCongr eL eK)⟩
  have hpr2 : CFSG.Open.pRank 5 (barSub V₀ V hV L ⊔ barSub V₀ V hV K) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact S17.pRank_eq_two_of_isA5xA5 hA5xA5 (Or.inr rfl)
  have hfive : 5 ∣ Nat.card (F11.CTilde D.M V₀ V) := by
    by_contra hnd
    have hsig : 5 ∈ D.sig := by
      rw [← h.p_eq]
      exact h.hyp.hp
    have h3 : 3 ≤ CFSG.Open.pRank 5 D.M := hx.three_le 5 hsig
    have hle : CFSG.Open.pRank 5 D.M ≤ CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) :=
      pRank_le_pRank_mbar_of_not_dvd (M := D.M) hV h.hyp.hyp125.pairFacts
        Nat.prime_five hnd
    have hEq : CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) =
        CFSG.Open.pRank 5 (Opp 5 (Mbar D.M V₀ V hV)) :=
      (s13_pRank_pElementSubgroup Nat.prime_five (Mbar D.M V₀ V hV)).symm
    have h32 : 3 ≤ 2 := by
      calc 3 ≤ CFSG.Open.pRank 5 D.M := h3
        _ ≤ CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) := hle
        _ = CFSG.Open.pRank 5 (Opp 5 (Mbar D.M V₀ V hV)) := hEq
        _ = CFSG.Open.pRank 5 (barSub V₀ V hV L ⊔ barSub V₀ V hV K) := by rw [hopp5]
        _ = 2 := hpr2
    omega
  exact ⟨⟨h, hm, hLne, hKne, hLalt, hKalt, hcomm, hopp3, hopp5, homega, hconj, hfive⟩,
    hcase⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
