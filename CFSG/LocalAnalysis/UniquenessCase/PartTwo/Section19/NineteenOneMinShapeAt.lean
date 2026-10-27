module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveCaseTwoBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiNe
public import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
public import CFSG.Quasithin.Background.GoldschmidtE23Comp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase

section Context

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_1_minShapeAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  R19_8_2At D V₀ V p L K h → R19_8_4At D V₀ V p L K h →
    Shape19_1Min (Mbar D.M V₀ V h.hyp.isElemAbelian) (barSub V₀ V h.hyp.isElemAbelian L)
      (barSub V₀ V h.hyp.isElemAbelian K)

theorem invFixAt_of_minShapeAt (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hsh : Gap19_1_minShapeAt D V₀ V p L K h) :
    R19_8_2At D V₀ V p L K h → R19_8_4At D V₀ V p L K h →
      s16n9bInvFix (Mbar D.M V₀ V h.hyp.isElemAbelian) 5 7 := by
  intro h82 h84
  exact invFix_of_shape_min (s15_Infra_vtil_sq_eq_one V₀ V h.hyp.isElemAbelian) (hsh h82 h84)

end Context

section BarFacts

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem five_mem_piSet_of_barSub_eq_bot (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {X : Subgroup G} (hXM : X ≤ D.M) (hX : barSub V₀ V h.isElemAbelian X = ⊥)
    (h5 : 5 ∣ Nat.card X) {v : G} (hv : v ∈ V) : 5 ∈ piSet (centModInM D V₀ v) := by
  have hp := h.pairFacts
  have hMS : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hle : X ≤ centModInM D V₀ v := by
    intro x hx
    have hxs : x ∈ stabTil V₀ V := hMS (hXM hx)
    have hact : actTil V₀ V h.isElemAbelian ⟨x, hxs⟩ = 1 := by
      have := actTil_mem_barSub V₀ V h.isElemAbelian hx hxs
      rw [hX, Subgroup.mem_bot] at this
      exact this
    exact ⟨hXM hx, hxs.2, (actTil_eq_one_iff V₀ V h.isElemAbelian ⟨x, hxs⟩).1 hact v hv⟩
  exact ⟨Nat.prime_five, h5.trans (Subgroup.card_dvd_of_le hle)⟩

theorem barSub_ne_bot_of_R19_8_4At (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h84 : R19_8_4At D V₀ V p L K h) :
    barSub V₀ V h.hyp.isElemAbelian L ≠ ⊥ ∧ barSub V₀ V h.hyp.isElemAbelian K ≠ ⊥ := by
  obtain ⟨v, hv, -, h5v⟩ := h84
  have hLM : L ≤ D.M := h.hyp.hL.1.1.le
  have hKM : K ≤ D.M := h.hK.1.le
  have h5L : 5 ∣ Nat.card L := by
    obtain ⟨-, hdvd⟩ := h.hyp.hL.2
    rw [h.p_eq] at hdvd
    exact hdvd
  have h5K : 5 ∣ Nat.card K := by
    have h60 := card_bar2_of_isAlt_five h.hKshape
    have hdvd : Nat.card (Bar2 K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
    rw [h60] at hdvd
    exact (by norm_num : 5 ∣ 60).trans hdvd
  exact ⟨fun hb => h5v (five_mem_piSet_of_barSub_eq_bot D h.hyp.hyp125 hLM hb h5L hv),
    fun hb => h5v (five_mem_piSet_of_barSub_eq_bot D h.hyp.hyp125 hKM hb h5K hv)⟩

theorem isAlt_barSub_K_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hK1 : barSub V₀ V h.hyp.isElemAbelian K ≠ ⊥) :
    IsAlt ↥(barSub V₀ V h.hyp.isElemAbelian K) 5 :=
  S18.isAlt_barSub_of_isAlt_bar2 h.hyp.hyp125 h.hK hK1 h.hKshape

theorem isAlt_barSub_L_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hL1 : barSub V₀ V h.hyp.isElemAbelian L ≠ ⊥) (hL2 : IsL2 (Bar2 L) 2) :
    IsAlt ↥(barSub V₀ V h.hyp.isElemAbelian L) 5 :=
  S18.isAlt_barSub_of_isAlt_bar2 h.hyp.hyp125 h.hyp.hL.1 hL1 (S17.isAlt_five_of_isL2_two hL2)

theorem commute_barSub_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) :
    ∀ x ∈ barSub V₀ V h.hyp.isElemAbelian L, ∀ y ∈ barSub V₀ V h.hyp.isElemAbelian K,
      x * y = y * x := by
  have hV := h.hyp.isElemAbelian
  have hp := h.hyp.hyp125.pairFacts
  have hMS : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hLM : L ≤ D.M := h.hyp.hL.1.1.le
  have hKM : K ≤ D.M := h.hK.1.le
  have hO2 : barSub V₀ V hV (CFSG.Open.pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV h.hyp.hL.1.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h.hyp.hyp125)
  have hcomm : ⁅barSub V₀ V hV L, barSub V₀ V hV K⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅barSub V₀ V hV L, barSub V₀ V hV K⁆
        ≤ barSub V₀ V hV ⁅L, K⁆ := S18.commutator_barSub_le hV (hLM.trans hMS) (hKM.trans hMS)
      _ ≤ barSub V₀ V hV (CFSG.Open.pCoreOf 2 L) :=
          barSub_mono V₀ V hV ((calC_commutator_le_of_ne h.hyp.hL.1 h.hK h.hne.symm).trans
            inf_le_left)
      _ = ⊥ := hO2
  intro x hx y hy
  have hm : ⁅x, y⁆ ∈ ⁅barSub V₀ V hV L, barSub V₀ V hV K⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  rw [hcomm, Subgroup.mem_bot] at hm
  exact commutatorElement_eq_one_iff_mul_comm.mp hm

theorem permutes_barSub_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) :
    ∀ φ ∈ Mbar D.M V₀ V h.hyp.isElemAbelian,
      ((∀ x ∈ barSub V₀ V h.hyp.isElemAbelian L, φ * x * φ⁻¹ ∈ barSub V₀ V h.hyp.isElemAbelian L) ∧
        (∀ x ∈ barSub V₀ V h.hyp.isElemAbelian K,
          φ * x * φ⁻¹ ∈ barSub V₀ V h.hyp.isElemAbelian K)) ∨
      ((∀ x ∈ barSub V₀ V h.hyp.isElemAbelian L, φ * x * φ⁻¹ ∈ barSub V₀ V h.hyp.isElemAbelian K) ∧
        (∀ x ∈ barSub V₀ V h.hyp.isElemAbelian K,
          φ * x * φ⁻¹ ∈ barSub V₀ V h.hyp.isElemAbelian L)) := by
  have hV := h.hyp.isElemAbelian
  have hp := h.hyp.hyp125.pairFacts
  have hMS : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := h.hyp.hL.1.1.le.trans hMS
  have hKS : K ≤ stabTil V₀ V := h.hK.1.le.trans hMS
  intro φ hφ
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hconj : ∀ {J J' : Subgroup G}, J ≤ stabTil V₀ V →
      J.map (MulAut.conj (m : G)).toMonoidHom = J' →
      ∀ x ∈ barSub V₀ V hV J,
        actTil V₀ V hV m * x * (actTil V₀ V hV m)⁻¹ ∈ barSub V₀ V hV J' := by
    intro J J' hJS hJJ' x hx
    have h1 := TwelveTwentyThree.barSub_map_conj (V₀ := V₀) hV hJS m.2
    rw [hJJ'] at h1
    rw [h1]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rcases permutesPair_of_ctx19_one h (m : G) hmM with ⟨hL, hK⟩ | ⟨hL, hK⟩
  · exact Or.inl ⟨hconj hLS hL, hconj hKS hK⟩
  · exact Or.inr ⟨hconj hLS hL, hconj hKS hK⟩

theorem map_conj_eq_self_of_isU3 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hU3 : IsU3 (Bar2 L) 2) :
    ∀ m ∈ D.M, L.map (MulAut.conj m).toMonoidHom = L := by
  intro m hm
  rcases permutesPair_of_ctx19_one h m hm with ⟨hL, -⟩ | ⟨hL, -⟩
  · exact hL
  · exfalso
    obtain ⟨e⟩ := S17.bar2_conj_equiv L m
    rw [hL] at e
    have hKU3 : IsU3 (Bar2 K) 2 := CFSG.Blueprint.LieModel.of_mulEquiv e hU3
    exact S17.not_isAlt_five_of_isU3_two hKU3 h.hKshape

theorem not_isU3_of_ctx19_1
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h128 : W4Lem12_8) (hMin : Inputs1719.K_SU3MinDegree) (h36 : Inputs1719.W4Lem3_6)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h82 : R19_8_2At D V₀ V p L K h) (h84 : R19_8_4At D V₀ V p L K h) :
    ¬ IsU3 (Bar2 L) 2 := by
  intro hU3
  classical
  let hV := h.hyp.isElemAbelian
  let Kb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let Z : Subgroup (Vtil V₀ V hV) := fixSupConjSet Kb Mb
  obtain ⟨hL1, hK1⟩ := barSub_ne_bot_of_R19_8_4At D h h84
  have hm4 : mBar D.M V₀ V hV = 4 := h82
  have hcomp : Kb ∈ compBar D.M V₀ V hV :=
    barSub_mem_compBar_of_ne_bot h.hyp.hyp125 h.hyp.hL.1 hL1
  have hSU2 : IsSU3 (Bar2 L) 2 := uc22p22d_isSU3_of_isU3 h.hyp.hL.1.2.2 hU3
  have hSU : IsSU3 ↥Kb 2 := S17.isSU3_barSub h.hyp.hyp125 h.hyp.hL.1 hL1 hSU2
  have hp := h.hyp.hyp125.pairFacts
  have hMS : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := h.hyp.hL.1.1.le.trans hMS
  have hKmem : Kb ∈ conjSet Kb Mb := ⟨1, Mb.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hconj : conjSet Kb Mb = {Kb} := by
    ext X
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
      have h1 := TwelveTwentyThree.barSub_map_conj (V₀ := V₀) hV hLS m.2
      rw [map_conj_eq_self_of_isU3 D h hU3 (m : G) hmM] at h1
      exact Set.mem_singleton_iff.mpr h1.symm
    · intro hX
      rw [Set.mem_singleton_iff] at hX
      rw [hX]
      exact hKmem
  have hnorm : ∀ φ ∈ Mb, ∀ k ∈ Kb, φ * k * φ⁻¹ ∈ Kb := by
    intro φ hφ k hk
    have hmem : Kb.map (MulAut.conj φ).toMonoidHom ∈ conjSet Kb Mb := ⟨φ, hφ, rfl⟩
    rw [hconj, Set.mem_singleton_iff] at hmem
    have h1 : φ * k * φ⁻¹ ∈ Kb.map (MulAut.conj φ).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [hmem] at h1
  have hHK : supConjSet Kb Mb = Kb := by
    show (⨆ X ∈ conjSet Kb Mb, X) = Kb
    rw [hconj, iSup_singleton]
  have hZbot : Z = ⊥ := by
    have hZfix : Z = fixV Kb := by
      show fixV (supConjSet Kb Mb) = fixV Kb
      rw [hHK]
    have hV0 : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
    have hirr := s15_semi_isIrrOn_Mbar h.hyp.hyp125 hV0
    have hstab : StableUnder Mb (fixV Kb) := by
      intro φ hφ w hw
      rw [mem_fixV] at hw ⊢
      intro k hk
      have h1 : k (φ w) = φ ((φ⁻¹ * k * φ⁻¹⁻¹) w) := by simp [MulAut.mul_apply]
      rw [h1, hw _ (hnorm φ⁻¹ (Mb.inv_mem hφ) k hk)]
    rw [hZfix]
    rcases hirr.2.2.2 _ hstab bot_le le_top with h1 | h1
    · exact h1
    · exfalso
      apply hL1
      refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => MulEquiv.ext fun w => ?_
      have hw : w ∈ fixV Kb := by rw [h1]; exact Subgroup.mem_top w
      rw [MulAut.one_apply]
      exact hw k hk
  rcases twelve_twentyFour D hx h61 h127 h1214 h128 h.hyp.hyp125 hcomp rfl with
    h1 | ⟨hsum, I, hI, hmn⟩ | ⟨Y, e, -, -, hsn, hnatY, -⟩
  ·
    have hd := hMin ↥Kb 2 hSU le_rfl
    exact absurd (hd.trans (h1.trans hm4.le)) (by norm_num)
  ·
    obtain ⟨-, -, hIeq, -⟩ := S17.caseTwo_three_six h.hyp.hyp125 h.hyp.hL.1 hL1 rfl rfl hsum hI
      hmn hSU2 le_rfl (hm4.trans_le (by norm_num)) h36
    have htop : commV (autQuot Kb Z) = ⊤ := by
      have h2 : (⨆ X ∈ conjSet Kb Mb, commV (autQuot X Z)) = ⊤ := by
        rw [iSup_subtype' (p := fun X : Subgroup (MulAut (Vtil V₀ V hV)) =>
          X ∈ conjSet Kb Mb) (f := fun X _ => commV (autQuot X Z))]
        exact hsum.2
      rw [hconj] at h2
      simpa using h2
    have hIstar : I.map (QuotientGroup.mk' Z) = ⊤ := by
      have hIeq' : I.map (QuotientGroup.mk' Z) = commV (autQuot Kb Z) := hIeq
      rw [hIeq', htop]
    have hItop : I = ⊤ := by
      refine top_le_iff.1 fun v _ => ?_
      have hv : QuotientGroup.mk' Z v ∈ I.map (QuotientGroup.mk' Z) := by
        rw [hIstar]; exact Subgroup.mem_top _
      obtain ⟨i, hi, hiv⟩ := Subgroup.mem_map.1 hv
      obtain ⟨c, hc, hic⟩ := (QuotientGroup.mk'_eq_mk' Z).1 hiv
      rw [hZbot, Subgroup.mem_bot] at hc
      rw [hc, mul_one] at hic
      rw [← hic]
      exact hi
    have hirrK : (⊤ : Subgroup (Vtil V₀ V hV)) ∈ IrrPlus Kb (⊤ : Subgroup (Vtil V₀ V hV)) := by
      rw [mem_irrPlus_top_iff]
      obtain ⟨hcomm, hlt, -, -, hmax⟩ := hI
      rw [hItop] at hcomm hlt hmax
      exact ⟨fun _ _ _ _ => Subgroup.mem_top _, hcomm, hlt, hmax⟩
    have hKS : K ≤ stabTil V₀ V := h.hK.1.le.trans hMS
    have h2M : barSub V₀ V hV (CFSG.Open.pCoreOf 2 D.M) = ⊥ :=
      barSub_pCoreOf_eq_bot_of_hyp125 h.hyp.hyp125
    have h2K : barSub V₀ V hV (CFSG.Open.pCoreOf 2 K) = ⊥ :=
      TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV h.hK.1 h2M
    have hq := TwelveTwentyThree.isQuasisimple_barSub hV hKS h.hK.2.2 h2K hK1
    have hP : Group.IsPerfect ↥(barSub V₀ V hV K) := Group.isPerfect_def.mpr hq.1
    have htriv := B69.trivial_of_perfect_commute (s15_Infra_vtil_sq_eq_one V₀ V hV) hirrK hP
      (fun k hk l hl => (commute_barSub_of_ctx19_1 D h l hl k hk).symm)
      (fun _ _ _ _ => Subgroup.mem_top _)
    apply hK1
    refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    exact htriv k hk w (Subgroup.mem_top w)
  ·
    exact Inputs1719.false_of_isSubnormal_isNaturalO4Plus_of_isSU3 hSU hsn hnatY

end BarFacts

section FiveElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fpf_five_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h84 : R19_8_4At D V₀ V p L K h)
    {f : Bar2 D.M} (hf : orderOf f = 5)
    (hfn : ∀ m : Bar2 D.M, m * f * m⁻¹ ∈ Subgroup.zpowers f) :
    ∃ g ∈ Mbar D.M V₀ V h.hyp.isElemAbelian, orderOf g = 5 ∧ fixV (Subgroup.zpowers g) = ⊥ ∧
      (∀ φ ∈ Mbar D.M V₀ V h.hyp.isElemAbelian, φ * g * φ⁻¹ ∈ Subgroup.zpowers g) ∧
      ∀ x ∈ barSub V₀ V h.hyp.isElemAbelian L ⊔ barSub V₀ V h.hyp.isElemAbelian K,
        x * g = g * x := by
  classical
  have hV := h.hyp.isElemAbelian
  have hp := h.hyp.hyp125.pairFacts
  have hMS : D.M ≤ stabTil V₀ V := le_stabTil hp.le_normalizer hp.le_normalizer₀
  have h2M : barSub V₀ V hV (CFSG.Open.pCoreOf 2 D.M) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_hyp125 h.hyp.hyp125
  set π := S18.bar2ActTilHom hV hMS h2M with hπ
  have hπs := S18.bar2ActTilHom_surjective hV hMS h2M
  set g : MulAut (Vtil V₀ V hV) := (π f : MulAut (Vtil V₀ V hV)) with hg
  have hgM : g ∈ Mbar D.M V₀ V hV := (π f).2
  have hgn : ∀ φ ∈ Mbar D.M V₀ V hV, φ * g * φ⁻¹ ∈ Subgroup.zpowers g := by
    intro φ hφ
    obtain ⟨y, hy⟩ := hπs ⟨φ, hφ⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hfn y)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 := congrArg (fun z => ((π z : ↥(barSub V₀ V hV D.M)) : MulAut (Vtil V₀ V hV))) hk
    simp only [map_zpow, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_zpow] at h1
    rw [hy] at h1
    exact h1
  have hg1 : g ≠ 1 := by
    intro hg1
    obtain ⟨v, hv, -, h5v⟩ := h84
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective f
    have hact : actTil V₀ V hV ⟨(x : G), hMS x.2⟩ = 1 := by
      have h1 := S18.bar2ActTilHom_mk hV hMS h2M x
      have h2 : ((S18.bar2ActTilHom hV hMS h2M (QuotientGroup.mk x) :
          ↥(barSub V₀ V hV D.M)) : MulAut (Vtil V₀ V hV)) = 1 := hg1
      rw [h1] at h2
      exact h2
    have h5x : 5 ∣ orderOf x := by
      have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) x
      rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) x = QuotientGroup.mk x from rfl,
        hf] at this
      exact this
    have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    set y : ↥D.M := x ^ (orderOf x / 5) with hy
    have hy5 : orderOf y = 5 := orderOf_pow_orderOf_div hx0 h5x
    have hyG : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe, hy5]
    have hyact : actTil V₀ V hV ⟨(y : G), hMS y.2⟩ = 1 := by
      have h1 : (⟨(y : G), hMS y.2⟩ : ↥(stabTil V₀ V)) = ⟨(x : G), hMS x.2⟩ ^ (orderOf x / 5) :=
        Subtype.ext (by simp [hy])
      rw [h1, map_pow, hact, one_pow]
    have hymem : (y : G) ∈ centModInM D V₀ v :=
      ⟨y.2, (hMS y.2).2, (actTil_eq_one_iff V₀ V hV ⟨(y : G), hMS y.2⟩).1 hyact v hv⟩
    exact h5v ⟨Nat.prime_five, hyG ▸ Subgroup.orderOf_dvd_natCard _ hymem⟩
  have hg5 : g ^ 5 = 1 := by
    have h1 : (π f) ^ 5 = 1 := by rw [← map_pow, ← hf, pow_orderOf_eq_one, map_one]
    have h2 := congrArg (fun z : ↥(barSub V₀ V hV D.M) => (z : MulAut (Vtil V₀ V hV))) h1
    simpa using h2
  have hgord : orderOf g = 5 := by
    have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one hg5
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h1
  have hV0 : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hirr := s15_semi_isIrrOn_Mbar h.hyp.hyp125 hV0
  have hfix : fixV (Subgroup.zpowers g) = ⊥ := by
    have hstab : StableUnder (Mbar D.M V₀ V hV) (fixV (Subgroup.zpowers g)) := by
      intro φ hφ w hw
      rw [CFSG.Quasithin.GE23.mem_fixV_zpowers_iff']
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        (hgn φ⁻¹ ((Mbar D.M V₀ V hV).inv_mem hφ))
      have hgk : (g ^ k) w = w := hw (g ^ k) (Subgroup.zpow_mem_zpowers g k)
      have h1 : g (φ w) = φ ((φ⁻¹ * g * φ⁻¹⁻¹) w) := by
        simp [MulAut.mul_apply]
      rw [h1, ← hk, hgk]
    rcases hirr.2.2.2 _ hstab bot_le le_top with h1 | h1
    · exact h1
    · exfalso
      apply hg1
      refine MulEquiv.ext fun w => ?_
      have hw : w ∈ fixV (Subgroup.zpowers g) := by rw [h1]; exact Subgroup.mem_top w
      rw [CFSG.Quasithin.GE23.mem_fixV_zpowers_iff'] at hw
      simpa using hw
  obtain ⟨hL1, hK1⟩ := barSub_ne_bot_of_R19_8_4At D h h84
  have hperf : ∀ {J : Subgroup G}, J ∈ calC D.M → barSub V₀ V hV J ≠ ⊥ →
      barSub V₀ V hV J ≤ Subgroup.centralizer ({g} : Set (MulAut (Vtil V₀ V hV))) := by
    intro J hJ hJ1
    have hJS : J ≤ stabTil V₀ V := hJ.1.le.trans hMS
    have h2J : barSub V₀ V hV (CFSG.Open.pCoreOf 2 J) = ⊥ :=
      TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hJ.1 h2M
    have hq := TwelveTwentyThree.isQuasisimple_barSub hV hJS hJ.2.2 h2J hJ1
    have hP : Group.IsPerfect ↥(barSub V₀ V hV J) := Group.isPerfect_def.mpr hq.1
    have hN : barSub V₀ V hV J ≤ Subgroup.normalizer (Subgroup.zpowers g : Set _) := by
      intro φ hφ
      have hφM : φ ∈ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hJ.1.le hφ
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgn φ hφM)
        refine Subgroup.mem_zpowers_iff.mpr ⟨j * k, ?_⟩
        rw [zpow_mul, hj, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      · intro hz
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
          (hgn φ⁻¹ ((Mbar D.M V₀ V hV).inv_mem hφM))
        refine Subgroup.mem_zpowers_iff.mpr ⟨j * k, ?_⟩
        have h1 : z = φ⁻¹ * (φ * z * φ⁻¹) * φ⁻¹⁻¹ := by group
        rw [h1, ← hk, zpow_mul, hj, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    exact CFSG.RankThree.PartTwo.Sec12.le_centralizer_of_isPerfect_of_le_normalizer_zpowers hP hN
  have hsup := sup_le (hperf h.hyp.hL.1 hL1) (hperf h.hK hK1)
  refine ⟨g, hgM, hgord, hfix, hgn, fun x hx => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hx)

theorem gap19_1_minShapeAt_of (D : Data G) {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h68 : S17.R17_68At D V₀ V)
    (hU3 : R19_8_2At D V₀ V p L K h → R19_8_4At D V₀ V p L K h → ¬ IsU3 (Bar2 L) 2) :
    Gap19_1_minShapeAt D V₀ V p L K h := by
  intro h82 h84
  have hL2 : IsL2 (Bar2 L) 2 := h.shape.resolve_right (hU3 h82 h84)
  obtain ⟨hL1, hK1⟩ := barSub_ne_bot_of_R19_8_4At D h h84
  obtain ⟨f, hf5, hfn⟩ := exists_normal_zpowers_five_bar2 D h h68 hL2
  obtain ⟨g, hgM, hg5, hgfix, hgn, hgc⟩ := exists_fpf_five_of_ctx19_1 D h h84 hf5 hfn
  exact ⟨barSub_mono V₀ V h.hyp.isElemAbelian h.hyp.hL.1.1.le,
    barSub_mono V₀ V h.hyp.isElemAbelian h.hK.1.le,
    isAlt_barSub_L_of_ctx19_1 D h hL1 hL2, isAlt_barSub_K_of_ctx19_1 D h hK1,
    commute_barSub_of_ctx19_1 D h, permutes_barSub_of_ctx19_1 D h,
    g, hgM, hg5, hgfix, hgn, hgc⟩

end FiveElement

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
