module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.WeakClosure81.W115TwelveDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNineProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTen
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup
public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Background.H132Irr
public import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstarTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Data
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

section Certified


private theorem isQuasisimple_of_isSpor_m22
    {X : Type} [Group X] (h : IsSpor X .M22) :
    CFSG.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  classical
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let : CommGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      { (inferInstance : Group (CFSG.Blueprint.NativeSporadic.Carrier .M22)) with
          mul_comm := h }
    have hp := (CommGroup.is_simple_iff_prime_card
      (α := CFSG.Blueprint.NativeSporadic.Carrier .M22)).mp inferInstance
    rw [hcard] at hp
    norm_num at hp
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_⟩
  have hcardZ : Nat.card (Subgroup.center X) = Nat.card (Subgroup.center
      (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hZ, Subgroup.card_bot] at hcardZ
  exact Subgroup.eq_bot_of_card_eq _ hcardZ

private theorem isSpor_quotCenter_of_isSpor_m22
    {X : Type} [Group X] (h : IsSpor X .M22) :
    IsSpor (X ⧸ Subgroup.center X) .M22 := by
  obtain ⟨-, hZ⟩ := isQuasisimple_of_isSpor_m22 h
  obtain ⟨e⟩ := h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

theorem mBar_le_bBar_add_two_of_M22
    (hV : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L)
    (h17_20 : R17_20At D V₀ V) (hKHex : Inputs1719.K_M22HexadPair)
    (hspor : IsSpor (BarInf L) .M22)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V) :
    mBar D.M V₀ V hV.isElemAbelian ≤ bBar L D.M V₀ V hV.isElemAbelian + 2 := by
  classical
  obtain ⟨hm3, hN, -⟩ := h17_20 L c
  have hk1 : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hsp3
  have hnt : ¬ F08.Thin8 L := by
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hconj : UC22.conjClosure D.M L = L :=
    Inputs1719.conjClosure_eq_self_of_normal c.mem_calC.1.le hN
  obtain ⟨E, X₁, X₂, hEM, hEcard, hEel, hX₁M, hX₂M, hX₁card, hX₂card,
    hX₁perm, hX₂perm, hEsub, hXsubM⟩ :=
    gap17_21_M22HexadPair_of_K hV h17_20 hKHex L c hspor
  have hEp : IsPGroup 3 ↥E := hEel.isPGroup
  have hEnc : ¬ IsCyclic ↥E :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.not_isCyclic_of_elemAbelian_nine hEel hEcard
  have hΓE : rankThreeGamma 1 3 E ≤ D.M :=
    ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hsp3 hEM hEp
  have hUE : UniqueMax D.M E :=
    uc22p22u_uniqueMax_of_noncyclic D h61 h63 Nat.prime_three (by norm_num) hEM hEp hEnc
      (Or.inl hΓE)
  have hU : UniqueMax D.M (X₁ ⊔ X₂ ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D hEsub hXsubM hUE
  have hTM : D.T ≤ D.M := D.sylowM.le
  set Δ : Finset (Subgroup G) := {X₁ ⊔ D.T, X₂ ⊔ D.T} with hΔdef
  have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
    intro H hH
    simp only [hΔdef, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact ⟨le_sup_right, sup_le hX₁M hTM⟩
    · exact ⟨le_sup_right, sup_le hX₂M hTM⟩
  have hsupeq : (⨆ H ∈ Δ, H) = X₁ ⊔ X₂ ⊔ D.T := by
    refine le_antisymm (iSup₂_le fun H hH => ?_) ?_
    · simp only [hΔdef, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
      · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    · rw [show X₁ ⊔ X₂ ⊔ D.T = (X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) by ac_rfl]
      exact sup_le
        (le_iSup₂_of_le (X₁ ⊔ D.T) (by simp [hΔdef]) le_rfl)
        (le_iSup₂_of_le (X₂ ⊔ D.T) (by simp [hΔdef]) le_rfl)
  have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
    rw [hsupeq]
    exact hU
  have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq ((fun _ => 1) H) H := by
    intro H hH
    simp only [hΔdef, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group
        X₁ D.T 3 Nat.prime_three (by norm_num) hX₁card D.sylowM.isPGroup hX₁perm
    · exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group
        X₂ D.T 3 Nat.prime_three (by norm_num) hX₂card D.sylowM.isPGroup hX₂perm
  have hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
    intro H hH
    simp only [hΔdef, Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · have hHM : X₁ ⊔ D.T ≤ D.M := sup_le hX₁M hTM
      have h3 : 3 ∣ Nat.card ↥(X₁ ⊔ D.T) := by
        rw [← hX₁card]
        exact Subgroup.card_dvd_of_le le_sup_left
      exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded
        Nat.prime_three (by norm_num)
        hHM h3 hsp3
    · have hHM : X₂ ⊔ D.T ≤ D.M := sup_le hX₂M hTM
      have h3 : 3 ∣ Nat.card ↥(X₂ ⊔ D.T) := by
        rw [← hX₂card]
        exact Subgroup.card_dvd_of_le le_sup_left
      exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded
        Nat.prime_three (by norm_num)
        hHM h3 hsp3
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    have hL1 : barSub ⊥ V hV.isElemAbelian L ≠ ⊥ :=
      barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV rfl
      c.mem_calC.1 c.mem_calC.2.2 hL1
      (uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt)
    rw [hconj] at h1
    omega
  · have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
      barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
    have h3 := twelve_twentyThree_three D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV0
      c.mem_calC.1 c.mem_calC.2.2 hL1 hΔ hΔU (fun _ => 1) hι hO2
    rw [hconj] at h3
    have hsup1 : Δ.sup (fun _ => 1) = 1 := Finset.sup_const (by simp [hΔdef]) 1
    rw [hsup1] at h3
    omega

theorem bBar_le_five_of_M22
    (hV : Hyp125 D V₀ V) (hrowM22 : Inputs1719.W4Thm11_1RowA .M22)
    (hLM : L ≤ D.M) (hN : (L.subgroupOf D.M).Normal)
    (hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22)
    (hirr : IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ 5 := by
  classical
  by_contra hle
  have hnot : ¬ bBar L D.M V₀ V hV.isElemAbelian < 6 := by omega
  have hex : ∃ A ∈ calABar 6 D.M V₀ V hV.isElemAbelian,
      ⁅barSub V₀ V hV.isElemAbelian L, A⁆ ≠ ⊥ := by
    by_contra hall
    apply hnot
    rw [bBar_lt_iff hV.isElemAbelian (by norm_num : 0 < 6)]
    push Not at hall
    exact hall
  obtain ⟨A, hA, hne⟩ := hex
  have hLMb : barSub V₀ V hV.isElemAbelian L ≤ Mbar D.M V₀ V hV.isElemAbelian :=
    barSub_mono V₀ V hV.isElemAbelian hLM
  have hYle : barSub V₀ V hV.isElemAbelian L ⊔ A ≤ Mbar D.M V₀ V hV.isElemAbelian :=
    sup_le hLMb hA.1
  have hA6Y : A ∈ E3.aSet 6 (barSub V₀ V hV.isElemAbelian L ⊔ A) :=
    ⟨le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hXnorm : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (Mbar D.M V₀ V hV.isElemAbelian)).Normal :=
    normal_barSub_of_normal hV.isElemAbelian hLM hN
  have hYnorm : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (barSub V₀ V hV.isElemAbelian L ⊔ A)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hYle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLMb).mp hXnorm))
  obtain ⟨hq, hZ⟩ := isQuasisimple_of_isSpor_m22 hSp
  have hSpQ := isSpor_quotCenter_of_isSpor_m22 hSp
  have ho2 : O2Trivial (barSub V₀ V hV.isElemAbelian L) :=
    o2Trivial_of_isQuasisimple_of_odd_center
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq)
      (by rw [hZ]; exact ⟨0, by norm_num⟩)
  have hirrR : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn
      (barSub V₀ V hV.isElemAbelian L) :=
    fun U hU => hirr.2.2.2 U hU bot_le le_top
  have hsq : ∀ w : Vtil V₀ V hV.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian
  have hmul : ∀ w : Vtil V₀ V hV.isElemAbelian, w * w = 1 :=
    fun w => by simpa [pow_two] using hsq w
  have hntW : Nontrivial (Vtil V₀ V hV.isElemAbelian) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hbot : (⊥ : Subgroup (Vtil V₀ V hV.isElemAbelian)) = ⊤ := by
      ext x
      rw [Subgroup.mem_bot]
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => Subsingleton.elim x 1⟩
    exact (ne_of_lt hirr.1) hbot
  have := hntW
  have hA2 : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hgen : CFSG.generalizedFitting
      ↥(barSub V₀ V hV.isElemAbelian L ⊔ A) =
      (barSub V₀ V hV.isElemAbelian L).subgroupOf
        (barSub V₀ V hV.isElemAbelian L ⊔ A) :=
    CFSG.GroupTheory.generalizedFitting_sup_eq_of_isPGroup_two_of_isIrrOn
      (W := Vtil V₀ V hV.isElemAbelian) hmul hq hLMb hA.1 hirrR hXnorm hA2
  have hF : Fstar (barSub V₀ V hV.isElemAbelian L ⊔ A) =
      barSub V₀ V hV.isElemAbelian L :=
    fstar_eq_of_generalizedFitting_eq le_sup_left hgen
  have h5 : E3.aParam (barSub V₀ V hV.isElemAbelian L ⊔ A) ≤ 5 :=
    hrowM22 (W := Vtil V₀ V hV.isElemAbelian) hsq (barSub V₀ V hV.isElemAbelian L ⊔ A)
      (barSub V₀ V hV.isElemAbelian L) le_sup_left hYnorm hF hq ho2 hSpQ
  have h6 : 6 ≤ E3.aParam (barSub V₀ V hV.isElemAbelian L ⊔ A) :=
    E3.le_aParam_of_mem_aSet (by norm_num) hA6Y
  omega

theorem card_vtil_eq_of_M22
    (hV : Hyp125 D V₀ V) (h4115 : WeakClosure81.W4Lem11_5Twelve)
    (hLM : L ≤ D.M) (hN : (L.subgroupOf D.M).Normal)
    (hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22)
    (hirr : IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥)
    (hm : mBar D.M V₀ V hV.isElemAbelian ≤ 11) :
    Nat.card (Vtil V₀ V hV.isElemAbelian) = 2 ^ 10 := by
  classical
  have hsq : ∀ w : Vtil V₀ V hV.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian
  have hmul : ∀ w : Vtil V₀ V hV.isElemAbelian, w * w = 1 :=
    fun w => by simpa [pow_two] using hsq w
  have hLMb : barSub V₀ V hV.isElemAbelian L ≤ Mbar D.M V₀ V hV.isElemAbelian :=
    barSub_mono V₀ V hV.isElemAbelian hLM
  have hcardL : Nat.card ↥(barSub V₀ V hV.isElemAbelian L) = 443520 := by
    obtain ⟨e⟩ := hSp
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have hevenL : Even (Nat.card ↥(barSub V₀ V hV.isElemAbelian L)) := by
    rw [hcardL]
    norm_num
  have hevenMb : Even (Nat.card ↥(Mbar D.M V₀ V hV.isElemAbelian)) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hevenL).trans
      (Subgroup.card_dvd_of_le hLMb))
  obtain ⟨u, huMb, hu1, hu2⟩ :=
    CFSG.CGT.PushingUpLit.LIT.Foote.L54.exists_involution_of_even hevenMb
  have huord : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hu2) hu1
  have hSne : ({n : ℕ | ∃ t ∈ Mbar D.M V₀ V hV.isElemAbelian,
      orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} : Set ℕ).Nonempty :=
    ⟨_, u, huMb, huord, rfl⟩
  obtain ⟨t₀, ht₀Mb, ht₀ord, ht₀rk⟩ := Nat.sInf_mem hSne
  have ht₀sq : t₀ * t₀ = 1 := by
    have h : t₀ ^ 2 = 1 := by
      rw [← ht₀ord]
      exact pow_orderOf_eq_one t₀
    simpa [pow_two] using h
  have ht₀ne : t₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht₀ord
    exact absurd ht₀ord (by norm_num)
  have hmParam : E3.mParam (Mbar D.M V₀ V hV.isElemAbelian) =
      sInf {n : ℕ | ∃ t ∈ Mbar D.M V₀ V hV.isElemAbelian,
        orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} := by
    simp only [E3.mParam, if_pos hevenMb]
  have hY0le : barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀ ≤
      Mbar D.M V₀ V hV.isElemAbelian :=
    sup_le hLMb (Subgroup.zpowers_le.mpr ht₀Mb)
  have hXnorm : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (Mbar D.M V₀ V hV.isElemAbelian)).Normal :=
    normal_barSub_of_normal hV.isElemAbelian hLM hN
  have hY0norm : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hY0le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLMb).mp hXnorm))
  obtain ⟨hq, hZ⟩ := isQuasisimple_of_isSpor_m22 hSp
  have ho2 : O2Trivial (barSub V₀ V hV.isElemAbelian L) :=
    o2Trivial_of_isQuasisimple_of_odd_center
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq)
      (by rw [hZ]; exact ⟨0, by norm_num⟩)
  have hirrR : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn
      (barSub V₀ V hV.isElemAbelian L) :=
    fun U hU => hirr.2.2.2 U hU bot_le le_top
  have hntW : Nontrivial (Vtil V₀ V hV.isElemAbelian) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hbot : (⊥ : Subgroup (Vtil V₀ V hV.isElemAbelian)) = ⊤ := by
      ext x
      rw [Subgroup.mem_bot]
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => Subsingleton.elim x 1⟩
    exact (ne_of_lt hirr.1) hbot
  have := hntW
  have hgen : CFSG.generalizedFitting
      ↥(barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀) =
      (barSub V₀ V hV.isElemAbelian L).subgroupOf
        (barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀) :=
    CFSG.GroupTheory.fstar_sup_zpowers_eq_of_quasisimple_normal
      (W := Vtil V₀ V hV.isElemAbelian) hmul hLMb hq hirrR hXnorm
      ht₀Mb ht₀sq ht₀ne
  have hF : Fstar (barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀) =
      barSub V₀ V hV.isElemAbelian L :=
    fstar_eq_of_generalizedFitting_eq le_sup_left hgen
  have hres := h4115 (W := Vtil V₀ V hV.isElemAbelian) hsq
    (barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀)
    (barSub V₀ V hV.isElemAbelian L) le_sup_left hY0norm hF hq ho2 hSp hirr
  rcases hres with h12 | hrk
  · exfalso
    have hmY : E3.mParam (barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀) ≤
        rkIdx (fixV (Subgroup.zpowers t₀)) :=
      CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)) ht₀ord
    have h1 : rkIdx (fixV (Subgroup.zpowers t₀)) =
        E3.mParam (Mbar D.M V₀ V hV.isElemAbelian) := ht₀rk.symm.trans hmParam.symm
    have hmY' : E3.mParam (barSub V₀ V hV.isElemAbelian L ⊔ Subgroup.zpowers t₀) ≤
        mBar D.M V₀ V hV.isElemAbelian := by
      rw [show mBar D.M V₀ V hV.isElemAbelian =
        E3.mParam (Mbar D.M V₀ V hV.isElemAbelian) from rfl]
      exact hmY.trans (le_of_eq h1)
    omega
  · rw [← Subgroup.card_top (G := Vtil V₀ V hV.isElemAbelian),
      CFSG.Quasithin.card_eq_two_pow hsq ⊤, CFSG.Quasithin.rk_top, hrk]

theorem centralizer_barSub_eq_bot_of_M22
    (hV : Hyp125 D V₀ V)
    (hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22)
    (hcard : Nat.card (Vtil V₀ V hV.isElemAbelian) = 2 ^ 10)
    (hirr : IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥) :
    Subgroup.centralizer (barSub V₀ V hV.isElemAbelian L :
      Set (MulAut (Vtil V₀ V hV.isElemAbelian))) = ⊥ := by
  classical
  have hsq : ∀ w : Vtil V₀ V hV.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian
  have hmul : ∀ w : Vtil V₀ V hV.isElemAbelian, w * w = 1 :=
    fun w => by simpa [pow_two] using hsq w
  have hirrFun : ∀ U : Subgroup (Vtil V₀ V hV.isElemAbelian),
      (∀ g ∈ barSub V₀ V hV.isElemAbelian L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr.2.2.2 U hU bot_le le_top
  have hcard30 : Nat.card (Vtil V₀ V hV.isElemAbelian) ≤ 2 ^ 30 := by
    rw [hcard]
    norm_num
  rcases CFSG.Quasithin.mathieuSmallIrr22_holds
    (W := Vtil V₀ V hV.isElemAbelian) hmul
    (barSub V₀ V hV.isElemAbelian L) hSp hirrFun hcard30 with hcode | hcocode
  · exact CFSG.Quasithin.H.ModelType.centralizer_eq_bot_of_code22 hcode
  · exact CFSG.Quasithin.H.ModelIrr.centralizer_eq_bot_of_cocode22 hcocode

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
