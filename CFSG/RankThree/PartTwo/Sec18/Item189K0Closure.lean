module

public import CFSG.RankThree.PartTwo.Sec18.Item189K0Center
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartTwo.Sec18.Item189K0Centralizes

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A B X M : Subgroup G} {c : G}

private theorem le_normalizer_inf_sup {P Q R Y : Subgroup G}
    (hP : Y ≤ Subgroup.normalizer (P : Set G)) (hQ : Y ≤ Subgroup.normalizer (Q : Set G))
    (hR : Y ≤ Subgroup.normalizer (R : Set G)) :
    Y ≤ Subgroup.normalizer ((P ⊓ (Q ⊔ R) : Subgroup G) : Set G) := by
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := Q ⊔ R)
    ⟨hP hg, Subgroup.inf_normalizer_le_normalizer_sup Q R ⟨hQ hg, hR hg⟩⟩

theorem K0Setting.inf_sup_theta_eq_bot (h46 : Sec4.Item4_6) (hC : Sec13.KS131CenterList46)
    (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ thetaComponentsIn M) (h3 : 3 ∣ Nat.card K₀)
    (hn : M ≤ Subgroup.normalizer (K₀ : Set G)) :
    B ⊓ (K₀ ⊔ inSubgroup (aschbacherSolvableCore 3) M) = ⊥ := by
  have hK₀M : K₀ ≤ M := le_of_mem_thetaComponentsIn hK₀
  have hBM : B ≤ M := h.le_A.trans h.hAM
  have hXN : X ≤ Subgroup.normalizer
      ((B ⊓ (K₀ ⊔ inSubgroup (aschbacherSolvableCore 3) M) : Subgroup G) : Set G) :=
    le_normalizer_inf_sup h.plane.le_normalizer_plane (fun g hg => hn (h.hXM hg))
      (fun g hg => Sec6.le_normalizer_theta M (h.hXM hg))
  rcases h.eq_bot_or_eq inf_le_left hXN with hU | hU
  · exact hU
  · exfalso
    have hBle : B ≤ K₀ ⊔ inSubgroup (aschbacherSolvableCore 3) M := hU.ge.trans inf_le_right
    have hBK : imM M B ≤ imM M K₀ := (imM_le_imM_iff hK₀M hBM).mpr hBle
    have hBC := h.le_thetaQuotCentralizer h45 hK₀
    have hcomm := imM_commute_of_le_thetaQuotCentralizer hK₀ hBM hBC
    have hcen : (imM M B).subgroupOf (imM M K₀) ≤ Subgroup.center ↥(imM M K₀) := by
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hcomm _ hz _ g.2).symm
    have hcard : Nat.card ((imM M B).subgroupOf (imM M K₀)) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv,
        imM_card_eq_of_isPGroup hBM h.isElemAbelian_B.isPGroup, h.plane.card_plane]
    have hdvd : 9 ∣ Nat.card (Subgroup.center ↥(imM M K₀)) := by
      have := Subgroup.card_dvd_of_le hcen
      rwa [hcard] at this
    have h3c : 3 ∣ Nat.card (Subgroup.center ↥(imM M K₀)) :=
      (by norm_num : (3 : ℕ) ∣ 9).trans hdvd
    have hc3 : Nat.card (Subgroup.center ↥(imM M K₀)) = 3 :=
      h.card_center_imM h46 hC hK₀ hBC h3c
    omega

theorem K0Setting.pRank_eq_one (h46 : Sec4.Item4_6) (hC : Sec13.KS131CenterList46)
    (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ thetaComponentsIn M) (h3 : 3 ∣ Nat.card K₀)
    (hn : M ≤ Subgroup.normalizer (K₀ : Set G)) : CFSG.Open.pRank 3 K₀ = 1 := by
  have hK₀M : K₀ ≤ M := le_of_mem_thetaComponentsIn hK₀
  have hBM : B ≤ M := h.le_A.trans h.hAM
  have hBK : imM M B ⊓ imM M K₀ = ⊥ :=
    imM_inf_eq_bot hK₀M hBM (h.inf_sup_theta_eq_bot h46 hC h45 hK₀ h3 hn)
  have hBC := h.le_thetaQuotCentralizer h45 hK₀
  have hcomm := imM_commute_of_le_thetaQuotCentralizer hK₀ hBM hBC
  have hBcard : Nat.card (imM M B) = 9 := by
    rw [imM_card_eq_of_isPGroup hBM h.isElemAbelian_B.isPGroup, h.plane.card_plane]
  refine pRank_eq_one_of h3 (fun E hEK hE => ?_)
  have hEM : E ≤ M := hEK.trans hK₀M
  have hEi : CFSG.Open.IsElemAbelian 3 (imM M E) := imM_isElemAbelian hEM hE
  have hEcard : Nat.card (imM M E) = Nat.card E := imM_card_eq_of_isPGroup hEM hE.isPGroup
  have hEK₀ : imM M E ≤ imM M K₀ := imM_mono hEK
  have hdisj : imM M E ⊓ imM M B = ⊥ := by
    rw [eq_bot_iff]
    calc imM M E ⊓ imM M B ≤ imM M K₀ ⊓ imM M B := inf_le_inf_right _ hEK₀
      _ = imM M B ⊓ imM M K₀ := inf_comm _ _
      _ = ⊥ := hBK
  have hPR : ∀ x ∈ imM M E, ∀ y ∈ imM M B, x * y = y * x := fun x hx y hy =>
    (hcomm y hy x (hEK₀ hx)).symm
  have hsup := isElemAbelian_sup_of_commute hEi (imM_isElemAbelian hBM h.isElemAbelian_B) hPR hdisj
  have hle := h.card_le_of_isElemAbelian_quot hsup.1
  rw [hsup.2, hEcard, hBcard] at hle
  omega

theorem K0Setting.exists_mem_inf_ne_one (h : K0Setting G A B X M c) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ thetaComponentsIn M) (h3 : 3 ∣ Nat.card K₀)
    (hn : M ≤ Subgroup.normalizer (K₀ : Set G)) :
    ∃ t ∈ A ⊓ K₀, t ≠ 1 ∧ t ^ 3 = 1 := by
  have hK₀M : K₀ ≤ M := le_of_mem_thetaComponentsIn hK₀
  obtain ⟨P, hP, hAP⟩ := exists_isSylowOf_ge h.isElemAbelian_A.isPGroup h.hAM
  have hPM : P ≤ M := hP.le
  have hPK : P ⊓ K₀ ≠ ⊥ := inf_ne_bot_of_sylow hK₀M hn hP h3
  have hN : ((P ⊓ K₀).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro x k hx hk
    exact ⟨P.mul_mem (P.mul_mem hk hx.1) (P.inv_mem hk),
      (Subgroup.mem_normalizer_iff.mp (hn (hPM hk)) x).mp hx.2⟩
  obtain ⟨t, htN, ht1, ht3, htc⟩ :=
    exists_mem_inf_center_of_normal hP.isPGroup inf_le_left hN hPK
  by_cases htA : t ∈ A
  · exact ⟨t, ⟨htA, htN.2⟩, ht1, ht3⟩
  · exfalso
    have hce : ∀ x ∈ A, x * t = t * x := fun x hx => htc x (hAP hx)
    obtain ⟨hE, hEc⟩ := isElemAbelian_zpowers_sup h.isElemAbelian_A ht3 hce htA
    have htM : t ∈ M := hPM htN.1
    have hle := h.card_le_of_isElemAbelian (sup_le (Subgroup.zpowers_le.mpr htM) h.hAM) hE
    rw [hEc, h.plane.card_eq] at hle
    omega

theorem K0Setting.inf_eq_zpowers (h46 : Sec4.Item4_6) (hC : Sec13.KS131CenterList46)
    (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ thetaComponentsIn M) (h3 : 3 ∣ Nat.card K₀)
    (hn : M ≤ Subgroup.normalizer (K₀ : Set G)) : A ⊓ K₀ = Subgroup.zpowers c := by
  have hBM : B ≤ M := h.le_A.trans h.hAM
  have hB5 := h.inf_sup_theta_eq_bot h46 hC h45 hK₀ h3 hn
  obtain ⟨t, htD, ht1, ht3⟩ := h.exists_mem_inf_ne_one hK₀ h3 hn
  have hDA : A ⊓ K₀ ≤ A := inf_le_left
  have hDB : A ⊓ K₀ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    calc A ⊓ K₀ ⊓ B ≤ B ⊓ (K₀ ⊔ inSubgroup (aschbacherSolvableCore 3) M) :=
          le_inf inf_le_right ((inf_le_left.trans inf_le_right).trans le_sup_left)
      _ = ⊥ := hB5
  have hDX : X ≤ Subgroup.normalizer ((A ⊓ K₀ : Subgroup G) : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := K₀)
      ⟨h.plane.le_normalizer hg, hn (h.hXM hg)⟩
  have hDE : CFSG.Open.IsElemAbelian 3 (A ⊓ K₀) := h.isElemAbelian_A.mono hDA
  have hcomm : ∀ x ∈ A ⊓ K₀, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    h.isElemAbelian_A.comm (hDA hx) (h.le_A hy)
  have hsup := isElemAbelian_sup_of_commute hDE h.isElemAbelian_B hcomm hDB
  have hle := h.card_le_of_isElemAbelian (sup_le (hDA.trans h.hAM) hBM) hsup.1
  rw [hsup.2, h.plane.card_plane] at hle
  have hpos : 0 < Nat.card (A ⊓ K₀ : Subgroup G) := Nat.card_pos
  have hdvd : 3 ∣ Nat.card (A ⊓ K₀ : Subgroup G) := by
    have ht : orderOf t = 3 := orderOf_eq_prime ht3 ht1
    have hz := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htD)
    rwa [Nat.card_zpowers, ht] at hz
  have hD3 : Nat.card (A ⊓ K₀ : Subgroup G) = 3 := by omega
  exact h.zpowers_eq_of_card_three hDA hD3 hDB hDX

theorem K0Setting.not_le_centralizer_imM (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ thetaComponentsIn M) (h3 : 3 ∣ Nat.card K₀) :
    ¬ imM M (Subgroup.zpowers c) ≤ Subgroup.centralizer (imM M K₀ : Set _) := by
  intro hle
  have hBM : B ≤ M := h.le_A.trans h.hAM
  have hcM : c ∈ M := h.hAM h.plane.mem
  have hBC := h.le_thetaQuotCentralizer h45 hK₀
  have hcomm := imM_commute_of_le_thetaQuotCentralizer hK₀ hBM hBC
  have hAC : imM M A ≤ Subgroup.centralizer (imM M K₀ : Set _) := by
    rw [h.plane.eq_sup, imM_sup (Subgroup.zpowers_le.mpr hcM) hBM]
    refine sup_le hle ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have hPE : CFSG.Open.IsElemAbelian 3 (imM M A) := imM_isElemAbelian h.hAM h.isElemAbelian_A
  have hPcard : Nat.card (imM M A) = 27 := by
    rw [imM_card_eq_of_isPGroup h.hAM h.isElemAbelian_A.isPGroup, h.plane.card_eq]
  obtain ⟨e, heK, he3, heP⟩ := Sec6.exists_pow_three_eq_one_not_mem (imM_isPerfect hK₀)
    (three_dvd_card_imM hK₀ h3) hAC
  have hce : ∀ x ∈ imM M A, x * e = e * x := fun x hx =>
    ((Subgroup.mem_centralizer_iff.mp (hAC hx)) e heK).symm
  obtain ⟨hE, hEc⟩ := isElemAbelian_zpowers_sup hPE he3 hce heP
  have hle27 := h.card_le_of_isElemAbelian_quot hE
  rw [hEc, hPcard] at hle27
  omega

theorem eq_of_imM_eq_of_isPerfect {K K₀ : Subgroup G} (hK₀ : K₀ ∈ thetaComponentsIn M)
    (hKK₀ : K ≤ K₀) (hKn : M ≤ Subgroup.normalizer (K : Set G)) (h : imM M K₀ ≤ imM M K) :
    K = K₀ := by
  have hK₀M : K₀ ≤ M := le_of_mem_thetaComponentsIn hK₀
  have hKM : K ≤ M := hKK₀.trans hK₀M
  have hθs : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) M) :=
    (Sec6.theta_solvable_and_not_dvd M).1
  have hPK : K₀ ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) M :=
    (imM_le_imM_iff hKM hK₀M).mp h
  have hKθ : K ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) M : Set G) :=
    hKM.trans (Sec6.le_normalizer_theta M)
  have hPK' : K₀ ≤ K ⊔ (K₀ ⊓ inSubgroup (aschbacherSolvableCore 3) M) := by
    intro x hx
    have hx' : x ∈ ((K ⊔ inSubgroup (aschbacherSolvableCore 3) M : Subgroup G) : Set G) :=
      hPK hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hKθ] at hx'
    obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    have htK₀ : t ∈ K₀ := by
      have h1 : k⁻¹ * (k * t) ∈ K₀ := K₀.mul_mem (K₀.inv_mem (hKK₀ hk)) hx
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem_sup hk ⟨htK₀, ht⟩
  have hN : (K.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKK₀).mpr (hK₀M.trans hKn)
  have hR : Group.IsSolvable ↥(K₀ ⊓ inSubgroup (aschbacherSolvableCore 3) M) := by
    haveI := hθs
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion
        (inf_le_right : K₀ ⊓ inSubgroup (aschbacherSolvableCore 3) M ≤
          inSubgroup (aschbacherSolvableCore 3) M))
      (Subgroup.inclusion_injective _)
  exact (eq_of_isPerfect_of_le_sup (isPerfect_of_mem_thetaComponentsIn hK₀) hKK₀ inf_le_left hN
    hR hPK').symm

theorem K0Setting.normalClosureIn_eq (h46 : Sec4.Item4_6) (hC : Sec13.KS131CenterList46)
    (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ thetaComponentsIn M) (h3 : 3 ∣ Nat.card K₀)
    (hn : M ≤ Subgroup.normalizer (K₀ : Set G)) : normalClosureIn M c = K₀ := by
  have hK₀M : K₀ ≤ M := le_of_mem_thetaComponentsIn hK₀
  have hcM : c ∈ M := h.hAM h.plane.mem
  have hcK₀ : c ∈ K₀ := by
    have hc : c ∈ A ⊓ K₀ := by
      rw [h.inf_eq_zpowers h46 hC h45 hK₀ h3 hn]
      exact Subgroup.mem_zpowers c
    exact hc.2
  have hKK₀ : normalClosureIn M c ≤ K₀ := by
    refine (Subgroup.closure_le K₀).mpr ?_
    rintro x ⟨m, hm, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hn hm) c).mp hcK₀
  have hKM : normalClosureIn M c ≤ M := hKK₀.trans hK₀M
  have hcK : c ∈ normalClosureIn M c := Subgroup.subset_closure ⟨1, M.one_mem, by simp⟩
  have hKn : M ≤ Subgroup.normalizer (normalClosureIn M c : Set G) :=
    le_normalizer_normalClosureIn_self M c
  have hsub : ((imM M (normalClosureIn M c)).subgroupOf (imM M K₀)).Normal :=
    (normal_imM hKM hKn).subgroupOf _
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (imM_isQuasisimple hK₀) hsub with
    htop | hcen
  · have himg : imM M K₀ ≤ imM M (normalClosureIn M c) := by
      intro y hy
      have hmem : (⟨y, hy⟩ : ↥(imM M K₀)) ∈
          (imM M (normalClosureIn M c)).subgroupOf (imM M K₀) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    exact eq_of_imM_eq_of_isPerfect hK₀ hKK₀ hKn himg
  · exfalso
    apply h.not_le_centralizer_imM h45 hK₀ h3
    have hzc : (⟨QuotientGroup.mk ⟨c, hcM⟩, mk_mem_imM hcM hcK₀⟩ : ↥(imM M K₀)) ∈
        Subgroup.center ↥(imM M K₀) :=
      hcen (Subgroup.mem_subgroupOf.mpr (mk_mem_imM hcM hcK))
    have hmemC : (QuotientGroup.mk ⟨c, hcM⟩ : ↥M ⧸ aschbacherSolvableCore 3 ↥M) ∈
        Subgroup.centralizer (imM M K₀ : Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩)
    intro x hx
    obtain ⟨k, hkM, hkc, rfl⟩ := mem_imM_iff.mp hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hkc
    have hkeq : (⟨c ^ i, hkM⟩ : ↥M) = (⟨c, hcM⟩ : ↥M) ^ i := Subtype.ext (by simp)
    rw [hkeq, QuotientGroup.mk_zpow]
    exact zpow_mem hmemC i

end CFSG.RankThree.PartTwo.Sec18
