module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBOutCover
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR861E
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAShared
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardG2General
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerActionOut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarCover
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CoverUpperCentral
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialCommutator
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69CenterApps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowInfCenter
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_9)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open scoped commutatorElement

private theorem r861cov_centralizerBar_of_centralizes_sylow
    {G : Type} [Group G] [Finite G] {L Q P : Subgroup G}
    (hQL : Q ≤ L) (hQP : Q ≤ P)
    (hQO2 : Q ⊓ pCoreOf 2 L = ⊥)
    (hQext : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hQsyl : ∃ S : Sylow 3 ↥L, (S : Subgroup ↥L) = Q.subgroupOf L)
    (hZbar : Nat.card (Subgroup.center (Bar2 L)) = 3) :
    ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) → q ∈ centralizerBar P L := by
  classical
  intro q hq hq_comm
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let f : ↥Q →* Bar2 L := π.comp (Subgroup.inclusion hQL)
  have hf : Function.Injective f := injective_comp_subgroupOf_mk' hQL hQO2
  have hf_range : f.range = (Q.subgroupOf L).map π := range_comp_subgroupOf_mk' hQL
  have hQsylb : ∃ Pb : Sylow 3 (Bar2 L), (Pb : Subgroup (Bar2 L)) = f.range := by
    obtain ⟨Pb, hPb⟩ := exists_sylow_map_subgroupOf_mk' hQsyl
    exact ⟨Pb, hPb.trans hf_range.symm⟩
  have hZcard : Nat.card (Subgroup.center (Bar2 L)) = 3 := hZbar
  obtain ⟨Pb, hPb⟩ := hQsylb
  have hZ3 : IsPGroup 3 (Subgroup.center (Bar2 L)) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hZlePb : Subgroup.center (Bar2 L) ≤ (Pb : Subgroup (Bar2 L)) :=
    hZ3.le_sylow_of_normal Pb
  have hZleRange : Subgroup.center (Bar2 L) ≤ f.range := by
    rw [hPb] at hZlePb
    exact hZlePb
  have hZleCenterRange : Subgroup.center (Bar2 L) ≤
      (Subgroup.center ↥f.range).map f.range.subtype := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZleRange hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hz (g : Bar2 L)
  have hcenterQcard : Nat.card ((Subgroup.center ↥Q).map f) = 3 := by
    rw [Subgroup.card_map_of_injective hf]
    have h := center_card_three_of_isExtraspecialExpP hQext
    rwa [Subgroup.card_map_of_injective Q.subtype_injective] at h
  have hCcard : Nat.card ((Subgroup.center ↥f.range).map f.range.subtype) = 3 := by
    rw [card_center_map_eq_of_injective f hf, hcenterQcard]
  have hZeq : Subgroup.center (Bar2 L) =
      (Subgroup.center ↥f.range).map f.range.subtype :=
    Subgroup.eq_of_le_of_card_ge hZleCenterRange (by rw [hCcard, hZcard])
  let qQ : ↥Q := ⟨q, hq⟩
  have hfq_centerRange : f qQ ∈ (Subgroup.center ↥f.range).map f.range.subtype := by
    refine Subgroup.mem_map.mpr
      ⟨⟨f qQ, MonoidHom.mem_range.mpr ⟨qQ, rfl⟩⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨qQ', hq'⟩ := MonoidHom.mem_range.mp g.2
    apply Subtype.ext
    change (g : Bar2 L) * f qQ = f qQ * (g : Bar2 L)
    rw [← hq']
    change f qQ' * f qQ = f qQ * f qQ'
    have hmul : qQ' * qQ = qQ * qQ' := Subtype.ext (hq_comm (qQ' : G) qQ'.2).symm
    rw [← map_mul, ← map_mul, hmul]
  have hfq_centerK : f qQ ∈ Subgroup.center (Bar2 L) := by
    rw [hZeq]
    exact hfq_centerRange
  refine mem_centralizerBar_iff.mpr ⟨hQP hq, ?_⟩
  intro y hy
  have hcomm : π ⟨y, hy⟩ * f qQ = f qQ * π ⟨y, hy⟩ :=
    Subgroup.mem_center_iff.mp hfq_centerK (π ⟨y, hy⟩)
  have hfq : f qQ = π ⟨q, hQL hq⟩ := rfl
  rw [hfq] at hcomm
  let a : ↥L := ⟨y, hy⟩ * ⟨q, hQL hq⟩
  let b : ↥L := ⟨q, hQL hq⟩ * ⟨y, hy⟩
  have hab : π a = π b := by
    dsimp only [a, b]
    rw [map_mul, map_mul]
    exact hcomm
  have hmem : a / b ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq_iff_div_mem.mp hab
  have hval : ((a / b : ↥L) : G) = ⁅y, q⁆ := by
    dsimp only [a, b]
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
    group
  have hyq : ⁅y, q⁆ ∈ pCoreOf 2 L := by
    rw [← hval, pCoreOf]
    exact Subgroup.mem_map.mpr ⟨a / b, hmem, rfl⟩
  rw [show ⁅q, y⁆ = ⁅y, q⁆⁻¹ from by rw [commutatorElement_inv]]
  exact (pCoreOf 2 L).inv_mem hyq

theorem r861_cover_of_spine
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h69 : R6_9 D) (h857 : R857 D) (h859 : R859 D) :
    ∀ L Q P : Subgroup G, Cex856 D L Q P → ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 →
      ¬ X ≤ Q → ¬ normalizer (X : Set G) ≤ D.M → HasGammaE9 D X →
        List857Clause2 (Bar2 L) → ⁅X, L⁆ ≤ pCoreOf 2 L := by
  intro L Q P hc X hXP hX3 hXQ hN hE hcl
  classical
  have hLM : L ≤ D.M := hc.mem.1.le
  have hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L := hc.sylowQ
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M := hc.sylowP
  have hQP : Q ≤ P := hc.le
  have hQL : Q ≤ L := hQ.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPNL : P ≤ Subgroup.normalizer (L : Set G) := h859 L Q P hc
  have hOut : ¬ 3 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
    not_three_dvd_card_outer_of_cover hcl
  have hQext : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q :=
    (h857 L Q P hc).2.2 hcl
  have hZbar : Nat.card (Subgroup.center (Bar2 L)) = 3 := by
    rcases hcl with h | h | h <;> exact h.2.1
  have hsub : D.sig ⊆ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hc.mem)
  obtain ⟨E, hEM, hEel, hEcard, hΓ, hEX⟩ := hE
  have hQO2 : Q ⊓ pCoreOf 2 L = ⊥ := hc.inf_pCore_eq_bot
  have hQeq : Q = P ⊓ L :=
    (hQ.eq_of_le (le_inf hQP hQL) inf_le_right (hP3.to_le inf_le_left)).symm
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hc.le_normalizer_sylowQ h859
  have hQnormP : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPQ
  have hInnerBar := inner_action_of_not_three_dvd_outer hOut hP3 hPNL
  have hXdecomp : X ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hQP hQL hQeq hQnormP hQ hP3 hPNL hXP
      (fun x hx => hInnerBar x (hXP hx))
  have hQC : ⁅Q, centralizerBar P L⁆ = ⊥ :=
    commutator_eq_bot_centralizerBar hQL hQO2 hPQ
  have hCQ : ∀ c ∈ centralizerBar P L, ∀ q ∈ Q, c * q = q * c := by
    intro c hc q hq
    have hmem : ⁅q, c⁆ ∈ ⁅Q, centralizerBar P L⁆ :=
      Subgroup.commutator_mem_commutator hq hc
    rw [hQC, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  have hQQ : ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype :=
    commutator_le_center_of_isExtraspecialExpP hQext
  let W : Subgroup G := Q ⊔ X
  have hWleP : W ≤ P := sup_le hQP hXP
  have hWleM : W ≤ D.M := hWleP.trans hP.le
  have hW3 : IsPGroup 3 W := hP3.to_le hWleP
  have hXW : X ≤ W := le_sup_right
  have hXZ2 : X ≤ (Subgroup.upperCentralSeries ↥W 2).map W.subtype :=
    le_map_upperCentralSeries_two_of_sup_cover hXdecomp hCQ hQQ hX3
  have hXZ : X ≤ (Subgroup.center ↥W).map W.subtype :=
    X_le_center_sup_of_R6_9 h69 hsub hEM hEel hEcard hΓ (hXP.trans hP.le) hX3 hEX hN
      hWleM hW3 hXW hXZ2
  have hXcentQ : ∀ x ∈ X, ∀ q ∈ Q, x * q = q * x := by
    intro x hx q hq
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hXZ hx)
    have hzx' : (z : G) = x := hzx
    have h := congrArg W.subtype
      (Subgroup.mem_center_iff.mp hz (⟨q, Subgroup.mem_sup_left hq⟩ : ↥W))
    have h' : q * x = x * q := by simpa [hzx'] using h
    exact h'.symm
  have hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) → q ∈ centralizerBar P L :=
    r861cov_centralizerBar_of_centralizes_sylow hQL hQP hQO2 hQext
      hQ.exists_sylow_eq_subgroupOf hZbar
  have hXC : X ≤ centralizerBar P L :=
    le_centralizerBar_of_centralizes_left hCQ hZQ hXdecomp hXcentQ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (mem_centralizerBar_iff.mp (hXC hx)).2 y hy

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
