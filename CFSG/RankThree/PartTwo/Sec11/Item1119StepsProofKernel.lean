module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
import CFSG.RankThree.PartTwo.KFacts.K71bCentList
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1119StepsProof

section Generic

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G}

theorem mem_sectionCentralizer_of_mem_thetaQuotCentralizer {e : G} (heA : e ∈ A)
    (heY : e ∈ Sec4.thetaQuotCentralizer Y) :
    e ∈ Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) := by
  refine ⟨heA, fun y hy => ?_⟩
  have h3 := (Sec6.mem_thetaQuotCentralizer_iff.mp heY).2 y hy
  have e1 : e * y * e⁻¹ * y⁻¹ = y * (y⁻¹ * (e * y * e⁻¹)) * y⁻¹ := by group
  rw [e1]
  exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y hy) _).mp h3

end Generic

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem commutator_mem_theta_sec11K_of_mem_thetaQuotCentralizer_Y
    (h : Sec11Std G A c L a R Y) {t : G} (htN : t ∈ Subgroup.normalizer (L : Set G))
    (hta : t * a = a * t) (htY : t ∈ Sec4.thetaQuotCentralizer Y) :
    ∀ k ∈ sec11K L a, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) (sec11K L a) := by
  intro k hk
  have hkY : k ∈ Y := h.sec11K_le hk
  have htKN : t ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (GroupTheory.SteinbergBY.mem_normalizer_inf htN
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hta)))
  have h1 : t * k * t⁻¹ * k⁻¹ ∈ sec11K L a :=
    (sec11K L a).mul_mem ((Subgroup.mem_normalizer_iff.mp htKN k).mp hk)
      ((sec11K L a).inv_mem hk)
  have h2 : t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    have h3 := (Sec6.mem_thetaQuotCentralizer_iff.mp htY).2 k hkY
    have e : t * k * t⁻¹ * k⁻¹ = k * (k⁻¹ * (t * k * t⁻¹)) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y hkY) _).mp h3
  exact Sec13.inf_inSubgroup_theta_le h.sec11K_le ⟨h1, h2⟩

theorem mem_zpowers_c_of_mem_zpowers_s (h : Sec11Data G A c L a R Y d x s r g) {u : G}
    (hus : u ∈ Subgroup.zpowers s) (hu1 : u ≠ 1) : c ∈ Subgroup.zpowers u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcs := h.c_mem_zpowers_s
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hsR : s ∈ R := (Item1116Proof.mem_R h).2.2
  set S := Subgroup.zpowers s with hS
  have hS3 : IsPGroup 3 S := h.isSylowOf.isPGroup.to_le (Subgroup.zpowers_le.mpr hsR)
  set U := (Subgroup.zpowers u).subgroupOf S with hU
  set C' := (Subgroup.zpowers c).subgroupOf S with hC'
  have hU3 : IsPGroup 3 U := hS3.to_subgroup _
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : (⟨u, hus⟩ : S) ∈ U := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers u)
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 (congrArg Subtype.val this)
  have h3 : 3 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU3
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hUne
      rw [pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq U hn
    rw [hn]
    exact dvd_pow_self 3 hn0
  have hC'3 : Nat.card C' = 3 := by
    rw [hC', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcs)).toEquiv,
      Nat.card_zpowers, hc3]
  have hle : C' ≤ U := (IsCyclic.subgroup_le_iff_card_dvd).mpr (hC'3 ▸ h3)
  have hcU : (⟨c, hcs⟩ : S) ∈ U := hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c))
  exact Subgroup.mem_subgroupOf.mp hcU

theorem eq_one_of_mem_zpowers_s_of_mem_thetaQuotCentralizer_Y (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) {u : G} (hus : u ∈ Subgroup.zpowers s)
    (huY : u ∈ Sec4.thetaQuotCentralizer Y) : u = 1 := by
  by_contra hu1
  have hcu := mem_zpowers_c_of_mem_zpowers_s h hus hu1
  have hcY : c ∈ Sec4.thetaQuotCentralizer Y := Subgroup.zpowers_le.mpr huY hcu
  have hsec := mem_sectionCentralizer_of_mem_thetaQuotCentralizer h.mem_A hcY
  rw [(h118 G A c L a R Y h.toSec11Std d g h.inf_eq h.closure_eq h.g_mem.2 h.g_not_mem
    h.conj_mem).2.2] at hsec
  exact (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).1 hsec

theorem a_mem_thetaQuotCentralizer_Y (h : Sec11Std G A c L a R Y) :
    a ∈ Sec4.thetaQuotCentralizer Y := by
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨?_, fun l hl => ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYC hy), mul_inv_cancel_right]
    exact hy
  · rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYC hl), mul_inv_cancel_right,
      inv_mul_cancel]
    exact Subgroup.one_mem _

theorem mem_zpowers_a_of_mem_thetaQuotCentralizer_Y (h45 : Sec4.Item4_5) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) {w : G} (hwR : w ∈ R) (hwa : w * a = a * w)
    (hwY : w ∈ Sec4.thetaQuotCentralizer Y) : w ∈ Subgroup.zpowers a := by
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  have hout : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with hf | hf
    · exact KFacts.InducesStdKind.inducesOuterTheta L hf (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hf (by decide)
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have htK := commutator_mem_theta_sec11K_of_mem_thetaQuotCentralizer_Y h.toSec11Std (hRL hwR)
    hwa hwY
  obtain ⟨i, hi⟩ := KFacts.exists_mul_pow_mem_thetaQuotCentralizer_of_list h.isList1016 hout ha3
    (hRL hwR) (Item1116Proof.exists_pow_eq_one_of_mem h hwR) hwa htK
  have hus : w * a ^ i ∈ Subgroup.zpowers s := by
    rw [← h.inf_centralizer_eq]
    exact ⟨R.mul_mem hwR (R.pow_mem haR i), hi⟩
  have huY : w * a ^ i ∈ Sec4.thetaQuotCentralizer Y :=
    Subgroup.mul_mem _ hwY (Subgroup.pow_mem _ (a_mem_thetaQuotCentralizer_Y h.toSec11Std) i)
  have h1 := eq_one_of_mem_zpowers_s_of_mem_thetaQuotCentralizer_Y h118 h hus huY
  have hw : w = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hw]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i)

end Data

end Item1119StepsProof

end CFSG.RankThree.PartTwo.Sec11
