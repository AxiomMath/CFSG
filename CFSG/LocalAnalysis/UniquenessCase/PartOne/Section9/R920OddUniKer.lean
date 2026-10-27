module

public import CFSG.CGT.Foote82.D1Lemma71
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSigPi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_range_barConj_comp_dvd {Λ : Type} [Group Λ] [Finite Λ] {q : ℕ} (hq : q.Prime)
    {T : Subgroup Λ} (hT : IsL2Odd (Bar2 T) q) {Q : Subgroup Λ}
    (hQ : IsPGroup q Q) (hQT : Q ≤ normalizer (T : Set Λ)) :
    Nat.card ((CFSG.CGT.Foote82.barConj T).comp (Subgroup.inclusion hQT)).range ∣ q := by
  haveI : Fact q.Prime := ⟨hq⟩
  set φ := (CFSG.CGT.Foote82.barConj T).comp (Subgroup.inclusion hQT)
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := (hQ.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).exists_card_eq
  have hdvd : Nat.card φ.range ∣ q * (q ^ 2 - 1) := by
    rw [← card_mulAut_of_isL2Odd hq hT]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hnd : ¬ q ∣ q ^ 2 - 1 := by
    intro h
    have h1 : q ∣ q ^ 2 - 1 + 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 hq.ne_zero))]
      exact dvd_pow_self q two_ne_zero
    exact hq.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))
  rw [hn] at hdvd ⊢
  exact (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hq).2 hnd)).dvd_of_dvd_mul_right
    hdvd

theorem le_inf_centralizer_sup_pCoreOf {Λ : Type} [Group Λ] [Finite Λ] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {T : Subgroup Λ} {u : Λ} (huT : u ∈ normalizer (T : Set Λ))
    (hu : orderOf u = q) (h1 : ∀ t ∈ T, u * t * u⁻¹ * t⁻¹ ∈ pCoreOf 2 T) :
    T ≤ (centralizer ({u} : Set Λ) ⊓ T) ⊔ pCoreOf 2 T := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT : pCoreOf 2 T ≤ T := CFSG.LieType.BorelTits.pCoreOf_le 2 T
  have hRN : pCoreOf 2 T ≤ normalizer (T : Set Λ) := hRT.trans Subgroup.le_normalizer
  set N := (pCoreOf 2 T).subgroupOf (normalizer (T : Set Λ)) with hN_def
  haveI : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).2
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 T)
  have hN : ¬ q ∣ Nat.card N := by
    rw [hN_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv]
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 T).exists_card_eq
    rw [hn]
    exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  set u' : ↥(normalizer (T : Set Λ)) := ⟨u, huT⟩
  have hQ : IsPGroup q (zpowers u') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← hu]
    exact Subgroup.orderOf_mk u huT
  intro t ht
  set t' : ↥(normalizer (T : Set Λ)) := ⟨t, Subgroup.le_normalizer ht⟩
  have hcomm : Commute (QuotientGroup.mk' N u') (QuotientGroup.mk' N t') := by
    have hk : u' * t' * u'⁻¹ * t'⁻¹ ∈ N := by
      rw [hN_def, Subgroup.mem_subgroupOf]
      exact h1 t ht
    have h2 : QuotientGroup.mk' N (u' * t' * u'⁻¹ * t'⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hmem : QuotientGroup.mk' N t' ∈ centralizer
      (((zpowers u').map (QuotientGroup.mk' N) : Subgroup (↥(normalizer (T : Set Λ)) ⧸ N)) :
        Set (↥(normalizer (T : Set Λ)) ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow]
    exact (hcomm.zpow_left k).eq
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN hQ] at hmem
  obtain ⟨c, hc, hct⟩ := hmem
  obtain ⟨z, hz, hcz⟩ := (QuotientGroup.mk'_eq_mk' N).1 hct
  have hcu : (c : Λ) * u = u * c :=
    (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc u' (Subgroup.mem_zpowers u'))).symm
  have hzR : (z : Λ) ∈ pCoreOf 2 T := by
    rw [hN_def, Subgroup.mem_subgroupOf] at hz
    exact hz
  have hczt : (c : Λ) * z = t := congrArg Subtype.val hcz
  have hcT : (c : Λ) ∈ T := by
    have h4 : (c : Λ) = t * (z : Λ)⁻¹ := by rw [← hczt, mul_inv_cancel_right]
    rw [h4]
    exact T.mul_mem ht (T.inv_mem (hRT hzR))
  rw [← hczt]
  exact Subgroup.mul_mem_sup
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hcu, hcT⟩) hzR

theorem exists_mem_orderOf_eq_not_isSolvable_inf {Λ : Type} [Group Λ] [Finite Λ] {q : ℕ}
    (hq : q.Prime) (hq5 : 5 < q) {T : Subgroup Λ} (hT : IsL2Odd (Bar2 T) q)
    {Q : Subgroup Λ} (hQ : IsPGroup q Q) (hQT : Q ≤ normalizer (T : Set Λ))
    (hQq : q ^ 2 ∣ Nat.card Q) :
    ∃ u ∈ Q, orderOf u = q ∧ ¬ Group.IsSolvable ↥(centralizer ({u} : Set Λ) ⊓ T) := by
  haveI : Fact q.Prime := ⟨hq⟩
  set φ := (CFSG.CGT.Foote82.barConj T).comp (Subgroup.inclusion hQT)
  have hker : q ∣ Nat.card φ.ker := by
    have h3 : q ^ 2 ∣ Nat.card φ.ker * q := by
      rw [← Subgroup.card_ker_mul_card_range φ] at hQq
      exact hQq.trans (mul_dvd_mul_left _ (card_range_barConj_comp_dvd hq hT hQ hQT))
    rw [pow_two] at h3
    exact Nat.dvd_of_mul_dvd_mul_right hq.pos h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hker
  have hy : CFSG.CGT.Foote82.barConj T (Subgroup.inclusion hQT (x : Q)) = 1 :=
    MonoidHom.mem_ker.1 x.2
  have hu : orderOf ((x : Q) : Λ) = q := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  refine ⟨((x : Q) : Λ), (x : Q).2, hu, fun hsol => ?_⟩
  have h1 : ∀ t ∈ T, ((x : Q) : Λ) * t * ((x : Q) : Λ)⁻¹ * t⁻¹ ∈ pCoreOf 2 T := fun t ht =>
    (CFSG.CGT.Foote82.barConj_mk_eq_iff T (Subgroup.inclusion hQT (x : Q)) ⟨t, ht⟩).1
      (by simp only [hy, MulAut.one_apply])
  have hle := le_inf_centralizer_sup_pCoreOf hq (by omega) (hQT (x : Q).2) hu h1
  have hsurj := surjective_mk_inclusion_of_sup
    (inf_le_right : centralizer ({((x : Q) : Λ)} : Set Λ) ⊓ T ≤ T)
    (le_antisymm hle (sup_le inf_le_right (CFSG.LieType.BorelTits.pCoreOf_le 2 T)))
  haveI := hsol
  haveI : Group.IsSolvable (Bar2 T) := Group.isSolvable_of_surjective hsurj
  haveI : IsSimpleGroup (Bar2 T) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hT
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isL2Odd hq5 hT
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
