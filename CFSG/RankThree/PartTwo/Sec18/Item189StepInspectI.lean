module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
import CFSG.RankThree.PartTwo.Sec18.Item189KType
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Omega
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem odd_of_two_pow_mod_three189 {f : ℕ} (h : 2 ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hf
  · rw [← two_mul, pow_mul, Nat.pow_mod] at h
    norm_num at h
  · exact hf

theorem even_of_two_pow_mod_three189 {f : ℕ} (h : 2 ^ f % 3 = 1) : Even f := by
  rcases Nat.even_or_odd f with hf | ⟨k, rfl⟩
  · exact hf
  · rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h
    norm_num at h

theorem center_eq_bot_of_isSimpleGroup189 {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hp : commutator Q = ⊤) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hc : commutator Q ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp ha b).symm
    rw [hp, le_bot_iff] at hc
    exact (bot_ne_top : (⊥ : Subgroup Q) ≠ ⊤) hc.symm

variable {G : Type} [Group G] [Finite G]

theorem ker_kToKAlpha189_eq_theta {M H : Subgroup G} {c : G} :
    (kToKAlpha189 M H c).ker = aschbacherSolvableCore 3 ↥(normalClosureIn M c) := by
  set K := normalClosureIn M c with hKdef
  obtain ⟨hθKs, hθKc, hθK3, hθKmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  ext k
  rw [mem_ker_kToKAlpha189]
  constructor
  · intro hk
    set Z := (K ⊓ theta189 M H c).subgroupOf K with hZ
    have hZn : Z.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (le_normalizer_inf_theta189 M H c)
    have hZs : Group.IsSolvable Z := by
      have := isSolvable_theta189 M H c
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion (inf_le_right : K ⊓ theta189 M H c ≤ theta189 M H c)).comp
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ theta189 M H c ≤ K)).toMonoidHom)
        ((Subgroup.inclusion_injective
          (inf_le_right : K ⊓ theta189 M H c ≤ theta189 M H c)).comp (MulEquiv.injective _))
    have hZ3 : ¬ 3 ∣ Nat.card Z := by
      rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : K ⊓ theta189 M H c ≤ K)).toEquiv]
      exact fun h3 => not_three_dvd_card_theta189 M H c
        (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact hθKmax Z hZn hZs hZ3 ⟨k.2, hk⟩
  · intro hk
    set Θ := (aschbacherSolvableCore 3 ↥K).map K.subtype with hΘ
    have hΘK : Θ ≤ K := Subgroup.map_subtype_le _
    have hΘSK : Θ ≤ sk189 M H c := hΘK.trans le_sup_right
    have hN : sk189 M H c ≤ Subgroup.normalizer (Θ : Set G) :=
      (sk189_le_normalizer_k M H c).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
    have hn : (Θ.subgroupOf (sk189 M H c)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hΘSK).mpr hN
    let eΘ : ↥(aschbacherSolvableCore 3 ↥K) ≃* ↥(Θ.subgroupOf (sk189 M H c)) :=
      (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
        (Subgroup.subgroupOfEquivOfLe hΘSK).symm
    have hs : Group.IsSolvable (Θ.subgroupOf (sk189 M H c)) :=
      Group.isSolvable_of_surjective (f := eΘ.toMonoidHom) eΘ.surjective
    have h3 : ¬ 3 ∣ Nat.card (Θ.subgroupOf (sk189 M H c)) := by
      rw [← Nat.card_congr eΘ.toEquiv]
      exact hθK3
    have hle := (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
      Nat.prime_three).2.2.2.1 _ hn hs h3
    have hkΘ : (k : G) ∈ Θ := ⟨k, hk, rfl⟩
    exact ⟨⟨k, hΘSK hkΘ⟩, hle (Subgroup.mem_subgroupOf.mpr hkΘ), rfl⟩

noncomputable def kThetaEquiv189 (M H : Subgroup G) (c : G) :
    ↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c) ≃*
      ↥(kAlpha189 M H c) :=
  (QuotientGroup.quotientMulEquivOfEq ker_kToKAlpha189_eq_theta.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ kToKAlpha189_surjective)

theorem step189InspectI_of_families (hL2e : Inspect189L2Even) (hL3e : Inspect189L3Even)
    (hU3e : Inspect189U3Even) (hL2o : Inspect189L2Odd) (hL3o : Inspect189L3Odd)
    (hU3o : Inspect189U3Odd) (hJ1 : Inspect189J1) : Step189InspectI := by
  intro G _ _ A M H c hset hi _
  have h := hset.toSec18H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := kAlpha189_normal M H c
  set ψ := kThetaEquiv189 M H c with hψ
  have hsimpleθ := ktype_simple hset.mem_thetaComponentsIn hset.pRank_eq
  have hQθ := quasisimple_of_mem_thetaComponentsIn hset.mem_thetaComponentsIn
  have hsimple : IsSimpleGroup ↥(kAlpha189 M H c) := ψ.symm.isSimpleGroup
  have hperfθ : Group.IsPerfect
      (↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c)) := hQθ.1
  have hperf : Group.IsPerfect ↥(kAlpha189 M H c) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hZ : Subgroup.center ↥(kAlpha189 M H c) = ⊥ :=
    center_eq_bot_of_isSimpleGroup189 hperf.commutator_eq_top
  have hC := centralizer_eq_bot_of_sup189 (kAlpha189_sup_sAlpha189 M H c)
    (isPGroup_sAlpha189 M H c) (aschbacherSolvableCore_sKAlpha189 M H c) hZ
  have hcK : c ∈ normalClosureIn M c := Sec20.self_mem_normalClosureIn M c
  have hcSK : c ∈ sk189 M H c := (le_sup_right : normalClosureIn M c ≤ sk189 M H c) hcK
  set cb := alpha189 M H c ⟨c, hcSK⟩ with hcbdef
  have hcbK : cb ∈ kAlpha189 M H c :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcK)
  have hc3 := pow_three_of_sec18H189 h
  have hc1 : c ≠ 1 := ne_one_of_pRank_eq_one189 hset.pRank_eq
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcbdef, ← map_pow]
    have : (⟨c, hcSK⟩ : ↥(sk189 M H c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    rw [hcbdef, alpha189, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c)) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    have hdvd := orderOf_dvd_natCard
      (⟨⟨c, hcSK⟩, h1⟩ : aschbacherSolvableCore 3 ↥(sk189 M H c))
    rw [hord] at hdvd
    exact (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
      Nat.prime_three).2.2.1 hdvd
  have hcbN : cb ∈ Subgroup.normalizer (sAlpha189 M H c : Set (SKAlpha189 M H c)) := by
    have hcS : c ∈ Subgroup.normalizer (s189 M H : Set G) :=
      le_normalizer_s189 h (mem_of_sec18H189 h)
    exact Subgroup.le_normalizer_map _
      (Subgroup.mem_map_of_mem _ (mem_normalizer_subgroupOf189 hcS))
  have hdata : InspectData189 (kAlpha189 M H c) (sAlpha189 M H c) cb :=
    { normal := kAlpha189_normal M H c
      simple := hsimple
      sup_eq := kAlpha189_sup_sAlpha189 M H c
      sylow := hi
      centralizer_eq := hC
      mem := hcbK
      orderOf_eq := orderOf_eq_prime hcb3 hcb1
      mem_normalizer := hcbN }
  suffices hgen : InspectGen189 (kAlpha189 M H c) (sAlpha189 M H c) cb by
    unfold GeneratedModAlpha189
    rw [imAlpha189_zpowers M H c hcSK]
    exact hgen
  rcases hset.rankOne with ⟨p, f, hp, hp3, hf, ⟨e⟩⟩ | ⟨p, f, hp, hf, hq, ⟨e⟩⟩ |
      ⟨p, f, hp, hf, hq, ⟨e⟩⟩ | hJ
  · by_cases hp2 : p = 2
    · subst hp2
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hf1 : f = 1 := by omega
        subst hf1
        exact not_nonempty_equiv_projSL_two_one189 ⟨ψ.symm.trans e⟩
      exact hL2e _ _ _ _ f hdata hf2 ⟨ψ.symm.trans e⟩
    · exact hL2o _ _ _ _ p f hdata hp2 hp3 hf ⟨ψ.symm.trans e⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact hL3e _ _ _ _ f hdata (odd_of_two_pow_mod_three189 hq) ⟨ψ.symm.trans e⟩
    · exact hL3o _ _ _ _ p f hdata hp2 hf hq ⟨ψ.symm.trans e⟩
  · by_cases hp2 : p = 2
    · subst hp2
      have hfe := even_of_two_pow_mod_three189 hq
      have hf2 : 2 ≤ f := by
        obtain ⟨k, rfl⟩ := hfe
        omega
      exact hU3e _ _ _ _ f hdata hfe hf2 ⟨ψ.symm.trans e⟩
    · exact hU3o _ _ _ _ p f hdata hp2 hf hq ⟨ψ.symm.trans e⟩
  · obtain ⟨e⟩ := hJ
    exact hJ1 _ _ _ _ hdata ⟨ψ.symm.trans e⟩

end CFSG.RankThree.PartTwo.Sec18
