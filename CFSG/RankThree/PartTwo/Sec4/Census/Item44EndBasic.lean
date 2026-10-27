module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem le_oddCore {N : Subgroup X} (hN : N.Normal) (hodd : Odd (Nat.card N)) : N ≤ oddCore X :=
  le_sSup ⟨hN, hodd⟩

theorem pCore_eq_bot_of_oddCore {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hO : oddCore X = ⊥) :
    pCore q X = ⊥ := by
  have : (pCore q X).Normal := pCore_normal
  refine le_bot_iff.mp (hO ▸ le_oddCore this ?_)
  obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup q (pCore q X)).exists_card_eq
  rw [hk]
  exact Odd.pow ((Fact.out : q.Prime).odd_of_ne_two hq2)

theorem fittingSubgroup_le_pCore_two (hO : oddCore X = ⊥) : fittingSubgroup X ≤ pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have : Fact (q : ℕ).Prime := ⟨hq⟩
  by_cases hq2 : (q : ℕ) = 2
  · rw [hq2]
  · rw [pCore_eq_bot_of_oddCore hq2 hO]
    exact bot_le

variable [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem centralizer_pCore_two_le (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) : Subgroup.centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq', hC⟩ := exists_centralizer_pCore_le hK hq
  have : Fact q.Prime := ⟨hq'⟩
  have hq2 : q = 2 := by
    by_contra hq2
    rw [pCore_eq_bot_of_oddCore hq2 hO] at hC
    have htop : (⊤ : Subgroup X) ≤ K := by
      intro g _
      apply hC
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
      rw [hx, one_mul, mul_one]
    exact (QuotientGroup.nontrivial_iff.mp inferInstance) (top_le_iff.mp htop)
  subst hq2
  set C := Subgroup.centralizer (pCore 2 X : Set X) with hCdef
  have : (pCore 2 X).Normal := pCore_normal
  have hCsol : Group.IsSolvable C := by
    have := hK
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hC)
  have hFC : (fittingSubgroup C).map C.subtype ≤ pCore 2 X :=
    (le_sSup ⟨inferInstance, Group.nilpotent_of_surjective (C.subtype.subgroupMap
      (fittingSubgroup C)) (C.subtype.subgroupMap_surjective _)⟩ :
        _ ≤ fittingSubgroup X).trans (fittingSubgroup_le_pCore_two hO)
  have hCC := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCsol
  intro c hc
  have hmem : (⟨c, hc⟩ : C) ∈ Subgroup.centralizer (fittingSubgroup C : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (f : X) (hFC ⟨f, hf, rfl⟩)
  exact hFC ⟨⟨c, hc⟩, hCC hmem, rfl⟩

theorem centralizer_le_of_isThompsonCritical (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) {T : Subgroup (pCore 2 X)}
    (hT : CFSG.SectionRank.Ccomm.IsThompsonCritical T) :
    Subgroup.centralizer ((T.map (pCore 2 X).subtype : Subgroup X) : Set X) ≤ pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 X).Normal := pCore_normal
  have hTchar : T.Characteristic := hT.1
  have : T.Normal := inferInstance
  have hCS := centralizer_pCore_two_le hK hO hq
  set C := Subgroup.centralizer ((T.map (pCore 2 X).subtype : Subgroup X) : Set X) with hCdef
  have hTn : (T.map (pCore 2 X).subtype).Normal := inferInstance
  have hCn : C.Normal := inferInstance
  have hodd : ∀ c ∈ C, ∀ r : ℕ, r.Prime → r ≠ 2 → orderOf c = r → c = 1 := by
    intro c hc r hr hr2 hcr
    have : Fact r.Prime := ⟨hr⟩
    let act : MulDistribMulAction (Subgroup.zpowers c) (pCore 2 X) :=
      MulDistribMulAction.compHom (pCore 2 X) ((MulAut.conjNormal : X →* MulAut (pCore 2 X)).comp
        (Subgroup.zpowers c).subtype)
    have hsmul : ∀ (a : Subgroup.zpowers c) (s : pCore 2 X), ((a • s : pCore 2 X) : X) = a * s * (a : X)⁻¹ :=
      fun a s => rfl
    have hpg : IsPGroup r (Subgroup.zpowers c) := by
      rintro ⟨_, n, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hcr,
        pow_orderOf_eq_one, one_zpow]
    have hfix : ∀ (a : Subgroup.zpowers c), ∀ t ∈ T, a • t = t := by
      rintro ⟨_, n, rfl⟩ t ht
      apply Subtype.ext
      rw [hsmul]
      have hct : c * (t : X) = t * c :=
        (Subgroup.mem_centralizer_iff.mp hc (t : X) ⟨t, ht, rfl⟩).symm
      have : Commute (c ^ n) (t : X) := (Commute.zpow_left hct n)
      simp only
      rw [this.eq, mul_inv_cancel_right]
    have hcrit : Subgroup.centralizer (T : Set (pCore 2 X)) ≤ T := by
      rw [hT.2.2.2]
      exact inf_le_left
    have htriv := CFSG.PreuniquenessRankFour.Helpers.coprime_pGroup_action_trivial_of_fixed_critical_subgroup
      r 2 hr2 hpg (pCore_isPGroup : IsPGroup 2 (pCore 2 X)) T hcrit hfix
    have hcS : c ∈ pCore 2 X := by
      apply hCS
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := congrArg Subtype.val (htriv ⟨c, Subgroup.mem_zpowers c⟩ ⟨s, hs⟩)
      rw [hsmul] at this
      calc s * c = c * s * c⁻¹ * c := by rw [this]
        _ = c * s := by group
    obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 X)) ⟨c, hcS⟩
    have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : r ∣ 2 ^ k := hcr ▸ orderOf_dvd_of_pow_eq_one hk'
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1)) hr2
  have hC2 : IsPGroup 2 C := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos).ne' fun {r} hr hrC => ?_⟩
    by_contra hr2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) r hrC
    have hc1 := hodd c c.2 r hr hr2 (by rw [Subgroup.orderOf_coe]; exact hc)
    have : orderOf (c : X) = 1 := by rw [hc1, orderOf_one]
    rw [Subgroup.orderOf_coe, hc] at this
    exact hr.one_lt.ne' this
  exact le_sSup ⟨hCn, hC2⟩

end CFSG.RankThree.PartTwo.Sec4.Census
