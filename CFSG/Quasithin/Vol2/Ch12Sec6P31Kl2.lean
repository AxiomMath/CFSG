module

public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover

private theorem kl2_card_pow16_multiplicative :
    Nat.card {g : Multiplicative (ZMod 3 × ZMod 4 × ZMod 4) // g ^ 16 = 1} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem kl2_card_pow16_of_mulEquiv {M : Type} [Group M]
    (e : M ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) :
    Nat.card {m : M // m ^ 16 = 1} = 16 :=
  (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun m => by simp [← map_pow])).trans
    kl2_card_pow16_multiplicative

private theorem kl2_coe_eq_setOf_pow16 {M : Type} [Group M] [Finite M]
    (e : M ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) (A : Subgroup M)
    (hA : Nat.card A = 16) : (A : Set M) = {m : M | m ^ 16 = 1} := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · intro m hm
    have h := A.orderOf_dvd_natCard hm
    rw [hA] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  · have h1 : ({m : M | m ^ 16 = 1}).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact kl2_card_pow16_of_mulEquiv e
    have h2 : (A : Set M).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact hA
    omega

private theorem kl2_card_hopfMultiplier {P : Type} [Group P]
    (e : hopfMultiplier P ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) :
    Nat.card (hopfMultiplier P) = 48 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  simp [Fintype.card_prod, ZMod.card]

private theorem kl2_card_hopfMultiplier_eq_mul {P : Type} [Group P] {E : Type} [Group E]
    [Group.IsPerfect E] (q : E →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) :
    Nat.card (hopfMultiplier P) =
      Nat.card ((hopfLift q hq hker).comp (hopfMultiplier P).subtype).ker * Nat.card q.ker := by
  have hrange : ((hopfLift q hq hker).comp (hopfMultiplier P).subtype).range = q.ker := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_hopfMultiplier_hopfLift q hq hker]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hopfLift q hq hker).comp (hopfMultiplier P).subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    ((hopfLift q hq hker).comp (hopfMultiplier P).subtype)).toEquiv, hrange] at h1
  exact h1.trans (mul_comm _ _)

private theorem kl2_coe_ker_comp_eq_setOf_pow16 {P : Type} [Group P] {E : Type} [Group E]
    [Group.IsPerfect E] (q : E →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E)
    (e : hopfMultiplier P ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4))
    (hq3 : Nat.card q.ker = 3) :
    (((hopfLift q hq hker).comp (hopfMultiplier P).subtype).ker : Set (hopfMultiplier P)) =
      {m : hopfMultiplier P | m ^ 16 = 1} := by
  have hM := kl2_card_hopfMultiplier e
  have hfin : Finite (hopfMultiplier P) := Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  have h := kl2_card_hopfMultiplier_eq_mul q hq hker
  rw [hM, hq3] at h
  have h16 : Nat.card ((hopfLift q hq hker).comp (hopfMultiplier P).subtype).ker = 16 := by
    omega
  exact kl2_coe_eq_setOf_pow16 e _ h16

private theorem kl2_ker_hopfLift_eq_map {P : Type} [Group P] {E : Type} [Group E]
    [Group.IsPerfect E] (q : E →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) :
    (hopfLift q hq hker).ker =
      ((hopfLift q hq hker).comp (hopfMultiplier P).subtype).ker.map
        (hopfMultiplier P).subtype := by
  ext x
  constructor
  · intro hx
    have hxM : x ∈ hopfMultiplier P := by
      have h1 : hopfCoverMap P x = q (hopfLift q hq hker x) := by
        rw [← MonoidHom.comp_apply, comp_hopfLift]
      have h2 : hopfLift q hq hker x = 1 := hx
      show hopfCoverMap P x = 1
      rw [h1, h2, map_one]
    exact ⟨⟨x, hxM⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy)

private theorem kl2_ker_hopfLift_eq {P : Type} [Group P] {E F : Type} [Group E] [Group F]
    [Group.IsPerfect E] [Group.IsPerfect F] (q : E →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) (p : F →* P) (hp : Function.Surjective p)
    (hpker : p.ker ≤ Subgroup.center F)
    (e : hopfMultiplier P ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4))
    (hq3 : Nat.card q.ker = 3) (hp3 : Nat.card p.ker = 3) :
    (hopfLift q hq hker).ker = (hopfLift p hp hpker).ker := by
  have hset := (kl2_coe_ker_comp_eq_setOf_pow16 q hq hker e hq3).trans
    (kl2_coe_ker_comp_eq_setOf_pow16 p hp hpker e hp3).symm
  rw [kl2_ker_hopfLift_eq_map q hq hker, kl2_ker_hopfLift_eq_map p hp hpker,
    SetLike.coe_injective hset]

private theorem kl2_card_center_dvd_of_hom {P : Type} [Group P] {X : Type} [Group X] [Finite X]
    (hX : Group.IsPerfect X)
    (hodd : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (e : hopfMultiplier P ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4))
    (q : X →* P) (hq : Function.Surjective q) (hker : q.ker = Subgroup.center X) :
    Nat.card (Subgroup.center X) ∣ 3 := by
  have hdvd : Nat.card q.ker ∣ 48 := by
    have h := kl2_card_hopfMultiplier_eq_mul q hq hker.le
    rw [kl2_card_hopfMultiplier e] at h
    exact Dvd.intro_left _ h.symm
  rw [hker] at hdvd
  have hodd2 : ¬ 2 ∣ Nat.card (Subgroup.center X) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 2 h2
    have hz2 : z ^ 2 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    have hzX : (z : X) ^ 2 = 1 := by
      have := congrArg Subtype.val hz2
      simpa using this
    have hz1 : (z : X) = 1 := hodd (z : X) z.2 1 (by rw [pow_one]; exact hzX)
    have hz' : z = 1 := Subtype.ext hz1
    rw [hz', orderOf_one] at hz
    norm_num at hz
  have hle : Nat.card (Subgroup.center X) ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card (Subgroup.center X) = n at hle hdvd hodd2 ⊢
  interval_cases n <;> omega

private abbrev kl2_statedSLquot (K : Type) [Field K] :
    ↥(StatedSL 3 K) →* StatedProj (StatedSL 3 K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))

private theorem kl2_statedSLquot_surjective (K : Type) [Field K] :
    Function.Surjective (kl2_statedSLquot K) :=
  QuotientGroup.mk'_surjective _

private theorem kl2_isPerfect_statedSL_three (K : Type) [Field K] :
    Group.IsPerfect ↥(StatedSL 3 K) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3) le_rfl
  exact Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
    (specialLinearGroupEquivStatedSL 3 K).surjective

private theorem kl2_ker_statedSLquot_le_center (K : Type) [Field K] :
    (kl2_statedSLquot K).ker ≤ Subgroup.center ↥(StatedSL 3 K) := by
  intro x hx
  rw [kl2_statedSLquot, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hx (g : GL (Fin 3) K))

private theorem kl2_card_ker_statedSLquot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (kl2_statedSLquot K).ker = 3 := by
  have hS : Nat.card ↥(StatedSL 3 K) = 60480 := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3), hK]
    decide
  have hP : Nat.card (StatedProj (StatedSL 3 K)) = 20160 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hK]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (kl2_statedSLquot K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (kl2_statedSLquot K)
    (kl2_statedSLquot_surjective K)).toEquiv, hS, hP] at h
  omega

private theorem kl2_nonempty_mulEquiv_statedSL_three {X : Type} [Group X] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 4) (hX : Group.IsPerfect X)
    (e : hopfMultiplier (StatedProj (StatedSL 3 K)) ≃*
      Multiplicative (ZMod 3 × ZMod 4 × ZMod 4))
    (q : X →* StatedProj (StatedSL 3 K)) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.center X) (h3 : Nat.card (Subgroup.center X) = 3) :
    Nonempty (X ≃* ↥(StatedSL 3 K)) := by
  haveI := hX
  haveI := kl2_isPerfect_statedSL_three K
  have hq3 : Nat.card q.ker = 3 := by rw [hker, h3]
  have hkey := kl2_ker_hopfLift_eq q hq hker.le (kl2_statedSLquot K)
    (kl2_statedSLquot_surjective K) (kl2_ker_statedSLquot_le_center K) e hq3
    (kl2_card_ker_statedSLquot hK)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective (hopfLift q hq hker.le)
    (hopfLift_surjective q hq hker.le)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkey).trans
      (QuotientGroup.quotientKerEquivOfSurjective (hopfLift (kl2_statedSLquot K)
          (kl2_statedSLquot_surjective K) (kl2_ker_statedSLquot_le_center K))
        (hopfLift_surjective (kl2_statedSLquot K) (kl2_statedSLquot_surjective K)
          (kl2_ker_statedSLquot_le_center K))))⟩

private theorem kl2_nonempty_hopfMultiplier_equiv {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .PSL 3 2 2) (hK : Nat.card K = 2 ^ 2) :
    Nonempty (hopfMultiplier (StatedProj (StatedSL 3 K)) ≃*
      Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) := by
  have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSL 3 K)) .PSL 3 2 2 :=
    Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, ⟨g⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four _ hLie
  exact ⟨(hopfMultiplierEquivGriess _).symm.trans g⟩

theorem card_center_dvd_three_of_quotient
    {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hodd : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (h : IsPSL 3 2 2 (X ⧸ Subgroup.center X)) : Nat.card (Subgroup.center X) ∣ 3 := by
  obtain ⟨K, hK, hKfin, hK4, ⟨ψ⟩⟩ := h.2
  obtain ⟨e⟩ := kl2_nonempty_hopfMultiplier_equiv h.1 hK4
  obtain ⟨q, hqdef⟩ : ∃ q : X →* StatedProj (StatedSL 3 K),
      q = ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) := ⟨_, rfl⟩
  have hq : Function.Surjective q := by
    rw [hqdef]
    exact ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center X := by
    rw [hqdef, MonoidHom.ker_comp_of_injective _ ψ.toMonoidHom ψ.injective,
      QuotientGroup.ker_mk']
  exact kl2_card_center_dvd_of_hom (Group.isPerfect_def.mpr hperf) hodd e q hq hker

theorem exists_mulEquiv_psl_or_sl_of_quotient
    {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hodd : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (h : IsPSL 3 2 2 (X ⧸ Subgroup.center X)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      (Nonempty (X ≃* StatedProj (StatedSL 3 F)) ∨ Nonempty (X ≃* ↥(StatedSL 3 F))) := by
  have hdvd := card_center_dvd_three_of_quotient hperf hodd h
  obtain ⟨K, hK, hKfin, hK4, ⟨ψ⟩⟩ := h.2
  have hK4' : Nat.card K = 4 := by rw [hK4]; norm_num
  refine ⟨K, hK, hKfin, hK4', ?_⟩
  obtain ⟨e⟩ := kl2_nonempty_hopfMultiplier_equiv h.1 hK4
  obtain ⟨q, hqdef⟩ : ∃ q : X →* StatedProj (StatedSL 3 K),
      q = ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) := ⟨_, rfl⟩
  have hq : Function.Surjective q := by
    rw [hqdef]
    exact ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center X := by
    rw [hqdef, MonoidHom.ker_comp_of_injective _ ψ.toMonoidHom ψ.injective,
      QuotientGroup.ker_mk']
  have hX : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · left
    have hinj : Function.Injective q := by
      rw [← MonoidHom.ker_eq_bot_iff, hker]
      exact Subgroup.card_eq_one.mp h1
    exact ⟨MulEquiv.ofBijective q ⟨hinj, hq⟩⟩
  · right
    exact kl2_nonempty_mulEquiv_statedSL_three hK4' hX e q hq hker h3

end CFSG.Quasithin.H13.S126P31
