module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c6_subsingleton_of_isPerfect_of_isPGroup {H : Type} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p H) (hperf : Group.IsPerfect H) :
    Subsingleton H := by
  by_contra h
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp h
  exact Group.IsPerfect.not_isNilpotent H (IsPGroup.isNilpotent hp)

theorem s16c6_pow_mul_mem {W : Subgroup G} {y : G}
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) {u : G} (huW : u ∈ W) (k : ℕ) :
    ∃ w ∈ W, (u * y) ^ k = w * y ^ k := by
  induction k with
  | zero => exact ⟨1, W.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨w, hwW, hwk⟩ := ih
    refine ⟨u * (y * w * y⁻¹), W.mul_mem huW ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hyW w).mp hwW
    · rw [pow_succ', hwk, pow_succ']
      group

theorem s16c6_commutatorElement_mem_of_pow3 {A B W X : Subgroup G}
    (hBA : B ≤ A) (hWB : W ≤ B)
    (hWA : A ≤ Subgroup.normalizer (W : Set G))
    (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hAx : ⁅A, X⁆ ≤ B) (hBx : ⁅B, X⁆ ≤ W)
    (hB3 : ¬ 3 ∣ Nat.card B)
    {x : G} (hxX : x ∈ X) {m : ℕ} (hm : orderOf x = 3 ^ m) {a : G} (haA : a ∈ A) :
    ⁅x, a⁆ ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set t : G := ⁅a, x⁆ with ht_def
  have htB : t ∈ B := (Subgroup.commutator_le.mp hAx) a haA x hxX
  have htA : t ∈ A := hBA htB
  have htAinv : t⁻¹ ∈ A := A.inv_mem htA
  have htWn : t⁻¹ ∈ Subgroup.normalizer (W : Set G) := hWA htAinv
  have hxtW : ⁅x, t⁆ ∈ W := by
    have h1 : ⁅t, x⁆ ∈ W := (Subgroup.commutator_le.mp hBx) t htB x hxX
    simpa [commutatorElement_inv] using W.inv_mem h1
  have hconj_t : x * t * x⁻¹ = ⁅x, t⁆ * t := by
    simp only [commutatorElement_def]; group
  have hconj_a : x * a * x⁻¹ = t⁻¹ * a := by
    rw [ht_def]; simp only [commutatorElement_def]; group
  have hvW : t⁻¹ * ⁅x, t⁆⁻¹ * t ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp (hWA htAinv) (⁅x, t⁆⁻¹)).mp
      (W.inv_mem hxtW)
    simpa only [inv_inv] using h
  have hv : x * t⁻¹ * x⁻¹ = (t⁻¹ * ⁅x, t⁆⁻¹ * t) * t⁻¹ := by
    rw [show x * t⁻¹ * x⁻¹ = (x * t * x⁻¹)⁻¹ by group, hconj_t]
    group
  have key : ∀ k : ℕ, ∃ w ∈ W, x ^ k * a * (x⁻¹) ^ k = w * (t⁻¹) ^ k * a := by
    intro k
    induction k with
    | zero => exact ⟨1, W.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨w, hwW, hwk⟩ := ih
      have hxw : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hXW hxX) w).mp hwW
      obtain ⟨w', hw'W, hw'⟩ := s16c6_pow_mul_mem (W := W) htWn hvW k
      have hxtk : x * (t⁻¹) ^ k * x⁻¹ = w' * (t⁻¹) ^ k := by
        rw [← conj_pow, hv]
        exact hw'
      refine ⟨(x * w * x⁻¹) * w', W.mul_mem hxw hw'W, ?_⟩
      have hstep : x ^ (k + 1) * a * (x⁻¹) ^ (k + 1) =
          x * (x ^ k * a * (x⁻¹) ^ k) * x⁻¹ := by
        rw [pow_succ', pow_succ]
        group
      rw [hstep, hwk]
      rw [show x * (w * (t⁻¹) ^ k * a) * x⁻¹ =
          (x * w * x⁻¹) * (x * (t⁻¹) ^ k * x⁻¹) * (x * a * x⁻¹) by group]
      rw [hxtk, hconj_a, pow_succ]
      group
  obtain ⟨w, hwW, hw⟩ := key (3 ^ m)
  have hxpow : x ^ (3 ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
  have hinvpow : (x⁻¹) ^ (3 ^ m) = 1 := by rw [inv_pow, hxpow, inv_one]
  rw [hxpow, hinvpow, one_mul, mul_one] at hw
  have ht3W : t ^ (3 ^ m) ∈ W := by
    have h1 : w * (t⁻¹) ^ (3 ^ m) = 1 := by
      have h := congrArg (fun z => z * a⁻¹) hw
      simpa [mul_assoc] using h.symm
    have h2 : (t⁻¹) ^ (3 ^ m) = w⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : t ^ (3 ^ m) = ((t⁻¹) ^ (3 ^ m))⁻¹ := by rw [inv_pow, inv_inv]
    rw [h3, h2, inv_inv]
    exact hwW
  have htW : t ∈ W := by
    let WB : Subgroup ↥B := W.subgroupOf B
    haveI hWBn : WB.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWB).mpr (hBA.trans hWA)
    let πB : ↥B →* ↥B ⧸ WB := QuotientGroup.mk' WB
    have htB' : (⟨t, htB⟩ : ↥B) ^ (3 ^ m) ∈ WB := Subgroup.mem_subgroupOf.mpr ht3W
    have horder : orderOf (πB ⟨t, htB⟩) ∣ 3 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := WB) _).mpr htB'
    have hdvd : orderOf (πB ⟨t, htB⟩) ∣ Nat.card (↥B ⧸ WB) :=
      orderOf_dvd_natCard (πB ⟨t, htB⟩)
    have h3q : ¬ 3 ∣ Nat.card (↥B ⧸ WB) :=
      fun h => hB3 (h.trans (Subgroup.card_quotient_dvd_card WB))
    have hcop : Nat.Coprime (3 ^ m) (Nat.card (↥B ⧸ WB)) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3q).pow_left m
    have hone : orderOf (πB ⟨t, htB⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop horder hdvd
    have h1 : πB ⟨t, htB⟩ = 1 := orderOf_eq_one_iff.mp hone
    have h2 : (⟨t, htB⟩ : ↥B) ∈ WB := (QuotientGroup.eq_one_iff (N := WB) _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  simpa [ht_def, commutatorElement_inv] using W.inv_mem htW

theorem s16c6_opp3_eq_self {X : Subgroup G} (hperf : ⁅X, X⁆ = X)
    (hsimple : IsSimpleGroup (Bar2 X)) (h3 : 3 ∣ Nat.card (Bar2 X)) :
    Opp 3 X = X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
  haveI h2core : IsPGroup 2 ↥(CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  haveI hsimple' : IsSimpleGroup (Bar2 X) := hsimple
  let Y : Subgroup G := Opp 3 X
  have hYX : Y ≤ X := CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 3 X
  have hYXn : X ≤ normalizer (Y : Set G) :=
    CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup 3 X
  haveI hYn : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hYXn
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have h3X : 3 ∣ Nat.card X :=
    h3.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X))
  have hmap_ne : (Y.subgroupOf X).map π ≠ ⊥ := by
    obtain ⟨xx, hxx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3X
    have hxx3 : orderOf (xx : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hxx
    have hxxY : (xx : G) ∈ Y := by
      refine Subgroup.subset_closure ⟨xx.2, 1, ?_⟩
      simpa using hxx3
    have hxne : π xx ≠ 1 := by
      intro h1
      have hxker : xx ∈ π.ker := (MonoidHom.mem_ker).mpr h1
      rw [show π.ker = CFSG.pCore 2 ↥X from QuotientGroup.ker_mk' _] at hxker
      have h3dvd : 3 ∣ Nat.card (CFSG.pCore 2 ↥X) := by
        have h := Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 ↥X) hxker
        rwa [hxx] at h
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
      rw [hk] at h3dvd
      exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3dvd)
    intro hbot
    have hmem : π xx ∈ (Y.subgroupOf X).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxxY)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hxne hmem
  have hmap_top : (Y.subgroupOf X).map π = ⊤ := by
    haveI : ((Y.subgroupOf X).map π).Normal := hYn.map π (QuotientGroup.mk'_surjective _)
    exact (Subgroup.Normal.eq_bot_or_eq_top _).resolve_left hmap_ne
  have htop : (Y.subgroupOf X) ⊔ (CFSG.pCore 2 ↥X) = ⊤ := by
    have h := Subgroup.comap_map_eq π (Y.subgroupOf X)
    rw [hmap_top, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hYtop : Y.subgroupOf X = ⊤ := by
    haveI hsub : Subsingleton (↥X ⧸ Y.subgroupOf X) := by
      haveI : Group.IsPerfect (↥X ⧸ Y.subgroupOf X) :=
        Group.IsPerfect.instQuotientSubgroup
      have h2group : IsPGroup 2 (↥X ⧸ Y.subgroupOf X) := by
        let f : ↥(CFSG.pCore 2 ↥X) →* (↥X ⧸ Y.subgroupOf X) :=
          (QuotientGroup.mk' (Y.subgroupOf X)).comp (CFSG.pCore 2 ↥X).subtype
        have hf : Function.Surjective f := by
          intro z
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf X) z
          have hx : x ∈ (Y.subgroupOf X) ⊔ (CFSG.pCore 2 ↥X) := by
            rw [htop]; exact Subgroup.mem_top x
          obtain ⟨y, hy, o, ho, hxy⟩ := (Subgroup.mem_sup_of_normal_left.mp hx)
          refine ⟨⟨o, ho⟩, ?_⟩
          show QuotientGroup.mk' (Y.subgroupOf X) (o : ↥X) =
            QuotientGroup.mk' (Y.subgroupOf X) x
          have hy1 : (QuotientGroup.mk' (Y.subgroupOf X)) y = 1 :=
            (QuotientGroup.eq_one_iff (N := Y.subgroupOf X) y).mpr hy
          rw [← hxy, map_mul, hy1, one_mul]
        exact h2core.of_surjective f hf
      exact s16c6_subsingleton_of_isPerfect_of_isPGroup h2group inferInstance
    rw [Subgroup.eq_top_iff']
    intro z
    rw [← QuotientGroup.eq_one_iff (N := Y.subgroupOf X) z]
    exact Subsingleton.elim _ _
  have hYXeq : Y = X := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (H := Y) (K := X) hYX, hYtop, Subgroup.map_top,
      Subgroup.range_subtype]
  exact hYXeq

theorem s16c6_le_pCoreOf_of_map_le {X Y : Type} [Group X] [Group Y] {p : ℕ}
    [Fact p.Prime] (f : X →* Y) (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    {B C : Subgroup X} (hCB : C ≤ B)
    (hmap : Subgroup.map f C ≤ CFSG.Open.pCoreOf p (Subgroup.map f B)) :
    C ≤ CFSG.Open.pCoreOf p B := by
  let H : Subgroup Y := CFSG.Open.pCoreOf p (Subgroup.map f B)
  let M : Subgroup X := Subgroup.comap f H
  have hBnorm : B ≤ Subgroup.normalizer (M : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hb' : f b ∈ Subgroup.normalizer (H : Set Y) :=
      (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p (Subgroup.map f B)))
        (Subgroup.mem_map_of_mem f hb)
    exact (Subgroup.mem_normalizer_iff.mp hb' (f x))
  have hNnormal : ((M ⊓ B).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf hBnorm Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hNpg : IsPGroup p ↥(M ⊓ B) :=
    (IsPGroup.comap_of_ker_isPGroup
      ((CFSG.pCore_isPGroup (p := p) (G := ↥(Subgroup.map f B))).map
        (Subgroup.map f B).subtype) f hker).to_le (inf_le_left : M ⊓ B ≤ M)
  have hNle : M ⊓ B ≤ CFSG.Open.pCoreOf p B :=
    CFSG.LieType.BorelTits.le_pCoreOf p inf_le_right hNnormal hNpg
  have hCN : C ≤ M ⊓ B := by
    intro c hc
    exact Subgroup.mem_inf.mpr ⟨by
      rw [Subgroup.mem_comap]
      exact hmap (Subgroup.mem_map_of_mem f hc), hCB hc⟩
  exact hCN.trans hNle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
