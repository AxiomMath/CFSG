module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.L2Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.L2Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.Sz
import CFSG.Adapters.StatedSLPerfect
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSub23.LargeArith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineB23

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23
open scoped commutatorElement

private theorem card_of_isSLn {W : Type} [Group W] {m : ℕ} (h : IsSLn W 3 m) :
    Nat.card W = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
  obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := h
  let _ : Field K := hF
  haveI : Finite K := hFin
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hK]

private theorem isPerfect_and_card_eq_of_surjective {W H : Type} [Group W] [Group H]
    (hWp : Group.IsPerfect W) (hWs : IsSimpleGroup W) (f : W →* H)
    (hf : Function.Surjective f) [Nontrivial H] :
    Group.IsPerfect H ∧ Nat.card H = Nat.card W := by
  haveI : Group.IsPerfect W := hWp
  haveI : IsSimpleGroup W := hWs
  rcases hWs.eq_bot_or_eq_top_of_normal f.ker with hN | hN
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hN
    have hbij : Function.Bijective f := ⟨hinj, hf⟩
    refine ⟨Group.IsPerfect.ofSurjective hf, ?_⟩
    exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm
  · exfalso
    have hf1 : f = 1 := MonoidHom.ker_eq_top_iff.mp hN
    haveI : Subsingleton H := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      rw [hf1]
      rfl⟩
    exact false_of_nontrivial_of_subsingleton H

private theorem statedSL_scalars_card {K : Type} [Field K] [Finite K] :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) =
      Nat.gcd 3 (Nat.card K - 1) := by
  rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 K]
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K :
      Matrix.SpecialLinearGroup (Fin 3) K →* StatedSL 3 K)
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).injective).toEquiv]
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (⟨0, by norm_num⟩ : Fin 3)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd,
    Fintype.card_fin, Nat.gcd_comm]

private theorem sl3_top_false {K : Type} [Field K] {H : Type} [Group H] [Nontrivial H]
    (f : StatedSL 3 K →* H) (hf : Function.Surjective f)
    (Z : Subgroup (StatedSL 3 K)) [Z.Normal]
    (hZcard : Nat.card Z = Nat.gcd 3 (Nat.card K - 1))
    (h : (f.ker).map (QuotientGroup.mk' Z) = ⊤)
    (hHperf : Group.IsPerfect H) : False := by
  have hsurj : Function.Surjective (f.comp Z.subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := hf y
    have hg : QuotientGroup.mk' Z g ∈ (f.ker).map (QuotientGroup.mk' Z) :=
      h ▸ Subgroup.mem_top _
    obtain ⟨x, hxN, hx⟩ := hg
    have hxg : x⁻¹ * g ∈ Z := QuotientGroup.eq.mp hx
    refine ⟨⟨x⁻¹ * g, hxg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
    rw [MonoidHom.mem_ker.mp hxN, inv_one, one_mul]
  have hφcard : Nat.card Z = Nat.card H * Nat.card (f.comp Z.subtype).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (f.comp Z.subtype).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (f.comp Z.subtype) hsurj).toEquiv]
  have hHdvdZ : Nat.card H ∣ Nat.card Z := by
    rw [hφcard]
    exact dvd_mul_right _ _
  have hHdvd3 : Nat.card H ∣ 3 := by
    rw [hZcard] at hHdvdZ
    exact hHdvdZ.trans (Nat.gcd_dvd_left 3 (Nat.card K - 1))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic H := isCyclic_of_card_dvd_prime hHdvd3
  haveI : Group.IsPerfect H := hHperf
  exact Group.IsPerfect.not_isSolvable H inferInstance

private theorem sl3_core {K : Type} [Field K] [Finite K] {H : Type} [Group H]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (f : StatedSL 3 K →* H) (hf : Function.Surjective f) [Nontrivial H] :
    Group.IsPerfect H ∧ ∃ d : ℕ, d ∣ 3 ∧ Nat.card H * d = Nat.card (StatedSL 3 K) ∧
      (d ≠ 1 → 3 ∣ 2 ^ m - 1) := by
  haveI : Finite H := Finite.of_surjective f hf
  let Z : Subgroup (StatedSL 3 K) :=
    (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)
  let N : Subgroup (StatedSL 3 K) := f.ker
  haveI : Group.IsPerfect (StatedSL 3 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (n := 3) (by norm_num) K
  have hHperf : Group.IsPerfect H := Group.IsPerfect.ofSurjective hf
  have hZcard : Nat.card Z = Nat.gcd 3 (Nat.card K - 1) := statedSL_scalars_card
  have hne1 : (3, 2 ^ m) ≠ (2, 2) := by simp
  have hne2 : (3, 2 ^ m) ≠ (2, 3) := by simp
  have hmodel : StatedClassicalModel (StatedProj (StatedSL 3 K)) .PSL 3 2 m :=
    ⟨⟨Nat.prime_two, hm, by norm_num, hne1, hne2⟩, K, inferInstance, inferInstance,
      hK, ⟨MulEquiv.refl _⟩⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSL 3 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  have hNm : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  haveI : IsSimpleGroup (StatedProj (StatedSL 3 K)) := hsimple
  rcases hNm.eq_bot_or_eq_top with h | h
  · have hNZ : N ≤ Z := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    have hNcard_dvd : Nat.card N ∣ 3 := by
      have h1 : Nat.card N ∣ Nat.card Z := Subgroup.card_dvd_of_le hNZ
      have h2 : Nat.card Z ∣ 3 := by
        rw [hZcard]
        exact Nat.gcd_dvd_left 3 (Nat.card K - 1)
      exact h1.trans h2
    have hcard : Nat.card (StatedSL 3 K) = Nat.card H * Nat.card N := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    refine ⟨hHperf, Nat.card N, hNcard_dvd, hcard.symm, ?_⟩
    intro hNne1
    have hN3 : Nat.card N = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hNcard_dvd with h1 | h3
      · exact absurd h1 hNne1
      · exact h3
    have hZle : Nat.card Z ≤ 3 := by
      rw [hZcard]
      exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (Nat.card K - 1))
    have hZge : 3 ≤ Nat.card Z := by
      calc 3 = Nat.card N := hN3.symm
        _ ≤ Nat.card Z := Subgroup.card_le_of_le hNZ
    have hZ3 : Nat.card Z = 3 := by omega
    rw [hZcard] at hZ3
    have h3K : 3 ∣ Nat.card K - 1 := (Nat.gcd_eq_left_iff_dvd).mp hZ3
    rwa [hK] at h3K
  · exfalso
    exact sl3_top_false f hf Z hZcard h hHperf

private theorem isPerfect_statedProj_statedSp {K : Type} [Field K] [Finite K] {m : ℕ}
    (hAdm : StatedLieAdmissible .PSp 2 2 m) (hK : Nat.card K = 2 ^ m) :
    Group.IsPerfect (StatedProj (StatedSp 2 K)) := by
  have hm1 : 1 ≤ m := hAdm.2.1
  have hne : (2, 2 ^ m) ≠ (2, 2) := hAdm.2.2.2
  have hmne1 : m ≠ 1 := by
    intro hm1
    exact hne (by rw [hm1]; norm_num)
  have hm2 : 2 ≤ m := by omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hfin4 : ∃ s : Finset K, s.card = 4 := by
    let _ : Fintype K := Fintype.ofFinite K
    have h4' : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact h4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) h4'
    exact ⟨t, ht⟩
  exact CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect
    (n := 2) (K := K) (Or.inl hfin4)

private theorem isPerfect_statedProj_statedSU {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = (2 ^ m) ^ 2) :
    Group.IsPerfect (StatedProj (StatedSU 4 (2 ^ m) K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := m) hK
  haveI : Group.IsPerfect (StatedSU 4 (2 ^ m) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) (p := 2) (f := m) (n := 4)
      (hK := hK) (hn := by norm_num) (hnq := by simp)
  exact Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk'
      ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ m) K)))
    (QuotientGroup.mk'_surjective _)

theorem card_mul_eq_of_surjective_large {W H : Type} [Group W] [Finite W] [Group H] {m : ℕ}
    (hm : 1 ≤ m) (hW : IsSLn W 3 m ∨ IsSp4 W m ∨ IsU4 W m) (f : W →* H)
    (hf : Function.Surjective f) [Nontrivial H] :
    Group.IsPerfect H ∧ ∃ d : ℕ, d ∣ 3 ∧ Nat.card H * d = Nat.card W ∧
      (d ≠ 1 → IsSLn W 3 m ∧ 3 ∣ 2 ^ m - 1) := by
  haveI : Finite H := Finite.of_surjective f hf
  rcases hW with hSL | hSp | hU4
  · have hSLkeep : IsSLn W 3 m := hSL
    obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ := hSL
    let _ : Field K := hF
    haveI : Finite K := hFin
    let f' : StatedSL 3 K →* H := f.comp e.symm.toMonoidHom
    have hf' : Function.Surjective f' := hf.comp e.symm.surjective
    obtain ⟨hperf, d, hdvd, hmul, hdimp⟩ := sl3_core hm hK f' hf'
    refine ⟨hperf, d, hdvd, ?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv]
      exact hmul
    · intro hd
      exact ⟨hSLkeep, hdimp hd⟩
  · obtain ⟨hAdm, K, hF, hFin, hK, ⟨e⟩⟩ := hSp.statedClassicalModel (by decide)
    let _ : Field K := hF
    haveI : Finite K := hFin
    haveI : Group.IsPerfect (StatedProj (StatedSp 2 K)) :=
      isPerfect_statedProj_statedSp hAdm hK
    have hWp : Group.IsPerfect W :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hWs : IsSimpleGroup W :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
    obtain ⟨hHperf, hcard⟩ := isPerfect_and_card_eq_of_surjective hWp hWs f hf
    refine ⟨hHperf, 1, by norm_num, ?_, ?_⟩
    · rw [mul_one]
      exact hcard
    · intro hd
      exact absurd rfl hd
  · obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hU4.statedClassicalModel (by decide)
    let _ : Field K := hF
    haveI : Finite K := hFin
    haveI : Group.IsPerfect (StatedProj (StatedSU 4 (2 ^ m) K)) :=
      isPerfect_statedProj_statedSU hK
    have hWp : Group.IsPerfect W :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hWs : IsSimpleGroup W :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
    obtain ⟨hHperf, hcard⟩ := isPerfect_and_card_eq_of_surjective hWp hWs f hf
    refine ⟨hHperf, 1, by norm_num, ?_, ?_⟩
    · rw [mul_one]
      exact hcard
    · intro hd
      exact absurd rfl hd

private theorem a5_false {W : Type} [Group W] [Finite W] {m d : ℕ} (hm3 : 3 ≤ m)
    (hord : targetOrder (2 ^ m) (Nat.card W)) (hd13 : d = 1 ∨ d = 3)
    (hmul : 60 * d = Nat.card W) : False := by
  have h9 : 2 ^ 9 ∣ Nat.card W := two_pow_nine_dvd_of_targetOrder hm3 hord
  have hge : 512 ≤ Nat.card W := Nat.le_of_dvd Nat.card_pos h9
  rcases hd13 with h1 | h3
  · rw [h1, mul_one] at hmul; omega
  · rw [h3] at hmul; omega

private theorem not_l2_image {S W : Type} [Group S] [Finite S]
    [Group W] [Finite W] {a m d : ℕ} (hm3 : 3 ≤ m) (hord : targetOrder (2 ^ m) (Nat.card W))
    (hL2 : IsL2 S a) (Y : Subgroup S) (hY : Group.IsPerfect ↥Y) (hne : Y ≠ ⊥)
    (hd13 : d = 1 ∨ d = 3) (hmul : Nat.card ↥Y * d = Nat.card W)
    (hSLcard : d ≠ 1 → Nat.card W =
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) : False := by
  haveI : Group.IsPerfect ↥Y := hY
  have hYY : ⁅Y, Y⁆ = Y := Subgroup.commutator_eq_self
  rcases isAlt_or_isL2_of_isL2 hL2 Y hYY hne with hAlt | ⟨b, -, hL2Y⟩
  · obtain ⟨e⟩ := hAlt
    have h60 : Nat.card ↥Y = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact a5_false hm3 hord hd13 (by rw [← h60]; exact hmul)
  · obtain ⟨hb, hbc⟩ := card_isL2 hL2Y
    rcases hd13 with h1 | h3
    · rw [h1, mul_one] at hmul
      exact knl_ne_l2_order (n := m) (a := b) (by omega) hb hord
        (by rw [← hmul]; exact hbc)
    · rw [h3] at hmul
      have heq : (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) =
          3 * (2 ^ b * ((2 ^ b) ^ 2 - 1)) := by
        rw [← hSLcard (by rw [h3]; norm_num), ← hmul, hbc]
        ring
      exact ne_l2_order_mul_three (by omega) hb heq

private theorem not_sz_image {S W : Type} [Group S] [Finite S]
    [Group W] [Finite W] {a m d : ℕ} (hord : targetOrder (2 ^ m) (Nat.card W)) (hSz : IsSz S a)
    (Y : Subgroup S) (hd13 : d = 1 ∨ d = 3) (hmul : Nat.card ↥Y * d = Nat.card W)
    (h3x : d ≠ 1 → 3 ∣ 2 ^ m - 1) : False := by
  have h3Y : 3 ∣ Nat.card ↥Y := by
    rcases hd13 with h1 | h3
    · rw [h1, mul_one] at hmul
      rw [hmul]
      exact knl_three_dvd_order hord
    · rw [h3] at hmul
      have h9 : 9 ∣ Nat.card W :=
        nine_dvd_of_targetOrder_of_three_dvd_sub_one hord (h3x (by rw [h3]; norm_num))
      rw [← hmul] at h9
      rcases h9 with ⟨k, hk⟩
      exact ⟨k, by omega⟩
  exact not_three_dvd_card_of_isSz hSz (h3Y.trans (Subgroup.card_subgroup_dvd_card Y))

private theorem not_l2odd_image {S W : Type} [Group S] [Finite S]
    [Group W] [Finite W] {p m d : ℕ} (hm3 : 3 ≤ m) (hq : p.Prime) (hq2 : p ≠ 2)
    (hord : targetOrder (2 ^ m) (Nat.card W)) (hS : IsL2Odd S p)
    (Y : Subgroup S) (hY : Group.IsPerfect ↥Y) (hne : Y ≠ ⊥)
    (hd13 : d = 1 ∨ d = 3) (hmul : Nat.card ↥Y * d = Nat.card W)
    (hSLcard : d ≠ 1 → Nat.card W =
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)))
    (h3x : d ≠ 1 → 3 ∣ 2 ^ m - 1) : False := by
  haveI : Group.IsPerfect ↥Y := hY
  have hYY : ⁅Y, Y⁆ = Y := Subgroup.commutator_eq_self
  rcases eq_top_or_isAlt_of_isL2Odd hq hq2 hS Y hYY hne with hTop | hAlt
  · have hYS : Nat.card ↥Y = Nat.card S := by rw [hTop]; simp
    have hSc := card_isL2Odd hq hq2 hS
    rcases hd13 with h1 | h3
    · rw [h1, mul_one] at hmul
      exact knl_ne_l2odd_order hm3 hq hq2 hord (by rw [← hmul, hYS]; exact hSc)
    · rw [h3] at hmul
      have heq : (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) * 2 =
          3 * (p * (p ^ 2 - 1)) := by
        rw [← hSLcard (by rw [h3]; norm_num), ← hmul, hYS]
        calc (Nat.card S * 3) * 2 = 3 * (Nat.card S * 2) := by ring
          _ = 3 * (p * (p ^ 2 - 1)) := by rw [hSc]
      exact ne_l2odd_order_mul_three hm3 hq hq2 (h3x (by rw [h3]; norm_num)) heq
  · obtain ⟨e⟩ := hAlt
    have h60 : Nat.card ↥Y = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact a5_false hm3 hord hd13 (by rw [← h60]; exact hmul)

private theorem not_j1_image {S W : Type} [Group S] [Finite S] [Group W] [Finite W]
    {m d : ℕ}
    (hm3 : 3 ≤ m) (hord : targetOrder (2 ^ m) (Nat.card W)) (hJ : IsJ1 S)
    (Y : Subgroup S) (hd13 : d = 1 ∨ d = 3)
    (hmul : Nat.card ↥Y * d = Nat.card W) : False := by
  have h9 : 2 ^ 9 ∣ Nat.card W := two_pow_nine_dvd_of_targetOrder hm3 hord
  have hodd : Odd d := by
    rcases hd13 with h | h <;> (rw [h]; norm_num)
  have hcop : Nat.Coprime (2 ^ 9) d :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  rw [← hmul] at h9
  have h9Y : 2 ^ 9 ∣ Nat.card ↥Y := hcop.dvd_of_dvd_mul_right h9
  have hdvd : Nat.card ↥Y ∣ 175560 := by
    rw [← card_isJ1 hJ]
    exact Subgroup.card_subgroup_dvd_card Y
  have hbad : 2 ^ 9 ∣ 175560 := h9Y.trans hdvd
  norm_num at hbad

theorem kSub23_two :
    ∀ (W S : Type) [Group W] [Finite W] [Group S] [Finite S] (m : ℕ),
      3 ≤ m → (IsSLn W 3 m ∨ IsSp4 W m ∨ IsU4 W m) → B23Shape S →
      ∀ Y : Subgroup S, (∃ f : W →* ↥Y, Function.Surjective f) → Y = ⊥ := by
  intro W S _ _ _ _ m hm3 hW hB Y hf
  obtain ⟨f, hf⟩ := hf
  by_contra hne
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hne
  obtain ⟨hY, d, hdvd, hmul, hdimp⟩ :=
    card_mul_eq_of_surjective_large (m := m) (by omega) hW f hf
  have hd13 : d = 1 ∨ d = 3 := (Nat.dvd_prime Nat.prime_three).mp hdvd
  have hord : targetOrder (2 ^ m) (Nat.card W) := card_target (by omega) hW
  have hSLcard : d ≠ 1 → Nat.card W =
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    fun hd => card_of_isSLn (hdimp hd).1
  have h3x : d ≠ 1 → 3 ∣ 2 ^ m - 1 := fun hd => (hdimp hd).2
  have hB' : (∃ a : ℕ, IsL2 S a ∨ IsSz S a) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd S q) ∨ IsJ1 S := hB
  rcases hB' with ⟨a, hL2 | hSz⟩ | ⟨q, hq, hq2, hL2o⟩ | hJ1
  · exact not_l2_image hm3 hord hL2 Y hY hne hd13 hmul hSLcard
  · exact not_sz_image hord hSz Y hd13 hmul h3x
  · exact not_l2odd_image hm3 hq hq2 hord hL2o Y hY hne hd13 hmul hSLcard h3x
  · exact not_j1_image hm3 hord hJ1 Y hd13 hmul

end CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

end
