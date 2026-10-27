module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcG2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcE2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcG2Sing
public import CFSG.Quasithin.EmptyFaithful.R3c18Q

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem two_le_factorization_sq_pow {p q₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q₀)
    (hpq : ¬ p ∣ q₀) (h : p ∣ (q₀ ^ p) ^ 2 - 1) : 2 ≤ ((q₀ ^ p) ^ 2 - 1).factorization p := by
  have h1 := CFSG.RankThree.PartOne.K128.dvd_sq_sub_one_of_dvd_pow hp hp2 hq hpq h
  rw [CFSG.RankThree.PartOne.K128.factorization_sq_pow hp hp2 hq hpq, if_pos h1]
  have h2 : 1 ≤ (q₀ ^ 2 - 1).factorization p := by
    have hne : q₀ ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ q₀ ^ 2 := by nlinarith
      omega
    exact (hp.dvd_iff_one_le_factorization hne).mp h1
  omega


theorem false_of_kF135Hyp_G2_E2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) {hv : (TauCeti.LieTypeIndex.G2 q).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (h : KF135Hyp S p P x u V)
    (hn : p ∣ q.exponent) (hplus : p ∣ q.card + 1) : False := by
  classical
  have hp := h.prime
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hp5 : 5 ≤ p := by omega
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hq1 : 1 ≤ q.card := by
    rw [hcard]
    exact Nat.one_le_two_pow
  obtain ⟨m, hm⟩ := hn
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := q.exponent_pos
      rw [hm, h0, mul_zero] at this
      omega
    · exact h0
  have hn2 : 2 ≤ q.exponent := by
    rw [hm]
    nlinarith
  obtain ⟨K, _, _, hK, hKc, ⟨e₁⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have : CharP K 2 := hq2 ▸ hKc
  have hK2 : Nat.card K = 2 ^ q.exponent := hK.trans hcard
  have f : S ≃* ↥(adjointGroup .G2 K) := e.trans e₁
  have hKq₀ : Nat.card K = (2 ^ m) ^ p := by rw [hK2, hm, ← pow_mul, mul_comm]
  have hq₀2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hpq₀ : ¬ p ∣ 2 ^ m := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hd : p ∣ Nat.card K ^ 2 - 1 := by
    rw [hK, sq_sub_one_eq_mul hq1]
    exact hplus.mul_left _
  have hshS := CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv f
    (CFSG.RankThree.PartOne.K128.sylowShape_G2 K hp hp5 hK2 (by omega) hd)
  have he2 : 2 ≤ (Nat.card K ^ 2 - 1).factorization p := by
    rw [hKq₀] at hd ⊢
    exact two_le_factorization_sq_pow hp hp2 hq₀2 hpq₀ hd
  have hout : CFSG.RankThree.PartOne.OutStructure.OutPChain p S :=
    (CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e
      (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outPNice_cat_G2 q hv hp)).toChain
  refine false_of_E2 h hout hshS he2 f fun φ₀ hφ₀ => ?_
  obtain ⟨ψ, σ, hσ, hψφ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.stdDescent_G2_even hn2 hK2 hp
      φ₀ hφ₀
  obtain ⟨-, hkcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega) hK2 σ
  rw [hσ, hm, Nat.mul_div_cancel_left _ hp.pos] at hkcard
  set k := fixSubfield σ with hk
  have hpk : p ∣ Nat.card k + 1 := by
    rw [hkcard]
    apply CFSG.Quasithin.R3c18.dvd_add_one_of_dvd_pow_add_one hp
    rw [← hKq₀, hK]
    exact hplus
  have hJ := CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage σ
  have hJle : ∀ y ∈ adjointGroup .G2 k,
      baseChangeGL (τ := .G2) k.subtype y ∈ adjointGroup .G2 K := fun y hy => by
    have h1 : baseChangeGL (τ := .G2) k.subtype y ∈ fixedFieldImage .G2 σ :=
      Subgroup.mem_map_of_mem _ hy
    rw [← hJ] at h1
    exact (mem_entrywiseFixedGroup.mp h1).1
  let β : ↥(adjointGroup .G2 k) →* ↥(adjointGroup .G2 K) :=
    ((baseChangeGL (τ := .G2) k.subtype).comp (adjointGroup .G2 k).subtype).codRestrict _
      (fun y => hJle y y.2)
  refine ⟨ψ, _, hψφ, ↥(adjointGroup .G2 k), inferInstance, β, fun y z hyz =>
    Subtype.ext (baseChangeGL_injective (τ := .G2) k.subtype (congrArg Subtype.val hyz)),
    fun t ht => ?_, fun y => ?_, fun A hA hAc => exists_singular_G2_qplus hp hp3 hpk hA hAc⟩
  · have h1 : (t : ModGL .G2 K) ∈ entrywiseFixedGroup .G2 σ := by
      refine mem_entrywiseFixedGroup.mpr ⟨t.2, ?_⟩
      have h2 := congrArg Subtype.val ht
      rwa [coe_entrywiseAdjointAut] at h2
    rw [hJ] at h1
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp h1
    exact MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, Subtype.ext hyt⟩
  · have h1 : ((β y : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ entrywiseFixedGroup .G2 σ := by
      rw [hJ]
      exact Subgroup.mem_map_of_mem _ y.2
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    exact (mem_entrywiseFixedGroup.mp h1).2

theorem false_of_kF135Hyp_G2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) {hv : (TauCeti.LieTypeIndex.G2 q).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (h : KF135Hyp S p P x u V) : False := by
  by_cases hres : p ∣ q.exponent ∧ p ∣ q.card + 1
  · exact false_of_kF135Hyp_G2_E2 hq2 e h hres.1 hres.2
  · exact false_of_kF135Hyp_G2_of_not_E2 hq2 e h hres

theorem kF135At_fam7G2 : KF135At Fam7G2 := by
  intro S _ _ p P x u V hS h
  obtain ⟨q, hq2, hv, ⟨e⟩⟩ := hS
  exact (false_of_kF135Hyp_G2 hq2 e h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
