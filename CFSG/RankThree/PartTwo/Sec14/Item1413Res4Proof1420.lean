module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item172Proof
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res4

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_mem_scriptQPiStar_top {A : Subgroup G} (hA : IsE27 A) {y : G} (hyA : y ∈ A)
    {R : Subgroup G} (hR : R ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hRK : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))) :
    CFSG.ABGLocalTools.IsSylowOf 2 R (pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK𝓠 : pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) ∈ scriptQ A (lB A) :=
    Sec17.Proof172.pPrimeCoreOf_centralizer_mem_scriptQ hA hyA
  have hAK : A ≤ Subgroup.normalizer
      (pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) : Set G) := hK𝓠.1.2.2
  have hK3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hK𝓠.1.2.1
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hR.prop
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR.prop.1.1.1.2.2
  obtain ⟨T, hT, hRT, hAT⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    Nat.prime_three Nat.prime_two hA.isPGroup hAK hK3 hRK hR2 hAR
  have hTmem : T ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hK𝓠 hT.le hAT, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT.isPGroup⟩
  rw [hR.eq_of_le hTmem hRT]
  exact hT

theorem exists_mem_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {K R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * g ∈ Subgroup.normalizer (R : Set G) := by
  have hle : R.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg r).mp (hR.le hr)
  have hcs : CFSG.ABGLocalTools.IsSylowOf p (R.map (MulAut.conj g).toMonoidHom) K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hR.card_eq
  obtain ⟨k, hk, hkconj⟩ := hR.exists_mem_conj hcs
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hA : g * x * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom ↔ x ∈ R := by
    constructor
    · rintro ⟨r, hr, hrx⟩
      have h1 : g * r * g⁻¹ = g * x * g⁻¹ := hrx
      have h2 : r = x := by simpa using h1
      exact h2 ▸ hr
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hB := hkconj (g * x * g⁻¹)
  have hC : k⁻¹ * (g * x * g⁻¹) * k = (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ := by group
  rw [← hA, hB, hC]

theorem pCoreOf_normalizer_inf_le_of_isSylowOf {R : Subgroup G} {y : G}
    (hRK : CFSG.ABGLocalTools.IsSylowOf 2 R
      (pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)))) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) ⊓
      Subgroup.centralizer ({y} : Set G) ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({y} : Set G) with hCdef
  set K := pPrimeCoreOf 3 C with hKdef
  set O := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) with hOdef
  set P := O ⊓ C with hPdef
  have hR2 : IsPGroup 2 R := hRK.isPGroup
  have hRK' : R ≤ K := hRK.le
  have hRC : R ≤ C := hRK'.trans (pPrimeCoreOf_le 3 C)
  have hRO : R ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 R hR2
  have hRP : R ≤ P := le_inf hRO hRC
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hPK : P ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans hCK
  have hMC : P ⊔ K ≤ C := sup_le inf_le_right (pPrimeCoreOf_le 3 C)
  have hNM : Subgroup.normalizer (R : Set G) ⊓ C ≤
      Subgroup.normalizer ((P ⊔ K : Subgroup G) : Set G) :=
    le_normalizer_sup
      (le_normalizer_inf (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (inf_le_right.trans Subgroup.le_normalizer))
      (inf_le_right.trans hCK)
  have hCM : C ≤ Subgroup.normalizer ((P ⊔ K : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨k, hk, hn⟩ := exists_mem_normalizer_of_isSylowOf hRK (hCK hg)
    have hkC : k ∈ C := pPrimeCoreOf_le 3 C hk
    have hnC : k⁻¹ * g ∈ C := C.mul_mem (C.inv_mem hkC) hg
    have hnM := hNM (Subgroup.mem_inf.mpr ⟨hn, hnC⟩)
    have hkM : k ∈ Subgroup.normalizer ((P ⊔ K : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (le_sup_right (a := P) hk)
    have hg' : g = k * (k⁻¹ * g) := by group
    rw [hg']
    exact mul_mem hkM hnM
  have hP3 : IsPiSubgroup (piCompl 3) P :=
    (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr
      (Proof1413Res3.not_three_dvd_of_isPGroup_two hP2)
  have hK3 : IsPiSubgroup (piCompl 3) K :=
    (isPiSubgroup_piCompl_iff Nat.prime_three K).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C))
  have hM3 := (isPiSubgroup_piCompl_iff Nat.prime_three (P ⊔ K)).mp
    (isPiSubgroup_piCompl_sup hP3 hK3 hPK)
  have hMK : P ⊔ K ≤ K :=
    le_pPrimeCoreOf hMC hCM ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3)
  have hPK' : P ≤ K := le_sup_left.trans hMK
  rw [hRK.eq_of_le hRP hPK' hP2]

omit [Finite G] in
theorem zpowers_ne_of_frame [Finite G] {L : Subgroup G} {c a : G}
    (h : Proof1413Res3.Frame2 L c a) {i j : ℕ} (hi : i % 3 ≠ 0) (hj : j % 3 ≠ 0) :
    Subgroup.zpowers (c ^ i * a ^ j) ≠ Subgroup.zpowers c ∧
      Subgroup.zpowers (c ^ i * a ^ j) ≠ Subgroup.zpowers a := by
  constructor
  · intro heq
    have hmem : c ^ i * a ^ j ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers _
    obtain ⟨n, hn⟩ : ∃ n : ℕ, c ^ n = c ^ i * a ^ j := by
      have h1 : c ^ i * a ^ j ∈ (Submonoid.powers c : Set G) := by
        rw [(isOfFinOrder_of_finite c).powers_eq_zpowers]
        exact hmem
      exact Submonoid.mem_powers_iff _ _ |>.mp h1
    have h2 : c ^ i * a ^ j = c ^ n * a ^ 0 := by rw [pow_zero, mul_one, hn]
    have := h.pow_eq_mod h2
    omega
  · intro heq
    have hmem : c ^ i * a ^ j ∈ Subgroup.zpowers a := heq ▸ Subgroup.mem_zpowers _
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a ^ n = c ^ i * a ^ j := by
      have h1 : c ^ i * a ^ j ∈ (Submonoid.powers a : Set G) := by
        rw [(isOfFinOrder_of_finite a).powers_eq_zpowers]
        exact hmem
      exact Submonoid.mem_powers_iff _ _ |>.mp h1
    have h2 : c ^ i * a ^ j = c ^ 0 * a ^ n := by rw [pow_zero, one_mul, hn]
    have := h.pow_eq_mod h2
    omega

end Proof1413Res4

end CFSG.RankThree.PartTwo.Sec14
