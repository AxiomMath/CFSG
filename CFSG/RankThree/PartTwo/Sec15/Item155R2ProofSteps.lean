module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof155R2

omit [Finite G] in
theorem commutator_sup_le_of {R O K : Subgroup G} (hRO : R ≤ Subgroup.normalizer (O : Set G))
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hRK : ⁅R, K⁆ ≤ O) : ⁅R ⊔ O, K⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have hw' : w ∈ (R : Set G) * (O : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R O hRO]
    exact hw
  obtain ⟨r, hr, o, ho, rfl⟩ := hw'
  have e : ⁅r * o, k⁆ = (r * ⁅o, k⁆ * r⁻¹) * ⁅r, k⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine mul_mem ?_ (hRK (Subgroup.commutator_mem_commutator hr hk))
  have hok : ⁅o, k⁆ ∈ O := by
    have h1 : k * o⁻¹ * k⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hk) o⁻¹).mp (inv_mem ho)
    have h2 := mul_mem ho h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using h2
  exact (Subgroup.mem_normalizer_iff.mp (hRO hr) _).mp hok

omit [Finite G] in
theorem commutator_pCoreOf_le (K : Subgroup G) :
    ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ CFSG.Open.pCoreOf 2 K :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)

theorem le_normalizer_of_commutator_le {R K : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRK0 : R ≤ Subgroup.normalizer (K : Set G)) (hK : K = oPrimeResidualOf 3 K)
    (hRK : ⁅R, K⁆ ≤ CFSG.Open.pCoreOf 2 K) (hZ : ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ R) :
    K ≤ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 K with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hRO : R ≤ Subgroup.normalizer (O : Set G) :=
    hRK0.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set W := R ⊔ O with hW
  have hW2 : IsPGroup 2 W := IsPGroup.to_sup_of_normal_right' hR2 hO2 hRO
  have hW3 : Nat.Coprime 3 (Nat.card W) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hWK : ⁅W, K⁆ ≤ O := commutator_sup_le_of hRO hKO hRK
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := by
    have heq : W = (R ⊔ ⁅R, K⁆) ⊔ O := by
      rw [hW, sup_assoc, sup_eq_right.mpr hRK]
    rw [heq]
    exact le_normalizer_sup (le_normalizer_sup_commutator R K) hKO
  calc K = oPrimeResidualOf 3 K := hK
    _ ≤ Subgroup.normalizer (R : Set G) := by
      rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
      rintro g ⟨hg, k, hgk⟩
      set E := Subgroup.zpowers g with hE
      have hE3 : IsPGroup 3 E := fun x => ⟨k, by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
          zpow_mul, zpow_natCast, hgk, one_zpow]⟩
      have hEK : E ≤ K := Subgroup.zpowers_le.mpr hg
      have hEW : E ≤ Subgroup.normalizer (W : Set G) := hEK.trans hKW
      have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3
        Nat.prime_three E W hE3 hEW hW3
      have hWE : ⁅W, E⁆ ≤ R := by
        rw [← hidem]
        exact (Subgroup.commutator_mono ((Subgroup.commutator_mono le_rfl hEK).trans hWK)
          hEK).trans hZ
      have hER : E ≤ Subgroup.normalizer (R : Set G) := by
        rw [Subgroup.le_normalizer_iff_commutator_le_left]
        exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hWE
      exact hER (Subgroup.mem_zpowers g)

variable {A : Subgroup G} {c : G} {L : Subgroup G}

end Proof155R2

end CFSG.RankThree.PartTwo.Sec15
