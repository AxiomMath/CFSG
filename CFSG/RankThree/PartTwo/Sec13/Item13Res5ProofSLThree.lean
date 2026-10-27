module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofOuter
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofThreeFree
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofSLThreeField
public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofAlpha
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec4.Item47CasesAlt
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofSLThreeInner

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

namespace Res5Proof

section Model

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem false_of_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {B : Subgroup (MulAut (slPi π 3 (p ^ f) K))} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9)
    (hF1 : ∀ x : slPi π 3 (p ^ f) K, orderOf x = 3 → (∀ β ∈ B, β x = x) →
      x ∈ Subgroup.center (slPi π 3 (p ^ f) K))
    (hNP : ∀ y : slPi π 3 (p ^ f) K, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) : False := by
  by_cases hI : ∃ β ∈ B, β ≠ 1 ∧
      β ∈ (MulAut.conj : slPi π 3 (p ^ f) K →* MulAut (slPi π 3 (p ^ f) K)).range
  · obtain ⟨β, hβB, hβ1, y, rfl⟩ := hI
    exact false_of_conj_mem hK hq hB.2 hF1 hNP hβB hβ1
  · push Not at hI
    exact false_of_inner_trivial hK hq hq2 hB hB9 fun β hβ hr => by
      by_contra h
      exact hI β hβ h hr

theorem false_of_mulEquiv_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {X : Type} [Group X] (φ : X ≃* slPi π 3 (p ^ f) K)
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hF1 : ∀ x : X, orderOf x = 3 → (∀ β ∈ B, β x = x) → x ∈ Subgroup.center X)
    (hNP : ∀ y : X, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) : False := by
  set κ : MulAut X ≃* MulAut (slPi π 3 (p ^ f) K) := MulAut.congr φ with hκ
  have hκapp : ∀ (β : MulAut X) (x : slPi π 3 (p ^ f) K), κ β x = φ (β (φ.symm x)) :=
    fun β x => rfl
  set B' : Subgroup (MulAut (slPi π 3 (p ^ f) K)) := B.map κ.toMonoidHom with hB'
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' := by
    have := hB.1
    refine ⟨⟨⟨fun β γ => ?_⟩⟩, ?_⟩
    · obtain ⟨_, β₀, hβ₀, rfl⟩ := β
      obtain ⟨_, γ₀, hγ₀, rfl⟩ := γ
      apply Subtype.ext
      change κ β₀ * κ γ₀ = κ γ₀ * κ β₀
      rw [← map_mul, ← map_mul]
      exact congrArg κ (congrArg Subtype.val (mul_comm' (⟨β₀, hβ₀⟩ : B) ⟨γ₀, hγ₀⟩))
    · rintro _ ⟨β₀, hβ₀, rfl⟩
      change (κ β₀) ^ 3 = 1
      rw [← map_pow, hB.2 β₀ hβ₀, map_one]
  have hB'9 : Nat.card B' = 9 := (Subgroup.card_map_of_injective κ.injective).trans hB9
  refine false_of_slPi hK hq hq2 hB'e hB'9 (fun x hx3 hfix => ?_) (fun y hy β hβ => ?_)
  · have hfix₀ : ∀ β ∈ B, β (φ.symm x) = φ.symm x := by
      intro β hβ
      have h1 := hfix (κ β) ⟨β, hβ, rfl⟩
      rw [hκapp] at h1
      have h2 := congrArg φ.symm h1
      simpa using h2
    have hc := hF1 (φ.symm x) (by rw [MulEquiv.orderOf_eq]; exact hx3) hfix₀
    have hc' : φ (φ.symm x) ∈ Subgroup.center (slPi π 3 (p ^ f) K) :=
      (MulEquivClass.apply_mem_center_iff φ).2 hc
    simpa using hc'
  · obtain ⟨β₀, hβ₀, rfl⟩ := hβ
    have hconj : κ (MulAut.conj (φ.symm y)) = MulAut.conj y := by
      rw [hκ, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    have hyB : MulAut.conj (φ.symm y) ∈ B := by
      obtain ⟨γ, hγ, hγeq⟩ := hy
      have : γ = MulAut.conj (φ.symm y) := κ.injective (hγeq.trans hconj.symm)
      exact this ▸ hγ
    have h1 := hNP (φ.symm y) hyB β₀ hβ₀
    change κ β₀ y = y
    rw [hκapp, h1, MulEquiv.apply_symm_apply]

end Model

end Res5Proof

open Res5Proof

theorem ks131SLThreeOuterE9 : KS131SLThreeOuterE9 := by
  intro X _ _ p e hp he hpe hX hq hZ3 B hB hB9 hF1 hNP _
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by rcases hpe with rfl | ⟨h, -⟩ <;> omega
  have hmod : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
    have h0 : p ^ e % 3 ≠ 0 := fun h0 => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))).symm
    omega
  have hZ : Subgroup.center X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    norm_num at hZ3
  obtain ⟨K, _, _, ⟨hK, hq1, ⟨φ⟩⟩ | ⟨hK, hq2, ⟨φ⟩⟩⟩ :=
    KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hX hmod hZ
  ·
    have hK' : PiField true p e K := ⟨hp, he, hK⟩
    have hgt : 2 < p ^ e := by
      have h1 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h1' : p ^ e % 3 = 1 := hq1
      omega
    exact false_of_mulEquiv_slPi (π := true) hK' hq1 hgt φ hB hB9 hF1 hNP
  ·
    have hK' : PiField false p e K := ⟨hp, he, hK⟩
    have hgt : 2 < p ^ e := by
      by_contra hle
      have h2 : p ^ e = 2 := by
        have h1 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        omega
      have hs : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) K) :=
        isSolvable_slPi_two hK' h2
      exact Sec4.false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    exact false_of_mulEquiv_slPi (π := false) hK' hq2 hgt φ hB hB9 hF1 hNP

theorem ks131CenterOuterE9 :
    KS131CenterOuterE9 :=
  ks131CenterOuterE9_of ks131SLThreeOuterE9

theorem ks131CentralCensus :
    KS131CentralCensus :=
  ks131CentralCensus_of ks131ThreeFreeNoE9 ks131CenterList46 ks131CenterOuterE9

theorem ks131AlphaInvolutionCentral_of_item4_6
    (h46 : Sec4.Item4_6) :
    KS131AlphaInvolutionCentral :=
  ks131AlphaInvolutionCentral_of_census h46 ks131CentralCensus

end CFSG.RankThree.PartTwo.Sec13
