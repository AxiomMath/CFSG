module

import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofCUL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof158Cartan

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec16.ProofKSL3Two (mem_of_pow_mem_of_coprime
  quotient_linearAutGroup_comm)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData card_ringAut_and_isCyclic)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup conjAut fieldAut
  dualAut mem_linearAutGroup_iff conjAut_mem_linearAutGroup automorphism_generation proj
  conjAut_proj standard_automorphism_transport)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitarySU unitaryProj)
open Matrix

theorem modNine_of_three_dvd {π : Bool} {p f : ℕ} (hq : ModThree π (p ^ f)) (hf : 3 ∣ f) :
    p ^ f % 9 = 1 ∨ p ^ f % 9 = 8 := by
  obtain ⟨k, rfl⟩ := hf
  have e : p ^ (3 * k) = (p ^ k) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [e] at hq ⊢
  have h9 : (p ^ k) ^ 3 % 9 = ((p ^ k) % 9) ^ 3 % 9 := Nat.pow_mod _ _ _
  have h3 : (p ^ k) ^ 3 % 3 = ((p ^ k) % 9) ^ 3 % 3 := by
    rw [Nat.pow_mod]
    conv_rhs => rw [Nat.pow_mod]
    congr 2
    omega
  rw [h9]
  have hr : (p ^ k) % 9 < 9 := Nat.mod_lt _ (by norm_num)
  cases π
  · change (p ^ k) ^ 3 % 3 = 2 at hq
    rw [h3] at hq
    interval_cases (p ^ k) % 9 <;> simp_all
  · change (p ^ k) ^ 3 % 3 = 1 at hq
    rw [h3] at hq
    interval_cases (p ^ k) % 9 <;> simp_all

theorem not_three_dvd_of_not_modNine {π : Bool} {p f : ℕ} (hq : ModThree π (p ^ f))
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) : ¬ 3 ∣ f :=
  fun hf => h9 (modNine_of_three_dvd hq hf)

variable {K : Type} [Field K] {p f : ℕ}

theorem inndiag_of_three_pow_linear' [Finite K] (hp : p.Prime) (hKc : Nat.card K = p ^ f)
    (hf3 : ¬ 3 ∣ f) (σ : MulAut (projImage (slPi true 3 (p ^ f) K)))
    (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) :
    ∃ y ∈ glPi true 3 (p ^ f) K, ∀ m : projImage (slPi true 3 (p ^ f) K),
      ((σ m : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  set ψ := pslEquivProjective (p ^ f) K with hψ
  set α := MulAut.congr ψ σ with hα
  obtain ⟨k, hk⟩ := hσ
  have hαk : α ^ 3 ^ k = 1 := by rw [hα, ← map_pow, hk, map_one]
  have : (linearAutGroup 3 K).Normal := (KFacts.stdPinnedPSL_stable (by norm_num)).normal
  have hcop : Nat.Coprime (3 ^ k) (2 * f) := Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · omega
      · exact hf3 h))
  have hαI : α ∈ linearAutGroup 3 K := by
    refine mem_of_pow_mem_of_coprime _ hcop (by rw [hαk]; exact one_mem _) ?_
    obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 3) (by norm_num)
    obtain ⟨A, τ, ε, -, hαA⟩ := hform α
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hαA, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A),
      one_mul, (show Commute _ _ from quotient_linearAutGroup_comm _ _).mul_pow]
    have hτn : τ ^ f = 1 := by
      have h := pow_card_eq_one' (G := RingAut K) (x := τ)
      rwa [(card_ringAut_and_isCyclic hp K hKc).1] at h
    have hδ2 : dualAut 3 K ^ 2 = 1 := by
      rw [sq]
      exact (standard_automorphism_transport (n := 3) (K := K)).2.2.2.1
    have hτ2n : fieldAut 3 K τ ^ (2 * f) = 1 := by
      rw [← map_pow, mul_comm, pow_mul, hτn, one_pow, map_one]
    have hδ2n : (dualAut 3 K ^ ε) ^ (2 * f) = 1 := by
      rw [← pow_mul, mul_comm ε, pow_mul, pow_mul, hδ2, one_pow, one_pow]
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, hτ2n, hδ2n, QuotientGroup.mk_one, mul_one]
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hαI
  refine ⟨A, mem_glPi_true _ _, fun m => ?_⟩
  obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) (p ^ f) m
  have hproj : ∀ t : SpecialLinearGroup (Fin 3) K,
      ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hσs : σ (slToPsl (p ^ f) K s) = ψ.symm (α (proj 3 K s)) := by
    have h1 : α (proj 3 K s) = ψ (σ (ψ.symm (proj 3 K s))) := rfl
    rw [h1, MulEquiv.symm_apply_apply, hproj]
  rw [hσs, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul,
    map_inv]

theorem inndiag_of_three_pow_unitary' (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    (hf3 : ¬ 3 ∣ f) (σ : MulAut (projImage (slPi false 3 (p ^ f) K)))
    (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) :
    ∃ y ∈ glPi false 3 (p ^ f) K, ∀ m : projImage (slPi false 3 (p ^ f) K),
      ((σ m : projImage (slPi false 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  have := h.finite
  set ψ := psuEquivUnitary h with hψ
  set α := MulAut.congr ψ σ with hα
  obtain ⟨k, hk⟩ := hσ
  have hαk : α ^ 3 ^ k = 1 := by rw [hα, ← map_pow, hk, map_one]
  have : ((KFacts.psuConj h).range).Normal := (KFacts.stdPinnedPSU3_stable hq2).normal
  have hcop : Nat.Coprime (3 ^ k) (2 * f) := Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · omega
      · exact hf3 h))
  have hαI : α ∈ (KFacts.psuConj h).range := by
    refine mem_of_pow_mem_of_coprime _ hcop (by rw [hαk]; exact one_mem _) ?_
    obtain ⟨A, τ, hαA⟩ := KFacts.exists_psuConj_mul_psuField hq2 α
    have hτ : τ ^ (2 * f) = 1 := by
      have h1 := pow_card_eq_one' (G := RingAut K) (x := τ)
      rwa [(card_ringAut_and_isCyclic h.prime K h.card).1] at h1
    have hA1 : KFacts.psuConj h A ∈ (KFacts.psuConj h).range := ⟨A, rfl⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hαA, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr hA1, one_mul, ← QuotientGroup.mk_pow, ← map_pow, hτ,
      map_one]
    rfl
  obtain ⟨A, hA⟩ := hαI
  refine ⟨A, (mem_glPi_false h).mpr A.2, fun m => ?_⟩
  obtain ⟨s, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) m
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hσs : σ (suToPsu p f K s) = ψ.symm (α (unitaryProj h 3 s)) := by
    have h1 : α (unitaryProj h 3 s) = ψ (σ (ψ.symm (unitaryProj h 3 s))) := rfl
    rw [h1, MulEquiv.symm_apply_apply, hproj]
  rw [hσs, ← hA, psuConj_unitaryProj, hproj, coe_suToPsu, coe_suToPsu, KFacts.coe_suConj,
    map_mul, map_mul, Subgroup.coe_inv, map_inv]

theorem inndiag_of_three_pow {π : Bool} (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (hf3 : ¬ 3 ∣ f) (σ : MulAut (projImage (slPi π 3 (p ^ f) K)))
    (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) :
    ∃ y ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
      ((σ m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  have := hK.finite
  cases π
  · exact inndiag_of_three_pow_unitary' hK.unitary hq2 hf3 σ hσ
  · have hKc : Nat.card K = p ^ f := by rw [hK.card]; rfl
    exact inndiag_of_three_pow_linear' hK.prime hKc hf3 σ hσ

end CFSG.RankThree.PartTwo.Sec15.Proof158Cartan
