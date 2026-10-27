module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.Open.PGLModelDefs
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSL
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL3FixLin
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3Aut
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartOne.KFOUT3.Galois

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

namespace L3Fix

open Matrix
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (stdAut3 exists_std_form)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation
  slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_sq slGraphAut_matrix)
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Aut
  (stdAut3_mul_slConjugation_mul_inv slGraphAut_mul_slFieldAut exists_scalar_of_slConjugation_eq)

section Power

theorem pow_mul_mem {G : Type*} [Group G] {N : Subgroup G} {s : G}
    (hs : ∀ c ∈ N, s * c * s⁻¹ ∈ N) (m : ℕ) {c : G} (hc : c ∈ N) :
    s ^ m * c * (s ^ m)⁻¹ ∈ N := by
  induction m generalizing c with
  | zero => simpa using hc
  | succ m ih =>
    have e : s ^ (m + 1) * c * (s ^ (m + 1))⁻¹ = s ^ m * (s * c * s⁻¹) * (s ^ m)⁻¹ := by
      rw [pow_succ]
      group
    rw [e]
    exact ih (hs c hc)

theorem exists_pow_eq_mul_pow {G : Type*} [Group G] {N : Subgroup G} {s : G}
    (hs : ∀ c ∈ N, s * c * s⁻¹ ∈ N) {c : G} (hc : c ∈ N) (m : ℕ) :
    ∃ c' ∈ N, (c * s) ^ m = c' * s ^ m := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨c' * (s ^ m * c * (s ^ m)⁻¹), N.mul_mem hc' (pow_mul_mem hs m hc), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

variable {K : Type} [Field K]

theorem stdAut3_pow_of_odd (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) {m : ℕ}
    (hm : Odd m) (hσ : σ ^ m = 1) :
    ∃ B : GL (Fin 3) K, stdAut3 A σ ε ^ m = stdAut3 B 1 ε := by
  set N : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K)) := (slConjugation 3 K).range with hN
  set s : MulAut (SpecialLinearGroup (Fin 3) K) :=
    slFieldAut (Fin 3) K σ * slGraphAut 3 K ^ ε with hs
  have hs1 : stdAut3 1 σ ε = s := by simp [stdAut3, hs]
  have hsN : ∀ c ∈ N, s * c * s⁻¹ ∈ N := by
    rintro _ ⟨D, rfl⟩
    have h := stdAut3_mul_slConjugation_mul_inv 1 σ ε D
    rw [hs1] at h
    rw [h]
    exact ⟨_, rfl⟩
  have hα : stdAut3 A σ ε = slConjugation 3 K A * s := by rw [stdAut3, hs, mul_assoc]
  obtain ⟨c', ⟨B, rfl⟩, hc'⟩ := exists_pow_eq_mul_pow hsN ⟨A, rfl⟩ m
  refine ⟨B, ?_⟩
  have hc0 : Commute (slGraphAut 3 K) (slFieldAut (Fin 3) K σ) := slGraphAut_mul_slFieldAut σ
  have hcomm : Commute (slFieldAut (Fin 3) K σ) (slGraphAut 3 K ^ ε) := hc0.symm.pow_right ε
  have hsm : s ^ m = slGraphAut 3 K ^ ε := by
    rw [hs, hcomm.mul_pow, ← map_pow, hσ, map_one, one_mul, ← pow_mul]
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · simp
    · obtain ⟨j, rfl⟩ := hm
      rw [one_mul, pow_succ, pow_mul, slGraphAut_sq, one_pow, one_mul, pow_one]
  rw [hα, hc', hsm, stdAut3, map_one, mul_one]

end Power

section Core

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem eq_one_of_fix_of_pow (hK : Nat.card F % 3 = 2) {y : SpecialLinearGroup (Fin 3) F}
    (hy : orderOf y = 3) (B : GL (Fin 3) F) (hfix : slConjugation 3 F B y = y) {k : ℕ}
    (hk : slConjugation 3 F B ^ 2 ^ k = 1) : slConjugation 3 F B = 1 := by
  have hBBi : (B : Matrix (Fin 3) (Fin 3) F) * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : (B : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * B := by
    have h := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
      hfix
    simp only [slConjugation_matrix] at h
    calc (B : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F)
        = ((B : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) *
            ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
            (B : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc _ _ (B : Matrix (Fin 3) (Fin 3) F), hBiB, Matrix.mul_one]
      _ = (y : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) := by rw [h]
  have hpow : slConjugation 3 F 1 = slConjugation 3 F (B ^ 2 ^ k) := by
    rw [map_pow, hk, map_one]
  obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq hpow
  have hBc : (B : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ k = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have h : (((1 : GL (Fin 3) F)⁻¹ * B ^ 2 ^ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (B : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ k := by
      rw [inv_one, one_mul, Units.val_pow_eq_pow_val]
    rw [← h, hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  obtain ⟨t, ht⟩ := L3Fix.exists_smul_one_of_pow_two_pow hK hy k hcomm ⟨c, hBc⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [slConjugation_matrix, MulAut.one_apply]
  have hBg : (B : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) = g * B := by
    rw [ht, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  rw [hBg, Matrix.mul_assoc, hBBi, Matrix.mul_one]

theorem false_of_conj_graph (hK : Nat.card F % 3 = 2) {y : SpecialLinearGroup (Fin 3) F}
    (hy : orderOf y = 3) {R : Subgroup (SpecialLinearGroup (Fin 3) F)} (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R) (B : GL (Fin 3) F)
    (hBR : ∀ r ∈ R, (slConjugation 3 F B * slGraphAut 3 F) r ∈ R) : False :=
  L3Fix.false_of_graph hK hy hR2 hR1 hyR (slGraphAut 3 F) (slConjugation 3 F B * slGraphAut 3 F) B
    (slGraphAut_matrix 3 F) (fun g => slConjugation_matrix 3 F B (slGraphAut 3 F g)) hBR

theorem res1AutFix_sl_three (hK : Nat.card F % 3 = 2) {n : ℕ} (hn : Odd n)
    (hσ : ∀ σ : F ≃+* F, σ ^ n = 1) : Res1AutFix (SpecialLinearGroup (Fin 3) F) := by
  intro y hy R₀ hR₀ hR2 hyR X hX hXy hXR
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hX ⟨α, hα⟩
  have hαk : α ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hβX : α ^ n ∈ X := X.pow_mem hα n
  have hβy : (α ^ n) y = y := hXy _ hβX
  have hβR : ∀ r ∈ R₀, (α ^ n) r ∈ R₀ := hXR _ hβX
  have hβk : (α ^ n) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hαk, one_pow]
  have hn1 : α ^ n = 1 := by
    obtain ⟨A, σ, ε, hε, hαeq⟩ := exists_std_form α
    obtain ⟨B, hB⟩ := stdAut3_pow_of_odd A σ ε hε hn (hσ σ)
    have hB' : α ^ n = stdAut3 B 1 ε := by rw [hαeq]; exact hB
    rw [hB'] at hβy hβR hβk ⊢
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · have h0 : stdAut3 B 1 0 = slConjugation 3 F B := by simp [stdAut3]
      rw [h0] at hβy hβk ⊢
      exact eq_one_of_fix_of_pow hK hy B hβy hβk
    · exfalso
      have h1 : stdAut3 B 1 1 = slConjugation 3 F B * slGraphAut 3 F := by simp [stdAut3]
      rw [h1] at hβR
      exact false_of_conj_graph hK hy hR2 hR₀ hyR B hβR
  have hcop : Nat.gcd n (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hn)
  have := pow_gcd_eq_one.mpr ⟨hn1, hαk⟩
  rwa [hcop, pow_one] at this

end Core

end L3Fix

theorem res1AutFix_projSL_three {n : ℕ} (hn : Odd n) :
    Res1AutFix ↥(CFSG.PGLModel.projSL 3 (GaloisField 2 n)) := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    have h3 : 3 ∣ 2 ^ n + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hn
    rw [hcard]
    omega
  have hσ : ∀ σ : GaloisField 2 n ≃+* GaloisField 2 n, σ ^ n = 1 := fun σ =>
    CFSG.RankThree.PartOne.KFOUT3.aut_pow_card (Nat.one_le_iff_ne_zero.mpr hn0) hcard σ
  have hres := L3Fix.res1AutFix_sl_three hK hn hσ
  exact Res1AutFix.of_mulEquiv
    ((CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 n)).trans
      (MulEquiv.ofBijective
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 (GaloisField 2 n))
        ⟨CFSG.RankThree.PartTwo.KFacts.proj_three_injective hK,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 _⟩).symm) hres

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
