module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightProj

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition

private lemma rckIIp_fePSU_dualPair_model {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e) :
    ∃ (t' : CFSG.Open.StatedLieTag) (m' f' : ℕ), f < f' ∧
      (t' = .PSL ∨ t' = .PSU) ∧
      CFSG.Open.StatedClassicalModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) t' m' 2 f' := by
  classical
  set d : ℕ := blockDegree (Algebra.adjoin F (Units.val '' S)) e with hd
  have hdeg' : 2 ≤ d := by rw [hd]; exact hdeg
  obtain ⟨m, K, hKfield, hKfin, hcard, hm, ⟨eiso⟩⟩ :=
    fePSU_dualPair_iso hc n ψ hψ S hSU hS hodd hε hJε he heε d hd hdeg' hpair hεeq
  let : Field K := hKfield
  have : Finite K := hKfin
  have hf : 1 ≤ f := fePSU_f_pos hc
  have h4 : 4 ≤ 2 * d * f := by
    calc (4 : ℕ) = (2 * 2) * 1 := by norm_num
      _ ≤ (2 * d) * f := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdeg') hf
      _ = 2 * d * f := by rw [mul_assoc]
  refine ⟨.PSL, m, 2 * d * f, ?_, Or.inl rfl, ?_⟩
  · have hlt : (1 : ℕ) * f < (2 * d) * f :=
      mul_lt_mul_of_pos_right (by omega : (1 : ℕ) < 2 * d) (by omega : 0 < f)
    simpa [one_mul] using hlt
  · refine ⟨?_, ?_⟩
    · refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.mul_pos (by omega : 0 < 2 * d) (by omega : 0 < f))
      · omega
      · intro h
        have hp : 2 ^ (2 * d * f) = 2 := (Prod.mk.inj h).2
        have hle : 4 ≤ 2 ^ (2 * d * f) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (2 * d * f) :=
                Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num : 2 ≤ 4) h4)
        omega
      · intro h
        have hp : 2 ^ (2 * d * f) = 3 := (Prod.mk.inj h).2
        have hle : 4 ≤ 2 ^ (2 * d * f) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (2 * d * f) :=
                Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num : 2 ≤ 4) h4)
        omega
    · refine ⟨K, hKfield, hKfin, ?_, ⟨eiso⟩⟩
      calc Nat.card K = (2 ^ f) ^ (2 * d) := hcard
        _ = 2 ^ (f * (2 * d)) := (pow_mul 2 f (2 * d)).symm
        _ = 2 ^ (2 * d * f) := by congr 1; ring

private lemma rckIIp_fePSU_selfDual_model {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hfix : e = ε) :
    ∃ (t' : CFSG.Open.StatedLieTag) (m' f' : ℕ), f < f' ∧
      (t' = .PSL ∨ t' = .PSU) ∧
      CFSG.Open.StatedClassicalModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) t' m' 2 f' := by
  classical
  set d : ℕ := blockDegree (Algebra.adjoin F (Units.val '' S)) e with hd
  have hdeg' : 2 ≤ d := by rw [hd]; exact hdeg
  have hf : 1 ≤ f := fePSU_f_pos hc
  have h2fd : 2 ≤ f * d := by
    calc (2 : ℕ) = 1 * 2 := by norm_num
      _ ≤ f * d := Nat.mul_le_mul hf hdeg'
  have hlt : f < f * d := by
    calc f = f * 1 := (mul_one f).symm
      _ < f * d := Nat.mul_lt_mul_of_pos_left (by omega) hf
  have h4fd : 4 ≤ 2 ^ (f * d) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) h2fd
  rcases fePSU_selfDual_iso hc n ψ hψ S hSU hS hodd hε hJε he d hd hdeg' hfix with
    ⟨m, K, hKfield, hKfin, hKcard, hm3, _, ⟨eiso⟩⟩ | ⟨K, hKfield, hKfin, hKcard, ⟨eiso⟩⟩
  · let : Field K := hKfield
    have : Finite K := hKfin
    have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
    refine ⟨.PSU, m, f * d, hlt, Or.inr rfl, ?_⟩
    refine ⟨⟨Nat.prime_two, ?_, hm3, ?_⟩, ?_⟩
    · exact Nat.mul_pos hf (by omega)
    · intro h
      have hp : 2 ^ (f * d) = 2 := (Prod.mk.inj h).2
      omega
    · refine ⟨K, hKfield, hKfin, ?_, ?_⟩
      · rw [hKcard, hq]
      · rw [hq] at eiso
        exact ⟨eiso⟩
  · let : Field K := hKfield
    have : Finite K := hKfin
    have hq : (2 ^ f) ^ d = 2 ^ (f * d) := (pow_mul 2 f d).symm
    refine ⟨.PSL, 2, f * d, hlt, Or.inl rfl, ?_⟩
    refine ⟨⟨Nat.prime_two, ?_, le_rfl, ?_, ?_⟩, ?_⟩
    · exact Nat.mul_pos hf (by omega)
    · intro h
      have hp : 2 ^ (f * d) = 2 := (Prod.mk.inj h).2
      omega
    · intro h
      have hp : 2 ^ (f * d) = 3 := (Prod.mk.inj h).2
      omega
    · refine ⟨K, hKfield, hKfin, ?_, ?_⟩
      · rw [hKcard, hq]
      · exact ⟨eiso⟩

private lemma rckIIp_component_model_PSL_or_PSU {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)}
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
      ε, glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (t' : CFSG.Open.StatedLieTag) (m' f' : ℕ), f < f' ∧
      (t' = .PSL ∨ t' = .PSU) ∧
      CFSG.Open.StatedClassicalModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) t' m' 2 f' := by
  rcases fePSU_dichotomy hc S hSU hS hε he heε with hfix | ⟨hpair, hεeq⟩
  · exact rckIIp_fePSU_selfDual_model hc n ψ hψ S hSU hS hodd hε hJε he hdeg hfix
  · exact rckIIp_fePSU_dualPair_model hc n ψ hψ S hSU hS hodd hε hJε he heε hdeg hpair hεeq

theorem rckIIp_PSU_fieldExt
    {X : Type} [Group X] {n g : ℕ}
    (φ : (ggU .PSU n (g + 1)).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hε : IsPrimAdjIdemIn
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) ε)
    {J' : Subgroup (ggU .PSU n (g + 1)).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S ε :
          Subgroup (ggU .PSU n (g + 1)).K),
        (glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S ε :
          Subgroup (ggU .PSU n (g + 1)).K)⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨t', m', f', hlt, ht', hmod⟩ :=
    rckIIp_component_model_PSL_or_PSU (f := g + 1)
      (card_galoisField_two_mul 2 (g + 1) (by omega)) n φ hφk S hSU hS hodd hε hJe he heε hdeg
  exact rckIIp_false_of_alt_eight_statedClassicalModel ht' (by omega) hmod hA8

end CFSG.StandardType.RCKC1
