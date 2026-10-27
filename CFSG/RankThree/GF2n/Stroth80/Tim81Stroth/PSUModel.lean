module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.HardMathSupport.Solomon.Proving.SU3CentreScalars
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open

private theorem card_galoisField_two_mul (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), mul_comm 2 f, pow_mul]

private theorem statedSU_one_eq_bot (q : ℕ) (K : Type) [Field K] :
    StatedSU 1 q K = ⊥ := by
  unfold StatedSU
  rw [eq_bot_iff, Subgroup.closure_le]
  intro A hA
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  apply Units.ext
  have hmat : (A : Matrix (Fin 1) (Fin 1) K) = 1 := by
    have hdet : (A : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
      simpa [Matrix.det_fin_one] using hA.1
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simpa using hdet
  exact hmat

private theorem subsingleton_statedSU_of_le_one {n : ℕ} (hn : n ≤ 1) (q : ℕ) (K : Type)
    [Field K] : Subsingleton ↥(StatedSU n q K) := by
  interval_cases n
  · infer_instance
  · rw [statedSU_one_eq_bot]
    infer_instance

private theorem center_statedSU_eq_scalars_galoisField (n f : ℕ) (hf : 1 ≤ f) :
    Subgroup.center (StatedSU n (2 ^ f) (GaloisField 2 (2 * f))) =
      (StatedScalars (Fin n) (GaloisField 2 (2 * f))).subgroupOf
        (StatedSU n (2 ^ f) (GaloisField 2 (2 * f))) := by
  let K := GaloisField 2 (2 * f)
  have hK : Nat.card K = (2 ^ f) ^ 2 := card_galoisField_two_mul f hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := inferInstance
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with
    rfl | rfl | rfl | rfl | hn4
  · haveI : Subsingleton ↥(StatedSU 0 (2 ^ f) K) :=
      subsingleton_statedSU_of_le_one (by omega) (2 ^ f) K
    exact Subsingleton.elim _ _
  · haveI : Subsingleton ↥(StatedSU 1 (2 ^ f) K) :=
      subsingleton_statedSU_of_le_one (by omega) (2 ^ f) K
    exact Subsingleton.elim _ _
  · rw [CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot hK]
    have hle : StatedSU 2 (2 ^ f) K ≤ StatedSL 2 K :=
      CFSG.Open.StatedAPI.statedSU_le_statedSL 2 (2 ^ f) K
    have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSU 2 (2 ^ f) K) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨(x : GL (Fin 2) K), hle x.2⟩ : ↥(StatedSL 2 K)) ∈
          (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
      rw [CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot,
        Subgroup.mem_bot] at hx'
      have hx'' : (x : GL (Fin 2) K) = 1 := by
        simpa using congrArg (fun y : ↥(StatedSL 2 K) => (y : GL (Fin 2) K)) hx'
      exact Subtype.ext hx''
    rw [hbot]
  · exact CFSG.HardMathSupport.Solomon.Proving.center_statedSU_three_eq_scalars (q := 2 ^ f) hK
  · have hnq : (n, 2 ^ f) ≠ (3, 2) := by
      intro h
      have h1 : n = 3 := congrArg Prod.fst h
      omega
    exact (isQuasisimple_statedSU_of_card (p := 2) (f := f) (n := n) hK (by omega) hnq).2

theorem isPSUModel_of_su_surjective {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (Φ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) →* X)
    (hsurj : Function.Surjective Φ)
    (hker : Φ.ker = Subgroup.center _) :
    IsPSUModel n (2 ^ f) X := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul f hf
  have hZ := center_statedSU_eq_scalars_galoisField n f hf
  refine ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (centerQuotientEquivStatedProj hK hZ))

end CFSG.RankThree.GF2n.Stroth80
