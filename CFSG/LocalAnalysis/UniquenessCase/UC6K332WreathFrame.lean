module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwistFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath

open CFSG.RankThree.PartTwo.Sec4.RonanK432
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (BlockFrame TwistFrame BlockFrame.toTwistFrame)

theorem factorization_factorial_three : (Nat.factorial 3).factorization 3 = 1 := by
  have h : Nat.factorial 3 = 2 * 3 := by decide
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd]

variable {S : Type} [Group S]

theorem finRotate_three_mem : finRotate 3 ∈ alternatingGroup (Fin 3) := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]
  decide

theorem finRotate_three_inv_apply (i : Fin 3) :
    ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) i = i - 1 := by
  fin_cases i <;> decide

theorem listRow_of_twistFrame [Finite S] {a : ℕ} (ha : 1 ≤ a) {μ : ℤ} (hμ : ¬ (3 : ℤ) ∣ μ - 1)
    (F : TwistFrame (Multiplicative (ZMod (3 ^ a))) 3 S μ)
    (hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card S) : ListRow S := by
  haveI : NeZero (3 ^ a) := ⟨pow_ne_zero _ (by norm_num)⟩
  let σ : alternatingGroup (Fin 3) := ⟨finRotate 3, finRotate_three_mem⟩
  have hσ3 : σ ^ 3 = 1 := by
    apply Subtype.ext
    show (finRotate 3) ^ 3 = 1
    decide
  have hC : Nat.card (Multiplicative (ZMod (3 ^ a))) = 3 ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  refine listRow_of_wreath ha hC F.T_injective hμ F.exists_twist (s := F.A σ) ?_ ?_ hS
  · rw [← map_pow, hσ3, map_one]
  · intro x
    rw [F.A_conj σ x]
    congr 1
    funext i
    simp only [Function.comp_apply, sh]
    show x (((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) i) = x (i - 1)
    rw [finRotate_three_inv_apply]

theorem listRow_of_blockFrame [Finite S] {a : ℕ} (ha : 1 ≤ a)
    (F : BlockFrame (Multiplicative (ZMod (3 ^ a))) 3 S)
    (hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card S) : ListRow S :=
  listRow_of_twistFrame ha (by norm_num) F.toTwistFrame hS

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath
