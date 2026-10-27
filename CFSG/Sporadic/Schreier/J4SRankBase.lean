
module

public import CFSG.Sporadic.Schreier.J4SRankCheckBase
public import CFSG.Sporadic.Schreier.J4SThreeBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SInvData
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SRankData
public meta import CFSG.Sporadic.Schreier.J4SRankData
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem rowsMatrix_sub_one_row (X : Array ℕ) (r : Fin 112) :
    (rowsMatrix 112 X - 1) r = toVecD 112 ((X[r.val]?.getD 0) ^^^ 2 ^ r.val) := by
  funext j
  rw [Matrix.sub_apply, SmallF2.rowsMatrix_apply, toVecD_xor, Pi.add_apply, sub_eq_add_neg,
    ZMod.neg_eq_self_mod_two]
  congr 1
  rw [Matrix.one_apply, toVecD_apply, Nat.testBit_two_pow]
  by_cases h : r = j
  · subst h; simp
  · have h' : r.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem three_le_rank_of_card {M : Matrix (Fin 112) (Fin 112) (ZMod 2)}
    (h : 8 ≤ Nat.card (Submodule.span (ZMod 2) (Set.range M))) : 3 ≤ M.rank := by
  rw [Matrix.rank_eq_finrank_span_row]
  set R := Submodule.span (ZMod 2) (Set.range M)
  show 3 ≤ Module.finrank (ZMod 2) R
  have key : 2 ^ Module.finrank (ZMod 2) R = Nat.card R :=
    @FiniteField.pow_finrank_eq_natCard 2 _ R (Submodule.addCommGroup R) _ (Submodule.module R)
  rw [← key] at h
  by_contra hlt3
  have h3 : Module.finrank (ZMod 2) R ≤ 2 := by omega
  have : 2 ^ Module.finrank (ZMod 2) R ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem three_le_rank_of_rows3 {X : Array ℕ} (h : rows3OK X = true) :
    3 ≤ (rowsMatrix 112 X - 1).rank := by
  unfold rows3OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hla, hlb⟩, hlc⟩, hinj⟩ := h
  set a := X[0]! ^^^ 1
  set b := X[1]! ^^^ 2
  set c := X[2]! ^^^ 4
  have hrow : ∀ (r : Fin 112), (rowsMatrix 112 X - 1) r = toVecD 112 (X[r.val]! ^^^ 2 ^ r.val) :=
    fun r => by rw [rowsMatrix_sub_one_row, ← getElem!_eq_getD']
  have h0 : (rowsMatrix 112 X - 1) 0 = toVecD 112 a := hrow 0
  have h1 : (rowsMatrix 112 X - 1) 1 = toVecD 112 b := hrow 1
  have h2 : (rowsMatrix 112 X - 1) 2 = toVecD 112 c := hrow 2
  set R := Submodule.span (ZMod 2) (Set.range (rowsMatrix 112 X - 1))
  have hlt : ∀ i, comb3 a b c i < 2 ^ 112 := by
    intro i
    unfold comb3
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_ <;> split_ifs <;>
      first | assumption | positivity
  have hmem : ∀ i, toVecD 112 (comb3 a b c i) ∈ R := by
    intro i
    unfold comb3
    rw [toVecD_xor, toVecD_xor]
    refine R.add_mem (R.add_mem ?_ ?_) ?_ <;> split_ifs
    · rw [← h0]; exact Submodule.subset_span ⟨0, rfl⟩
    · rw [toVecD_zero]; exact R.zero_mem
    · rw [← h1]; exact Submodule.subset_span ⟨1, rfl⟩
    · rw [toVecD_zero]; exact R.zero_mem
    · rw [← h2]; exact Submodule.subset_span ⟨2, rfl⟩
    · rw [toVecD_zero]; exact R.zero_mem
  have hf : Function.Injective fun i : Fin 8 => (⟨toVecD 112 (comb3 a b c i), hmem i⟩ : R) := by
    intro i j hij
    have e := congrArg Subtype.val hij
    dsimp only at e
    rcases hinj i i.isLt j j.isLt with h | h
    · exact Fin.ext h
    · exact absurd (toVecD_injective (hlt _) (hlt _) e) h
  refine three_le_rank_of_card ?_
  have := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_fin] at this

theorem three_le_rank_of_rep {g : J} {P : Pair} (hg : Rep Sp φ g P) (h : rows3OK P.1 = true) :
    3 ≤ (φ g - 1).rank := by
  rw [← hg.2.2.1]
  exact three_le_rank_of_rows3 h

theorem rank_conj (c g : J) : (φ (c * g * c⁻¹) - 1).rank = (φ g - 1).rank := by
  have hc : IsUnit (φ c).det := by
    rw [φ_apply]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have hci : IsUnit (φ c⁻¹).det := by
    rw [φ_apply]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have e : φ (c * g * c⁻¹) - 1 = φ c * (φ g - 1) * φ c⁻¹ := by
    have h1 : φ c * φ c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, map_mul, map_mul]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hci,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hc]

theorem Q3GenPairs_eq {i : ℕ} (hi : i < 2) :
    Q3GenPairs[i]! = powP (wordP Xn Yn q3Words[i]!) q3Exps[i]! := by
  interval_cases i <;> rfl

end CFSG.Sporadic.J4Schreier
