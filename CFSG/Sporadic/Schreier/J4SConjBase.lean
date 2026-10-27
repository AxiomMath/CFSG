
module

public import CFSG.Sporadic.Schreier.J4SBinaryBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem toVecD_app11_comp11 (C D : Array ℕ) (a : ℕ) :
    toVecD 11 (app11 (comp11 C D) a) = toVecD 11 (app11 C (app11 D a)) := by
  rw [← colsMatrix_mulVec, ← colsMatrix_mulVec, ← colsMatrix_mulVec, colsMatrix_comp11,
    Matrix.mulVec_mulVec]

theorem toVecD_app11_idRows (a : ℕ) : toVecD 11 (app11 (idRows 11) a) = toVecD 11 a := by
  rw [← colsMatrix_mulVec, colsMatrix_idRows, Matrix.one_mulVec]

@[expose] def letterApp (l : ℤ) (a : ℕ) : ℕ :=
  if l = 1 then app11 xColumns a else if l = -1 then app11 xInvColumns a
  else if l = 2 then app11 yColumns a else if l = -2 then app11 yInvColumns a else a

@[expose] def app11W : List ℤ → ℕ → ℕ
  | [], a => a
  | l :: w, a => letterApp l (app11W w a)

abbrev NN : Subgroup J := Subgroup.normalizer (N : Set J)

theorem mem_normalizer_N_of {g : J} (hg : ∀ j : Fin 11, g * u j * g⁻¹ ∈ N) :
    g ∈ NN := by
  have fwd : ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro n hn
    induction hn using Subgroup.closure_induction with
    | mem n hn =>
      obtain ⟨j, rfl⟩ := hn
      exact hg j
    | one => rw [mul_one, mul_inv_cancel]; exact N.one_mem
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact N.mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem ha
  have hf : Function.Injective (fun n : N => (⟨g * n * g⁻¹, fwd n n.2⟩ : N)) := by
    intro a b hab
    have h := Subtype.ext_iff.1 hab
    dsimp only at h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have hs := Finite.injective_iff_surjective.1 hf
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fwd n, fun hn => ?_⟩
  obtain ⟨m, hm⟩ := hs ⟨g * n * g⁻¹, hn⟩
  have e := Subtype.ext_iff.1 hm
  dsimp only at e
  have e2 : (m : J) = n := mul_left_cancel (mul_right_cancel e)
  rw [← e2]
  exact m.2

end CFSG.Sporadic.J4Schreier
