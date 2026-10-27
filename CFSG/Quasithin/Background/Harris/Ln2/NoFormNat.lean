module

public import CFSG.Quasithin.Background.Harris.Ln2.NoFormCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix

@[expose] def tv {n : ℕ} (s : Fin n) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  Matrix.transvection 0 s.succ 1

theorem tv_apply {n : ℕ} (s : Fin n) (v : Fin (n + 1) → ZMod 2) :
    tv s *ᵥ v = v + Pi.single 0 (v s.succ) := by
  rw [tv, Matrix.transvection, add_mulVec, one_mulVec, single_mulVec]
  simp
  rfl

theorem tv_mul_self {n : ℕ} (s : Fin n) : tv s * tv s = 1 := by
  rw [tv, transvection_mul_transvection_same _ _ (Fin.succ_ne_zero s).symm 1 1,
    show (1 : ZMod 2) + 1 = 0 from by decide, transvection_zero]

theorem tv_fixed {n : ℕ} {x : Fin (n + 1) → ZMod 2} (hx : ∀ s : Fin n, tv s *ᵥ x = x)
    (s : Fin n) : x s.succ = 0 := by
  have := congr_fun (hx s) 0
  rw [tv_apply] at this
  simpa using this

theorem no_form_nat {n : ℕ} (hn : 2 ≤ n) (f : LinearMap.BilinForm (ZMod 2) (Fin (n + 1) → ZMod 2))
    (hf : f.Nondegenerate) (hinv : ∀ s x y, f (tv s *ᵥ x) (tv s *ᵥ y) = f x y) : False := by
  refine no_form (c := 1) tv (fun s y => ⟨tv s *ᵥ y, ?_⟩) {0} ?_ ?_ ?_ f hf hinv
  · rw [mulVec_mulVec, tv_mul_self, one_mulVec]
  · intro s v q hq
    rw [tv_apply]
    have : q ≠ 0 := by simpa using hq
    simp [this]
  · refine le_trans (Nat.card_le_card_of_injective (fun x => x.1 0) fun a b h => ?_) (by simp)
    refine Subtype.ext (funext fun q => ?_)
    refine Fin.cases h ?_ q
    intro j
    rw [tv_fixed a.2 j, tv_fixed b.2 j]
  · simp; omega

end CFSG.Quasithin.G11.Harris.Ln2
