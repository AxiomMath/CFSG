module

public import Certificates.Certificate272032
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple
import all CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Sporadic.Th

noncomputable def letG (z : ℤ) : J3Model :=
  if 0 < z then uN (z - 1).toNat else (uN (-z - 1).toNat)⁻¹

theorem lift_letter (i : Fin 7) (s : Bool) :
    FreeGroup.lift uJ (FreeGroup.mk [(i, s)]) =
      letG (if s then (i.val : ℤ) + 1 else -((i.val : ℤ) + 1)) := by
  cases s
  · simp [letG, uJ]
  · simp [letG, uJ]

theorem lift_eq (r : List (Fin 7 × Bool)) :
    FreeGroup.lift uJ (FreeGroup.mk r) = wordG letG (encodeWord r) := by
  induction r with
  | nil => simp [wordG, encodeWord]
  | cons x r ih =>
    obtain ⟨i, s⟩ := x
    have e1 : (i, s) :: r = [(i, s)] ++ r := rfl
    rw [e1, ← FreeGroup.mul_mk, map_mul, ih]
    have e2 : wordG letG (encodeWord ([(i, s)] ++ r)) =
        letG (if s then (i.val : ℤ) + 1 else -((i.val : ℤ) + 1)) * wordG letG (encodeWord r) := by
      simp only [wordG, encodeWord, List.cons_append, List.nil_append, List.map_cons,
        List.prod_cons]
    rw [e2, lift_letter]

theorem letG_mem {z : ℤ} (hz : 1 ≤ z.natAbs ∧ z.natAbs ≤ 7) :
    letG z ∈ Subgroup.closure (Set.range uJ) := by
  unfold letG
  split_ifs with h
  · have hk : (z - 1).toNat < 7 := by omega
    exact Subgroup.subset_closure ⟨⟨(z - 1).toNat, hk⟩, rfl⟩
  · have hk : (-z - 1).toNat < 7 := by omega
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨(-z - 1).toNat, hk⟩, rfl⟩)


theorem uJ_satisfies : SatisfiesJ3Words uJ := Certificates.certificate272032.1

theorem closure_uJ : Subgroup.closure (Set.range uJ) = ⊤ := Certificates.certificate272032.2

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
