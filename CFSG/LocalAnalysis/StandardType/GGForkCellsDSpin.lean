module

public import CFSG.LocalAnalysis.StandardType.GGForkNullPosTail
public import CFSG.LocalAnalysis.StandardType.GGForkCellsDLeaf

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNoNullPos_D5_3 : ¬ GGAttachNullPos (CartanMatrix.D 5) 3 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 1 | some i => ![1, 2, 3, 2, 2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D5_4 : ¬ GGAttachNullPos (CartanMatrix.D 5) 4 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 1 | some i => ![1, 2, 3, 2, 2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D6_4 : ¬ GGAttachNullPos (CartanMatrix.D 6) 4 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 2 | some i => ![1, 2, 3, 4, 3, 2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D6_5 : ¬ GGAttachNullPos (CartanMatrix.D 6) 5 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 2 | some i => ![1, 2, 3, 4, 2, 3] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D7_5 : ¬ GGAttachNullPos (CartanMatrix.D 7) 5 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 2 | some i => ![2, 3, 4, 5, 6, 4, 3] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D7_6 : ¬ GGAttachNullPos (CartanMatrix.D 7) 6 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 2 | some i => ![2, 3, 4, 5, 6, 3, 4] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D_center (m : ℕ) :
    ¬ GGAttachNullPos (CartanMatrix.D (m + 5)) ⟨m + 2, by omega⟩ :=
  ggAttachNullPos_false_of_tail (CartanMatrix.D (m + 5)) ⟨m + 2, by omega⟩
    (fun i j hij => CartanMatrix.D_off_diag_nonpos _ i j hij)
    (CartanMatrix.D 5) 2 (Fin.natAddEmb m)
    (fun i j => cartanMatrix_D_natAdd m (by norm_num) i j)
    (Fin.ext (by simp [Fin.natAddEmb_apply]))
    (fun | none => -1 | some i => ![0, -1, -2, -1, -1] i)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D_spin_far (m : ℕ) {i : Fin (m + 9)} (hi : i.val = m + 7 ∨ i.val = m + 8) :
    ¬ GGAttachNullPos (CartanMatrix.D (m + 9)) i := by
  rcases hi with hi | hi
  · exact ggAttachNullPos_false_of_tail (CartanMatrix.D (m + 9)) i
      (fun a b hab => CartanMatrix.D_off_diag_nonpos _ a b hab)
      (CartanMatrix.D 9) 7 (Fin.natAddEmb m)
      (fun a b => cartanMatrix_D_natAdd m (by norm_num) a b)
      (Fin.ext (by simpa [Fin.natAddEmb_apply] using hi))
      (fun | none => -2 | some a => ![0, -1, -2, -3, -4, -5, -6, -4, -3] a)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ggAttachNullPos_false_of_tail (CartanMatrix.D (m + 9)) i
      (fun a b hab => CartanMatrix.D_off_diag_nonpos _ a b hab)
      (CartanMatrix.D 9) 8 (Fin.natAddEmb m)
      (fun a b => cartanMatrix_D_natAdd m (by norm_num) a b)
      (Fin.ext (by simpa [Fin.natAddEmb_apply] using hi))
      (fun | none => -2 | some a => ![0, -1, -2, -3, -4, -5, -6, -3, -4] a)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_D_spin (m : ℕ) (hm : m ≠ 3) {i : Fin (m + 5)}
    (hi : i.val = m + 3 ∨ i.val = m + 4) : ¬ GGAttachNullPos (CartanMatrix.D (m + 5)) i := by
  rcases m with _ | _ | _ | _ | m'
  · rcases hi with hi | hi
    · have hii : i = (3 : Fin (0 + 5)) := Fin.ext (by rw [hi]; simp)
      rw [hii]
      exact ggNoNullPos_D5_3
    · have hii : i = (4 : Fin (0 + 5)) := Fin.ext (by rw [hi]; simp)
      rw [hii]
      exact ggNoNullPos_D5_4
  · rcases hi with hi | hi
    · have hii : i = (4 : Fin (1 + 5)) := Fin.ext (by rw [hi]; simp)
      rw [hii]
      exact ggNoNullPos_D6_4
    · have hii : i = (5 : Fin (1 + 5)) := Fin.ext (by rw [hi]; simp)
      rw [hii]
      exact ggNoNullPos_D6_5
  · rcases hi with hi | hi
    · have hii : i = (5 : Fin (2 + 5)) := Fin.ext (by rw [hi]; simp)
      rw [hii]
      exact ggNoNullPos_D7_5
    · have hii : i = (6 : Fin (2 + 5)) := Fin.ext (by rw [hi]; simp)
      rw [hii]
      exact ggNoNullPos_D7_6
  · exact absurd rfl hm
  · exact ggNoNullPos_D_spin_far m' hi

end CFSG.StandardType
