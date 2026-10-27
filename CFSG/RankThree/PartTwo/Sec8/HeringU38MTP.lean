module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MF4

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

@[expose] def Eich (a b : F) : Mat3 := ⟨1 + b, b, cj a, b, 1 + b, cj a, a, a, 1⟩

@[expose] def T0list : List Mat3 :=
  [Eich 0 0, Eich 0 1, Eich 1 ωF, Eich 1 ω2F, Eich ωF ωF, Eich ωF ω2F, Eich ω2F ωF,
    Eich ω2F ω2F]

@[expose] def Dg (l m : F) : Mat3 := Mat3.diag l l m

theorem T0_len : T0list.length = 8 := by decide +kernel

theorem T0_nodup : T0list.Nodup := by decide +kernel

theorem T0_unit : ∀ M ∈ T0list, IsU M ∧ M.det = 1 := by decide +kernel

theorem T0_one : (1 : Mat3) ∈ T0list := by decide +kernel

theorem T0_mul : ∀ M ∈ T0list, ∀ N ∈ T0list, M * N ∈ T0list := by decide +kernel

theorem T0_cjT : ∀ M ∈ T0list, M.cjT ∈ T0list := by decide +kernel

theorem T0_conj : ∀ l ∈ allF, ∀ m ∈ allF, l ≠ 0 → m ≠ 0 →
    ∀ M ∈ T0list, Dg l m * M * (Dg l m).cjT ∈ T0list := by decide +kernel

theorem T0_comm : ∀ l ∈ allF, ∀ m ∈ allF, l ≠ 0 → m ≠ 0 → l ≠ m →
    ∀ M ∈ T0list, ∃ t1 ∈ T0list, ∃ t2 ∈ T0list,
      M = Mat3.commGen (Dg l m) t1 * Mat3.commGen (Dg l m) t2 := by decide +kernel

@[expose] def x0 : Mat3 := Mat3.diag ωF ω2F 1

@[expose] def x0i : Mat3 := Mat3.diag ω2F ωF 1

@[expose] def piM : Mat3 := ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩

@[expose] def zM : Mat3 := Mat3.smul ω2F 1

@[expose] def P0list : List Mat3 :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    (List.range 3).map fun k => zM ^ i * x0 ^ j * piM ^ k

theorem P0_len : P0list.length = 27 := by decide +kernel

theorem P0_nodup : P0list.Nodup := by decide +kernel

theorem P0_unit : ∀ M ∈ P0list, IsU M ∧ M.det = 1 := by decide +kernel

theorem P0_one : (1 : Mat3) ∈ P0list := by decide +kernel

theorem P0_mul : ∀ M ∈ P0list, ∀ N ∈ P0list, M * N ∈ P0list := by decide +kernel

theorem P0_cjT : ∀ M ∈ P0list, M.cjT ∈ P0list := by decide +kernel

theorem P0_conj : ∀ t ∈ T0list, ∀ p ∈ P0list, t * p * t.cjT ∈ P0list := by decide +kernel

theorem P0_form : ∀ p ∈ P0list, ∃ i < 3, ∃ j < 3, ∃ k < 3, p = zM ^ i * x0 ^ j * piM ^ k := by
  intro p hp
  simp only [P0list, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := hp
  exact ⟨i, hi, j, hj, k, hk, rfl⟩

theorem T0_normalizes_x0 : Eich 1 ωF * x0 * (Eich 1 ωF).cjT = piM := by decide +kernel

theorem Eich_mem : Eich 1 ωF ∈ T0list := by decide +kernel

theorem comm_pi_x0 : piM * x0 * piM.cjT * x0.cjT = zM := by decide +kernel

theorem x0_x0i : x0 * x0i = 1 ∧ x0i * x0 = 1 := by decide +kernel

theorem x0_unit : IsU x0 ∧ x0.det = 1 := by decide +kernel

theorem x0i_unit : IsU x0i ∧ x0i.det = 1 := by decide +kernel

theorem piM_unit : IsU piM ∧ piM.det = 1 := by decide +kernel

theorem zM_unit : IsU zM ∧ zM.det = 1 := by decide +kernel

@[expose] def blk (a b c d : F) : Mat3 := ⟨a, b, 0, c, d, 0, 0, 0, 1⟩

theorem su2_cls : ∀ a ∈ allF, ∀ b ∈ allF, ∀ c ∈ allF, ∀ d ∈ allF, IsU (blk a b c d) →
    (blk a b c d).det = 1 → blk a b c d * blk a b c d * blk a b c d = 1 → blk a b c d ≠ 1 →
      blk a b c d = x0 ∨ blk a b c d = x0i := by decide +kernel

@[expose] def s1 : Mat3 := ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] def s2 : Mat3 := ⟨0, ω2F, 0, ωF, 0, 0, 0, 0, 1⟩

theorem s_unit : IsU s1 ∧ s1.det = 1 ∧ s1 * s1 = 1 ∧ IsU s2 ∧ s2.det = 1 ∧ s2 * s2 = 1 := by
  decide +kernel

theorem x0_eq : x0 = s1 * s2 := by decide +kernel

theorem x0i_eq : x0i = s2 * s1 := by decide +kernel

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
