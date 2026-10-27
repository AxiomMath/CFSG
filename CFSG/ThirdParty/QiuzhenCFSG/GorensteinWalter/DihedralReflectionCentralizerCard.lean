module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizers of reflections in even dihedral groups

When the rotation parameter is even and nonzero, an element commuting with a
fixed reflection has one of at most four forms: the identity or half-turn
rotation, or one of the two corresponding reflections.
-/

namespace CFSG.GorensteinWalter

/-- A reflection centralizer in `Dih(2k)` has at most four elements when
`k` is nonzero. -/
public theorem card_centralizer_reflection_dihedral_even_le_four
    {k : ℕ} [NeZero k] (j : ZMod (2 * k)) :
    Nat.card (Subgroup.centralizer
      ({DihedralGroup.sr j} : Set (DihedralGroup (2 * k)))) ≤ 4 := by
  classical
  let h : ZMod (2 * k) := k
  let C : Subgroup (DihedralGroup (2 * k)) :=
    Subgroup.centralizer
      ({DihedralGroup.sr j} : Set (DihedralGroup (2 * k)))
  have htwo_iff (i : ZMod (2 * k)) :
      (2 : ZMod (2 * k)) * i = 0 ↔ i = 0 ∨ i = h := by
    constructor
    · intro hi
      let v : ℕ := i.val
      have hieq : i = (v : ZMod (2 * k)) :=
        (ZMod.natCast_zmod_val i).symm
      have hcast : (((2 * v : ℕ) : ZMod (2 * k))) = 0 := by
        simpa [hieq, Nat.cast_mul] using hi
      have hdvd : 2 * k ∣ 2 * v :=
        (ZMod.natCast_eq_zero_iff (2 * v) (2 * k)).mp hcast
      have hkdvd : k ∣ v :=
        Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
      rcases hkdvd with ⟨a, ha⟩
      have hvlt : v < 2 * k := ZMod.val_lt i
      have hkpos : 0 < k := NeZero.pos k
      have halt : a < 2 := by
        rw [ha] at hvlt
        nlinarith
      have ha_cases : a = 0 ∨ a = 1 := by omega
      rcases ha_cases with ha0 | ha1
      · left
        rw [hieq, ha, ha0]
        simp
      · right
        rw [hieq, ha, ha1]
        simp [h]
    · rintro (rfl | rfl)
      · simp
      · dsimp [h]
        calc
          (2 : ZMod (2 * k)) * (k : ZMod (2 * k)) =
              ((2 * k : ℕ) : ZMod (2 * k)) := by
            push_cast
            rfl
          _ = 0 := ZMod.natCast_self (2 * k)
  have hsubset : (C : Set (DihedralGroup (2 * k))) ⊆
      {DihedralGroup.r 0, DihedralGroup.r h,
        DihedralGroup.sr j, DihedralGroup.sr (j + h)} := by
    intro x hx
    have hcomm : DihedralGroup.sr j * x = x * DihedralGroup.sr j :=
      (Subgroup.mem_centralizer_iff.mp hx)
        (DihedralGroup.sr j) (by simp)
    rcases x with i | i
    · have hji : j + i = j - i := DihedralGroup.sr.inj hcomm
      have h2i : (2 : ZMod (2 * k)) * i = 0 := by
        calc
          (2 : ZMod (2 * k)) * i = i + i := by ring
          _ = (j + i) - j + i := by abel
          _ = (j - i) - j + i := by rw [hji]
          _ = 0 := by abel
      rcases (htwo_iff i).mp h2i with hi0 | hih
      · simp [hi0]
      · simp [hih]
    · have hij : i - j = j - i := DihedralGroup.r.inj hcomm
      have h2ij : (2 : ZMod (2 * k)) * (i - j) = 0 := by
        calc
          (2 : ZMod (2 * k)) * (i - j) =
              (i - j) + (i - j) := by ring
          _ = (i - j) + (j - i) := by rw [hij]
          _ = 0 := by abel
      rcases (htwo_iff (i - j)).mp h2ij with h0 | hh
      · have hi : i = j := sub_eq_zero.mp h0
        simp [hi]
      · have hi : i = j + h := by
          calc
            i = (i - j) + j := by abel
            _ = h + j := by rw [hh]
            _ = j + h := by rw [add_comm]
        simp [hi]
  calc
    Nat.card C = (C : Set (DihedralGroup (2 * k))).ncard :=
      Nat.card_coe_set_eq (C : Set (DihedralGroup (2 * k)))
    _ ≤ Set.ncard
          ({DihedralGroup.r 0, DihedralGroup.r h,
            DihedralGroup.sr j, DihedralGroup.sr (j + h)} :
            Set (DihedralGroup (2 * k))) :=
      Set.ncard_le_ncard hsubset
    _ ≤ 4 := by
      calc
        _ ≤ Set.ncard
              ({DihedralGroup.r h, DihedralGroup.sr j,
                DihedralGroup.sr (j + h)} :
                Set (DihedralGroup (2 * k))) + 1 :=
          Set.ncard_insert_le _ _
        _ ≤ (Set.ncard
              ({DihedralGroup.sr j, DihedralGroup.sr (j + h)} :
                Set (DihedralGroup (2 * k))) + 1) + 1 := by
          exact Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
        _ ≤ ((Set.ncard
              ({DihedralGroup.sr (j + h)} :
                Set (DihedralGroup (2 * k))) + 1) + 1) + 1 := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1
        _ = 4 := by simp

end CFSG.GorensteinWalter
