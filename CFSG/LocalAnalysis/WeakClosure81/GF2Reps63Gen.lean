module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup

variable {Q : Type*} [Group Q]

@[expose] def conjSup (L : Subgroup Q) (a b : Q) : Subgroup Q :=
  L ⊔ L.map (MulAut.conj a).toMonoidHom ⊔ L.map (MulAut.conj b).toMonoidHom ⊔
    L.map (MulAut.conj (a * b)).toMonoidHom

theorem le_conjSup (L : Subgroup Q) (a b : Q) : L ≤ conjSup L a b := by
  rw [conjSup]
  exact le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem commutator_conjSup {L : Subgroup Q} (hperf : ⁅L, L⁆ = L) (a b : Q) :
    ⁅conjSup L a b, conjSup L a b⁆ = conjSup L a b := by
  haveI hLp : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  let fA : Q →* Q := (MulAut.conj a).toMonoidHom
  let fB : Q →* Q := (MulAut.conj b).toMonoidHom
  let fAB : Q →* Q := (MulAut.conj (a * b)).toMonoidHom
  have hA : Group.IsPerfect ↥(L.map fA) := Group.IsPerfect.map (H := L) fA
  have hB : Group.IsPerfect ↥(L.map fB) := Group.IsPerfect.map (H := L) fB
  have hAB : Group.IsPerfect ↥(L.map fAB) := Group.IsPerfect.map (H := L) fAB
  have hAeq : ⁅L.map fA, L.map fA⁆ = L.map fA := Subgroup.isPerfect_iff.mp hA
  have hBeq : ⁅L.map fB, L.map fB⁆ = L.map fB := Subgroup.isPerfect_iff.mp hB
  have hABeq : ⁅L.map fAB, L.map fAB⁆ = L.map fAB := Subgroup.isPerfect_iff.mp hAB
  have hLX : L ≤ ((L ⊔ L.map fA) ⊔ L.map fB) ⊔ L.map fAB :=
    le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hAX : L.map fA ≤ ((L ⊔ L.map fA) ⊔ L.map fB) ⊔ L.map fAB :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hBX : L.map fB ≤ ((L ⊔ L.map fA) ⊔ L.map fB) ⊔ L.map fAB :=
    le_sup_right.trans le_sup_left
  have hABX : L.map fAB ≤ ((L ⊔ L.map fA) ⊔ L.map fB) ⊔ L.map fAB := le_sup_right
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  rw [conjSup]
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact hperf.ge.trans (Subgroup.commutator_mono hLX hLX)
  · exact hAeq.ge.trans (Subgroup.commutator_mono hAX hAX)
  · exact hBeq.ge.trans (Subgroup.commutator_mono hBX hBX)
  · exact hABeq.ge.trans (Subgroup.commutator_mono hABX hABX)

theorem conj_mem_conjSup {L : Subgroup Q} {a b : Q} (ha : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) {x : Q} (hx : x ∈ conjSup L a b) :
    a * x * a⁻¹ ∈ conjSup L a b ∧ b * x * b⁻¹ ∈ conjSup L a b := by
  let fA : Q →* Q := (MulAut.conj a).toMonoidHom
  let fB : Q →* Q := (MulAut.conj b).toMonoidHom
  let fAB : Q →* Q := (MulAut.conj (a * b)).toMonoidHom
  have hconjAA : MulAut.conj a * MulAut.conj a = 1 := by
    rw [← map_mul, ha, map_one]
  have hconjAB : MulAut.conj a * MulAut.conj b = MulAut.conj (a * b) := by
    rw [← map_mul]
  have hconjAAB : MulAut.conj a * MulAut.conj (a * b) = MulAut.conj b := by
    have h : a * (a * b) = b := by
      calc a * (a * b) = (a * a) * b := by group
        _ = b := by rw [ha, one_mul]
    calc MulAut.conj a * MulAut.conj (a * b) = MulAut.conj (a * (a * b)) := by
          rw [← map_mul]
      _ = MulAut.conj b := by rw [h]
  have hconjBB : MulAut.conj b * MulAut.conj b = 1 := by
    rw [← map_mul, hbb, map_one]
  have hconjBA : MulAut.conj b * MulAut.conj a = MulAut.conj (a * b) := by
    calc MulAut.conj b * MulAut.conj a = MulAut.conj (b * a) := by rw [← map_mul]
      _ = MulAut.conj (a * b) := by rw [hab]
  have hconjBAB : MulAut.conj b * MulAut.conj (a * b) = MulAut.conj a := by
    have h : b * (a * b) = a := by
      calc b * (a * b) = (b * a) * b := by group
        _ = (a * b) * b := by rw [hab]
        _ = a * (b * b) := by group
        _ = a := by rw [hbb, mul_one]
    calc MulAut.conj b * MulAut.conj (a * b) = MulAut.conj (b * (a * b)) := by
          rw [← map_mul]
      _ = MulAut.conj a := by rw [h]
  have hcompAA : fA.comp fA = MonoidHom.id Q := by
    ext y
    change (MulAut.conj a * MulAut.conj a) y = y
    rw [hconjAA]
    rfl
  have hcompAB : fA.comp fB = fAB := by
    ext y
    change (MulAut.conj a * MulAut.conj b) y = (MulAut.conj (a * b)) y
    rw [hconjAB]
  have hcompAAB : fA.comp fAB = fB := by
    ext y
    change (MulAut.conj a * MulAut.conj (a * b)) y = (MulAut.conj b) y
    rw [hconjAAB]
  have hcompBB : fB.comp fB = MonoidHom.id Q := by
    ext y
    change (MulAut.conj b * MulAut.conj b) y = y
    rw [hconjBB]
    rfl
  have hcompBA : fB.comp fA = fAB := by
    ext y
    change (MulAut.conj b * MulAut.conj a) y = (MulAut.conj (a * b)) y
    rw [hconjBA]
  have hcompBAB : fB.comp fAB = fA := by
    ext y
    change (MulAut.conj b * MulAut.conj (a * b)) y = (MulAut.conj a) y
    rw [hconjBAB]
  have hmapA : (conjSup L a b).map fA ≤ conjSup L a b := by
    rw [conjSup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rw [hcompAA, hcompAB, hcompAAB]
    simp only [Subgroup.map_id]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (le_sup_right : L.map fA ≤ L ⊔ L.map fA).trans
        (le_sup_left.trans le_sup_left)
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right
    · exact (le_sup_right : L.map fB ≤ (L ⊔ L.map fA) ⊔ L.map fB).trans le_sup_left
  have hmapB : (conjSup L a b).map fB ≤ conjSup L a b := by
    rw [conjSup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rw [hcompBA, hcompBB, hcompBAB]
    simp only [Subgroup.map_id]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (le_sup_right : L.map fB ≤ (L ⊔ L.map fA) ⊔ L.map fB).trans le_sup_left
    · exact le_sup_right
    · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
    · exact (le_sup_right : L.map fA ≤ L ⊔ L.map fA).trans
        (le_sup_left.trans le_sup_left)
  constructor
  · have h : fA x ∈ conjSup L a b := hmapA (Subgroup.mem_map_of_mem fA hx)
    simpa [fA, MulAut.conj_apply] using h
  · have h : fB x ∈ conjSup L a b := hmapB (Subgroup.mem_map_of_mem fB hx)
    exact h

theorem conjSup_le_closure {L : Subgroup Q} {a b g : Q} (ha : a * a = 1) (hab : a * b = b * a)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x) (hgL : g ∈ L)
    (hLg : L ≤ closure {z | ∃ y ∈ L, z = y * g * y⁻¹ * g⁻¹}) :
    conjSup L a b ≤ closure ((fun y => y * (a * y * a)) '' (L : Set Q) ∪ {b} ∪
      (fun y => g * (y * (a * y * a)) * g⁻¹) '' (L : Set Q)) := by
  let fA : Q →* Q := (MulAut.conj a).toMonoidHom
  let fB : Q →* Q := (MulAut.conj b).toMonoidHom
  let fAB : Q →* Q := (MulAut.conj (a * b)).toMonoidHom
  set S : Set Q := (fun y => y * (a * y * a)) '' (L : Set Q) ∪ {b} ∪
      (fun y => g * (y * (a * y * a)) * g⁻¹) '' (L : Set Q) with hS
  change conjSup L a b ≤ closure S
  set C : Subgroup Q := closure S with hC
  have hψmem : ∀ y ∈ L, y * (a * y * a) ∈ S := by
    intro y hy
    rw [hS]
    exact Or.inl (Or.inl ⟨y, hy, rfl⟩)
  have hgψmem : ∀ y ∈ L, g * (y * (a * y * a)) * g⁻¹ ∈ S := by
    intro y hy
    rw [hS]
    exact Or.inr ⟨y, hy, rfl⟩
  have hbmem : b ∈ S := by
    rw [hS]
    exact Or.inl (Or.inr rfl)
  have hLC : L ≤ C := by
    have hD : closure {z | ∃ y ∈ L, z = y * g * y⁻¹ * g⁻¹} ≤ C := by
      rw [Subgroup.closure_le]
      rintro z ⟨y, hy, rfl⟩
      have hψC : y * (a * y * a) ∈ C := Subgroup.subset_closure (hψmem y hy)
      have hgψC : g * (y * (a * y * a)) * g⁻¹ ∈ C :=
        Subgroup.subset_closure (hgψmem y hy)
      have hcommC : g * (y * (a * y * a)) * g⁻¹ * (y * (a * y * a))⁻¹ ∈ C :=
        mul_mem hgψC (inv_mem hψC)
      have hgy : (a * y * a) * g⁻¹ = g⁻¹ * (a * y * a) :=
        (hLa (g⁻¹) (L.inv_mem hgL) y hy).symm
      have heq : g * (y * (a * y * a)) * g⁻¹ * (y * (a * y * a))⁻¹ =
          g * y * g⁻¹ * y⁻¹ := by
        have hfac : ∀ u : Q, u * g⁻¹ = g⁻¹ * u →
            g * y * u * g⁻¹ * u⁻¹ * y⁻¹ = g * y * g⁻¹ * y⁻¹ := by
          intro u hu
          calc
            g * y * u * g⁻¹ * u⁻¹ * y⁻¹ = g * y * (u * g⁻¹) * u⁻¹ * y⁻¹ := by
              group
            _ = g * y * (g⁻¹ * u) * u⁻¹ * y⁻¹ := by rw [hu]
            _ = g * y * g⁻¹ * y⁻¹ := by group
        simpa [mul_inv_rev, mul_assoc] using hfac (a * y * a) hgy
      have h1 : g * y * g⁻¹ * y⁻¹ ∈ C := by
        rw [heq] at hcommC
        exact hcommC
      have h2 : (g * y * g⁻¹ * y⁻¹)⁻¹ ∈ C := inv_mem h1
      simpa [mul_inv_rev, mul_assoc] using h2
    exact hLg.trans hD
  have hpsiC : ∀ y ∈ L, a * y * a ∈ C := by
    intro y hy
    have hyC : y ∈ C := hLC hy
    have hψC : y * (a * y * a) ∈ C := Subgroup.subset_closure (hψmem y hy)
    have h : y⁻¹ * (y * (a * y * a)) ∈ C := mul_mem (inv_mem hyC) hψC
    simpa [mul_assoc] using h
  have hmapA : L.map fA ≤ C := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    have h : a * y * a ∈ C := hpsiC y hy
    simpa [fA, MulAut.conj_apply, inv_eq_of_mul_eq_one_right ha] using h
  have hbC : b ∈ C := Subgroup.subset_closure hbmem
  have hmapB : L.map fB ≤ C := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    have hyC : y ∈ C := hLC hy
    have h : b * y * b⁻¹ ∈ C := mul_mem (mul_mem hbC hyC) (inv_mem hbC)
    exact h
  have hmapAB : L.map fAB ≤ C := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    have h : b * (a * y * a) * b⁻¹ ∈ C :=
      mul_mem (mul_mem hbC (hpsiC y hy)) (inv_mem hbC)
    have heq : (a * b) * y * (a * b)⁻¹ = b * (a * y * a) * b⁻¹ := by
      rw [hab, mul_inv_rev, inv_eq_of_mul_eq_one_right ha]
      group
    have : (a * b) * y * (a * b)⁻¹ ∈ C := by
      rw [heq]
      exact h
    exact this
  rw [conjSup]
  exact sup_le (sup_le (sup_le hLC hmapA) hmapB) hmapAB

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
