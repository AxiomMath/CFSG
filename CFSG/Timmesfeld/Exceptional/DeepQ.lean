module

public import CFSG.Timmesfeld.Exceptional.DeepQWalk
public meta import CFSG.Timmesfeld.Exceptional.DeepQData
public meta import CFSG.Certificates.CosetTableWalkC
public import CFSG.Timmesfeld.Exceptional.DeepQInputs
public import Certificates.Certificate8054
public import Certificates.Certificate8055
public import Certificates.Certificate8056
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableWalkC
public meta import CFSG.Certificates.WordPresentation
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Certificates CFSG.CosetTable

theorem checks :
    (Finite (PG (subsetOf 3 [0, 1]).length relsAB) ∧
        Nat.card (PG (subsetOf 3 [0, 1]).length relsAB) ≤ 360) ∧
      (Finite (PG 3 (relsQ ++ [wQC3])) ∧ Nat.card (PG 3 (relsQ ++ [wQC3])) ≤ 1) ∧
      (∀ r ∈ relsQ, signedProd psi r = 1) ∧ signedProd psi wQC6 = 1 ∧
      ∀ i j : Fin 360, signedProd psi (w3 i) = signedProd psi (w3 j) → i = j :=
  Certificates.certificate8054

theorem lift_eq_one_of {m : ℕ} {K : Type*} [Group K] {ws : List (List (Fin m × Bool))}
    (x : Fin m → K) (hx : ∀ r ∈ ws, signedProd x r = 1) :
    ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift x r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk_eq_signedProd]
  exact hx w hw

noncomputable def pgHom {m : ℕ} {K : Type*} [Group K] (ws : List (List (Fin m × Bool)))
    (x : Fin m → K) (hx : ∀ r ∈ ws, signedProd x r = 1) : PG m ws →* K :=
  PresentedGroup.toGroup (lift_eq_one_of x hx)

theorem pgHom_mk {m : ℕ} {K : Type*} [Group K] (ws : List (List (Fin m × Bool)))
    (x : Fin m → K) (hx : ∀ r ∈ ws, signedProd x r = 1) (w : List (Fin m × Bool)) :
    pgHom ws x hx (PresentedGroup.mk _ (FreeGroup.mk w)) = signedProd x w := by
  rw [← lift_mk_eq_signedProd]
  rfl

theorem pgHom_of {m : ℕ} {K : Type*} [Group K] (ws : List (List (Fin m × Bool)))
    (x : Fin m → K) (hx : ∀ r ∈ ws, signedProd x r = 1) (i : Fin m) :
    pgHom ws x hx (PresentedGroup.of i) = x i :=
  PresentedGroup.toGroup.of _

noncomputable abbrev subAB : Subgroup (PG 3 relsQ) :=
  genSub {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk} (subsetOf 3 [0, 1])

theorem subsetOf_ab : subsetOf 3 [0, 1] = [0, 1] := by decide

theorem mk_mem_subAB {w : List (Fin 3 × Bool)} (hw : ∀ l ∈ w, l.1.val < 2) :
    PresentedGroup.mk _ (FreeGroup.mk w) ∈ subAB := by
  induction w with
  | nil => exact subAB.one_mem
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    refine subAB.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have hl : l.1 ∈ subsetOf 3 [0, 1] := by
      have := hw l List.mem_cons_self
      rw [subsetOf_ab]
      obtain ⟨⟨i, hi⟩, b⟩ := l
      interval_cases i <;> simp_all
    have hof : PresentedGroup.of (rels := {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk})
        l.1 ∈ subAB := Subgroup.subset_closure ⟨l.1, hl, rfl⟩
    obtain ⟨i, b⟩ := l
    cases b with
    | true => exact hof
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv]
      exact subAB.inv_mem hof

noncomputable def psiHom :
    PG 3 relsQ →* Equiv.Perm (Fin 162) := pgHom relsQ psi checks.2.2.1

noncomputable def pi360 (i : Fin 360) : subAB :=
  ⟨PresentedGroup.mk _ (FreeGroup.mk (w3 i)), mk_mem_subAB fun l hl => by
    simp only [w3, List.mem_map] at hl
    obtain ⟨k, -, rfl⟩ := hl
    exact k.isLt⟩

theorem psiHom_pi360
    (i : Fin 360) : psiHom (pi360 i) = signedProd psi (w3 i) :=
  pgHom_mk _ _ _ _

theorem w3_zero : w3 0 = [] := rfl

theorem card_subAB_le
    : Finite subAB ∧ Nat.card subAB ≤ 360 := by
  obtain ⟨hf, hc⟩ := checks.1
  obtain ⟨hf', hc'⟩ := card_genSub_le relsQ (subsetOf 3 [0, 1])
  exact ⟨hf', hc'.trans hc⟩

theorem psiHom_injOn
    {g : PG 3 relsQ} (hg : g ∈ subAB) (h1 : psiHom g = 1) : g = 1 := by
  obtain ⟨hfin, hcard⟩ := card_subAB_le
  have hinj : Function.Injective pi360 := fun i j h =>
    checks.2.2.2.2 i j (by rw [← psiHom_pi360, ← psiHom_pi360, h])
  have hbij := hinj.bijective_of_nat_card_le (by simpa using hcard)
  obtain ⟨i, hi⟩ := hbij.2 ⟨g, hg⟩
  have hgi : g = (pi360 i : PG 3 relsQ) := by rw [hi]
  rw [hgi, psiHom_pi360] at h1
  have hi0 : i = 0 := checks.2.2.2.2 i 0 (by rw [h1, w3_zero, signedProd_nil])
  rw [hgi, hi0]
  show PresentedGroup.mk _ (FreeGroup.mk (w3 0)) = 1
  rw [w3_zero]
  rfl

theorem mk_wQC6
    :
    PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk}
    (FreeGroup.mk wQC6) = 1 := by
  refine psiHom_injOn walk ?_
  rw [psiHom, pgHom_mk]
  exact checks.2.2.2.1

theorem signedProd_wQC6
    {K : Type*} [Group K] (x : Fin 3 → K)
    (hx : ∀ r ∈ relsQ, signedProd x r = 1) : signedProd x wQC6 = 1 := by
  rw [← pgHom_mk relsQ x hx, mk_wQC6, map_one]

theorem eq_one_of_wQC3
    {K : Type*} [Group K] (x : Fin 3 → K)
    (hx : ∀ r ∈ relsQ, signedProd x r = 1) (h3 : signedProd x wQC3 = 1) (i : Fin 3) :
    x i = 1 := by
  obtain ⟨hf, hc⟩ := checks.2.1
  have hx' : ∀ r ∈ relsQ ++ [wQC3], signedProd x r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hx r hr
    · rw [List.mem_singleton.1 hr]
      exact h3
  have hsub : Subsingleton (PG 3 (relsQ ++ [wQC3])) := Finite.card_le_one_iff_subsingleton.1 hc
  rw [← pgHom_of _ x hx' i, Subsingleton.elim (PresentedGroup.of i) 1, map_one]

end CFSG.Timmesfeld.Moufang.Deep
