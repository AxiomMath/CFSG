module

public import CFSG.Monster.GMS.Leech.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement Matrix

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

@[expose] def typeSet (i : Fin 3) : Set G := {g | g ∈ leechQ z ∧ L.vec g ∈ co1Orbit i}

theorem mem_typeSet {i : Fin 3} {g : G} :
    g ∈ L.typeSet i ↔ g ∈ leechQ z ∧ L.vec g ∈ co1Orbit i := Iff.rfl

include L

theorem typeSet_subset (i : Fin 3) : L.typeSet i ⊆ leechQ z := fun _ h => h.1

theorem vec_ne_zero_of_mem_typeSet {i : Fin 3} {g : G} (h : g ∈ L.typeSet i) : L.vec g ≠ 0 :=
  Leech.ne_zero_of_mem_co1Orbit h.2

theorem ne_one_of_mem_typeSet {i : Fin 3} {g : G} (h : g ∈ L.typeSet i) : g ≠ 1 :=
  ((L.vec_ne_zero_iff h.1).1 (L.vec_ne_zero_of_mem_typeSet h)).1

theorem ne_z_of_mem_typeSet {i : Fin 3} {g : G} (h : g ∈ L.typeSet i) : g ≠ z :=
  ((L.vec_ne_zero_iff h.1).1 (L.vec_ne_zero_of_mem_typeSet h)).2

theorem exists_mem_typeSet
    {q : G} (hq : q ∈ leechQ z) (h1 : q ≠ 1) (hz : q ≠ z) :
    ∃ i, q ∈ L.typeSet i := by
  have hv := (L.vec_ne_zero_iff hq).2 ⟨h1, hz⟩
  obtain ⟨i, hi, -⟩ := Leech.existsUnique_co1Orbit hv
  exact ⟨i, hq, hi⟩

theorem disjoint_typeSet
    {i j : Fin 3} (hij : i ≠ j) : Disjoint (L.typeSet i) (L.typeSet j) := by
  rw [Set.disjoint_left]
  intro g hi hj
  obtain ⟨k, -, huniq⟩ := Leech.existsUnique_co1Orbit (L.vec_ne_zero_of_mem_typeSet hi)
  exact hij ((huniq i hi.2).trans (huniq j hj.2).symm)

theorem mul_z_mem_typeSet {i : Fin 3} {q : G} (hq : q ∈ L.typeSet i) : q * z ∈ L.typeSet i :=
  ⟨mul_mem hq.1 L.z_mem, by rw [L.vec_mul_z hq.1]; exact hq.2⟩

theorem conj_mem_typeSet {i : Fin 3} {q g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hq : q ∈ L.typeSet i) : g * q * g⁻¹ ∈ L.typeSet i :=
  ⟨L.conj_mem' hg hq.1, by rw [L.vec_conj' hg hq.1]; exact Leech.co1Act_mem_co1Orbit hq.2 _⟩

theorem exists_conj_of_mem_typeSet
    {i : Fin 3} {q q' : G} (hq : q ∈ L.typeSet i)
    (hq' : q' ∈ L.typeSet i) :
    ∃ g ∈ Subgroup.centralizer ({z} : Set G), g * q * g⁻¹ = q' := by
  obtain ⟨x, hx⟩ := Leech.exists_co1Act_eq hq.2 hq'.2
  obtain ⟨c, rfl⟩ := L.φ_surj x
  have hind : LinearIndependent (ZMod 2) fun _ : Unit => L.vec q' :=
    linearIndependent_unique_iff.2 (L.vec_ne_zero_of_mem_typeSet hq')
  obtain ⟨p, hp, hpa⟩ := L.exists_conj_eq (a := fun _ : Unit => (c : G) * q * (c : G)⁻¹)
    (b := fun _ : Unit => q') (fun _ => L.conj_mem c hq.1) (fun _ => hq'.1)
    (fun _ => by rw [L.vec_conj c q hq.1, hx]) hind
  refine ⟨p * c, mul_mem (L.mem_centralizer hp) c.2, ?_⟩
  calc p * c * q * (p * c)⁻¹ = p * ((c : G) * q * (c : G)⁻¹) * p⁻¹ := by group
    _ = q' := hpa ()

theorem ncard_typeSet (i : Fin 3) : (L.typeSet i).ncard = 2 * (co1Orbit i).ncard :=
  L.ncard_preimage (co1Orbit i)

theorem mul_self_of_mem_typeSet_zero
    {q : G} (hq : q ∈ L.typeSet 0) : q * q = 1 :=
  (L.mul_self_eq_one_iff hq.1).2 (Leech.q₀_eq_zero_of_mem_co1Orbit_zero hq.2)

theorem mul_self_of_mem_typeSet_two
    {q : G} (hq : q ∈ L.typeSet 2) : q * q = 1 :=
  (L.mul_self_eq_one_iff hq.1).2 (Leech.q₀_eq_zero_of_mem_co1Orbit_two hq.2)

theorem mul_self_of_mem_typeSet_one
    {q : G} (hq : q ∈ L.typeSet 1) : q * q = z :=
  (L.mul_self_eq_z_iff hq.1).2 (Leech.q₀_eq_one_of_mem_co1Orbit_one hq.2)

theorem mem_typeSet_zero_or_two
    {q : G} (hq : q ∈ leechQ z) (h1 : q ≠ 1) (hz : q ≠ z)
    (hsq : q * q = 1) : q ∈ L.typeSet 0 ∨ q ∈ L.typeSet 2 := by
  obtain ⟨i, hi⟩ := L.exists_mem_typeSet hq h1 hz
  fin_cases i
  · exact Or.inl hi
  · exfalso
    have := L.mul_self_of_mem_typeSet_one hi
    rw [hsq] at this
    exact L.z_ne_one this.symm
  · exact Or.inr hi

theorem mul_mem_typeSet_iff {i : Fin 3} {p q : G} (hp : p ∈ leechQ z) (hq : q ∈ leechQ z) :
    p * q ∈ L.typeSet i ↔ L.vec p + L.vec q ∈ co1Orbit i := by
  rw [mem_typeSet, L.vec_mul p hp q hq]
  exact ⟨fun h => h.2, fun h => ⟨mul_mem hp hq, h⟩⟩

end LeechSystem

end CFSG.Monster.GMS
