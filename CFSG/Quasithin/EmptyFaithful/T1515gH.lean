module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.SteinbergCBI16Alt7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem a7_incl_proj (C : CFSG.Quasithin.SteinbergCB.I16.DnCoords 7 6) {x : Fin 7 → ZMod 2}
    (hx : ∑ i, x i = 0) : C.incl (C.proj x) = x := by
  have hsd : ∑ i, (x - C.incl (C.proj x)) i = 0 := by
    have := C.sum_incl (C.proj x)
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hx, this, sub_zero]
  have hpd : C.proj (x - C.incl (C.proj x)) = 0 := by
    rw [map_sub, C.proj_incl, sub_self]
  rcases C.ker_proj _ hsd hpd with h0 | h1
  · exact (sub_eq_zero.mp h0).symm
  · exfalso
    rw [h1] at hsd
    revert hsd
    decide

theorem a7_cocycle_coboundary_of (C : CFSG.Quasithin.SteinbergCB.I16.DnCoords 7 6)
    (hC : CFSG.Quasithin.JonesParshall.Z1A C.actA ≤ CFSG.Quasithin.JonesParshall.B1A C.actA)
    (f : ↥(alternatingGroup (Fin 7)) → ↥(evenWeight 7))
    (hf : ∀ a b, f (a * b) = f a + permWeight 7 (a : Equiv.Perm (Fin 7)) (f b)) :
    ∃ y : ↥(evenWeight 7), ∀ a, f a = permWeight 7 (a : Equiv.Perm (Fin 7)) y - y := by
  have hsum : ∀ z : ↥(evenWeight 7), ∑ i, (z : Fin 7 → ZMod 2) i = 0 := fun z => by
    have := z.2
    simpa [evenWeight] using this
  have hsumpv : ∀ (a : Equiv.Perm (Fin 7)) (z : ↥(evenWeight 7)),
      ∑ i, (permWeight 7 a z : Fin 7 → ZMod 2) i = 0 := fun a z => hsum _
  let f' : ↥(alternatingGroup (Fin 7)) → (Fin 6 → ZMod 2) := fun a => C.proj (f a : Fin 7 → ZMod 2)
  have hf' : f' ∈ CFSG.Quasithin.JonesParshall.Z1A C.actA := by
    intro a b
    simp only [f']
    rw [hf a b, AddSubgroup.coe_add, map_add]
    congr 1
    rw [C.actA_apply, a7_incl_proj C (hsum _)]
    rfl
  obtain ⟨m, hm⟩ := hC hf'
  refine ⟨⟨C.incl m, by simpa [evenWeight] using C.sum_incl m⟩, fun a => ?_⟩
  have h1 : (f a : Fin 7 → ZMod 2) = C.incl (f' a) := (a7_incl_proj C (hsum _)).symm
  have h2 : f' a = C.actA a m - m := (congrFun hm a).symm
  apply Subtype.ext
  rw [AddSubgroup.coe_sub, h1, h2, map_sub, C.actA_apply]
  have h3 := a7_incl_proj C (x := (permWeight 7 (a : Equiv.Perm (Fin 7))
    ⟨C.incl m, by simpa [evenWeight] using C.sum_incl m⟩ : Fin 7 → ZMod 2)) (hsumpv _ _)
  simp only [permWeight] at h3 ⊢
  have h3' : C.incl (C.proj ((CFSG.Quasithin.SteinbergCB.I16.pv (a : Equiv.Perm (Fin 7))) (C.incl m))) =
      fun i => C.incl m ((a : Equiv.Perm (Fin 7))⁻¹ i) := h3
  rw [h3']

theorem a7_cocycle_coboundary (f : ↥(alternatingGroup (Fin 7)) → ↥(evenWeight 7))
    (hf : ∀ a b, f (a * b) = f a + permWeight 7 (a : Equiv.Perm (Fin 7)) (f b)) :
    ∃ y : ↥(evenWeight 7), ∀ a, f a = permWeight 7 (a : Equiv.Perm (Fin 7)) y - y :=
  a7_cocycle_coboundary_of CFSG.Quasithin.SteinbergCB.I16.coords7
    CFSG.Quasithin.SteinbergCB.I16.Z1A_le_B1A_7 f hf

end CFSG.Quasithin
