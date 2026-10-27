module

public import CFSG.Monster.AxisCount.CertData0
public import CFSG.Monster.AxisCount.CertData1
public import CFSG.Monster.AxisCount.CertData2
public import CFSG.Monster.AxisCount.CertData3

public section

namespace CFSG.Monster.AxisCount.Cert

open CFSG.Monster.AxisCount.Native

@[expose] def orbits : Array OrbitData :=
  #[orbit0, orbit1, orbit2, orbit3, orbit4, orbit5, orbit6, orbit7, orbit8, orbit9, orbit10, orbit11]

@[expose] def nW (i : Fin 12) : Nat := orbits[i.val]!.h.size

@[expose] def gammaW (i : Fin 12) : List Gen := orbits[i.val]!.gamma

@[expose] def UA (i : Fin 12) : List Gen := orbits[i.val]!.UA

@[expose] def UB (i : Fin 12) : List Gen := orbits[i.val]!.UB

@[expose] def UW (i : Fin 12) : List (List Gen) := [UA i, UB i]

@[expose] def hW (i : Fin 12) (r : Nat) : List Gen := orbits[i.val]!.h[r]!

@[expose] def kappaW (i : Fin 12) (r : Nat) : Bool → List Gen
  | true => orbits[i.val]!.kappaPlus[r]!
  | false => orbits[i.val]!.kappaMinus[r]!

@[expose] def tW (i : Fin 12) (r : Nat) : Bool → Nat
  | true => orbits[i.val]!.tPlus[r]!
  | false => orbits[i.val]!.tMinus[r]!

@[expose] def sizeW (i : Fin 12) (r : Nat) : Nat := orbits[i.val]!.size[r]!

@[expose] def lamW (i : Fin 12) (r : Nat) : Nat := orbits[i.val]!.lam[r]!

@[expose] def OrbitData.wf (d : OrbitData) : Bool :=
  d.kappaPlus.size == d.h.size && d.kappaMinus.size == d.h.size && d.tPlus.size == d.h.size &&
  d.tMinus.size == d.h.size && d.size.size == d.h.size && d.lam.size == d.h.size &&
  d.tPlus.toList.all (· < 12) && d.tMinus.toList.all (· < 12)

theorem orbits_wf : orbits.size = 12 ∧ ∀ i < 12, orbits[i]!.wf = true := by decide +kernel

theorem tW_lt (i : Fin 12) (r : Nat) (ε : Bool) : tW i r ε < 12 := by
  obtain ⟨-, hwf⟩ := orbits_wf
  have h := hwf i i.2
  simp only [OrbitData.wf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hp⟩, hm⟩ := h
  cases ε
  · simp only [tW]
    by_cases hr : r < orbits[i.val]!.tMinus.size
    · rw [getElem!_pos _ r hr]
      exact of_decide_eq_true (List.all_eq_true.1 hm _ (Array.getElem_mem_toList hr))
    · rw [getElem!_neg _ r hr]
      exact Nat.succ_pos 11
  · simp only [tW]
    by_cases hr : r < orbits[i.val]!.tPlus.size
    · rw [getElem!_pos _ r hr]
      exact of_decide_eq_true (List.all_eq_true.1 hp _ (Array.getElem_mem_toList hr))
    · rw [getElem!_neg _ r hr]
      exact Nat.succ_pos 11

@[expose] def tFin (i : Fin 12) (r : Nat) (ε : Bool) : Fin 12 := ⟨tW i r ε, tW_lt i r ε⟩

end CFSG.Monster.AxisCount.Cert
