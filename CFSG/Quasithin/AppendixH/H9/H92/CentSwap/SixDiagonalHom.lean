module

public import CFSG.Quasithin.AppendixH.H9.H92.SixHom
public import CFSG.Quasithin.AppendixH.H9.H92.CentSwap.DiagonalCommutator

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem sixToFive_add (x y : Fin 6 → ZMod 2) :
    sixToFive (x + y) = sixToFive x + sixToFive y := by
  funext i
  simp only [sixToFive, Pi.add_apply]
  ring

private theorem sixToFive_zero : sixToFive 0 = 0 := by
  funext i
  simp [sixToFive]

private theorem sum_sixToFive_of_sum_eq_zero {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) :
    ∑ i, sixToFive x i = 0 := by
  have h : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 → ∑ i, sixToFive x i = 0 := by decide +kernel
  exact h x hx

private theorem exists_sixToFive_eq {c : Fin 5 → ZMod 2} (hc : ∑ i, c i = 0) :
    ∃ x : Fin 6 → ZMod 2, ∑ i, x i = 0 ∧ sixToFive x = c := by
  have h : ∀ c : Fin 5 → ZMod 2, ∑ i, c i = 0 →
      ∃ x : Fin 6 → ZMod 2, ∑ i, x i = 0 ∧ sixToFive x = c := by decide +kernel
  exact h c hc

private theorem sixToFive_eq_zero_iff (x : Fin 6 → ZMod 2) :
    sixToFive x = 0 ↔ x = 0 ∨ x = fun _ => 1 := by
  have h : ∀ x : Fin 6 → ZMod 2, sixToFive x = 0 ↔ x = 0 ∨ x = fun _ => 1 := by decide +kernel
  exact h x

@[expose] def sixDiagHom : G6.coreMod 6 →* PairN 5 where
  toFun u := pairVec (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)))
    (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)))
  map_one' := by
    show pairVec (sixToFive (Multiplicative.toAdd (1 : G6.PermMod 6)))
      (sixToFive (Multiplicative.toAdd (1 : G6.PermMod 6))) = 1
    rw [toAdd_one, sixToFive_zero]
    exact pairVec_one.symm
  map_mul' u u' := by
    show pairVec (sixToFive (Multiplicative.toAdd ((u : G6.PermMod 6) * (u' : G6.PermMod 6))))
      (sixToFive (Multiplicative.toAdd ((u : G6.PermMod 6) * (u' : G6.PermMod 6)))) =
      pairVec (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)))
        (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6))) *
      pairVec (sixToFive (Multiplicative.toAdd (u' : G6.PermMod 6)))
        (sixToFive (Multiplicative.toAdd (u' : G6.PermMod 6)))
    rw [toAdd_mul, sixToFive_add, pairVec_mul]

theorem sixDiagHom_apply (u : G6.coreMod 6) :
    sixDiagHom u = pairVec (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)))
      (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6))) := rfl

theorem range_sixDiagHom : sixDiagHom.range = evenDiag 5 := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, sum_sixToFive_of_sum_eq_zero u.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨y, hy, rfl⟩ := exists_sixToFive_eq hc
    exact ⟨⟨Multiplicative.ofAdd y, hy⟩, rfl⟩

theorem ker_sixDiagHom : sixDiagHom.ker = G6.natKer 6 := by
  ext u
  rw [MonoidHom.mem_ker, sixDiagHom_apply, pairVec_one, pairVec_inj, G6.natKer, Subgroup.mem_comap]
  have h1 : (G6.allOnes 6) * (G6.allOnes 6) = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [G6.allOnes]
    decide
  have key := sixToFive_eq_zero_iff (Multiplicative.toAdd (u : G6.PermMod 6))
  constructor
  · rintro ⟨h, -⟩
    rcases key.mp h with h0 | h0
    · rw [Subgroup.coe_subtype]
      have : (u : G6.PermMod 6) = 1 := Multiplicative.toAdd.injective h0
      rw [this]
      exact Subgroup.one_mem _
    · rw [Subgroup.coe_subtype]
      have : (u : G6.PermMod 6) = G6.allOnes 6 := Multiplicative.toAdd.injective h0
      rw [this]
      exact Subgroup.mem_zpowers _
  · intro hu
    rw [Subgroup.coe_subtype] at hu
    rcases mem_zpowers_involution h1 hu with h | h
    · have : sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)) = 0 :=
        key.mpr (Or.inl (by rw [h]; rfl))
      exact ⟨this, this⟩
    · have : sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)) = 0 :=
        key.mpr (Or.inr (by rw [h]; rfl))
      exact ⟨this, this⟩

end CFSG.ASVolI.ChH
