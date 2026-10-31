module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Basic.Finite.Defs
import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-- The Omega subgroup. -/
@[expose]
public def CFSG.omega (G : Type*) [Group G] {p : ℕ} (k : ℕ) : Subgroup G :=
  Subgroup.closure {x : G | x ^ (p ^ k) = 1}

/-- The first omega subgroup `Ω₁(G)` with respect to the prime `p`. -/
public abbrev CFSG.omega₁ (G : Type*) [Group G] {p : ℕ} : Subgroup G :=
  omega (G := G) (p := p) 1

public theorem CFSG.omega_characteristic (G : Type*) [Group G] {p : ℕ} (k : ℕ) :
    (omega (G := G) (p := p) k).Characteristic := by
  classical
  -- `omega` is defined by a group-theoretic property stable under automorphisms.
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  let S : Set G := {x : G | x ^ (p ^ k) = 1}
  have hS : (fun x : G => φ x) '' S = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ^ (p ^ k) = 1 := by simpa [S] using hy
      have : (φ y) ^ (p ^ k) = 1 := by
        simpa using congrArg φ.toMonoidHom hy'
      simpa [S] using this
    · intro hx
      refine ⟨φ.symm x, ?_, by simp⟩
      have hx' : x ^ (p ^ k) = 1 := by simpa [S] using hx
      have : (φ.symm x) ^ (p ^ k) = 1 := by
        simpa using congrArg φ.symm.toMonoidHom hx'
      simpa [S] using this
  calc
    (omega (G := G) (p := p) k).map φ.toMonoidHom
        = (Subgroup.closure S).map φ.toMonoidHom := by simp [omega, S]
    _ = Subgroup.closure ((fun x : G => φ x) '' S) := by
          simpa using (MonoidHom.map_closure (f := φ.toMonoidHom) S)
    _ = Subgroup.closure S := by simp [hS]
    _ = omega (G := G) (p := p) k := by simp [omega, S]

public theorem CFSG.omega₁_characteristic (G : Type*) [Group G] {p : ℕ} :
    (omega₁ (G := G) (p := p)).Characteristic := by
  simpa [omega₁] using (omega_characteristic (G := G) (p := p) 1)

public lemma CFSG.elementaryAbelian_le_omega₁ {p : ℕ} {G : Type*} [Group G] {E : Subgroup G}
    [IsElementaryAbelian p E] : E ≤ omega₁ (G := G) (p := p) := by
  intro x hx
  rw [omega₁, omega]
  exact Subgroup.subset_closure (by
    simpa [pow_one] using elemPow_eq_one_of_isElementaryAbelian x hx)

/-- In a commutative group, `Ω₁` is elementary abelian. -/
public theorem CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [IsMulCommutative G] :
    IsElementaryAbelian p (omega₁ (G := G) (p := p)) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : G | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

public theorem CFSG.omega₁_map_subtype_ne_bot {G : Type*} [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    [Fact p.Prime] (hp_dvd : p ∣ Nat.card (↥M)) :
    (omega₁ (G := (↥M)) (p := p)).map M.subtype ≠ ⊥ := by
  classical
  letI : Fintype (↥M) := Fintype.ofFinite (↥M)
  have hp_dvd' : p ∣ Fintype.card (↥M) := by
    simpa [Nat.card_eq_fintype_card] using hp_dvd
  obtain ⟨x, hx_order⟩ := _root_.exists_prime_orderOf_dvd_card (G := (↥M)) p hp_dvd'
  have hx_ne_one : x ≠ (1 : ↥M) := by
    intro hx
    have : 1 = p := by simpa [hx] using hx_order
    exact (Fact.out : p.Prime).ne_one this.symm
  have hx_pow : x ^ p = 1 := by
    simpa [hx_order] using pow_orderOf_eq_one x
  have hx_mem : x ∈ omega₁ (G := (↥M)) (p := p) := by
    change x ∈ Subgroup.closure {y : ↥M | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hx_pow
  have hx_mem_map : (M.subtype x) ∈ (omega₁ (G := (↥M)) (p := p)).map M.subtype :=
    Subgroup.mem_map_of_mem M.subtype hx_mem
  intro hbot
  have hx1 : M.subtype x = 1 := by
    have : M.subtype x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hx_mem_map
    simpa using this
  have : x = 1 := by
    apply Subtype.ext
    simpa using hx1
  exact hx_ne_one this
