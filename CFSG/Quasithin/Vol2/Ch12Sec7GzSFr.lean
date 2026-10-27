module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSAct

public section

namespace CFSG.Quasithin.H13.I1277

open Subgroup

namespace FrData

variable {G : Type} [Group G] {H Q N : Subgroup G} {d : Nat} (D : FrData H Q N d)

def bitKer (i : Nat) : Subgroup ↥Q where
  carrier := {y | (D.wc y.1).testBit i = false}
  one_mem' := by
    show (D.wc ((1 : ↥Q) : G)).testBit i = false
    rw [Subgroup.coe_one, D.wc_one]; simp
  mul_mem' := by
    intro a b ha hb
    show (D.wc ((a * b : ↥Q) : G)).testBit i = false
    rw [Subgroup.coe_mul, D.wc_mul _ a.2 _ b.2, Nat.testBit_xor]
    have ha' : (D.wc a.1).testBit i = false := ha
    have hb' : (D.wc b.1).testBit i = false := hb
    rw [ha', hb']; rfl
  inv_mem' := by
    intro a ha
    show (D.wc ((a⁻¹ : ↥Q) : G)).testBit i = false
    rw [Subgroup.coe_inv, D.wc_inv a.2]
    exact ha

theorem mem_bitKer (i : Nat) (y : ↥Q) : y ∈ D.bitKer i ↔ (D.wc y.1).testBit i = false := Iff.rfl

theorem isCoatom_bitKer (i : Nat) {x : ↥Q} (hx : (D.wc x.1).testBit i = true) :
    IsCoatom (D.bitKer i) := by
  refine ⟨?_, fun M' hlt => ?_⟩
  · intro htop
    have : x ∈ D.bitKer i := by rw [htop]; exact Subgroup.mem_top _
    rw [mem_bitKer] at this
    rw [hx] at this
    exact absurd this (by simp)
  · obtain ⟨y, hyM', hyK⟩ := SetLike.exists_of_lt hlt
    rw [mem_bitKer] at hyK
    have hy : (D.wc y.1).testBit i = true := by simpa using hyK
    rw [eq_top_iff]
    intro w _
    by_cases hw : (D.wc w.1).testBit i = false
    · exact hlt.le ((mem_bitKer D i w).2 hw)
    · have hw' : (D.wc w.1).testBit i = true := by simpa using hw
      have h1 : w * y⁻¹ ∈ D.bitKer i := by
        rw [mem_bitKer, Subgroup.coe_mul, D.wc_mul _ w.2 _ (y⁻¹).2, Subgroup.coe_inv,
          D.wc_inv y.2, Nat.testBit_xor, hw', hy]
        rfl
      have h2 : w * y⁻¹ ∈ M' := hlt.le h1
      have : w = (w * y⁻¹) * y := by group
      rw [this]
      exact M'.mul_mem h2 hyM'

include D in
theorem frattini_le [Finite G] {x : ↥Q} (hx : x ∈ frattini ↥Q) : (x : G) ∈ N := by
  by_contra hxN
  have hne : D.wc x.1 ≠ 0 := fun h => hxN ((D.wc_ker x.1 x.2).1 h)
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  have hcoatom := D.isCoatom_bitKer i hi
  have hxM : x ∈ D.bitKer i := by
    have h1 : x ∈ ⨅ M : Subgroup ↥Q, ⨅ (_ : IsCoatom M), M := hx
    rw [Subgroup.mem_iInf] at h1
    have h2 := h1 (D.bitKer i)
    rw [Subgroup.mem_iInf] at h2
    exact h2 hcoatom
  rw [mem_bitKer, hi] at hxM
  exact absurd hxM (by simp)

end FrData

end CFSG.Quasithin.H13.I1277

end
