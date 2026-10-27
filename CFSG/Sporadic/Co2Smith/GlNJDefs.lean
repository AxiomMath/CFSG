module

public import CFSG.Sporadic.Co2Smith.GlWInputs
public import CFSG.Sporadic.Co2Smith.GlData
public import CFSG.Sporadic.Co2Smith.GlDefs

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glNJB_letters : ∀ i < 10, ∀ k ∈ Native.glNJB[i]!, k < 22 := by
  decide +kernel

theorem glNJB_size : Native.glNJB.size = 10 := rfl

theorem glNJBR_get {i : ℕ} (hi : i < 10) : Native.glNJBR[i]! = Native.glR Native.glNJB[i]! :=
  getElem!_map_of_lt _ _ (by rw [glNJB_size]; exact hi)

section Defs


@[expose] noncomputable def jcB (i : ℕ) : K := glE Native.glNJB[i]!

@[expose] noncomputable def jcElt (m : ℕ) : K :=
  (List.range 10).foldr (fun i acc => if m.testBit i then jcB i * acc else acc) 1

@[expose] noncomputable def Jc : Subgroup K := closure (Set.range fun i : Fin 10 => jcB i)

theorem jcB_val {i : ℕ} (hi : i < 10) :
    (jcB i).val.val = rowsMatrix 22 Native.glNJBR[i]! := by
  rw [jcB, glE_val (glNJB_letters i hi), glNJBR_get hi]

theorem jcB_mem {i : ℕ} (hi : i < 10) : jcB i ∈ Jc :=
  subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem foldr_bits_val (m : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 10) →
      (l.foldr (fun i acc => if m.testBit i then jcB i * acc else acc) (1 : K)).val.val =
        rowsMatrix 22 (Native.glBitsR Native.glNJBR m l)
  | [], _ => by
    rw [List.foldr_nil, Native.glBitsR, List.foldr_nil, rowsMatrix_idRows]
    rfl
  | i :: l, hl => by
    have ih := foldr_bits_val m l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    simp only [List.foldr_cons]
    rw [Native.glBitsR, List.foldr_cons]
    split_ifs with h
    · rw [val_val_mul, jcB_val (hl i List.mem_cons_self), ih, ← rowsMatrix_mulRows]
      rfl
    · exact ih

theorem jcElt_val (m : ℕ) : (jcElt m).val.val = rowsMatrix 22 (Native.glJcR m) :=
  foldr_bits_val m (List.range 10) fun _ hi => List.mem_range.1 hi

theorem foldr_bits_mem (m : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 10) →
      l.foldr (fun i acc => if m.testBit i then jcB i * acc else acc) (1 : K) ∈ Jc
  | [], _ => Jc.one_mem
  | i :: l, hl => by
    have ih := foldr_bits_mem m l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    simp only [List.foldr_cons]
    split_ifs
    · exact Jc.mul_mem (jcB_mem (hl i List.mem_cons_self)) ih
    · exact ih

theorem jcElt_mem (m : ℕ) : jcElt m ∈ Jc :=
  foldr_bits_mem m (List.range 10) fun _ hi => List.mem_range.1 hi

end Defs

@[expose] def SmithNJChart :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G → SmithHyp G z →
    ∀ φ : centralizer ({z} : Set G) ≃* Cz, SmithGlobalHyps z φ →
      ∃ ψ : normalizer (Jc : Set K) →* G,
        ∀ (x : normalizer (Jc : Set K)) (hx : (x : K) ∈ Cz), ψ x = (φ.symm ⟨x, hx⟩ : G)

end CFSG.Sporadic.Co2Smith
