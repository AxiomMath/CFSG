module

public import CFSG.Quasithin.EmptyFaithful.T1515gB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem a7_fixed_by_gens (z : Fin 7 → ZMod 2) (hz : ∑ i, z i = 0)
    (h1 : ∀ i, z (((Equiv.swap (2 : Fin 7) 3 * Equiv.swap 3 4)⁻¹ : Equiv.Perm (Fin 7)) i) = z i)
    (h2 : ∀ i, z (((Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5)⁻¹ : Equiv.Perm (Fin 7)) i) = z i)
    (h3 : ∀ i, z (((Equiv.swap (4 : Fin 7) 5 * Equiv.swap 5 6)⁻¹ : Equiv.Perm (Fin 7)) i) = z i)
    (h4 : ∀ i, z (((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3)⁻¹ : Equiv.Perm (Fin 7)) i) = z i) :
    z = 0 ∨ z = fun k => (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0) := by
  revert z
  decide +kernel

theorem a7_decomp_fun : ∀ f : Fin 7 → ZMod 2, ∑ i, f i = 0 →
    f = ∑ i : Fin 6, if f i.succ = 1 then
      (fun k => (if k = 0 then 1 else 0) + (if k = i.succ then 1 else 0) : Fin 7 → ZMod 2) else 0 := by
  decide +kernel

theorem a7_decomp (x : ↥(evenWeight 7)) :
    x = ∑ i : Fin 6, if (x : Fin 7 → ZMod 2) i.succ = 1 then a7PairVec 0 i.succ else 0 := by
  apply Subtype.ext
  have hx : ∑ i, (x : Fin 7 → ZMod 2) i = 0 := by
    have := x.2
    simpa [evenWeight] using this
  have h := a7_decomp_fun _ hx
  rw [AddSubmonoidClass.coe_finsetSum]
  convert h using 2
  split_ifs <;> rfl

theorem a7_exists_perm_pair (i : Fin 7) (hi : i ≠ 0) :
    ∃ a : Equiv.Perm (Fin 7), a ∈ alternatingGroup (Fin 7) ∧
      permWeight 7 a (a7PairVec 0 1) = a7PairVec 0 i := by
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨1, by simp, rfl⟩
  · refine ⟨Equiv.swap 1 2 * Equiv.swap 3 4, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · apply Subtype.ext
      funext k
      revert k
      decide +kernel
  · refine ⟨Equiv.swap 1 3 * Equiv.swap 2 4, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · apply Subtype.ext
      funext k
      revert k
      decide +kernel
  · refine ⟨Equiv.swap 1 4 * Equiv.swap 2 3, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · apply Subtype.ext
      funext k
      revert k
      decide +kernel
  · refine ⟨Equiv.swap 1 5 * Equiv.swap 2 3, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · apply Subtype.ext
      funext k
      revert k
      decide +kernel
  · refine ⟨Equiv.swap 1 6 * Equiv.swap 2 3, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    · apply Subtype.ext
      funext k
      revert k
      decide +kernel

theorem a7_schur (τ : ↥(evenWeight 7) →+ ↥(evenWeight 7))
    (hτ : ∀ (a : alternatingGroup (Fin 7)) (x : ↥(evenWeight 7)),
      τ (permWeight 7 (a : Equiv.Perm (Fin 7)) x) = permWeight 7 (a : Equiv.Perm (Fin 7)) (τ x)) :
    τ = 0 ∨ τ = AddMonoidHom.id _ := by
  have hfix : ∀ g : Equiv.Perm (Fin 7), g ∈ alternatingGroup (Fin 7) →
      permWeight 7 g (a7PairVec 0 1) = a7PairVec 0 1 →
      ∀ i, ((τ (a7PairVec 0 1) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) ((g⁻¹ : Equiv.Perm (Fin 7)) i) =
        ((τ (a7PairVec 0 1) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) i := by
    intro g hg hgw i
    have h1 := hτ ⟨g, hg⟩ (a7PairVec 0 1)
    simp only at h1
    rw [hgw] at h1
    have h2 := congrArg (fun z : ↥(evenWeight 7) => (z : Fin 7 → ZMod 2) i) h1
    simpa [permWeight] using h2.symm
  have hsum : ∑ i, ((τ (a7PairVec 0 1) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) i = 0 := by
    have hmem : ((τ (a7PairVec 0 1) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) ∈ evenWeight 7 :=
      (τ (a7PairVec 0 1)).2
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hmem
    exact hmem
  have hmemg : ∀ a b c d : Fin 7, (a ≠ b ∧ c ≠ d) → (Equiv.swap a b * Equiv.swap c d) ∈
      alternatingGroup (Fin 7) := by
    intro a b c d ⟨hab, hcd⟩
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
    decide
  have hz := a7_fixed_by_gens _ hsum
    (hfix _ (hmemg 2 3 3 4 ⟨by decide, by decide⟩) (by apply Subtype.ext; funext k; revert k; decide +kernel))
    (hfix _ (hmemg 3 4 4 5 ⟨by decide, by decide⟩) (by apply Subtype.ext; funext k; revert k; decide +kernel))
    (hfix _ (hmemg 4 5 5 6 ⟨by decide, by decide⟩) (by apply Subtype.ext; funext k; revert k; decide +kernel))
    (hfix _ (hmemg 0 1 2 3 ⟨by decide, by decide⟩) (by apply Subtype.ext; funext k; revert k; decide +kernel))
  have hτi : ∀ i : Fin 7, i ≠ 0 → ∃ a ∈ alternatingGroup (Fin 7),
      permWeight 7 a (a7PairVec 0 1) = a7PairVec 0 i ∧
        τ (a7PairVec 0 i) = permWeight 7 a (τ (a7PairVec 0 1)) := by
    intro i hi
    obtain ⟨a, hmem, heq⟩ := a7_exists_perm_pair i hi
    refine ⟨a, hmem, heq, ?_⟩
    rw [← heq]
    exact hτ ⟨a, hmem⟩ _
  have key : ∀ x : ↥(evenWeight 7), τ x = ∑ i : Fin 6,
      if (x : Fin 7 → ZMod 2) i.succ = 1 then τ (a7PairVec 0 i.succ) else 0 := by
    intro x
    conv_lhs => rw [a7_decomp x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rcases hz with h0 | h1
  · left
    have hτw : τ (a7PairVec 0 1) = 0 := Subtype.ext h0
    refine AddMonoidHom.ext fun x => ?_
    rw [key x]
    have : ∀ i : Fin 6, τ (a7PairVec 0 i.succ) = 0 := by
      intro i
      obtain ⟨a, -, -, h⟩ := hτi i.succ (Fin.succ_ne_zero i)
      rw [h, hτw]
      apply Subtype.ext
      funext k
      simp [permWeight]
    simp [this]
  · right
    have hτw : τ (a7PairVec 0 1) = a7PairVec 0 1 := Subtype.ext h1
    refine AddMonoidHom.ext fun x => ?_
    rw [key x]
    have : ∀ i : Fin 6, τ (a7PairVec 0 i.succ) = a7PairVec 0 i.succ := by
      intro i
      obtain ⟨a, -, hw, h⟩ := hτi i.succ (Fin.succ_ne_zero i)
      rw [h, hτw, hw]
    simp only [this, AddMonoidHom.id_apply]
    exact (a7_decomp x).symm

end CFSG.Quasithin
