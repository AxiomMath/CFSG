module

public import CFSG.Sporadic.Co2Smith.GlNJCheck
public import CFSG.Certificates.NativeRefine
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Certificates CFSG.Certificates.Native MulAction

@[expose] def njAut : Subgroup (Equiv.Perm (Fin 77)) where
  carrier := {σ | NbrInv Native.glNJNbr σ}
  one_mem' _ _ := Iff.rfl
  mul_mem' ha hb := AdjFacts.nbrInv_mul ha hb
  inv_mem' ha := AdjFacts.nbrInv_inv ha

theorem mem_njAut {σ : Equiv.Perm (Fin 77)} : σ ∈ njAut ↔ NbrInv Native.glNJNbr σ := Iff.rfl

@[expose] def njAut0 : Subgroup (Equiv.Perm (Fin 77)) :=
  njAut ⊓ stabilizer (Equiv.Perm (Fin 77)) (0 : Fin 77)

theorem mem_njAut0 {σ : Equiv.Perm (Fin 77)} : σ ∈ njAut0 ↔ σ ∈ njAut ∧ σ 0 = 0 :=
  Iff.rfl

@[expose] def njBasePt (s : ℕ) : Fin 77 :=
  ⟨Native.glNJBase.getD s 0 % 77, Nat.mod_lt _ (by norm_num)⟩

theorem njBasePt_val {s : ℕ} (hs : s < 8) : (njBasePt s : ℕ) = Native.glNJBase.getD s 0 :=
  Nat.mod_eq_of_lt (by interval_cases s <;> decide)

section Ref

theorem glNJNbr_pointList (x : Fin 77) : PointList 77 Native.glNJNbr[(x : ℕ)]! where
  lt q hq := (glNJ3_spec.2.2.2.2.1 x x.2).1 q hq
  sorted := strictIncr_pairwise (glNJ3_spec.2.2.2.2.1 x x.2).2

theorem glNJBase_take {s : ℕ} {v : Fin 77} (hv : (v : ℕ) ∈ Native.glNJBase.take s) :
    ∃ j < s, njBasePt j = v := by
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
  simp only [List.length_take] at hj
  have hj8 : j < Native.glNJBase.length := by omega
  refine ⟨j, by omega, Fin.ext ?_⟩
  rw [njBasePt_val (by rw [glNJ3_spec.2.1] at hj8; exact hj8), List.getD_eq_getElem _ _ hj8]
  rw [List.getElem_take] at hjv
  exact hjv

theorem colInv_of_fix {s : ℕ} {σ : Equiv.Perm (Fin 77)} (hσ : σ ∈ njAut)
    (hfix : ∀ j < s, σ (njBasePt j) = njBasePt j) :
    ColInv 77 (Native.glNJColour Native.glNJNbr s) σ := by
  refine refineIter_inv glNJNbr_pointList hσ (individualize_inv ?_) 3
  intro v hv
  obtain ⟨j, hj, rfl⟩ := glNJBase_take hv
  exact hfix j hj

theorem njAut0_fix {σ : Equiv.Perm (Fin 77)} (hσ : σ ∈ njAut0) : σ (njBasePt 0) = njBasePt 0 :=
  (mem_njAut0.1 hσ).2

@[expose] def njBase1 (s : ℕ) : Fin 77 := njBasePt (s + 1)

theorem fix_of_mem_stabChain {s : ℕ} {τ : njAut0} (hτ : τ ∈ stabChain (G := njAut0) njBase1 s) :
    ∀ j < s + 1, (τ : Equiv.Perm (Fin 77)) (njBasePt j) = njBasePt j := by
  intro j hj
  rcases j with _ | j
  · exact njAut0_fix τ.2
  · exact mem_stabChain.1 hτ j (by omega)

theorem njAut0_orbit {s : ℕ} (hs : s < 7) :
    (orbit (stabChain (G := njAut0) njBase1 s) (njBase1 s)).ncard ≤
      Native.glNJBounds.getD (s + 1) 0 := by
  have hb : Native.glNJBounds.getD (s + 1) 0 = Native.glNJBounds[s + 1]! := by
    rw [List.getD_eq_getElem?_getD, getElem!_def]
    rfl
  rw [hb, ← glNJ3_spec.2.2.2.2.2.1 (s + 1) (by omega), Native.glNJClassCount,
    ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨⟨τ, hτ⟩, rfl⟩
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  have hbase : (njBasePt (s + 1) : ℕ) = Native.glNJBase[s + 1]! := by
    rw [njBasePt_val (by omega), List.getD_eq_getElem?_getD, getElem!_def]
    rfl
  have hc := colInv_of_fix τ.2.1 (fix_of_mem_stabChain hτ) (njBasePt (s + 1))
  rw [← hbase]
  exact hc

theorem njAut0_stabChain_seven : stabChain (G := njAut0) njBase1 7 = ⊥ := by
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  have hc := colInv_of_fix τ.2.1 (fix_of_mem_stabChain hτ)
  have hnd := glNJ3_spec.2.2.2.2.2.2.2
  have hsize := glNJ3_spec.2.2.2.2.2.2.1
  set σ : Equiv.Perm (Fin 77) := τ.1
  have hτ1 : σ = 1 := by
    refine Equiv.ext fun v => Fin.ext ?_
    have h := hc v
    rw [getElem!_pos _ _ (by rw [hsize]; exact (σ v).2),
      getElem!_pos _ _ (by rw [hsize]; exact v.2), ← Array.getElem_toList,
      ← Array.getElem_toList] at h
    exact (hnd.getElem_inj_iff).1 h
  exact Subtype.ext hτ1

theorem card_njAut0_le : Nat.card njAut0 ≤ 11520 := by
  have h := card_le_prod_of_stabChain (G := njAut0) njBase1
    (fun s => Native.glNJBounds.getD (s + 1) 0) 7 (fun s hs => njAut0_orbit hs)
    njAut0_stabChain_seven
  refine h.trans (le_of_eq ?_)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  rfl

end Ref

end CFSG.Sporadic.Co2Smith
