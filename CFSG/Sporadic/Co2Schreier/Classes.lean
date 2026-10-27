module

public import CFSG.Sporadic.Co2Schreier.ClassCheck
public import CFSG.Sporadic.Co2Inv
public import CFSG.Sporadic.Co2Schreier.ThirdEBase
public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

structure ClassFacts : Prop where
  u_sq : eqA 2300 (compA 2300 uArr uArr) (idA 2300) = true
  u_ne : (!eqA 2300 uArr (idA 2300)) = true
  reps : allLt 3 (fun r =>
      isInvA 2300 (cRepArr co2PosTable r) (invCand 2300 (cRepArr co2PosTable r)) &&
      allLt 2300 (fun k => co2PackedVecs[(cRepArr co2PosTable r)[k]!]! ==
        vecMulN 22 (transposeRows 22 CFSG.Sporadic.Co2Inv.co2InvReps[r]!) co2PackedVecs[k]!) &&
      lettersOK 2 (fuseWords.getD r []) &&
      isInvA 2300 (wordArr aArrs (fuseWords.getD r []))
        (invCand 2300 (wordArr aArrs (fuseWords.getD r []))) &&
      eqA 2300 (powA (compA 2300 (pickRep zArr tArr uArr r) (compA 2300
        (compA 2300 (wordArr aArrs (fuseWords.getD r [])) (cRepArr co2PosTable r))
        (invCand 2300 (wordArr aArrs (fuseWords.getD r []))))) (fuseExps.getD r 0))
        (idA 2300)) = true

theorem classFacts : ClassFacts := by
  have h := class_check
  simp only [classCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem classFacts_r {r : ℕ} (hr : r < 3) :
    isInvA 2300 (cRepArr co2PosTable r) (invCand 2300 (cRepArr co2PosTable r)) = true ∧
      (∀ k < 2300, co2PackedVecs[(cRepArr co2PosTable r)[k]!]! =
        vecMulN 22 (transposeRows 22 CFSG.Sporadic.Co2Inv.co2InvReps[r]!) co2PackedVecs[k]!) ∧
      lettersOK 2 (fuseWords.getD r []) = true ∧
      isInvA 2300 (wordArr aArrs (fuseWords.getD r []))
        (invCand 2300 (wordArr aArrs (fuseWords.getD r []))) = true ∧
      eqA 2300 (powA (compA 2300 (pickRep zArr tArr uArr r) (compA 2300
        (compA 2300 (wordArr aArrs (fuseWords.getD r [])) (cRepArr co2PosTable r))
        (invCand 2300 (wordArr aArrs (fuseWords.getD r []))))) (fuseExps.getD r 0))
        (idA 2300) = true := by
  have h := allLt_iff.1 classFacts.reps r hr
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, fun k hk => beq_iff_eq.1 (allLt_iff.1 h2 k hk), h3, h4, h5⟩

@[expose] def uP : co2P := ⟨locU, locU_mem⟩

@[expose] def repP
    (r : ℕ) : co2P := co2PermEquiv (CFSG.Sporadic.Co2Inv.repCo2 r)

theorem repP_eq
    {r : ℕ} (hr : r < 3) :
    ((repP r : co2P) : Equiv.Perm (Fin 2300)) = permOfArr 2300 (cRepArr co2PosTable r) := by
  have hc := classFacts_r hr
  have hπ := (rep_permOfArr hc.1).1
  refine Equiv.ext fun i => Fin.ext (co2Vec_injective (Fin.isLt _) (Fin.isLt _) ?_)
  have h1 : co2Vec ((((repP r : co2P) : Equiv.Perm (Fin 2300)) i : ℕ)) =
      (CFSG.Sporadic.Co2Inv.repCo2 r).val.val *ᵥ co2Vec (i : ℕ) :=
    co2Vec_permEquiv _ i
  rw [h1, CFSG.Sporadic.Co2Inv.repCo2_val hr, co2Vec_eq i.2, rowsMatrix_mulVec,
    ← hc.2.1 i i.2, ← hπ i, co2Vec_eq (hπ.lt i.2)]

theorem rep_repP
    {r : ℕ} (hr : r < 3) :
    Rep 2300 (cRepArr co2PosTable r) ((repP r : co2P) : Equiv.Perm (Fin 2300)) := by
  rw [repP_eq hr]
  exact (rep_permOfArr (classFacts_r hr).1).1

theorem repP_sq
    {r : ℕ} (hr : r < 3) : repP r * repP r = 1 := by
  rw [repP, ← map_mul, CFSG.Sporadic.Co2Inv.repCo2_sq hr, map_one]

@[expose] def myRep
    (r : ℕ) : co2P := if r = 0 then zP else if r = 1 then tP else uP

theorem rep_myRep
    {r : ℕ} (hr : r < 3) :
    Rep 2300 (pickRep zArr tArr uArr r) ((myRep r : co2P) : Equiv.Perm (Fin 2300)) := by
  interval_cases r
  · simp only [pickRep, myRep, ↓reduceIte]
    exact rep_z
  · simp only [pickRep, myRep, ↓reduceIte, one_ne_zero]
    exact rep_t
  · simp only [pickRep, myRep, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    exact rep_u

theorem uP_sq :
    uP * uP = 1 :=
  Subtype.ext (eq_of_eqA (rep_compA rep_u rep_u) rep_idA classFacts.u_sq)

theorem uP_ne_one :
    uP ≠ 1 := by
  intro h
  have h1 : locU = 1 := congrArg Subtype.val h
  have h2 := (eqA_iff rep_u rep_idA).2 h1
  have h3 := classFacts.u_ne
  rw [h2] at h3
  exact absurd h3 (by decide)

theorem myRep_sq
    {r : ℕ} (hr : r < 3) : myRep r * myRep r = 1 := by
  interval_cases r
  · show zP * zP = 1
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      change locZ * locZ = 1
      rw [← pow_two]
      exact locZ_sq)
  · show tP * tP = 1
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      change locT * locT = 1
      rw [← pow_two]
      exact locT_sq)
  · show uP * uP = 1
    exact uP_sq

theorem isConj_myRep_repP
    {r : ℕ} (hr : r < 3) : IsConj (myRep r) (repP r) := by
  obtain ⟨-, -, hl, hwinv, hpow⟩ := classFacts_r hr
  set w := fuseWords.getD r [] with hw
  have hrw : Rep 2300 (wordArr aArrs w) (wordValue aSeeds w) :=
    repTuple_a.word wordFacts.invA (by rw [aSeeds_length]; exact hl)
  have hrwi := rep_inv_of_isInvA hrw hwinv
  set W : co2P := ⟨wordValue aSeeds w, wordValue_mem _ _ aSeeds_mem w⟩ with hW
  have hprod : (myRep r * (W * repP r * W⁻¹)) ^ (fuseExps.getD r 0) = 1 := by
    apply Subtype.ext
    have := eq_of_eqA (rep_powA (rep_compA (rep_myRep hr) (rep_compA (rep_compA hrw (rep_repP hr))
      hrwi)) _) rep_idA hpow
    rw [Subgroup.coe_pow]
    exact this
  have hodd : Odd (fuseExps.getD r 0) := by
    interval_cases r <;> decide
  have hsq : (W * repP r * W⁻¹) * (W * repP r * W⁻¹) = 1 := by
    calc (W * repP r * W⁻¹) * (W * repP r * W⁻¹) = W * (repP r * repP r) * W⁻¹ := by group
      _ = 1 := by rw [repP_sq hr, mul_one, mul_inv_cancel]
  have h1 := CFSG.Sporadic.Co2Inv.isConj_of_odd_pow (myRep_sq hr) hsq hodd hprod
  exact h1.trans (isConj_iff.2 ⟨W⁻¹, by group⟩)

theorem invol_isConj_repP
    (a : co2P) (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ r < 3, IsConj a (repP r) := by
  set x := co2PermEquiv.symm a with hx
  have hxx : x * x = 1 := by rw [hx, ← map_mul, ha, map_one]
  have hx1 : x ≠ 1 := fun h => ha1 (by
    rw [← co2PermEquiv.apply_symm_apply a, ← hx, h, map_one])
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Co2Inv.exists_conj_mem_sylowS x
    (CFSG.Sporadic.Co2Inv.isPGroup_zpowers_of_invol hxx hx1)
  obtain ⟨k, hk, hke⟩ := CFSG.Sporadic.Co2Inv.exists_eltS_of_mem hg
  have h2 : CFSG.Sporadic.Co2Inv.eltS k * CFSG.Sporadic.Co2Inv.eltS k = 1 := by
    rw [hke]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
  have h1 : CFSG.Sporadic.Co2Inv.eltS k ≠ 1 := by
    rw [hke]
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  obtain ⟨r, hr, hconj⟩ := CFSG.Sporadic.Co2Inv.exists_rep_of_invol hk h2 h1
  have hxk : IsConj x (CFSG.Sporadic.Co2Inv.eltS k) := by
    rw [hke]
    exact isConj_iff.2 ⟨g, rfl⟩
  refine ⟨r, hr, ?_⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 (hxk.trans hconj)
  refine isConj_iff.2 ⟨co2PermEquiv c, ?_⟩
  rw [repP, ← hc, map_mul, map_mul, map_inv, hx, MulEquiv.apply_symm_apply]

theorem invol_cases
    (a : co2P) (ha : a * a = 1) (ha1 : a ≠ 1) :
    IsConj a zP ∨ IsConj a tP ∨ IsConj a uP := by
  obtain ⟨r, hr, h⟩ := invol_isConj_repP a ha ha1
  have h' := h.trans (isConj_myRep_repP hr).symm
  interval_cases r
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h')

end CFSG.Sporadic.Co2Schreier
