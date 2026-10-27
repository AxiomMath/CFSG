module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped Matrix

section Helpers

variable {K k : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2] {b c : K}

private theorem c2slomqmn_epsHt_single {n : ℕ} (i : Fin (n - 1)) (z : ℤ) :
    epsHt n (Pi.single i z) = (((n - 1 : ℕ) : ℤ) - i) * z := by
  simp [epsHt, Pi.single_apply]

private theorem c2slomqmn_zero_succ_lt {n : ℕ} (hn : 4 ≤ n) :
    (⟨0, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by
  have h0 : (⟨0, by omega⟩ : Fin (n - 1)).val = 0 := rfl
  omega

private theorem c2slomqmn_epsHt_le {n : ℕ}
    (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    epsHt n (minusWt n a) ≤ ((n - 1 : ℕ) : ℤ) := by
  rcases a with a | a | a
  · simp only [minusWt, c2slomqmn_epsHt_single]
    have ha : (a : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
      have := a.2
      omega
    linarith
  · simp only [minusWt, c2slomqmn_epsHt_single]
    have ha : (a : ℤ) < ((n - 1 : ℕ) : ℤ) := by
      have := a.2
      omega
    linarith
  · simp only [minusWt, map_zero]
    positivity

private theorem c2slomqmn_naturalRep_map_vector {n : ℕ} (φ : K →+* k)
    (g : spinGroup (quadMinus n K b c)) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    SmallO8mCurtis.naturalRep n b c φ g (fun a => φ (v a)) =
      fun a => φ (spinAction (quadMinus n K b c) g v a) := by
  rw [SmallO8mCurtis.naturalRep_apply]
  have hact : (mat n g) *ᵥ v = spinAction (quadMinus n K b c) g v := by
    rw [mat, coe_spinMatrix]
    exact LinearMap.toMatrix'_mulVec _ v
  rw [← hact]
  ext a
  simp [Matrix.mulVec_apply_eq_sum, map_sum, map_mul]

private theorem c2slomqmn_naturalRep_Weyl_highest {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (φ : K →+* k) (i : Fin (n - 1)) :
    SmallO8mCurtis.naturalRep n b c φ (minusWeyl n hirrQ i)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
      if i.val = 0 then Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k)
      else Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) := by
  have hact : spinAction (quadMinus n K b c) (minusWeyl n hirrQ i)
      (eVec n (⟨0, by omega⟩ : Fin (n - 1))) =
      if i.val = 0 then eVec n (⟨1, by omega⟩ : Fin (n - 1))
      else eVec n (⟨0, by omega⟩ : Fin (n - 1)) := by
    by_cases h0 : i.val = 0
    · have hi : i = (⟨0, by omega⟩ : Fin (n - 1)) := Fin.ext h0
      rw [if_pos h0, hi, minusWeyl_of_lt n hirrQ
        (k := (⟨0, by omega⟩ : Fin (n - 1))) (c2slomqmn_zero_succ_lt hn)]
      have h := (minusFrame n b c).toHypFrame.spinAction_longWeyl_vec_left
        (succ_ne_of_lt n (k := (⟨0, by omega⟩ : Fin (n - 1)))
          (c2slomqmn_zero_succ_lt hn)) true false
      simpa [minusFrame_vec, minusVec_true, eVec, CharTwo.neg_eq] using h
    · have hzi : (⟨0, by omega⟩ : Fin (n - 1)) ≠ i := by
        intro h
        exact h0 (by simpa using congrArg Fin.val h.symm)
      rw [if_neg h0]
      by_cases hlt : i.val + 1 < n - 1
      · have hzj : (⟨0, by omega⟩ : Fin (n - 1)) ≠ (⟨i.val + 1, hlt⟩ : Fin (n - 1)) := by
          intro h
          exact Nat.succ_ne_zero i.val (congrArg Fin.val h).symm
        rw [minusWeyl_of_lt n hirrQ hlt]
        have h := (minusFrame n b c).toHypFrame.spinAction_longWeyl_vec_of_ne
          (succ_ne_of_lt n hlt) true false (k := (⟨0, by omega⟩ : Fin (n - 1))) hzi hzj true
        simpa [minusFrame_vec, minusVec_true, eVec] using h
      · rw [minusWeyl_of_not_lt n hirrQ hlt]
        have h := spinAction_shortWeylElt_eVec_of_ne n hirrQ
          (i := i) (j := (⟨0, by omega⟩ : Fin (n - 1))) hzi planeOne
        simpa [shortWeyl] using h
  have h := c2slomqmn_naturalRep_map_vector φ (minusWeyl n hirrQ i)
    (eVec n (⟨0, by omega⟩ : Fin (n - 1)))
  rw [hact] at h
  have hvec : ∀ j : Fin (n - 1), (fun a => φ (eVec n j a)) =
      (Pi.single (Sum.inl j) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → k) := by
    intro j
    ext a
    simp [eVec, Pi.single_apply]
  simp only [hvec] at h
  split_ifs at h ⊢ <;> simpa only [hvec] using h

private theorem c2slomqmn_naturalRep_first_X_next_of_val_eq_zero {n : ℕ} (hn : 4 ≤ n)
    (φ : K →+* k) {j : Fin (n - 1)} (hj : j.val + 1 < n - 1) (hj0 : j.val = 0) (a : K) :
    SmallO8mCurtis.naturalRep n b c φ
        ((minusFrame n b c).longRoot (succ_ne_of_lt n hj) true false (.ofAdd a))
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k)) =
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k) +
        φ a • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) := by
  have hj1 : (⟨j.val + 1, hj⟩ : Fin (n - 1)) = (⟨1, by omega⟩ : Fin (n - 1)) := by
    apply Fin.ext
    simp [hj0]
  have hj0e : eVec (K := K) n j = eVec (K := K) n (⟨0, by omega⟩ : Fin (n - 1)) := by
    simp only [eVec]
    exact congrArg (fun i => (Pi.single (Sum.inl i) 1 :
      Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) (Fin.ext hj0)
  have hact : spinAction (quadMinus n K b c)
      ((minusFrame n b c).longRoot (succ_ne_of_lt n hj) true false (.ofAdd a))
      (eVec n (⟨1, by omega⟩ : Fin (n - 1))) =
      eVec n (⟨1, by omega⟩ : Fin (n - 1)) + a • eVec n (⟨0, by omega⟩ : Fin (n - 1)) := by
    have hvec1 : minusVec n (⟨j.val + 1, hj⟩ : Fin (n - 1)) (!false) =
        eVec (K := K) n (⟨1, by omega⟩ : Fin (n - 1)) := by
      simp only [Bool.not_false, minusVec_true, hj1]
    have hvec0 : minusVec n j true = eVec (K := K) n (⟨0, by omega⟩ : Fin (n - 1)) := by
      rw [minusVec_true, hj0e]
    have h := (minusFrame n b c).toHypFrame.spinAction_longRoot_vec_not_right
      (succ_ne_of_lt n hj) true false a
    rw [minusFrame_vec] at h
    rw [hvec1, hvec0] at h
    exact h
  have h := c2slomqmn_naturalRep_map_vector φ
    ((minusFrame n b c).longRoot (succ_ne_of_lt n hj) true false (.ofAdd a))
    (eVec n (⟨1, by omega⟩ : Fin (n - 1)))
  rw [hact] at h
  have hvec : (fun i => φ (eVec n (⟨1, by omega⟩ : Fin (n - 1)) i)) =
      (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) 1 :
        Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → k) := by
    ext i
    simp [eVec, Pi.single_apply]
  rw [hvec] at h
  rw [h]
  ext i
  simp [eVec, Pi.single_apply, map_add, Pi.smul_apply]
  split_ifs <;> simp_all

private theorem c2slomqmn_highestVec_mem_fixU {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (φ : K →+* k) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) ∈
      (SmallO8mCurtis.curtisDatum n hn hirrQ).fixU
        (SmallO8mCurtis.naturalRep n b c φ) := by
  rw [CurtisDatum.mem_fixU]
  intro g hg
  change g ∈ CFSG.LieType.Steinberg.posUnipotent (minusDatum n hirrQ) at hg
  change g ∈ ⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < ht γ},
    minusRootGroup n hirrQ γ at hg
  have htri := idBelow_of_mem_iSup n hirrQ 1
    {γ | γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < ht γ}
    (fun γ hγ => by
      change γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < ht γ at hγ
      exact ⟨hγ.1, by simpa only [one_mul] using hγ.2⟩) hg
  have hcol : ∀ a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2,
      mat n g a (.inl (⟨0, by omega⟩ : Fin (n - 1))) =
        (1 : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) a
          (.inl (⟨0, by omega⟩ : Fin (n - 1))) := by
    intro a
    apply htri a (.inl (⟨0, by omega⟩ : Fin (n - 1)))
    have h := c2slomqmn_epsHt_le a
    have h0 : epsHt n (minusWt n (.inl (⟨0, by omega⟩ : Fin (n - 1)))) =
        ((n - 1 : ℕ) : ℤ) := by
      simp only [minusWt, c2slomqmn_epsHt_single]
      simp
    simpa only [AddMonoidHom.smul_apply, one_smul, h0] using
      (show epsHt n (minusWt n a) - ((n - 1 : ℕ) : ℤ) < 1 by omega)
  rw [SmallO8mCurtis.naturalRep_apply]
  ext a
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, hcol,
    Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem c2slomqmn_naturalRep_highestChar {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (φ : K →+* k)
    {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H) :
    SmallO8mCurtis.naturalRep n b c φ g
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
      φ ((mat n g) (Sum.inl (⟨0, by omega⟩ : Fin (n - 1)))
        (Sum.inl (⟨0, by omega⟩ : Fin (n - 1)))) •
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) := by
  have hdiag : BlockDiag n (mat n g) := by
    change g ∈ ⨆ j, minusTorus n hirrQ j at hg
    exact Subgroup.iSup_induction (minusTorus n hirrQ)
      (C := fun g => BlockDiag n (mat n g)) hg
      (fun j x hx => blockDiag_mat_of_mem_minusTorus n hirrQ j hx)
      (by rw [mat_one]; exact blockDiag_one n)
      (fun x y hx hy => by rw [mat_mul]; exact blockDiag_mul n hx hy)
  ext a
  simp only [SmallO8mCurtis.naturalRep_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.map_apply]
  by_cases ha : a = Sum.inl (⟨0, by omega⟩ : Fin (n - 1))
  · subst ha
    simp
  · rw [hdiag.apply_eq_zero n ha (Or.inr (fun t => by simp))]
    simp [ha]

private theorem c2slomqmn_naturalRep_heckeT_highestVec {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (φ : K →+* k)
    (hK : 4 ≤ Nat.card K) (i : Fin (n - 1)) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).heckeT
      (SmallO8mCurtis.naturalRep n b c φ) i
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) = 0 := by
  classical
  let D := SmallO8mCurtis.curtisDatum n hn hirrQ
  have : Fintype (D.X i) := Fintype.ofFinite _
  have : Fintype K := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcount : (Fintype.card (D.X i) : k) = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff k 2 _).mpr (D.dvd_card_X i)
  rw [D.heckeT_apply]
  have hnn : D.n i = minusWeyl n hirrQ i := rfl
  have hmul : ∀ x : D.X i,
      SmallO8mCurtis.naturalRep n b c φ ((x : spinGroup _) * D.n i)
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
        SmallO8mCurtis.naturalRep n b c φ (x : spinGroup _)
          (SmallO8mCurtis.naturalRep n b c φ (D.n i)
            (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k))) := by
    intro x
    rw [map_mul, Module.End.mul_apply]
  have hsum : (∑ x : D.X i,
        SmallO8mCurtis.naturalRep n b c φ ((x : spinGroup _) * D.n i)
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k))) =
      ∑ x : D.X i, SmallO8mCurtis.naturalRep n b c φ (x : spinGroup _)
        (if i.val = 0 then Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k)
         else Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) :=
    Finset.sum_congr rfl fun x _ => by
      rw [hmul, hnn, c2slomqmn_naturalRep_Weyl_highest hn hirrQ φ i]
  rw [hsum]
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    clear hmul hnn hsum hcount
    have hk : i.val + 1 < n - 1 := by omega
    let f : K → D.X i := fun a =>
      ⟨(minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false (.ofAdd a),
        by
          change _ ∈ minusRootGroup n hirrQ (Pi.single i 1)
          rw [minusRootGroup_single_of_lt n hirrQ (k := i) hk]
          exact ⟨.ofAdd a, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a a' h => ?_, ?_⟩
      · have hx := congrArg Subtype.val h
        exact Multiplicative.ofAdd.injective
          ((minusFrame n b c).toHypFrame.longRoot_injective (succ_ne_of_lt n hk) true false hx)
      · intro x
        have hx : (x : spinGroup _) ∈ minusRootGroup n hirrQ (Pi.single i 1) := x.2
        rw [minusRootGroup_single_of_lt n hirrQ (k := i) hk] at hx
        obtain ⟨a, ha⟩ := hx
        exact ⟨a.toAdd, Subtype.ext ha⟩
    rw [← (Equiv.ofBijective f hf).sum_comp]
    simp_rw [Equiv.ofBijective_apply, show ∀ a : K,
      SmallO8mCurtis.naturalRep n b c φ (f a : spinGroup _)
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k)) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k) +
          φ a • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) from
      fun a => c2slomqmn_naturalRep_first_X_next_of_val_eq_zero hn φ hk hi a]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul k, ← Finset.sum_smul, ← map_sum]
    have hcard : (Fintype.card K : k) = 0 := by
      obtain ⟨m, -, hm⟩ := FiniteField.card K 2
      rw [hm, Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow (PNat.ne_zero m)]
    have hsum0 : ∑ a : K, a = 0 := by
      simpa using FiniteField.sum_pow_lt_card_sub_one K 1 (by
        rw [← Nat.card_eq_fintype_card]; omega)
    rw [hcard, zero_smul, hsum0, map_zero, zero_smul, add_zero]
  · rw [if_neg hi]
    have hfix : ∀ x : D.X i,
        SmallO8mCurtis.naturalRep n b c φ (x : spinGroup _)
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) :=
      fun x => (D.mem_fixU (SmallO8mCurtis.naturalRep n b c φ)).mp
        (c2slomqmn_highestVec_mem_fixU hn hirrQ φ) _ (D.X_le i x.2)
    simp_rw [hfix, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      hcount, zero_smul]

end Helpers

theorem omq_isCurtisType_omMinus_natural {n : ℕ} (hn : 4 ≤ n) {K k : Type} [Field K] [Finite K]
    [CharP K 2] [Field k] [CharP k 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : 4 ≤ Nat.card K) (φ : K →+* k) :
    (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType (SmallO8mCurtis.naturalRep n b c φ)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k))
      (fun g => φ ((mat n g) (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩))) 0 := by
  refine ⟨c2slomqmn_highestVec_mem_fixU hn hirr φ, ?_,
    fun g hg => c2slomqmn_naturalRep_highestChar hn hirr φ hg, fun i => ?_⟩
  · intro h
    have h0 := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin (n - 1)))
    simp at h0
  · simpa using c2slomqmn_naturalRep_heckeT_highestVec hn hirr φ hK i

end CFSG.LocalAnalysis.WeakClosure81
