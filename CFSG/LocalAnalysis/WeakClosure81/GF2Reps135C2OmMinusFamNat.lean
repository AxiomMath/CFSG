module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisDescent
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNatSimpleF2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix TensorProduct

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

section Helpers

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {k : Type} [Field k] [CharP k 2]

private theorem w135c2_omfMNat_epsHt_single {n : ℕ} (i : Fin (n - 1)) (z : ℤ) :
    epsHt n (Pi.single i z) = (((n - 1 : ℕ) : ℤ) - i) * z := by
  simp [epsHt, Pi.single_apply]

private theorem w135c2_omfMNat_zero_succ_lt {n : ℕ} (hn : 4 ≤ n) :
    (⟨0, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by
  have h0 : (⟨0, by omega⟩ : Fin (n - 1)).val = 0 := rfl
  omega

private theorem w135c2_omfMNat_epsHt_le {n : ℕ}
    (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    epsHt n (minusWt n a) ≤ ((n - 1 : ℕ) : ℤ) := by
  rcases a with a | a | a
  · simp only [minusWt, w135c2_omfMNat_epsHt_single]
    have ha : (a : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
      have := a.2
      omega
    linarith
  · simp only [minusWt, w135c2_omfMNat_epsHt_single]
    have ha : (a : ℤ) < ((n - 1 : ℕ) : ℤ) := by
      have := a.2
      omega
    linarith
  · simp only [minusWt, map_zero]
    positivity

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem w135c2_omfMNat_naturalRep_map_vector {n : ℕ} (φ : K →+* k)
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

omit [Finite K] [CharP k 2] in
private theorem w135c2_omfMNat_naturalRep_Weyl_highest {n : ℕ} (hn : 4 ≤ n)
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
        (k := (⟨0, by omega⟩ : Fin (n - 1))) (w135c2_omfMNat_zero_succ_lt hn)]
      have h := (minusFrame n b c).toHypFrame.spinAction_longWeyl_vec_left
        (succ_ne_of_lt n (k := (⟨0, by omega⟩ : Fin (n - 1)))
          (w135c2_omfMNat_zero_succ_lt hn)) true false
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
  have h := w135c2_omfMNat_naturalRep_map_vector (n := n) φ (minusWeyl n hirrQ i)
    (eVec n (⟨0, by omega⟩ : Fin (n - 1)))
  rw [hact] at h
  have hvec : ∀ j : Fin (n - 1), (fun a => φ (eVec n j a)) =
      (Pi.single (Sum.inl j) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → k) := by
    intro j
    ext a
    simp [eVec, Pi.single_apply]
  simp only [hvec] at h
  split_ifs at h ⊢ <;> simpa only [hvec] using h

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem w135c2_omfMNat_naturalRep_first_X_next_of_val_eq_zero {n : ℕ} (_hn : 4 ≤ n)
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
  have h := w135c2_omfMNat_naturalRep_map_vector (n := n) φ
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

omit [CharP k 2] in
private theorem w135c2_omfMNat_highestVec_mem_fixU {n : ℕ} (hn : 4 ≤ n)
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
    have h := w135c2_omfMNat_epsHt_le a
    have h0 : epsHt n (minusWt n (.inl (⟨0, by omega⟩ : Fin (n - 1)))) =
        ((n - 1 : ℕ) : ℤ) := by
      simp only [minusWt, w135c2_omfMNat_epsHt_single]
      simp
    simpa only [AddMonoidHom.smul_apply, one_smul, h0] using
      (show epsHt n (minusWt n a) - ((n - 1 : ℕ) : ℤ) < 1 by omega)
  rw [SmallO8mCurtis.naturalRep_apply]
  ext a
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, hcol,
    Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

omit [CharP K 2] [CharP k 2] in
private theorem w135c2_omfMNat_naturalRep_shortTorus_fixes {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (φ : K →+* k)
    {h : spinGroup (quadMinus n K b c)}
    (hh : h ∈ shortTorus n hirrQ ⟨n - 2, by omega⟩) :
    SmallO8mCurtis.naturalRep n b c φ h
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) := by
  obtain ⟨a, -, rfl⟩ := (mem_shortTorus_iff n hirrQ ⟨n - 2, by omega⟩).1 hh
  have h0 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ (⟨n - 2, by omega⟩ : Fin (n - 1)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have h := w135c2_omfMNat_naturalRep_map_vector (n := n) φ
    (shortTorusElt n hirrQ ⟨n - 2, by omega⟩ a)
    (eVec n (⟨0, by omega⟩ : Fin (n - 1)))
  rw [spinAction_shortTorusElt_eVec_of_ne n hirrQ
    (i := ⟨n - 2, by omega⟩) (j := ⟨0, by omega⟩) h0 a] at h
  have hvec : (fun b => φ (eVec n (⟨0, by omega⟩ : Fin (n - 1)) b)) =
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) := by
    ext b
    simp [eVec, Pi.single_apply]
  simpa [hvec] using h

omit [CharP k 2] in
private lemma w135c2_omfMNat_sum_X_zero {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i : Fin (n - 1)} (hi : i.val = 0)
    [Fintype K] [Fintype ((SmallO8mCurtis.curtisDatum n hn hirrQ).X i)]
    (φ : K →+* k) :
    (∑ x : (SmallO8mCurtis.curtisDatum n hn hirrQ).X i,
        SmallO8mCurtis.naturalRep n b c φ (x : spinGroup _)
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k))) =
      ∑ a : K, (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k) +
        φ a • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) := by
  classical
  have hk : i.val + 1 < n - 1 := by omega
  let D := SmallO8mCurtis.curtisDatum n hn hirrQ
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
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Equiv.ofBijective_apply]
  simpa using w135c2_omfMNat_naturalRep_first_X_next_of_val_eq_zero hn φ hk hi a

omit [Finite K] [CharP K 2] in
private lemma w135c2_omfMNat_pair_eq_univ [Fintype K] [DecidableEq K]
    (hK : Nat.card K = 2) : ({0, 1} : Finset K) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_pair (zero_ne_one : (0 : K) ≠ 1), ← Nat.card_eq_fintype_card, hK]

omit [Finite K] [CharP K 2] in
private lemma w135c2_omfMNat_sum_K_eq_one [Fintype K] [DecidableEq K]
    (hK : Nat.card K = 2) : ∑ a : K, a = 1 := by
  rw [← w135c2_omfMNat_pair_eq_univ hK, Finset.sum_pair (zero_ne_one : (0 : K) ≠ 1)]
  simp

omit [Field K] [Finite K] [CharP K 2] in
private lemma w135c2_omfMNat_card_K_eq_zero [Fintype K] (hK : Nat.card K = 2) :
    (Fintype.card K : k) = 0 := by
  rw [← Nat.card_eq_fintype_card, hK]
  exact CharTwo.two_eq_zero

private theorem w135c2_omfMNat_heckeT_zero {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) (φ : K →+* k)
    {i : Fin (n - 1)} (hi : i.val = 0) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).heckeT (SmallO8mCurtis.naturalRep n b c φ) i
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
      (1 : k) • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := SmallO8mCurtis.curtisDatum n hn hirrQ
  have : Fintype (D.X i) := Fintype.ofFinite _
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
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin (n - 1))) (1 : k)) :=
    Finset.sum_congr rfl fun x _ => by
      rw [hmul, hnn, w135c2_omfMNat_naturalRep_Weyl_highest hn hirrQ φ i, if_pos hi]
  rw [hsum, w135c2_omfMNat_sum_X_zero hn hirrQ hi φ]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
    ← Finset.sum_smul, ← map_sum]
  rw [w135c2_omfMNat_card_K_eq_zero hK, zero_smul, w135c2_omfMNat_sum_K_eq_one hK,
    map_one, one_smul, zero_add]

private theorem w135c2_omfMNat_heckeT_ne {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (φ : K →+* k) {i : Fin (n - 1)}
    (hi : i.val ≠ 0) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).heckeT (SmallO8mCurtis.naturalRep n b c φ) i
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
      (0 : k) • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) := by
  classical
  let D := SmallO8mCurtis.curtisDatum n hn hirrQ
  have : Fintype (D.X i) := Fintype.ofFinite _
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
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) :=
    Finset.sum_congr rfl fun x _ => by
      rw [hmul, hnn, w135c2_omfMNat_naturalRep_Weyl_highest hn hirrQ φ i, if_neg hi]
  rw [hsum]
  have hfix : ∀ x : D.X i,
      SmallO8mCurtis.naturalRep n b c φ (x : spinGroup _)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k) :=
    fun x => (D.mem_fixU (SmallO8mCurtis.naturalRep n b c φ)).mp
      (w135c2_omfMNat_highestVec_mem_fixU hn hirrQ φ) _ (D.X_le i x.2)
  simp_rw [hfix, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, hcount]

omit [Finite K] [CharP K 2] [CharP k 2] in
private theorem w135c2_omfMNat_matRep_matMap_matHom {n : ℕ} (φ : K →+* k) :
    CFSG.QuasithinUnique.Setup.X7.matRep
        (CFSG.QuasithinUnique.Setup.X7.matMap φ (matHom n)) =
      SmallO8mCurtis.naturalRep n b c φ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply,
    CFSG.QuasithinUnique.Setup.X7.matMap_apply, SmallO8mCurtis.naturalRep_apply]
  rfl

end Helpers

theorem isCurtisType_omMinus_two_natural_family (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k] [CharP k 2] (φ : K →+* k)
    {χ : spinGroup (quadMinus n K b c) → k}
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h = 1) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).IsCurtisType (SmallO8mCurtis.naturalRep n b c φ)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k)) χ
      (fun s => if s.val = 0 then 1 else 0) := by
  refine ⟨w135c2_omfMNat_highestVec_mem_fixU hn hirrQ φ, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin (n - 1)))
    simp at this
  · intro h hh
    rw [w135c2_omfMNat_naturalRep_shortTorus_fixes hn hirrQ φ
        (omMinus_two_H_le_shortTorus hK hn hirrQ hh), hχ h hh, one_smul]
  · intro s
    simp only []
    by_cases hs : s.val = 0
    · rw [if_pos hs]
      exact w135c2_omfMNat_heckeT_zero hn hirrQ hK φ hs
    · rw [if_neg hs]
      exact w135c2_omfMNat_heckeT_ne hn hirrQ φ hs

theorem omMinus_two_exists_addEquiv_of_isCurtisType (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) V) [ρ.IsIrreducible]
    (k : Type) [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus n K b c))) ρ.asModule) k]
    (φ : K →+* k)
    {y : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus n K b c))) ρ.asModule]
      ρ.asModule}
    {χ : spinGroup (quadMinus n K b c) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ
      (fun s => if s.val = 0 then 1 else 0))
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h = 1) :
    ∃ β : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      ∀ (g : spinGroup (quadMinus n K b c)) (v : V), β (ρ g v) = mat n g *ᵥ β v := by
  refine exists_addEquiv_of_isCurtisType (D := SmallO8mCurtis.curtisDatum n hn hirrQ)
    (ρ := ρ) (R := matHom n) ?_ k φ ?_ ht ?_
    (y := Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n - 1))) (1 : k))
  · intro A hA
    exact omq_omMinus_natural_addSubgroup_simple hn hirrQ A fun g v hv =>
      (show spinMatrix (quadMinus n K b c) g *ᵥ v ∈ A from hA g (v := v) hv)
  · rw [w135c2_omfMNat_matRep_matMap_matHom]
    exact SmallO8mCurtis.naturalRep_isSimple hn hirrQ φ
  · rw [w135c2_omfMNat_matRep_matMap_matHom]
    exact isCurtisType_omMinus_two_natural_family hK hn hirrQ φ hχ

end CFSG.LocalAnalysis.WeakClosure81
