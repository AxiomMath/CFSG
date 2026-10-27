module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNF
public import CFSG.LieType.D4Small.Om8Datum
public import CFSG.RankThree.GF2n.Stroth80.SmithEightHolds
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small CFSG.StandardType CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance CFSG.Open
  CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

@[expose] noncomputable def natRep (K : Type) [Field K] :
    Representation K (Om8 K) (Fin 4 ⊕ Fin 4 → K) where
  toFun g := Matrix.mulVecLin
    ((((reindexOm8 K).symm g : StatedOmega (StatedQuadPlus 4 K)) : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)
  map_one' := by
    rw [map_one]
    exact Matrix.mulVecLin_one
  map_mul' g h := by
    rw [map_mul]
    exact Matrix.mulVecLin_mul _ _

theorem natRep_apply {K : Type} [Field K] (g : Om8 K) (v : Fin 4 ⊕ Fin 4 → K) :
    natRep K g v = (((((reindexOm8 K).symm g : StatedOmega (StatedQuadPlus 4 K)) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) :=
  rfl

theorem natRep_reindex_symm {K : Type} [Field K] (g : Om8 K) (x : Fin (2 * 4) → K) :
    natRep K g ((reindexVectorEquiv (plusIndexEquiv 4)).symm x) =
      (reindexVectorEquiv (plusIndexEquiv 4)).symm (D4Rank.act g x) := by
  rw [natRep_apply]
  have h := statedDerivedReindexEquiv_symm_vector (plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K) g x
  simp only [matrixLinearEquiv_apply, toLinEquiv_apply] at h
  exact h

@[expose] def natW (N : ℕ) (k : Fin 4) (r : Bool) : Fin 4 → ZMod N :=
  castW N (Pi.single k (boolSign r))

theorem natW_apply (N : ℕ) (k : Fin 4) (r : Bool) (p : Fin 4) :
    natW N k r p = if p = k then ((boolSign r : ℤ) : ZMod N) else 0 := by
  by_cases h : p = k <;> simp [natW, castW, h]

theorem natW_self (N : ℕ) (k : Fin 4) (r : Bool) :
    natW N k r k = ((boolSign r : ℤ) : ZMod N) := by
  rw [natW_apply, if_pos rfl]

theorem natW_of_ne {N : ℕ} {k p : Fin 4} (h : p ≠ k) (r : Bool) : natW N k r p = 0 := by
  rw [natW_apply, if_neg h]

theorem natW_true (N : ℕ) (k : Fin 4) : natW N k true = Pi.single k 1 := by
  funext p
  rw [natW_apply, Pi.single_apply]
  simp

theorem natW_false (N : ℕ) (k : Fin 4) : natW N k false = Pi.single k (-1) := by
  funext p
  rw [natW_apply, Pi.single_apply]
  simp

theorem natW_not (N : ℕ) (k : Fin 4) (r : Bool) : natW N k (!r) = -natW N k r := by
  funext p
  rw [Pi.neg_apply, natW_apply, natW_apply]
  split_ifs <;> simp

theorem castW_lv_eq_natW_add (N : ℕ) (i j : Fin 4) (s t : Bool) :
    castW N (lv i j s t) = natW N i s + natW N j t := by
  funext p
  simp only [castW, natW, Pi.add_apply, Pi.single_apply, Int.cast_add]

private theorem int_not_dvd_two {N : ℕ} (hN : 3 ≤ N) {z : ℤ} (hz : z = 2 ∨ z = -2) :
    ¬ (N : ℤ) ∣ z := by
  intro h
  have h2 : (N : ℤ) ∣ 2 := by
    rcases hz with rfl | rfl
    · exact h
    · exact dvd_neg.1 h
  have := Int.le_of_dvd (by norm_num) h2
  omega

private theorem boolSign_cast_ne_zero {N : ℕ} (hN : 3 ≤ N) (r : Bool) :
    ((boolSign r : ℤ) : ZMod N) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : (N : ℤ) ∣ 1 := by
    rcases boolSign_eq_one_or_eq_neg_one r with h' | h' <;> rw [h'] at h
    · exact h
    · exact dvd_neg.1 h
  have := Int.le_of_dvd one_pos h1
  omega

private theorem boolSign_cast_inj {N : ℕ} (hN : 3 ≤ N) {r r' : Bool}
    (h : ((boolSign r : ℤ) : ZMod N) = boolSign r') : r = r' := by
  by_contra hne
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  refine int_not_dvd_two hN ?_ h
  cases r <;> cases r' <;> simp_all

private theorem eq_not_of_boolSign_cast_add {N : ℕ} (hN : 3 ≤ N) {r r' : Bool}
    (h : ((boolSign r : ℤ) : ZMod N) + boolSign r' = 0) : r = !r' := by
  by_contra hne
  rw [← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  refine int_not_dvd_two hN ?_ h
  cases r <;> cases r' <;> simp_all

theorem natW_inj {N : ℕ} (hN : 3 ≤ N) {k k' : Fin 4} {r r' : Bool}
    (h : natW N k r = natW N k' r') : k = k' ∧ r = r' := by
  have hk : k = k' := by
    by_contra hne
    have h1 := congrFun h k
    rw [natW_self, natW_of_ne hne] at h1
    exact boolSign_cast_ne_zero hN r h1
  subst hk
  refine ⟨rfl, boolSign_cast_inj hN ?_⟩
  have h1 := congrFun h k
  rwa [natW_self, natW_self] at h1

theorem natW_eq_iff {N : ℕ} (hN : 3 ≤ N) {k k' : Fin 4} {r r' : Bool} :
    natW N k r = natW N k' r' ↔ k = k' ∧ r = r' :=
  ⟨natW_inj hN, fun h => h.1 ▸ h.2 ▸ rfl⟩

theorem natW_not_add_castW_lv_j {N : ℕ} (i j : Fin 4) (s t : Bool) :
    natW N j (!t) + castW N (lv i j s t) = natW N i s := by
  rw [castW_lv_eq_natW_add, natW_not]
  abel

theorem natW_not_add_castW_lv_i {N : ℕ} (i j : Fin 4) (s t : Bool) :
    natW N i (!s) + castW N (lv i j s t) = natW N j t := by
  rw [castW_lv_eq_natW_add, natW_not]
  abel

theorem natW_add_castW_lv_ne {N : ℕ} (hN : 3 ≤ N) {i j : Fin 4} (hij : i ≠ j) {k : Fin 4}
    {r : Bool} (s t : Bool) (h1 : ¬ (k = j ∧ r = !t)) (h2 : ¬ (k = i ∧ r = !s)) (m : Fin 4)
    (r' : Bool) : natW N k r + castW N (lv i j s t) ≠ natW N m r' := by
  intro h
  rw [castW_lv_eq_natW_add] at h
  have hj := congrFun h j
  have hi := congrFun h i
  simp only [Pi.add_apply] at hj hi
  by_cases hk : k = j
  · have hki : i ≠ k := fun h => hij (h.trans hk)
    rw [natW_of_ne hki, natW_self, natW_of_ne hij, zero_add, add_zero] at hi
    have hm : i = m := by
      by_contra hm
      rw [natW_of_ne hm] at hi
      exact boolSign_cast_ne_zero hN s hi
    subst hm
    rw [hk, natW_self, natW_of_ne hij.symm, natW_self, natW_of_ne hij.symm, zero_add] at hj
    exact h1 ⟨hk, eq_not_of_boolSign_cast_add hN hj⟩
  · rw [natW_of_ne (Ne.symm hk), natW_of_ne hij.symm, natW_self, zero_add, zero_add] at hj
    have hm : j = m := by
      by_contra hm
      rw [natW_of_ne hm] at hj
      exact boolSign_cast_ne_zero hN t hj
    subst hm
    rw [natW_of_ne hij, natW_of_ne hij, natW_self, add_zero] at hi
    by_cases hki : i = k
    · subst hki
      rw [natW_self] at hi
      exact h2 ⟨rfl, eq_not_of_boolSign_cast_add hN hi⟩
    · rw [natW_of_ne hki, zero_add] at hi
      exact boolSign_cast_ne_zero hN s hi

section Basis

variable {K : Type} [Field K]

@[expose] noncomputable def natWts : Finset (Fin 4 → ZMod (Nat.card Kˣ)) :=
  Finset.univ.image (fun k : Fin 4 => (Pi.single k 1 : Fin 4 → ZMod (Nat.card Kˣ))) ∪
    Finset.univ.image (fun k : Fin 4 => (Pi.single k (-1) : Fin 4 → ZMod (Nat.card Kˣ)))

theorem mem_natWts {a : Fin 4 → ZMod (Nat.card Kˣ)} : a ∈ natWts (K := K) ↔ IsNatWt 1 a := by
  simp only [natWts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, IsNatWt]
  constructor
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨k, Or.inl rfl⟩
    · exact ⟨k, Or.inr rfl⟩
  · rintro ⟨k, rfl | rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩

@[expose] noncomputable def natBasis (a : Fin 4 → ZMod (Nat.card Kˣ)) : Fin 4 ⊕ Fin 4 → K :=
  Sum.elim (fun k => if a = Pi.single k 1 then 1 else 0)
    (fun k => if a = Pi.single k (-1) then 1 else 0)

theorem natBasis_inl (a : Fin 4 → ZMod (Nat.card Kˣ)) (k : Fin 4) :
    natBasis a (Sum.inl k) = (if a = Pi.single k 1 then 1 else 0 : K) := rfl

theorem natBasis_inr (a : Fin 4 → ZMod (Nat.card Kˣ)) (k : Fin 4) :
    natBasis a (Sum.inr k) = (if a = Pi.single k (-1) then 1 else 0 : K) := rfl

theorem exists_natW_of_mem {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ natWts (K := K)) :
    ∃ (k : Fin 4) (r : Bool), a = natW (Nat.card Kˣ) k r := by
  obtain ⟨k, rfl | rfl⟩ := mem_natWts.1 ha
  · exact ⟨k, true, (natW_true _ k).symm⟩
  · exact ⟨k, false, (natW_false _ k).symm⟩

theorem natW_mem_natWts (k : Fin 4) (r : Bool) :
    natW (Nat.card Kˣ) k r ∈ natWts (K := K) := by
  rw [mem_natWts]
  cases r
  · exact ⟨k, Or.inr (natW_false _ k)⟩
  · exact ⟨k, Or.inl (natW_true _ k)⟩

theorem natBasis_natW_inl (hN : 3 ≤ Nat.card Kˣ) (k m : Fin 4) (r : Bool) :
    natBasis (natW (Nat.card Kˣ) k r) (Sum.inl m) = (if k = m ∧ r = true then 1 else 0 : K) := by
  rw [natBasis_inl, ← natW_true]
  simp only [natW_eq_iff hN]

theorem natBasis_natW_inr (hN : 3 ≤ Nat.card Kˣ) (k m : Fin 4) (r : Bool) :
    natBasis (natW (Nat.card Kˣ) k r) (Sum.inr m) = (if k = m ∧ r = false then 1 else 0 : K) := by
  rw [natBasis_inr, ← natW_false]
  simp only [natW_eq_iff hN]

theorem natBasis_natW (hN : 3 ≤ Nat.card Kˣ) (k : Fin 4) (r : Bool) :
    natBasis (natW (Nat.card Kˣ) k r) = (plusVec 4 K k r) := by
  funext x
  rcases x with m | m
  · rw [natBasis_natW_inl hN]
    cases r <;> by_cases h : k = m <;> simp [plusVec, Pi.single_apply, h, eq_comm]
  · rw [natBasis_natW_inr hN]
    cases r <;> by_cases h : k = m <;> simp [plusVec, Pi.single_apply, h, eq_comm]

theorem natBasis_single_one (hN : 3 ≤ Nat.card Kˣ) (k : Fin 4) :
    natBasis (Pi.single k 1 : Fin 4 → ZMod (Nat.card Kˣ)) =
      (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) := by
  rw [← natW_true, natBasis_natW hN, plusVec_true]

theorem natBasis_single_neg_one (hN : 3 ≤ Nat.card Kˣ) (k : Fin 4) :
    natBasis (Pi.single k (-1) : Fin 4 → ZMod (Nat.card Kˣ)) =
      (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) := by
  rw [← natW_false, natBasis_natW hN, plusVec_false]

theorem nfType_natWts : NFType 0 (natWts (K := K)) :=
  Or.inl fun a => by rw [pow_zero]; exact mem_natWts

end Basis

section Action

variable {K : Type} [Field K]

theorem reindexVectorEquiv_symm_pvec (k : Fin 4) (r : Bool) :
    (reindexVectorEquiv (plusIndexEquiv 4)).symm (AutOm.pvec k r) = (plusVec 4 K k r) :=
  LinearEquiv.symm_apply_apply _ _

theorem natRep_plusVec (g : Om8 K) (k : Fin 4) (r : Bool) :
    natRep K g (plusVec 4 K k r) =
      (reindexVectorEquiv (plusIndexEquiv 4)).symm (D4Rank.act g (AutOm.pvec k r)) := by
  rw [← natRep_reindex_symm, reindexVectorEquiv_symm_pvec]

theorem natRep_h_plusVec [Finite K] [CharP K 2] (t : Fin 4 → Kˣ) (k : Fin 4) (r : Bool) :
    natRep K ((om8Datum K).h t) (plusVec 4 K k r) =
      ((t k : K) ^ boolSign r) • plusVec 4 K k r := by
  rw [natRep_plusVec, om8Datum_h, act_dg_pvec, map_smul, reindexVectorEquiv_symm_pvec]

theorem wtChar_natW [Finite K] [CharP K 2] (k : Fin 4) (r : Bool) (t : Fin 4 → Kˣ) :
    ((D4Datum.wtChar (natW (Nat.card Kˣ) k r) t : Kˣ) : K) = (t k : K) ^ boolSign r := by
  rw [natW, D4Datum.wtChar_castW, torusChar_single, Units.val_zpow_eq_zpow_val]

theorem natRep_plusVec_mem_wtSpace [Finite K] [CharP K 2] (k : Fin 4) (r : Bool) :
    plusVec 4 K k r ∈ (om8Datum K).wtSpace (natRep K) (natW (Nat.card Kˣ) k r) := by
  rw [D4Datum.mem_wtSpace]
  intro t
  rw [natRep_h_plusVec, wtChar_natW]

private theorem neg_vec_eq_self [CharP K 2] {ι : Type*} (v : ι → K) : -v = v :=
  funext fun i => CharTwo.neg_eq (v i)

theorem natRep_X8_plusVec [CharP K 2] {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : K)
    (k : Fin 4) (r : Bool) :
    natRep K (X8 (fromStd (lv i j s t)) c) (plusVec 4 K k r) =
      plusVec 4 K k r + (if k = j ∧ r = !t then c • plusVec 4 K i s else 0) +
        (if k = i ∧ r = !s then c • plusVec 4 K j t else 0) := by
  rw [natRep_plusVec, act_X8_pvec hij (toStdD_fromStd_lv i j s t hij) c k r, sub_eq_add_neg,
    map_add, map_add, map_neg, reindexVectorEquiv_symm_pvec]
  by_cases h1 : k = j ∧ r = !t
  · have h2 : ¬ (k = i ∧ r = !s) := fun h => hij (h.1.symm.trans h1.1)
    simp only [if_pos h1, if_neg h2, map_zero, map_smul, reindexVectorEquiv_symm_pvec, neg_zero,
      add_zero]
  · by_cases h2 : k = i ∧ r = !s
    · simp only [if_neg h1, if_pos h2, map_zero, map_smul, reindexVectorEquiv_symm_pvec,
        neg_vec_eq_self, add_zero]
    · simp only [if_neg h1, if_neg h2, map_zero, neg_zero, add_zero]

end Action

section Normal

variable {K : Type} [Field K]

theorem nf_natRep [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    NF (om8Datum K) (natRep K) 0 natWts natBasis where
  ne_zero a ha := by
    have hN : 3 ≤ Nat.card Kˣ := by rw [Nat.card_units]; omega
    obtain ⟨k, r, rfl⟩ := exists_natW_of_mem ha
    rw [natBasis_natW hN]
    cases r
    · rw [plusVec_false]
      exact Pi.single_ne_zero_iff.mpr one_ne_zero
    · rw [plusVec_true]
      exact Pi.single_ne_zero_iff.mpr one_ne_zero
  mem_wtSpace a ha := by
    have hN : 3 ≤ Nat.card Kˣ := by rw [Nat.card_units]; omega
    obtain ⟨k, r, rfl⟩ := exists_natW_of_mem ha
    rw [natBasis_natW hN]
    exact natRep_plusVec_mem_wtSpace k r
  span_eq := by
    have hN : 3 ≤ Nat.card Kˣ := by rw [Nat.card_units]; omega
    refine eq_top_iff.2 ?_
    rw [← (Pi.basisFun K (Fin 4 ⊕ Fin 4)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, rfl⟩
    rw [Pi.basisFun_apply]
    rcases x with k | k
    · exact ⟨natW (Nat.card Kˣ) k true, natW_mem_natWts k true, by
        rw [natBasis_natW hN, plusVec_true]⟩
    · exact ⟨natW (Nat.card Kˣ) k false, natW_mem_natWts k false, by
        rw [natBasis_natW hN, plusVec_false]⟩
  root α hα c a ha := by
    have hN : 3 ≤ Nat.card Kˣ := by rw [Nat.card_units]; omega
    obtain ⟨i, j, s, t, hij, rfl, -⟩ := exists_lv_of_isD4Root hα
    obtain ⟨k, r, rfl⟩ := exists_natW_of_mem ha
    simp only [pow_zero, one_smul, pow_one]
    rw [om8Datum_x, natBasis_natW hN, natRep_X8_plusVec hij s t c k r]
    by_cases h1 : k = j ∧ r = !t
    · have h2 : ¬ (k = i ∧ r = !s) := fun h => hij (h.1.symm.trans h1.1)
      have hw : natW (Nat.card Kˣ) k r + castW (Nat.card Kˣ) (lv i j s t) =
          natW (Nat.card Kˣ) i s := by
        rw [h1.1, h1.2]
        exact natW_not_add_castW_lv_j i j s t
      rw [hw, if_pos (natW_mem_natWts i s), natBasis_natW hN, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : k = i ∧ r = !s
      · have hw : natW (Nat.card Kˣ) k r + castW (Nat.card Kˣ) (lv i j s t) =
            natW (Nat.card Kˣ) j t := by
          rw [h2.1, h2.2]
          exact natW_not_add_castW_lv_i i j s t
        rw [hw, if_pos (natW_mem_natWts j t), natBasis_natW hN, if_neg h1, if_pos h2, add_zero]
      · have hn : natW (Nat.card Kˣ) k r + castW (Nat.card Kˣ) (lv i j s t) ∉
            natWts (K := K) := by
          intro hmem
          obtain ⟨m, r', hm⟩ := exists_natW_of_mem hmem
          exact natW_add_castW_lv_ne hN hij s t h1 h2 m r' hm
        rw [if_neg hn, if_neg h1, if_neg h2, add_zero, add_zero]

end Normal

end CFSG.RankThree.GF2n.Stroth80.Tri

end
