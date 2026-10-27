module

public import CFSG.Timmesfeld.Transvection.OddModelHeis

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

variable {m : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (hm : ¬Even m)

private theorem antidiag_mul_apply' (C : Matrix (Fin m) (Fin m) F) (x b : Fin m) :
    ((antidiag m : Matrix (Fin m) (Fin m) F) * C) x b = C (Fin.rev x) b := by
  simp only [antidiag, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mul_antidiag_apply' (C : Matrix (Fin m) (Fin m) F) (a b : Fin m) :
    (C * (antidiag m : Matrix (Fin m) (Fin m) F)) a b = C a (Fin.rev b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev b)]
  · simp [antidiag, Fin.rev_rev]
  · intro k _ hk
    have h : b ≠ Fin.rev k := by
      intro e
      apply hk
      rw [e, Fin.rev_rev]
    simp only [antidiag, Matrix.of_apply, if_neg h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem antidiag_mul_antidiag' :
    (antidiag m : Matrix (Fin m) (Fin m) F) * antidiag m = 1 := by
  ext a b
  rw [antidiag_mul_apply']
  simp only [antidiag, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · have h2 : b ≠ Fin.rev (Fin.rev a) := by rw [Fin.rev_rev]; exact Ne.symm h
    simp [h, Ne.symm h, h2]

theorem mat_inv_apply (g : SU σ m) (i j : Fin m) :
    mat σ m g⁻¹ i j = σ (mat σ m g (Fin.rev j) (Fin.rev i)) := by
  have hiso := conjTr_mat_mul g
  have hleft : (antidiag m * conjTr σ (mat σ m g) * antidiag m) * mat σ m g = 1 := by
    calc (antidiag m * conjTr σ (mat σ m g) * antidiag m) * mat σ m g
        = antidiag m * (conjTr σ (mat σ m g) * antidiag m * mat σ m g) := by
          simp only [Matrix.mul_assoc]
      _ = antidiag m * antidiag m := by rw [hiso]
      _ = 1 := antidiag_mul_antidiag'
  have hmatinv : mat σ m g⁻¹ =
      (antidiag m * conjTr σ (mat σ m g) * antidiag m : Matrix (Fin m) (Fin m) F) := by
    have h1 : (mat σ m g)⁻¹ =
        (antidiag m * conjTr σ (mat σ m g) * antidiag m : Matrix (Fin m) (Fin m) F) :=
      Matrix.inv_eq_left_inv hleft
    have h2 : mat σ m g * mat σ m g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h3 : (mat σ m g)⁻¹ = mat σ m g⁻¹ := Matrix.inv_eq_right_inv h2
    rw [← h3, h1]
  rw [hmatinv]
  have hentry : (antidiag m * conjTr σ (mat σ m g) * antidiag m :
      Matrix (Fin m) (Fin m) F) i j =
      conjTr σ (mat σ m g) (Fin.rev i) (Fin.rev j) := by
    rw [Matrix.mul_assoc, antidiag_mul_apply', mul_antidiag_apply']
  rw [hentry]
  simp [conjTr, Matrix.transpose_apply]


private def wtRoot (a : Fin (m / 2) ⊕ Fin (m / 2)) : Fin (m / 2) → ℤ :=
  match a with
  | Sum.inl k => fun j => if k.val ≤ j.val then 1 else 0
  | Sum.inr k => fun j => if k.val ≤ j.val then -1 else 0

private theorem toStd_wtRoot (hm : ¬Even m) (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    toStd m (wtRoot (m := m) a) = wt a := by
  rcases a with k | k
  · funext j
    rw [toStd, if_neg hm]
    by_cases hjk : j = k
    · subst hjk
      simp [wtRoot, wt]
    · simp only [wtRoot, wt, Pi.sub_apply, Pi.single_apply, if_neg hjk]
      split_ifs <;> omega
  · funext j
    rw [toStd, if_neg hm]
    by_cases hjk : j = k
    · subst hjk
      simp [wtRoot, wt]
    · simp only [wtRoot, wt, Pi.sub_apply, Pi.single_apply, if_neg hjk, Pi.neg_apply]
      split_ifs <;> omega

variable (σ) in
@[expose] def flagSubgroup (a : Fin (m / 2) ⊕ Fin (m / 2)) : Subgroup (SU σ m) where
  carrier := {g | ∀ i j, j ≠ crd (Sum.swap a) → i ≠ j → i ≠ crd a → mat σ m g i j = 0}
  mul_mem' := by
    intro g h hg hh i j hj hij hia
    rw [map_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkj : k = j
    · rw [hkj, hg i j hj hij hia, zero_mul]
    · by_cases hka : k = crd a
      · have hne : crd a ≠ crd (Sum.swap a) := by
          rw [crd_swap]
          exact crd_ne_rev a
        rw [hka, hg i (crd a) hne hia hia, zero_mul]
      · rw [hh k j hj hkj hka, mul_zero]
  one_mem' := by
    intro i j hj hij hia
    rw [map_one, Matrix.one_apply]
    exact if_neg hij
  inv_mem' := by
    intro g hg i j hj hij hia
    rw [mat_inv_apply, hg (Fin.rev j) (Fin.rev i) ?_ ?_ ?_, map_zero]
    · rw [crd_swap]
      exact fun e => hia (Fin.rev_injective e)
    · exact fun e => hij (Fin.rev_injective e).symm
    · intro e
      apply hj
      rw [crd_swap, ← e, Fin.rev_rev]

private theorem suHeis_mem_flagSubgroup_of_valid {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v : F}
    (h : v + σ v + σ u * u = 0) :
    suHeis σ hσ hm a u v ∈ flagSubgroup σ a := by
  rw [flagSubgroup]
  intro i j hj hij hia
  rw [mat_suHeis hσ hm h, heisenbergMatrix]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp_all [crd_swap]

theorem suHeis_mem_flagSubgroup (a : Fin (m / 2) ⊕ Fin (m / 2)) (u v : F) :
    suHeis σ hσ hm a u v ∈ flagSubgroup σ a := by
  have hγ := toStd_wtRoot (m := m) hm a
  have hmem := suHeis_mem hσ hm hγ u v
  obtain ⟨u', v', hv', heq⟩ :=
    (mem_rootGroup_iff_suHeis hσ hm hγ (suHeis σ hσ hm a u v)).mp hmem
  rw [← heq]
  exact suHeis_mem_flagSubgroup_of_valid hσ hm hv'

theorem suElt_mem_flagSubgroup {a d : Fin (m / 2) ⊕ Fin (m / 2)} (had : idx a ≠ idx d) (t : F) :
    suElt σ hσ a d t ∈ flagSubgroup σ a := by
  rw [flagSubgroup]
  intro i j hj hij hia
  rw [mat_suElt hσ had]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, single_apply]
  simp [hij, hia, hj, Ne.symm hia, Ne.symm hj]

theorem suLong_mem_flagSubgroup (a : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) :
    suLong σ a c ∈ flagSubgroup σ a := by
  rw [flagSubgroup]
  by_cases h : c + σ c = 0
  · intro i j hj hij hia
    rw [mat_suLong a h]
    simp only [Matrix.add_apply, Matrix.one_apply, single_apply]
    simp [hij, hia, hj, Ne.symm hia, Ne.symm hj]
  · intro i j hj hij hia
    rw [suLong, dite_eq_right h, map_one, Matrix.one_apply]
    exact if_neg hij

theorem suHeis_mem_flagSubgroup_iff {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {u v : F} (h : v + σ v + σ u * u = 0) :
    suHeis σ hσ hm b u v ∈ flagSubgroup σ a ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hmem
    have hba : crd b ≠ crd a := fun e => ne_of_idx_ne hab (crd_injective e)
    have hmem' : ∀ i j, j ≠ crd (Sum.swap a) → i ≠ j → i ≠ crd a →
        mat σ m (suHeis σ hσ hm b u v) i j = 0 := hmem
    change ∀ i j, j ≠ crd (Sum.swap a) → i ≠ j → i ≠ crd a →
        mat σ m (suHeis σ hσ hm b u v) i j = 0 at hmem'

    have h1 : mat σ m (suHeis σ hσ hm b u v) (crd b) (midIdx m hm) = 0 :=
      hmem' (crd b) (midIdx m hm) (crd_ne_midIdx hm (Sum.swap a)).symm
        (crd_ne_midIdx hm b) hba
    rw [mat_suHeis_apply_mid hσ hm h] at h1
    obtain ⟨_, _, _, hbb⟩ := ne_facts hab.symm
    have hbba : crd (Sum.swap b) ≠ crd (Sum.swap a) := fun e => hbb (crd_injective e)
    have h2 : mat σ m (suHeis σ hσ hm b u v) (crd b) (crd (Sum.swap b)) = 0 :=
      hmem' (crd b) (crd (Sum.swap b)) hbba (by rw [crd_swap]; exact crd_ne_rev b) hba
    rw [mat_suHeis_apply_swap hσ hm h] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rw [suHeis_zero_left hσ hm b, suLong_zero]
    exact one_mem _


private theorem idxFacts (hm : ¬Even m) {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) :
    crd a ≠ crd b ∧ crd a ≠ Fin.rev (crd b) ∧ Fin.rev (crd a) ≠ crd b ∧
      Fin.rev (crd a) ≠ Fin.rev (crd b) ∧ crd a ≠ Fin.rev (crd a) ∧
      crd b ≠ Fin.rev (crd b) ∧ crd a ≠ midIdx m hm ∧ crd b ≠ midIdx m hm ∧
      Fin.rev (crd a) ≠ midIdx m hm ∧ Fin.rev (crd b) ≠ midIdx m hm ∧ a ≠ b := by
  obtain ⟨hba, hbAa, hbAa', hbb⟩ := ne_facts hab
  refine ⟨?_, ?_, ?_, ?_, crd_ne_rev a, crd_ne_rev b, crd_ne_midIdx hm a, crd_ne_midIdx hm b,
    ?_, ?_, hba⟩
  · exact fun e => hba (crd_injective e)
  · intro e
    have e' : crd a = crd (Sum.swap b) := by rwa [← crd_swap] at e
    exact hbAa' (crd_injective e')
  · intro e
    have e' : crd (Sum.swap a) = crd b := by rwa [← crd_swap] at e
    exact hbAa (crd_injective e')
  · intro e
    have e' : crd (Sum.swap a) = crd (Sum.swap b) := by rwa [← crd_swap, ← crd_swap] at e
    exact hbb (crd_injective e')
  · rw [← crd_swap]; exact crd_ne_midIdx hm (Sum.swap a)
  · rw [← crd_swap]; exact crd_ne_midIdx hm (Sum.swap b)


private def heisNil (σ : F ≃+* F) (hm : ¬Even m) (a : Fin (m / 2) ⊕ Fin (m / 2)) (u v : F) :
    Matrix (Fin m) (Fin m) F :=
  single (crd a) (midIdx m hm) u - single (midIdx m hm) (Fin.rev (crd a)) (σ u) +
    single (crd a) (Fin.rev (crd a)) v

private def suEltNil (σ : F ≃+* F) (a d : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) :
    Matrix (Fin m) (Fin m) F :=
  single (crd a) (crd (Sum.swap d)) c - single (crd d) (crd (Sum.swap a)) (σ c)

private theorem matrix_charP (hm : ¬Even m) [CharP F 2] :
    CharP (Matrix (Fin m) (Fin m) F) 2 := by
  have hm0 : m ≠ 0 := fun h => hm (by rw [h]; exact ⟨0, rfl⟩)
  have hpos : 0 < m := Nat.pos_of_ne_zero hm0
  refine charP_of_injective_ringHom (f := Matrix.scalar (Fin m)) ?_ 2
  intro x y h
  have h' : (fun _ : Fin m => x) = (fun _ : Fin m => y) := by
    apply Matrix.diagonal_injective
    simpa [Matrix.scalar_apply] using h
  exact congrFun h' ⟨0, hpos⟩

private theorem heisNil_prod_facts [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) {u v u' v' : F} :
    heisNil σ hm b u v * heisNil σ hm b u v =
        single (crd b) (Fin.rev (crd b)) (u * σ u) ∧
    heisNil σ hm a u' v' * heisNil σ hm a u' v' =
        single (crd a) (Fin.rev (crd a)) (u' * σ u') ∧
    heisNil σ hm b u v * heisNil σ hm a u' v' =
        single (crd b) (crd (Sum.swap a)) (u * σ u') ∧
    heisNil σ hm a u' v' * heisNil σ hm b u v =
        single (crd a) (crd (Sum.swap b)) (u' * σ u) ∧
    heisNil σ hm b u v * heisNil σ hm b u v * heisNil σ hm b u v = 0 ∧
    heisNil σ hm a u' v' * heisNil σ hm a u' v' * heisNil σ hm a u' v' = 0 ∧
    heisNil σ hm b u v * heisNil σ hm b u v * heisNil σ hm a u' v' = 0 ∧
    heisNil σ hm b u v * heisNil σ hm a u' v' * heisNil σ hm a u' v' = 0 ∧
    heisNil σ hm a u' v' * heisNil σ hm b u v * heisNil σ hm b u v = 0 ∧
    heisNil σ hm a u' v' * heisNil σ hm b u v * heisNil σ hm a u' v' = 0 ∧
    heisNil σ hm b u v * heisNil σ hm a u' v' * heisNil σ hm b u v = 0 ∧
    heisNil σ hm a u' v' * heisNil σ hm b u v * heisNil σ hm a u' v' = 0 := by
  obtain ⟨h_ab, h_aB, h_Ab, h_AB, h_aa, h_bb, h_am, h_bm, h_Am, h_Bm, hba⟩ := idxFacts hm hab
  haveI := matrix_charP (F := F) (m := m) hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [heisNil, add_mul, mul_add, sub_mul, mul_sub, single_mul_single', crd_injective.eq_iff,
      Fin.rev_inj, Sum.swap_swap, crd_swap, h_ab, h_ab.symm, h_aB, h_aB.symm, h_Ab, h_Ab.symm,
      h_AB, h_AB.symm, h_aa, h_aa.symm, h_bb, h_bb.symm, h_am, h_am.symm, h_bm, h_bm.symm,
      h_Am, h_Am.symm, h_Bm, h_Bm.symm, hba, hba.symm, CharTwo.neg_eq, zero_mul, mul_zero,
      add_zero, zero_add, sub_self, sub_zero]



private def nilSuEltSwap (a b : Fin (m / 2) ⊕ Fin (m / 2)) (s : F) : Matrix (Fin m) (Fin m) F :=
  suEltNil σ a (Sum.swap b) s

private def nilSuHeis (b : Fin (m / 2) ⊕ Fin (m / 2)) (u v : F) : Matrix (Fin m) (Fin m) F :=
  heisNil σ hm b u v

private def nilSuHeisScaled (a : Fin (m / 2) ⊕ Fin (m / 2)) (s u v : F) :
    Matrix (Fin m) (Fin m) F :=
  heisNil σ hm a (s * u) (σ s * s * v)

private def nilSuEltScaled (a b : Fin (m / 2) ⊕ Fin (m / 2)) (s v : F) :
    Matrix (Fin m) (Fin m) F :=
  suEltNil σ a b (s * σ v)

private theorem mat_eq_one_add_nil_six [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b)
    (s : F) {u v : F} (h : v + σ v + σ u * u = 0) :
    mat σ m (suElt σ hσ a (Sum.swap b) s) = 1 + nilSuEltSwap (σ := σ) a b s ∧
    mat σ m (suHeis σ hσ hm b u v) = 1 + nilSuHeis (σ := σ) (hm := hm) b u v ∧
    mat σ m (suElt σ hσ a (Sum.swap b) s)⁻¹ = 1 + nilSuEltSwap (σ := σ) a b s ∧
    mat σ m (suHeis σ hσ hm b (-u) (-v - u * σ u)) =
      1 + nilSuHeis (σ := σ) (hm := hm) b u v + nilSuHeis (σ := σ) (hm := hm) b u v *
        nilSuHeis (σ := σ) (hm := hm) b u v ∧
    mat σ m (suHeis σ hσ hm a (s * u) (σ s * s * v)) =
      1 + nilSuHeisScaled (σ := σ) (hm := hm) a s u v ∧
    mat σ m (suElt σ hσ a b (s * σ v)) = 1 + nilSuEltScaled (σ := σ) a b s v := by
  have hbs : idx a ≠ idx (Sum.swap b) := by rwa [idx_swap]
  have h2 := Pres.heis_neg_valid hσ h
  obtain ⟨h_ab, h_aB, h_Ab, h_AB, h_aa, h_bb, h_am, h_bm, h_Am, h_Bm, hba⟩ := idxFacts hm hab
  haveI := matrix_charP (F := F) (m := m) hm
  have hv : σ v = v + σ u * u := by
    calc σ v = -(v + σ u * u) := by linear_combination h
      _ = v + σ u * u := by rw [CharTwo.neg_eq]
  have hV : σ s * s * v + σ (σ s * s * v) + σ (s * u) * (s * u) = 0 := by
    rw [map_mul, map_mul, map_mul, hσ]
    have e : σ s * s * v + s * σ s * σ v + σ s * σ u * (s * u) =
        σ s * s * (v + σ v + σ u * u) := by ring
    rw [e, h, mul_zero]
  have hHH : nilSuHeis (σ := σ) (hm := hm) b u v * nilSuHeis (σ := σ) (hm := hm) b u v =
      single (crd b) (Fin.rev (crd b)) (u * σ u) := by
    rw [nilSuHeis, heisNil]
    simp [add_mul, mul_add, sub_mul, mul_sub, single_mul_single', crd_injective.eq_iff,
      Fin.rev_inj, Sum.swap_swap, crd_swap, h_ab, h_ab.symm,
      hba, hba.symm, h_aB, h_aB.symm, h_Ab, h_Ab.symm,
      h_AB, h_AB.symm, h_aa, h_aa.symm, h_bb, h_bb.symm, h_am, h_am.symm, h_bm, h_bm.symm,
      h_Am, h_Am.symm, h_Bm, h_Bm.symm, CharTwo.neg_eq, zero_mul, mul_zero, add_zero,
      zero_add, sub_self, sub_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mat_suElt hσ hbs]
    simp only [nilSuEltSwap, suEltNil, Sum.swap_swap, crd_swap]
    abel
  · rw [mat_suHeis hσ hm h, heisenbergMatrix_eq_one_add]
    simp only [nilSuHeis, heisNil]
  · have hmul : suElt σ hσ a (Sum.swap b) s * suElt σ hσ a (Sum.swap b) (-s) = 1 := by
      rw [← suElt_add, add_neg_cancel, suElt_zero]
    have hinv : (suElt σ hσ a (Sum.swap b) s)⁻¹ = suElt σ hσ a (Sum.swap b) (-s) :=
      inv_eq_of_mul_eq_one_right hmul
    rw [hinv, mat_suElt hσ hbs]
    simp only [CharTwo.neg_eq, Sum.swap_swap, crd_swap, nilSuEltSwap, suEltNil]
    abel
  · rw [mat_suHeis hσ hm h2, heisenbergMatrix_eq_one_add, hHH]
    simp only [nilSuHeis, heisNil, map_neg, CharTwo.neg_eq, neg_one_smul, CharTwo.sub_eq_add]
    rw [single_add]
    abel
  · rw [mat_suHeis hσ hm hV, heisenbergMatrix_eq_one_add]
    simp only [nilSuHeisScaled, heisNil]
  · rw [mat_suElt hσ hab]
    simp only [nilSuEltScaled, suEltNil, crd_swap]
    abel


private theorem nil_products_eq_zero [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b)
    (s : F) {u v : F} :
    nilSuEltSwap (σ := σ) a b s * nilSuEltSwap (σ := σ) a b s = 0 ∧
    nilSuHeis (σ := σ) (hm := hm) b u v * nilSuHeis (σ := σ) (hm := hm) b u v *
      nilSuHeis (σ := σ) (hm := hm) b u v = 0 ∧
    nilSuHeis (σ := σ) (hm := hm) b u v * nilSuEltSwap (σ := σ) a b s *
      nilSuHeis (σ := σ) (hm := hm) b u v = 0 ∧
    nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v *
      nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v = 0 ∧
    nilSuHeis (σ := σ) (hm := hm) b u v * nilSuEltSwap (σ := σ) a b s *
      nilSuHeis (σ := σ) (hm := hm) b u v * nilSuHeis (σ := σ) (hm := hm) b u v = 0 ∧
    nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v *
      nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v *
        nilSuHeis (σ := σ) (hm := hm) b u v = 0 ∧
    nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v *
      nilSuHeis (σ := σ) (hm := hm) b u v * nilSuHeis (σ := σ) (hm := hm) b u v = 0 ∧
    nilSuHeisScaled (σ := σ) (hm := hm) a s u v * nilSuEltScaled (σ := σ) a b s v = 0 := by
  obtain ⟨h_ab, h_aB, h_Ab, h_AB, h_aa, h_bb, h_am, h_bm, h_Am, h_Bm, hba⟩ := idxFacts hm hab
  haveI := matrix_charP (F := F) (m := m) hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [nilSuEltSwap, nilSuHeis, nilSuHeisScaled, nilSuEltScaled, suEltNil, heisNil,
      add_mul, mul_add, sub_mul, mul_sub,
      single_mul_single', crd_injective.eq_iff, Fin.rev_inj, Sum.swap_swap, crd_swap,
      h_ab, h_ab.symm, hba, hba.symm, h_aB, h_aB.symm, h_Ab, h_Ab.symm,
      h_AB, h_AB.symm, h_aa, h_aa.symm, h_bb, h_bb.symm, h_am, h_am.symm, h_bm, h_bm.symm,
      h_Am, h_Am.symm, h_Bm, h_Bm.symm, CharTwo.neg_eq, zero_mul, mul_zero, add_zero,
      zero_add, sub_self, sub_zero]


private theorem nil_products_eq [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    (s : F) {u v : F} :
    nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v =
      single (crd a) (midIdx m hm) (s * u) +
        single (crd a) (Fin.rev (crd b)) (s * v) ∧
    nilSuHeis (σ := σ) (hm := hm) b u v * nilSuEltSwap (σ := σ) a b s =
      single (midIdx m hm) (Fin.rev (crd a)) (σ u * σ s) +
        single (crd b) (Fin.rev (crd a)) (v * σ s) ∧
    nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v *
        nilSuEltSwap (σ := σ) a b s =
      single (crd a) (Fin.rev (crd a)) (s * v * σ s) ∧
    nilSuEltSwap (σ := σ) a b s * nilSuHeis (σ := σ) (hm := hm) b u v *
        nilSuHeis (σ := σ) (hm := hm) b u v =
      single (crd a) (Fin.rev (crd b)) (s * u * σ u) := by
  obtain ⟨h_ab, h_aB, h_Ab, h_AB, h_aa, h_bb, h_am, h_bm, h_Am, h_Bm, hba⟩ := idxFacts hm hab
  haveI := matrix_charP (F := F) (m := m) hm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [nilSuEltSwap, nilSuHeis, suEltNil, heisNil, add_mul, mul_add, sub_mul, mul_sub,
      single_mul_single', crd_injective.eq_iff, Fin.rev_inj, Sum.swap_swap, crd_swap,
      h_ab, h_ab.symm, hba, hba.symm, h_aB, h_aB.symm, h_Ab, h_Ab.symm,
      h_AB, h_AB.symm, h_aa, h_aa.symm, h_bb, h_bb.symm, h_am, h_am.symm, h_bm, h_bm.symm,
      h_Am, h_Am.symm, h_Bm, h_Bm.symm, CharTwo.neg_eq, zero_mul, mul_zero, add_zero,
      zero_add, sub_self, sub_zero]

private theorem nsmul_two_eq_zero {R : Type*} [Ring R] [CharP R 2] (X : R) :
    (2 : ℕ) • X = 0 := by
  rw [two_nsmul, CharTwo.add_self_eq_zero]

private theorem nsmul_three_eq_self {R : Type*} [Ring R] [CharP R 2] (X : R) :
    (3 : ℕ) • X = X := by
  rw [three_nsmul]
  simp only [CharTwo.add_self_eq_zero, add_zero, zero_add]

private theorem comm_four_poly {R : Type*} [Ring R] (B C : R) :
    (1+B)*(1+C)*(1+B+B*B)*(1+C+C*C) =
      1 + B*C + C*B +
        (2 • B + 2 • C + 2 • (B*B) + 2 • (B*C) + 2 • (C*C)) +
        (B*B*B + 2 • (B*B*C) + B*C*B + 3 • (B*C*C) + C*B*B + C*B*C + C*C*C +
         B*B*B*C + 2 • (B*B*C*C) + B*C*B*B + B*C*B*C + B*C*C*C +
         C*B*B*C + C*B*C*C + B*B*B*C*C + B*C*B*B*C + B*C*B*C*C +
         C*B*B*C*C + B*C*B*B*C*C) := by
  noncomm_ring





private theorem comm_four_char2 {R : Type*} [Ring R] [CharP R 2] (B C : R)
    (hB3 : B*B*B = 0) (hC3 : C*C*C = 0)
    (hB2C : B*B*C = 0) (hBC2 : B*C*C = 0)
    (hCBB : C*B*B = 0) (hCBC : C*B*C = 0)
    (hBCB : B*C*B = 0) (hCB2 : C*B*C = 0) :
    (1+B)*(1+C)*(1+B+B*B)*(1+C+C*C) = 1 + B*C + C*B := by
  rw [comm_four_poly B C]
  simp only [nsmul_two_eq_zero, nsmul_three_eq_self, hB3, hC3, hB2C, hBC2, hCBB, hCBC,
    hBCB, hCB2, zero_mul, mul_zero, add_zero, zero_add]


private theorem heis_short_poly {R : Type*} [Ring R] (A B : R) :
    (1+A)*(1+B)*(1+A)*(1+B+B*B) =
      1 + A*B + B*A + A*B*A + A*B*B +
        (2 • A + 2 • B + A*A + 2 • (A*B) + 2 • (B*B) + A*A*B + 2 • (A*B*B) +
          B*A*B + B*B*B + A*A*B*B + A*B*A*B + A*B*B*B + B*A*B*B + A*B*A*B*B) := by
  noncomm_ring

private theorem heis_short_char2 {R : Type*} [Ring R] [CharP R 2] (A B : R)
    (hA2 : A*A = 0) (hB3 : B*B*B = 0) (hBAB : B*A*B = 0)
    (hABAB : A*B*A*B = 0) (hBABB : B*A*B*B = 0) (hABABB : A*B*A*B*B = 0)
    (hAB3 : A*B*B*B = 0) :
    (1+A)*(1+B)*(1+A)*(1+B+B*B) = 1 + A*B + B*A + A*B*A + A*B*B := by
  rw [heis_short_poly A B]
  simp only [nsmul_two_eq_zero, hA2, hB3, hBAB, hABAB, hBABB, hABABB, hAB3, zero_mul, mul_zero,
    add_zero, zero_add]

theorem commutator_suHeis_suHeis [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {u v u' v' : F} (h : v + σ v + σ u * u = 0) (h' : v' + σ v' + σ u' * u' = 0) :
    ⁅suHeis σ hσ hm b u v, suHeis σ hσ hm a u' v'⁆ = suElt σ hσ a b (σ u * u') := by
  have h2 := Pres.heis_neg_valid hσ h
  have h2' := Pres.heis_neg_valid hσ h'
  obtain ⟨h_ab, h_aB, h_Ab, h_AB, h_aa, h_bb, h_am, h_bm, h_Am, h_Bm, hba⟩ := idxFacts hm hab
  haveI := matrix_charP (F := F) (m := m) hm
  set B : Matrix (Fin m) (Fin m) F := heisNil σ hm b u v with hBdef
  set C : Matrix (Fin m) (Fin m) F := heisNil σ hm a u' v' with hCdef
  obtain ⟨hBB, hCC, hBC, hCB, hB3, hC3, hB2C, hBC2, hCBB, hCBC, hBCB, hCB2⟩ :=
    heisNil_prod_facts (σ := σ) (hm := hm) hab (u := u) (v := v) (u' := u') (v' := v')
  rw [← hBdef] at hBB hBC hCB hB3 hB2C hBC2 hCBB hCBC hBCB hCB2
  rw [← hCdef] at hCC hBC hCB hC3 hB2C hBC2 hCBB hCBC hBCB hCB2
  have hprod := comm_four_char2 B C hB3 hC3 hB2C hBC2 hCBB hCBC hBCB hCB2
  have hBmat : mat σ m (suHeis σ hσ hm b u v) = 1 + B := by
    rw [mat_suHeis hσ hm h, heisenbergMatrix_eq_one_add, hBdef, heisNil]
  have hCmat : mat σ m (suHeis σ hσ hm a u' v') = 1 + C := by
    rw [mat_suHeis hσ hm h', heisenbergMatrix_eq_one_add, hCdef, heisNil]
  have hBinv : mat σ m (suHeis σ hσ hm b (-u) (-v - u * σ u)) = 1 + B + B * B := by
    rw [mat_suHeis hσ hm h2, heisenbergMatrix_eq_one_add, hBB, hBdef, heisNil]
    simp only [map_neg, CharTwo.neg_eq, neg_one_smul, CharTwo.sub_eq_add]
    rw [single_add]
    abel
  have hCinv : mat σ m (suHeis σ hσ hm a (-u') (-v' - u' * σ u')) = 1 + C + C * C := by
    rw [mat_suHeis hσ hm h2', heisenbergMatrix_eq_one_add, hCC, hCdef, heisNil]
    simp only [map_neg, CharTwo.neg_eq, neg_one_smul, CharTwo.sub_eq_add]
    rw [single_add]
    abel
  have hRHS : mat σ m (suElt σ hσ a b (σ u * u')) = 1 + B * C + C * B := by
    rw [mat_suElt_two hσ hab (σ u * u'), hBC, hCB]
    simp only [hσ, map_mul]
    rw [show u' * σ u = σ u * u' by ring]
    abel
  apply mat_injective
  rw [commutatorElement_def, suHeis_inv hσ hm h, suHeis_inv hσ hm h',
    map_mul, map_mul, map_mul, hBmat, hCmat, hBinv, hCinv, hprod, hRHS]

theorem commutator_suElt_swap_suHeis [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) (s : F)
    {u v : F} (h : v + σ v + σ u * u = 0) :
    ⁅suElt σ hσ a (Sum.swap b) s, suHeis σ hσ hm b u v⁆ =
      suHeis σ hσ hm a (s * u) (σ s * s * v) * suElt σ hσ a b (s * σ v) := by
  obtain ⟨hEmat, hHmat, hEinv, hHinv, hHam, hEam⟩ := mat_eq_one_add_nil_six hσ hm hab s h
  obtain ⟨hE2, hH3, hHEH, hEHEH, hHEHH, hEHEHH, hEHHH, hHaEa⟩ :=
    nil_products_eq_zero (σ := σ) (hm := hm) hab s
  obtain ⟨hEH, hHE, hEHE, hEHH⟩ := nil_products_eq (σ := σ) (hm := hm) hab s
  haveI := matrix_charP (F := F) (m := m) hm
  have hcomm := heis_short_char2 (nilSuEltSwap (σ := σ) a b s) (nilSuHeis (σ := σ) (hm := hm) b u v)
    hE2 hH3 hHEH hEHEH hHEHH hEHEHH hEHHH
  have hv : σ v = v + σ u * u := by
    calc σ v = -(v + σ u * u) := by linear_combination h
      _ = v + σ u * u := by rw [CharTwo.neg_eq]
  apply mat_injective
  rw [commutatorElement_def, suHeis_inv hσ hm h, map_mul, map_mul, map_mul,
    hEmat, hHmat, hEinv, hHinv, hcomm]
  rw [map_mul, hHam, hEam]
  rw [show (1 + nilSuHeisScaled (σ := σ) (hm := hm) a s u v) *
      (1 + nilSuEltScaled (σ := σ) a b s v) =
      1 + nilSuHeisScaled (σ := σ) (hm := hm) a s u v + nilSuEltScaled (σ := σ) a b s v by
    rw [mul_add, mul_one, add_mul, one_mul, hHaEa, add_zero]]
  rw [hEHE, hEHH, hEH, hHE]
  simp only [nilSuHeisScaled, nilSuEltScaled, nilSuHeis, nilSuEltSwap, heisNil, suEltNil,
    map_mul, hσ, crd_swap]
  rw [show s * σ v = s * v + s * u * σ u by rw [hv]; ring]
  rw [show s * v * σ s = σ s * s * v by ring]
  rw [show σ u * σ s = σ s * σ u by ring]
  rw [show v * σ s = σ s * v by ring]
  simp only [sub_eq_add_neg]
  rw [show -single (midIdx m hm) (Fin.rev (crd a)) (σ s * σ u) =
      single (midIdx m hm) (Fin.rev (crd a)) (σ s * σ u) by rw [CharTwo.neg_eq]]
  rw [show -single (crd b) (Fin.rev (crd a)) (σ s * v) =
      single (crd b) (Fin.rev (crd a)) (σ s * v) by rw [CharTwo.neg_eq]]
  rw [single_add]
  abel

theorem conj_suHeis_suHeis [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {u v u' v' : F} (h : v + σ v + σ u * u = 0) (h' : v' + σ v' + σ u' * u' = 0) :
    suHeis σ hσ hm b u v * suHeis σ hσ hm a u' v' * (suHeis σ hσ hm b u v)⁻¹ =
      suElt σ hσ a b (σ u * u') * suHeis σ hσ hm a u' v' := by
  rw [show suHeis σ hσ hm b u v * suHeis σ hσ hm a u' v' * (suHeis σ hσ hm b u v)⁻¹ =
      ⁅suHeis σ hσ hm b u v, suHeis σ hσ hm a u' v'⁆ * suHeis σ hσ hm a u' v' by
    rw [commutatorElement_def]
    group]
  rw [commutator_suHeis_suHeis hσ hm hab h h']

theorem conj_suHeis_suElt_swap [CharP F 2] {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    (s : F) {u v : F} (h : v + σ v + σ u * u = 0) :
    suHeis σ hσ hm b u v * suElt σ hσ a (Sum.swap b) s * (suHeis σ hσ hm b u v)⁻¹ =
      (suHeis σ hσ hm a (s * u) (σ s * s * v) * suElt σ hσ a b (s * σ v))⁻¹ *
        suElt σ hσ a (Sum.swap b) s := by
  rw [show suHeis σ hσ hm b u v * suElt σ hσ a (Sum.swap b) s * (suHeis σ hσ hm b u v)⁻¹ =
      ⁅suHeis σ hσ hm b u v, suElt σ hσ a (Sum.swap b) s⁆ * suElt σ hσ a (Sum.swap b) s by
    rw [commutatorElement_def]
    group]
  rw [← commutatorElement_inv, commutator_suElt_swap_suHeis hσ hm hab s h]

end CFSG.Timmesfeld.Transvection.Pres
