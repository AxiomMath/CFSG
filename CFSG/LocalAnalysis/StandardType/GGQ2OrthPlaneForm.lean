module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmChar

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix

noncomputable section

variable (K : Type) [Field K] (t : ℕ) (δ : Fin 2)

@[expose] def planeQForm : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :=
  ∑ i : Fin (t + δ.val), (QuadraticMap.proj (R := K) (Sum.inl i) (Sum.inr i) +
    if (i : ℕ) < t then
      QuadraticMap.proj (R := K) (Sum.inl i) (Sum.inl i) +
        QuadraticMap.proj (R := K) (Sum.inr i) (Sum.inr i)
    else 0)

theorem coe_planeQForm : ⇑(planeQForm K t δ) = planeQ (K := K) t δ := by
  funext w
  simp only [planeQForm, planeQ, QuadraticMap.sum_apply, QuadraticMap.add_apply,
    QuadraticMap.proj_apply, sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

variable {K t δ}

private theorem opf_planeQForm_apply (v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    planeQForm K t δ v = ∑ i, (v (Sum.inl i) * v (Sum.inr i) +
      if (i : ℕ) < t then v (Sum.inl i) ^ 2 + v (Sum.inr i) ^ 2 else 0) := by
  rw [coe_planeQForm]
  rfl

private theorem opf_term_add [CharP K 2] (a b a' b' : K) (c : Prop) [Decidable c] :
    ((a + a') * (b + b') + (if c then (a + a') ^ 2 + (b + b') ^ 2 else 0)) +
        (a * b + (if c then a ^ 2 + b ^ 2 else 0)) +
        (a' * b' + (if c then a' ^ 2 + b' ^ 2 else 0)) =
      a * b' + a' * b := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  split_ifs with hc
  · linear_combination
      (a * b + a' * b' + a ^ 2 + b ^ 2 + a * a' + b * b' + a' ^ 2 + b' ^ 2) * h2
  · linear_combination (a * b + a' * b') * h2

private theorem opf_polar_planeQForm [CharP K 2] (v w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    QuadraticMap.polar (planeQForm K t δ) v w =
      ∑ i, (v (Sum.inl i) * w (Sum.inr i) + w (Sum.inl i) * v (Sum.inr i)) := by
  rw [coe_planeQForm]
  simp only [planeQ, QuadraticMap.polar, Pi.add_apply]
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact opf_term_add (v (Sum.inl i)) (v (Sum.inr i)) (w (Sum.inl i)) (w (Sum.inr i))
    ((i : ℕ) < t)


private theorem opf_polarBilin_planeQForm [CharP K 2] :
    QuadraticMap.polarBilin (planeQForm K t δ) =
      QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus (t + δ.val) K) := by
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    opf_polar_planeQForm, CFSG.LieType.Universal.Spin.polar_quadPlus]

private theorem opf_Q_single_inl_add (i j : Fin (t + δ.val)) (hij : i ≠ j) :
    planeQForm K t δ (Pi.single (Sum.inl i) (1 : K) + Pi.single (Sum.inl j) (1 : K)) =
      (if (i : ℕ) < t then 1 else 0) + (if (j : ℕ) < t then 1 else 0) := by
  let v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inl i) (1 : K) + Pi.single (Sum.inl j) (1 : K)
  change planeQForm K t δ v = _
  rw [opf_planeQForm_apply]
  have hsupp : ∀ x ∈ (Finset.univ : Finset (Fin (t + δ.val))),
      x ∉ ({i, j} : Finset (Fin (t + δ.val))) →
      (v (Sum.inl x) * v (Sum.inr x) +
        (if (x : ℕ) < t then v (Sum.inl x) ^ 2 + v (Sum.inr x) ^ 2 else 0)) = 0 := by
    intro x _ hx
    have hxi : x ≠ i := by intro h; exact hx (by simp [h])
    have hxj : x ≠ j := by intro h; exact hx (by simp [h])
    have h1 : (Sum.inl x : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inl i := by
      simpa using hxi
    have h2 : (Sum.inl x : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inl j := by
      simpa using hxj
    simp [v, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin (t + δ.val)))) hsupp,
    Finset.sum_pair hij]
  have h1 : (Sum.inl i : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inl j := by
    simpa using hij
  have h2 : (Sum.inl j : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inl i := by
    simpa using hij.symm
  simp [v, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

private theorem opf_Q_single_inr_add (i j : Fin (t + δ.val)) (hij : i ≠ j) :
    planeQForm K t δ (Pi.single (Sum.inr i) (1 : K) + Pi.single (Sum.inr j) (1 : K)) =
      (if (i : ℕ) < t then 1 else 0) + (if (j : ℕ) < t then 1 else 0) := by
  let v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inr i) (1 : K) + Pi.single (Sum.inr j) (1 : K)
  change planeQForm K t δ v = _
  rw [opf_planeQForm_apply]
  have hsupp : ∀ x ∈ (Finset.univ : Finset (Fin (t + δ.val))),
      x ∉ ({i, j} : Finset (Fin (t + δ.val))) →
      (v (Sum.inl x) * v (Sum.inr x) +
        (if (x : ℕ) < t then v (Sum.inl x) ^ 2 + v (Sum.inr x) ^ 2 else 0)) = 0 := by
    intro x _ hx
    have hxi : x ≠ i := by intro h; exact hx (by simp [h])
    have hxj : x ≠ j := by intro h; exact hx (by simp [h])
    have h1 : (Sum.inr x : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inr i := by
      simpa using hxi
    have h2 : (Sum.inr x : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inr j := by
      simpa using hxj
    simp [v, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin (t + δ.val)))) hsupp,
    Finset.sum_pair hij]
  have h1 : (Sum.inr i : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inr j := by
    simpa using hij
  have h2 : (Sum.inr j : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inr i := by
    simpa using hij.symm
  simp [v, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

private theorem opf_Q_single_inl (i : Fin (t + δ.val)) :
    planeQForm K t δ (Pi.single (Sum.inl i) (1 : K)) = (if (i : ℕ) < t then 1 else 0) := by
  rw [opf_planeQForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have h1 : (Sum.inl j : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inl i := by
      simpa using hji
    simp [Pi.single_eq_of_ne h1]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem opf_B_inl_inr [CharP K 2] {i j : Fin (t + δ.val)} :
    QuadraticMap.polar (planeQForm K t δ) (Pi.single (Sum.inl i) (1 : K))
      (Pi.single (Sum.inr j) (1 : K)) = if i = j then 1 else 0 := by
  rw [opf_polar_planeQForm, Finset.sum_eq_single i]
  · by_cases h : i = j
    · simp [h]
    · simp [h]
  · intro x _ hxi
    have h1 : (Sum.inl x : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inl i := by
      simpa using hxi
    simp [Pi.single_eq_of_ne h1]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem opf_B_inl_inl [CharP K 2] {i j : Fin (t + δ.val)} :
    QuadraticMap.polar (planeQForm K t δ) (Pi.single (Sum.inl i) (1 : K))
      (Pi.single (Sum.inl j) (1 : K)) = 0 := by
  rw [opf_polar_planeQForm]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp

private theorem opf_B_inr_inl [CharP K 2] {i j : Fin (t + δ.val)} :
    QuadraticMap.polar (planeQForm K t δ) (Pi.single (Sum.inr i) (1 : K))
      (Pi.single (Sum.inl j) (1 : K)) = if i = j then 1 else 0 := by
  rw [opf_polar_planeQForm, Finset.sum_eq_single i]
  · by_cases h : i = j
    · simp [h]
    · simp [h]
  · intro x _ hxi
    have h1 : (Sum.inr x : Fin (t + δ.val) ⊕ Fin (t + δ.val)) ≠ Sum.inr i := by
      simpa using hxi
    simp [Pi.single_eq_of_ne h1]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem opf_case_four [CharP K 2] (h4 : 4 ≤ t) :
    ∃ T : Submodule K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, planeQForm K t δ v = 0 := by
  have hm : 4 ≤ t + δ.val := by omega
  let i0 : Fin (t + δ.val) := ⟨0, by omega⟩
  let i1 : Fin (t + δ.val) := ⟨1, by omega⟩
  let i2 : Fin (t + δ.val) := ⟨2, by omega⟩
  let i3 : Fin (t + δ.val) := ⟨3, by omega⟩
  let a : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inl i0) (1 : K) + Pi.single (Sum.inl i1) (1 : K)
  let b : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inr i0) (1 : K) + Pi.single (Sum.inr i1) (1 : K)
  let c : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inl i2) (1 : K) + Pi.single (Sum.inl i3) (1 : K)
  have h0t : (i0 : ℕ) < t := by simp [i0]; omega
  have h1t : (i1 : ℕ) < t := by simp [i1]; omega
  have h2t : (i2 : ℕ) < t := by simp [i2]; omega
  have h3t : (i3 : ℕ) < t := by simp [i3]; omega
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h23 : i2 ≠ i3 := by simp [i2, i3]
  have h02 : i0 ≠ i2 := by simp [i0, i2]
  have h03 : i0 ≠ i3 := by simp [i0, i3]
  have h12 : i1 ≠ i2 := by simp [i1, i2]
  have h13 : i1 ≠ i3 := by simp [i1, i3]
  have ha : planeQForm K t δ a = 0 := by
    change planeQForm K t δ (Pi.single (Sum.inl i0) (1 : K) +
      Pi.single (Sum.inl i1) (1 : K)) = 0
    rw [opf_Q_single_inl_add i0 i1 h01]
    rw [if_pos h0t, if_pos h1t, CharTwo.add_self_eq_zero]
  have hb : planeQForm K t δ b = 0 := by
    change planeQForm K t δ (Pi.single (Sum.inr i0) (1 : K) +
      Pi.single (Sum.inr i1) (1 : K)) = 0
    rw [opf_Q_single_inr_add i0 i1 h01]
    rw [if_pos h0t, if_pos h1t, CharTwo.add_self_eq_zero]
  have hc : planeQForm K t δ c = 0 := by
    change planeQForm K t δ (Pi.single (Sum.inl i2) (1 : K) +
      Pi.single (Sum.inl i3) (1 : K)) = 0
    rw [opf_Q_single_inl_add i2 i3 h23]
    rw [if_pos h2t, if_pos h3t, CharTwo.add_self_eq_zero]
  have hab : QuadraticMap.polar (planeQForm K t δ) a b = 0 := by
    change QuadraticMap.polar (planeQForm K t δ)
      (Pi.single (Sum.inl i0) (1 : K) + Pi.single (Sum.inl i1) (1 : K))
      (Pi.single (Sum.inr i0) (1 : K) + Pi.single (Sum.inr i1) (1 : K)) = 0
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
    rw [opf_B_inl_inr (i := i0) (j := i0), if_pos rfl,
      opf_B_inl_inr (i := i0) (j := i1), if_neg h01,
      opf_B_inl_inr (i := i1) (j := i0), if_neg (Ne.symm h01),
      opf_B_inl_inr (i := i1) (j := i1), if_pos rfl]
    rw [add_zero, zero_add, CharTwo.add_self_eq_zero]
  have hac : QuadraticMap.polar (planeQForm K t δ) a c = 0 := by
    change QuadraticMap.polar (planeQForm K t δ)
      (Pi.single (Sum.inl i0) (1 : K) + Pi.single (Sum.inl i1) (1 : K))
      (Pi.single (Sum.inl i2) (1 : K) + Pi.single (Sum.inl i3) (1 : K)) = 0
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
    rw [opf_B_inl_inl (i := i0) (j := i2), opf_B_inl_inl (i := i0) (j := i3),
      opf_B_inl_inl (i := i1) (j := i2), opf_B_inl_inl (i := i1) (j := i3)]
    rw [zero_add, add_zero]
  have hbc : QuadraticMap.polar (planeQForm K t δ) b c = 0 := by
    change QuadraticMap.polar (planeQForm K t δ)
      (Pi.single (Sum.inr i0) (1 : K) + Pi.single (Sum.inr i1) (1 : K))
      (Pi.single (Sum.inl i2) (1 : K) + Pi.single (Sum.inl i3) (1 : K)) = 0
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
    rw [opf_B_inr_inl (i := i0) (j := i2), if_neg h02,
      opf_B_inr_inl (i := i0) (j := i3), if_neg h03,
      opf_B_inr_inl (i := i1) (j := i2), if_neg h12,
      opf_B_inr_inl (i := i1) (j := i3), if_neg h13]
    rw [zero_add, add_zero]
  have hli : LinearIndependent K ![a, b, c] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have h0 : g 0 = 0 := by
      have hc := congrFun hg (Sum.inl i0)
      simpa [a, b, c, h01, h01.symm, h02, h02.symm, h03, h03.symm, h12, h12.symm,
        h13, h13.symm, h23, h23.symm] using hc
    have h1 : g 1 = 0 := by
      have hc := congrFun hg (Sum.inr i0)
      simpa [a, b, c, h01, h01.symm, h02, h02.symm, h03, h03.symm, h12, h12.symm,
        h13, h13.symm, h23, h23.symm] using hc
    have h2 : g 2 = 0 := by
      have hc := congrFun hg (Sum.inl i2)
      simpa [a, b, c, h01, h01.symm, h02, h02.symm, h03, h03.symm, h12, h12.symm,
        h13, h13.symm, h23, h23.symm] using hc
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨Submodule.span K (Set.range ![a, b, c]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · have hself : ∀ x, QuadraticMap.polar (planeQForm K t δ) x x = 0 := fun x => by
      rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
    have hba : QuadraticMap.polar (planeQForm K t δ) b a = 0 := by
      rw [QuadraticMap.polar_comm]; exact hab
    have hca : QuadraticMap.polar (planeQForm K t δ) c a = 0 := by
      rw [QuadraticMap.polar_comm]; exact hac
    have hcb : QuadraticMap.polar (planeQForm K t δ) c b = 0 := by
      rw [QuadraticMap.polar_comm]; exact hbc
    have hS : ∀ u ∈ Set.range ![a, b, c], planeQForm K t δ u = 0 := by
      rintro u ⟨k, rfl⟩
      fin_cases k
      · exact ha
      · exact hb
      · exact hc
    have hB : ∀ u ∈ Set.range ![a, b, c], ∀ w ∈ Set.range ![a, b, c],
        QuadraticMap.polar (planeQForm K t δ) u w = 0 := by
      rintro u ⟨k, rfl⟩ w ⟨l, rfl⟩
      fin_cases k <;> fin_cases l <;>
        simp [hab, hba, hac, hca, hbc, hcb, hself]
    exact fun v hv => CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span hS hB hv

private theorem opf_case_three [CharP K 2] (h3 : t = 3) (hδ : δ.val = 1) :
    ∃ T : Submodule K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, planeQForm K t δ v = 0 := by
  have hm : 4 ≤ t + δ.val := by omega
  let i0 : Fin (t + δ.val) := ⟨0, by omega⟩
  let i1 : Fin (t + δ.val) := ⟨1, by omega⟩
  let i3 : Fin (t + δ.val) := ⟨3, by omega⟩
  let a : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inl i0) (1 : K) + Pi.single (Sum.inl i1) (1 : K)
  let b : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    Pi.single (Sum.inr i0) (1 : K) + Pi.single (Sum.inr i1) (1 : K)
  let c : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K := Pi.single (Sum.inl i3) (1 : K)
  have h0t : (i0 : ℕ) < t := by simp [i0]; omega
  have h1t : (i1 : ℕ) < t := by simp [i1]; omega
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h03 : i0 ≠ i3 := by simp [i0, i3]
  have h13 : i1 ≠ i3 := by simp [i1, i3]
  have ha : planeQForm K t δ a = 0 := by
    change planeQForm K t δ (Pi.single (Sum.inl i0) (1 : K) +
      Pi.single (Sum.inl i1) (1 : K)) = 0
    rw [opf_Q_single_inl_add i0 i1 h01]
    rw [if_pos h0t, if_pos h1t, CharTwo.add_self_eq_zero]
  have hb : planeQForm K t δ b = 0 := by
    change planeQForm K t δ (Pi.single (Sum.inr i0) (1 : K) +
      Pi.single (Sum.inr i1) (1 : K)) = 0
    rw [opf_Q_single_inr_add i0 i1 h01]
    rw [if_pos h0t, if_pos h1t, CharTwo.add_self_eq_zero]
  have hc : planeQForm K t δ c = 0 := by
    change planeQForm K t δ (Pi.single (Sum.inl i3) (1 : K)) = 0
    rw [opf_Q_single_inl i3]
    rw [if_neg (by simp [i3, h3])]
  have hab : QuadraticMap.polar (planeQForm K t δ) a b = 0 := by
    change QuadraticMap.polar (planeQForm K t δ)
      (Pi.single (Sum.inl i0) (1 : K) + Pi.single (Sum.inl i1) (1 : K))
      (Pi.single (Sum.inr i0) (1 : K) + Pi.single (Sum.inr i1) (1 : K)) = 0
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
    rw [opf_B_inl_inr (i := i0) (j := i0), if_pos rfl,
      opf_B_inl_inr (i := i0) (j := i1), if_neg h01,
      opf_B_inl_inr (i := i1) (j := i0), if_neg (Ne.symm h01),
      opf_B_inl_inr (i := i1) (j := i1), if_pos rfl]
    rw [add_zero, zero_add, CharTwo.add_self_eq_zero]
  have hac : QuadraticMap.polar (planeQForm K t δ) a c = 0 := by
    change QuadraticMap.polar (planeQForm K t δ)
      (Pi.single (Sum.inl i0) (1 : K) + Pi.single (Sum.inl i1) (1 : K))
      (Pi.single (Sum.inl i3) (1 : K)) = 0
    simp only [QuadraticMap.polar_add_left]
    rw [opf_B_inl_inl (i := i0) (j := i3), opf_B_inl_inl (i := i1) (j := i3)]
    rw [add_zero]
  have hbc : QuadraticMap.polar (planeQForm K t δ) b c = 0 := by
    change QuadraticMap.polar (planeQForm K t δ)
      (Pi.single (Sum.inr i0) (1 : K) + Pi.single (Sum.inr i1) (1 : K))
      (Pi.single (Sum.inl i3) (1 : K)) = 0
    simp only [QuadraticMap.polar_add_left]
    rw [opf_B_inr_inl (i := i0) (j := i3), if_neg h03,
      opf_B_inr_inl (i := i1) (j := i3), if_neg h13]
    rw [add_zero]
  have hli : LinearIndependent K ![a, b, c] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have h0 : g 0 = 0 := by
      have hc := congrFun hg (Sum.inl i0)
      simpa [a, b, c, Pi.single_eq_same, Pi.single_eq_of_ne, h01, h01.symm, h03, h03.symm]
        using hc
    have h1 : g 1 = 0 := by
      have hc := congrFun hg (Sum.inr i0)
      simpa [a, b, c, Pi.single_eq_same, Pi.single_eq_of_ne, h01, h01.symm, h03, h03.symm,
        h13, h13.symm] using hc
    have h2 : g 2 = 0 := by
      have hc := congrFun hg (Sum.inl i3)
      simpa [a, b, c, Pi.single_eq_same, Pi.single_eq_of_ne, h03, h03.symm, h13, h13.symm]
        using hc
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨Submodule.span K (Set.range ![a, b, c]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · have hself : ∀ x, QuadraticMap.polar (planeQForm K t δ) x x = 0 := fun x => by
      rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
    have hba : QuadraticMap.polar (planeQForm K t δ) b a = 0 := by
      rw [QuadraticMap.polar_comm]; exact hab
    have hca : QuadraticMap.polar (planeQForm K t δ) c a = 0 := by
      rw [QuadraticMap.polar_comm]; exact hac
    have hcb : QuadraticMap.polar (planeQForm K t δ) c b = 0 := by
      rw [QuadraticMap.polar_comm]; exact hbc
    have hS : ∀ u ∈ Set.range ![a, b, c], planeQForm K t δ u = 0 := by
      rintro u ⟨k, rfl⟩
      fin_cases k
      · exact ha
      · exact hb
      · exact hc
    have hB : ∀ u ∈ Set.range ![a, b, c], ∀ w ∈ Set.range ![a, b, c],
        QuadraticMap.polar (planeQForm K t δ) u w = 0 := by
      rintro u ⟨k, rfl⟩ w ⟨l, rfl⟩
      fin_cases k <;> fin_cases l <;>
        simp [hab, hba, hac, hca, hbc, hcb, hself]
    exact fun v hv => CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span hS hB hv

theorem nondegenerate_planeQForm [CharP K 2] :
    (QuadraticMap.polarBilin (planeQForm K t δ)).Nondegenerate := by
  rw [opf_polarBilin_planeQForm]
  exact CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (t + δ.val) K

theorem exists_totallySingular_planeQForm [CharP K 2] (h : 4 ≤ t + δ.val) :
    ∃ T : Submodule K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, planeQForm K t δ v = 0 := by
  by_cases ht : 4 ≤ t
  · exact opf_case_four ht
  · have ht3 : t = 3 := by omega
    have hδ1 : δ.val = 1 := by have := δ.isLt; omega
    exact opf_case_three ht3 hδ1

private theorem opf_chi_sum [CharP K 2] [Finite K] {ι : Type} (s : Finset ι) (f : ι → K) :
    OrdPNsOm.chi (∑ i ∈ s, f i) = ∏ i ∈ s, OrdPNsOm.chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [OrdPNsOm.chi_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, OrdPNsOm.chi_add, ih]

private theorem opf_chi_one [CharP K 2] [Fintype K] (hK : Nat.card K = 2) :
    OrdPNsOm.chi (1 : K) = -1 := by
  classical
  refine OrdPNsOm.chi_of_not_mem ?_
  rintro ⟨z, hz⟩
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  have huniv : (Finset.univ : Finset K) = {0, 1} := (Finset.eq_univ_of_card _ hc).symm
  have hz' : z = 0 ∨ z = 1 := by
    have : z ∈ ({0, 1} : Finset K) := by rw [← huniv]; exact Finset.mem_univ z
    simpa using this
  rcases hz' with rfl | rfl
  · rw [OrdPNsOm.wp_apply, zero_pow (by norm_num), zero_add] at hz
    exact zero_ne_one hz
  · rw [OrdPNsOm.wp_apply, one_pow, CharTwo.add_self_eq_zero] at hz
    exact zero_ne_one hz

private theorem opf_sum_aniso [CharP K 2] [Fintype K] (hK : Nat.card K = 2) :
    ∑ a : K, ∑ b : K, OrdPNsOm.chi (a * b + (a ^ 2 + b ^ 2)) = -2 := by
  classical
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  have huniv : (Finset.univ : Finset K) = {0, 1} := (Finset.eq_univ_of_card _ hc).symm
  rw [huniv]
  rw [Finset.sum_pair (a := (0 : K)) (b := 1) zero_ne_one]
  rw [Finset.sum_pair (a := (0 : K)) (b := 1) zero_ne_one]
  rw [Finset.sum_pair (a := (0 : K)) (b := 1) zero_ne_one]
  have h1 : OrdPNsOm.chi (1 : K) = -1 := opf_chi_one hK
  simp [OrdPNsOm.chi_zero, h1, CharTwo.add_self_eq_zero]

private theorem opf_sum_hyp [CharP K 2] [Fintype K] (hK : Nat.card K = 2) :
    ∑ a : K, ∑ b : K, OrdPNsOm.chi (a * b) = 2 := by
  classical
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  have huniv : (Finset.univ : Finset K) = {0, 1} := (Finset.eq_univ_of_card _ hc).symm
  rw [huniv]
  rw [Finset.sum_pair (a := (0 : K)) (b := 1) zero_ne_one]
  rw [Finset.sum_pair (a := (0 : K)) (b := 1) zero_ne_one]
  rw [Finset.sum_pair (a := (0 : K)) (b := 1) zero_ne_one]
  have h1 : OrdPNsOm.chi (1 : K) = -1 := opf_chi_one hK
  simp [OrdPNsOm.chi_zero, h1]

private theorem opf_charSum_main [CharP K 2] [Finite K] [Fintype K] (hK : Nat.card K = 2) :
    OrdPNsOm.charSum (planeQForm K t δ) ⊤ = (-2) ^ t * 2 ^ δ.val := by
  classical
  let m := t + δ.val
  let P : Fin m → K → K → K := fun i a b =>
    a * b + if (i : ℕ) < t then a ^ 2 + b ^ 2 else 0
  have hQ : ∀ v : Fin m ⊕ Fin m → K,
      planeQForm K t δ v = ∑ i, P i (v (Sum.inl i)) (v (Sum.inr i)) := by
    intro v
    rw [opf_planeQForm_apply]
  have step1 : OrdPNsOm.charSum (planeQForm K t δ) ⊤ =
      ∑ v : Fin m ⊕ Fin m → K, OrdPNsOm.chi (planeQForm K t δ v) := by
    rw [OrdPNsOm.charSum_eq]
    refine Fintype.sum_equiv (Submodule.topEquiv (R := K) (M := Fin m ⊕ Fin m → K)) _ _ fun v => ?_
    rfl
  rw [step1]
  let e : (Fin m ⊕ Fin m → K) ≃ (Fin m → K) × (Fin m → K) :=
    Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) K
  have step2 : (∑ v : Fin m ⊕ Fin m → K, OrdPNsOm.chi (planeQForm K t δ v)) =
      ∑ p : (Fin m → K) × (Fin m → K),
        OrdPNsOm.chi (∑ i, P i (p.1 i) (p.2 i)) := by
    refine Fintype.sum_equiv e _ _ fun v => ?_
    simp only [e, hQ v, Equiv.sumArrowEquivProdArrow_apply_fst,
      Equiv.sumArrowEquivProdArrow_apply_snd]
  rw [step2, Fintype.sum_prod_type]
  simp_rw [opf_chi_sum]
  have stepY : ∀ x : Fin m → K, (∑ y : Fin m → K, ∏ i, OrdPNsOm.chi (P i (x i) (y i))) =
      ∏ i, ∑ b : K, OrdPNsOm.chi (P i (x i) b) := by
    intro x
    have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset K))
      (fun i b => OrdPNsOm.chi (P i (x i) b))
    rw [Fintype.piFinset_univ] at h
    exact h.symm
  simp_rw [stepY]
  have stepX : (∑ x : Fin m → K, ∏ i, ∑ b : K, OrdPNsOm.chi (P i (x i) b)) =
      ∏ i, ∑ a : K, ∑ b : K, OrdPNsOm.chi (P i a b) := by
    have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset K))
      (fun i a => ∑ b : K, OrdPNsOm.chi (P i a b))
    rw [Fintype.piFinset_univ] at h
    exact h.symm
  rw [stepX]
  have hfactor : ∀ i : Fin m, (∑ a : K, ∑ b : K, OrdPNsOm.chi (P i a b)) =
      if (i : ℕ) < t then (-2 : ℤ) else 2 := by
    intro i
    by_cases hi : (i : ℕ) < t
    · rw [if_pos hi]
      simp only [P, hi, if_true]
      exact opf_sum_aniso hK
    · rw [if_neg hi]
      simp only [P, hi, if_false, add_zero]
      exact opf_sum_hyp hK
  rw [Finset.prod_congr rfl fun i _ => hfactor i]
  have hprod : (∏ i : Fin (t + δ.val), (if (i : ℕ) < t then (-2 : ℤ) else 2)) =
      (-2) ^ t * 2 ^ δ.val := by
    fin_cases δ
    · simp only [Nat.add_zero]
      rw [Finset.prod_congr rfl fun i _ => if_pos i.isLt, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      simp
    · simp only [Nat.add_one]
      rw [Fin.prod_univ_castSucc]
      have h1 : (∏ i : Fin t, (if ((Fin.castSucc i : Fin (t + 1)) : ℕ) < t then (-2 : ℤ) else 2)) =
          (-2) ^ t := by
        rw [Finset.prod_congr rfl fun i _ => if_pos i.isLt, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
      rw [h1]
      simp
  exact hprod

private theorem opf_modEq_main [CharP K 2] [Finite K] [Fintype K] (hK : Nat.card K = 2) :
    OrdPNsOm.charSum (planeQForm K t δ) ⊤ ≡ (if δ = 0 then 1 else -1) [ZMOD 3] := by
  rw [opf_charSum_main hK]
  fin_cases δ
  · simp only [pow_zero, mul_one]
    exact (Int.ModEq.pow t (by decide : (-2 : ℤ) ≡ 1 [ZMOD 3])).trans (by simp)
  · simp only [pow_one]
    have h : ((-2 : ℤ) ^ t * 2) ≡ (1 ^ t * (-1)) [ZMOD 3] :=
      (Int.ModEq.pow t (by decide : (-2 : ℤ) ≡ 1 [ZMOD 3])).mul
        (by decide : (2 : ℤ) ≡ -1 [ZMOD 3])
    simpa using h

theorem charSum_planeQForm [CharP K 2] [Finite K] (hK : Nat.card K = 2) :
    OrdPNsOm.charSum (planeQForm K t δ) ⊤ = (-2) ^ t * 2 ^ δ.val := by
  exact @opf_charSum_main K _ t δ _ _ (Fintype.ofFinite K) hK

theorem charSum_planeQForm_modEq [CharP K 2] [Finite K] (hK : Nat.card K = 2) :
    OrdPNsOm.charSum (planeQForm K t δ) ⊤ ≡ (if δ = 0 then 1 else -1) [ZMOD 3] := by
  exact @opf_modEq_main K _ t δ _ _ (Fintype.ofFinite K) hK

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
