module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphAlgebra

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma pslB1_smul_one_pow {n : ℕ} {K : Type} [CommSemiring K] (a : K) (m : ℕ) :
    ((a • (1 : Matrix (Fin n) (Fin n) K)) ^ m) = a ^ m • (1 : Matrix (Fin n) (Fin n) K) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_succ]

private lemma pslB1_scalar_of_sq {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (hodd : Odd (orderOf B))
    (hsq : ∃ c : Kˣ, (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (c : K) • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ b : Kˣ, (B : Matrix (Fin n) (Fin n) K) = (b : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨k, hk⟩ := hodd
  have hval : (B : Matrix (Fin n) (Fin n) K) ^ orderOf B = 1 := by
    have h := Units.val_pow_eq_pow_val B (orderOf B)
    rw [pow_orderOf_eq_one, Units.val_one] at h
    exact h.symm
  have hpow1 : (B : Matrix (Fin n) (Fin n) K) ^ (2 * k + 1) = 1 := by
    rw [← hk]; exact hval
  have hB2 : (B : Matrix (Fin n) (Fin n) K) ^ 2 =
      (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [pow_two]; exact hc
  refine ⟨c ^ (k + 1), ?_⟩
  have hmain : (B : Matrix (Fin n) (Fin n) K) =
      (c : K) ^ (k + 1) • (1 : Matrix (Fin n) (Fin n) K) := by
    calc (B : Matrix (Fin n) (Fin n) K)
        = (B : Matrix (Fin n) (Fin n) K) ^ (2 * k + 2) := by
          rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, pow_succ, hpow1, one_mul]
      _ = ((B : Matrix (Fin n) (Fin n) K) ^ 2) ^ (k + 1) := by
          rw [← pow_mul]; congr 1
      _ = ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) ^ (k + 1) := by rw [hB2]
      _ = (c : K) ^ (k + 1) • (1 : Matrix (Fin n) (Fin n) K) :=
          pslB1_smul_one_pow (c : K) (k + 1)
  rw [hmain, Units.val_pow_eq_pow_val]

private lemma pslB1_chat_top {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {B : GL (Fin n) K} {b : Kˣ}
    (hB : (B : Matrix (Fin n) (Fin n) K) = (b : K) • (1 : Matrix (Fin n) (Fin n) K)) :
    ∀ x : SpecialLinearGroup (Fin n) K, x ∈ pslChat B := by
  intro x
  show proj n K x ∈ pslCent B
  show conjAut n K B (proj n K x) = proj n K x
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hcomm : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) := by
    rw [hB, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  have hBBinv : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hcomm, Matrix.mul_assoc, hBBinv, Matrix.mul_one]

private lemma pslB1_exists_third {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ l : Fin n, l ≠ i ∧ l ≠ j := by
  by_contra h
  have h' : ∀ l : Fin n, l = i ∨ l = j := by
    intro l
    by_cases hli : l = i
    · exact Or.inl hli
    · by_cases hlj : l = j
      · exact Or.inr hlj
      · exact absurd ⟨l, hli, hlj⟩ h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
    intro x _
    rcases h' x with hx | hx
    · exact Finset.mem_insert.mpr (Or.inl hx)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hx))
  have hcard : (Finset.univ : Finset (Fin n)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card hsub) ?_
    have hle := Finset.card_insert_le i ({j} : Finset (Fin n))
    simp only [Finset.card_singleton] at hle
    omega
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

private lemma pslB1_formAdj_single {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (i j : Fin n) (a : K) :
    formAdj (RingHom.id K) G (Matrix.single i j a) =
      G⁻¹ * Matrix.single j i a * G := by
  have hmap : (Matrix.single i j a).map (RingHom.id K) = Matrix.single i j a := by
    ext p q; rfl
  unfold formAdj
  rw [hmap, Matrix.transpose_single]

private lemma pslB1_single_neg_one {n : ℕ} {K : Type} [Field K] (i j : Fin n) :
    Matrix.single i j (-1 : K) = (-1 : K) • Matrix.single i j (1 : K) := by
  ext p q
  by_cases h : i = p ∧ j = q <;> simp [Matrix.single_apply, Matrix.smul_apply, h]

private lemma pslB1_formAdj_transvection {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (hG : IsUnit G.det) (i j : Fin n) :
    formAdj (RingHom.id K) G (Matrix.transvection i j (-1)) =
      1 - G⁻¹ * Matrix.single j i (1 : K) * G := by
  rw [Matrix.transvection, Geo.formAdj_add, Geo.formAdj_one (RingHom.id K) hG,
    pslB1_formAdj_single]
  rw [pslB1_single_neg_one, Matrix.mul_smul, Matrix.smul_mul, neg_one_smul, sub_eq_add_neg]

private lemma pslB1_single_mul_apply {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (i j a b : Fin n) :
    (Matrix.single j i (1 : K) * G) a b = if a = j then G i b else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.single_apply]
    by_cases h : a = j
    · rw [if_pos h, if_pos ⟨h.symm, rfl⟩, one_mul]
    · have h' : ¬ (j = a ∧ i = i) := fun hh => h hh.1.symm
      rw [if_neg h', if_neg h, zero_mul]
  · intro x _ hx
    rw [Matrix.single_apply]
    simp [Ne.symm hx]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma pslB1_mul_single_apply {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (i j a b : Fin n) :
    (G * Matrix.single i j (1 : K)) a b = if b = j then G a i else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.single_apply]
    by_cases h : b = j
    · rw [if_pos h, if_pos ⟨rfl, h.symm⟩, mul_one]
    · have h' : ¬ (i = i ∧ j = b) := fun hh => h hh.2.symm
      rw [if_neg h', if_neg h, mul_zero]
  · intro x _ hx
    rw [Matrix.single_apply]
    simp [Ne.symm hx]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma pslB1_conj_single_apply {n : ℕ} {K : Type} [Field K]
    (H G : Matrix (Fin n) (Fin n) K) (i j a b : Fin n) :
    (H * Matrix.single j i (1 : K) * G) a b = H a j * G i b := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hinner : ∀ x, (Matrix.single j i (1 : K) * G) x b = if x = j then G i b else 0 := by
    intro x
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.single_apply]
      by_cases h : x = j
      · rw [if_pos h, if_pos ⟨h.symm, rfl⟩, one_mul]
      · have h' : ¬ (j = x ∧ i = i) := fun hh => h hh.1.symm
        rw [if_neg h', if_neg h, zero_mul]
    · intro y _ hy
      rw [Matrix.single_apply]
      simp [Ne.symm hy]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [hinner]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro x _ hx
    rw [if_neg hx, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma pslB1_row_support {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (hn : 3 ≤ n)
    (hall : ∀ x : SpecialLinearGroup (Fin n) K, ∃ d : Kˣ,
      formAdj (RingHom.id K) G ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (d : K) • (x : Matrix (Fin n) (Fin n) K))
    (i j : Fin n) (hij : i ≠ j) :
    ∀ b : Fin n, b ≠ j → G i b = 0 := by
  obtain ⟨l, hli, hlj⟩ := pslB1_exists_third hn i j
  let x : SpecialLinearGroup (Fin n) K :=
    ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩
  obtain ⟨d, hd⟩ := hall x
  have hxval : (x : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j (1 : K) := rfl
  have hyval : ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transvection i j (-1) := by
    let y : SpecialLinearGroup (Fin n) K :=
      ⟨Matrix.transvection i j (-1), Matrix.det_transvection_of_ne i j hij (-1)⟩
    have hxy : x * y = 1 := by
      apply Subtype.ext
      show Matrix.transvection i j 1 * Matrix.transvection i j (-1) = 1
      rw [Matrix.transvection_mul_transvection_same i j hij 1 (-1), add_neg_cancel,
        Matrix.transvection_zero]
    have h := congrArg (fun z : SpecialLinearGroup (Fin n) K =>
      (z : Matrix (Fin n) (Fin n) K)) (inv_eq_of_mul_eq_one_right hxy)
    simpa using h
  have hform := pslB1_formAdj_transvection G hG i j
  have hd' : (1 : Matrix (Fin n) (Fin n) K) - G⁻¹ * Matrix.single j i (1 : K) * G =
      (d : K) • (1 : Matrix (Fin n) (Fin n) K) + (d : K) • Matrix.single i j (1 : K) := by
    have h := hd
    rw [hyval, hform, hxval, smul_add] at h
    exact h
  have hA : (G⁻¹) i j * G i l = 0 := by
    have he := congrFun (congrFun hd' i) l
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      pslB1_conj_single_apply, Matrix.single_apply] at he
    simp [Ne.symm hli, Ne.symm hlj] at he
    simpa using he
  have hB : (G⁻¹) i j * G i i = 1 - (d : K) := by
    have he := congrFun (congrFun hd' i) i
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      pslB1_conj_single_apply, Matrix.single_apply] at he
    simp [hij.symm] at he
    rw [← he]; abel
  have hC : (G⁻¹) l j * G i l = 1 - (d : K) := by
    have he := congrFun (congrFun hd' l) l
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      pslB1_conj_single_apply, Matrix.single_apply] at he
    simp [Ne.symm hli, Ne.symm hlj] at he
    rw [← he]; abel
  have hd1 : (d : K) = 1 := by
    by_cases hAj : (G⁻¹) i j = 0
    · have h0 : (1 : K) - (d : K) = 0 := by
        rw [hAj, zero_mul] at hB
        exact hB.symm
      exact (sub_eq_zero.mp h0).symm
    · have hGil : G i l = 0 := by
        rcases mul_eq_zero.mp hA with h | h
        · exact absurd h hAj
        · exact h
      rw [hGil, mul_zero] at hC
      have h0 : (1 : K) - (d : K) = 0 := hC.symm
      exact (sub_eq_zero.mp h0).symm
  have hBeq : G⁻¹ * Matrix.single j i (1 : K) * G = - Matrix.single i j (1 : K) := by
    have h := hd'
    rw [hd1] at h
    simp only [one_smul] at h
    rw [sub_eq_add_neg] at h
    have h2 := add_left_cancel h
    rw [← h2, neg_neg]
  have hGE : Matrix.single j i (1 : K) * G = -(G * Matrix.single i j (1 : K)) := by
    have hmul := congrArg (fun M : Matrix (Fin n) (Fin n) K => G * M) hBeq
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv G hG, Matrix.one_mul] at hmul
    exact hmul
  intro b hbj
  have he := congrFun (congrFun hGE j) b
  simp only [pslB1_single_mul_apply, Matrix.neg_apply, pslB1_mul_single_apply] at he
  simp [hbj] at he
  exact he

private lemma pslB1_not_all {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (hn : 3 ≤ n) :
    ¬ ∀ x : SpecialLinearGroup (Fin n) K, ∃ d : Kˣ,
      formAdj (RingHom.id K) G ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (d : K) • (x : Matrix (Fin n) (Fin n) K) := by
  intro hall
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let j' : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [i, j, Fin.val_mk] at hv
    omega
  have hij' : i ≠ j' := by
    intro h
    have hv := congrArg Fin.val h
    simp only [i, j', Fin.val_mk] at hv
    omega
  have hjj' : j ≠ j' := by
    intro h
    have hv := congrArg Fin.val h
    simp only [j, j', Fin.val_mk] at hv
    omega
  have hrowj := pslB1_row_support hG hn hall i j hij
  have hrowj' := pslB1_row_support hG hn hall i j' hij'
  have hrowzero : ∀ b : Fin n, G i b = 0 := by
    intro b
    by_cases hbj : b = j
    · rw [hbj]; exact hrowj' j hjj'
    · exact hrowj b hbj
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have h := congrFun (congrFun hGG i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_zero (fun k _ => by rw [hrowzero k, zero_mul])] at h
  exact one_ne_zero h.symm

theorem pslGraph_theta_ne_one {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    ∃ a ∈ pslAlg B, formAdj (RingHom.id K) G a ≠ a := by
  by_contra h
  have hfix : ∀ a ∈ pslAlg B, formAdj (RingHom.id K) G a = a := by
    intro a ha
    by_contra hne
    exact h ⟨a, ha, hne⟩
  have hBmem : (B : Matrix (Fin n) (Fin n) K) ∈ pslAlg B :=
    Algebra.subset_adjoin ⟨B, Set.mem_singleton B, rfl⟩
  have hBfix : formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) := hfix _ hBmem
  obtain ⟨c, hc⟩ := S.star_mul
  rw [hBfix] at hc
  obtain ⟨b, hb⟩ := pslB1_scalar_of_sq S.odd ⟨c, hc⟩
  exact pslB1_not_all S.det_isUnit S.three_le (fun x => S.fix x (pslB1_chat_top hb x))

private lemma pslB1_formAdj_zero {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  have h := Geo.formAdj_add (RingHom.id K) G 0 0
  rw [add_zero] at h
  have h2 : formAdj (RingHom.id K) G 0 + 0 = formAdj (RingHom.id K) G 0 +
      formAdj (RingHom.id K) G 0 := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

private lemma pslB1_formAdj_sum {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (∑ x ∈ s, f x) = ∑ x ∈ s, formAdj (RingHom.id K) G (f x) := by
  induction s using Finset.induction_on with
  | empty => simp [pslB1_formAdj_zero G]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Geo.formAdj_add, ih]

theorem pslGraph_exists_not_typeI {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    ∃ e ∈ P, ¬ pslTypeI G B e := by
  classical
  by_contra h
  have htypeI : ∀ e ∈ P, pslTypeI G B e := by
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩
  obtain ⟨_, _, hPsum⟩ := hP
  have hall : ∀ a ∈ pslAlg B, formAdj (RingHom.id K) G a = a := by
    intro a ha
    have hsum_a : a = ∑ e ∈ P, a * e := by
      calc a = a * 1 := (mul_one a).symm
        _ = a * (∑ e ∈ P, e) := by rw [hPsum]
        _ = ∑ e ∈ P, a * e := Finset.mul_sum P (fun e => e) a
    calc formAdj (RingHom.id K) G a
        = formAdj (RingHom.id K) G (∑ e ∈ P, a * e) :=
            congrArg (formAdj (RingHom.id K) G) hsum_a
      _ = ∑ e ∈ P, formAdj (RingHom.id K) G (a * e) :=
            pslB1_formAdj_sum G P (fun e => a * e)
      _ = ∑ e ∈ P, a * e := by
            refine Finset.sum_congr rfl ?_
            intro e he
            exact (htypeI e he).2 a ha
      _ = a := hsum_a.symm
  obtain ⟨a, ha, hne⟩ := pslGraph_theta_ne_one S
  exact hne (hall a ha)

theorem pslGraph_typeI_star {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (e : Matrix (Fin n) (Fin n) K) :
    pslTypeI G B (formAdj (RingHom.id K) G e) ↔ pslTypeI G B e := by
  have hmapid : G.map (RingHom.id K) = G := by ext a b; rfl
  have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by rw [hmapid, S.symm]
  have hGG : formAdj (RingHom.id K) G (formAdj (RingHom.id K) G e) = e :=
    Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit hGh e
  constructor
  · intro h
    have h1 : formAdj (RingHom.id K) G e = e := by
      have hh := h.1
      rw [hGG] at hh
      exact hh.symm
    refine ⟨h1, ?_⟩
    intro a ha
    simpa [h1] using h.2 a ha
  · intro h
    have h1 : formAdj (RingHom.id K) G e = e := h.1
    refine ⟨?_, ?_⟩
    · rw [hGG, h1]
    · intro a ha
      simpa [h1] using h.2 a ha

end CFSG.StandardType
