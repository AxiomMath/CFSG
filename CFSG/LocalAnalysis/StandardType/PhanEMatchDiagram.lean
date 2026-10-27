module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchFin

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.PhanCode

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}

structure SLDiagram (A : Matrix (Fin n) (Fin n) ℤ) : Prop where
  symm : ∀ i j, A i j = 0 → A j i = 0
  sl : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1
  notri : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → A i j ≠ 0 → A i k ≠ 0 → A j k = 0

theorem SLDiagram.of_isFiniteType (h : TauCeti.IsFiniteType A)
    (hsl : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1) : SLDiagram A :=
  ⟨fun _ _ hij => h.apply_eq_zero_symm hij, hsl, fun _ _ _ hij hik hjk hj hk =>
    h.apply_eq_zero_of_apply_ne_zero hij hik hjk hj hk⟩

private lemma plh_symm_ne (hA : SLDiagram A) (i j : Fin n) : A i j ≠ 0 ↔ A j i ≠ 0 :=
  ⟨fun h hji => h (hA.symm j i hji), fun h hij => h (hA.symm i j hij)⟩

theorem exists_code_matches3 (hA : SLDiagram A) {J I : Set (Fin n)} (hIJ : I ⊆ J)
    {π : Fin n → Fin n} (hπI : ∀ i ∈ I, π i ∈ I) (hππ : ∀ i ∈ I, π (π i) = i)
    (hπA : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (A (π i) (π j) ≠ 0 ↔ A i j ≠ 0)) (hJ : J.ncard = 3) :
    ∃ (c : PhanCode) (σ : Fin 3 → Fin n), c ∈ codes3 ∧ c.rank = 3 ∧ Function.Injective σ ∧
      Set.range σ = J ∧
      (∀ i j : Fin 3, i ≠ j → A (σ i) (σ j) = if c.coxN i j = 3 then -1 else 0) ∧
      (∀ i : Fin 3, σ i ∈ I ↔ c.coreN i = true) ∧
      ∀ i : Fin 3, σ i ∈ I → ∃ j : Fin 3, j.val = c.permN i ∧ σ j = π (σ i) := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hJeq⟩ := Set.ncard_eq_three.mp hJ
  let ε : Fin 3 → Fin n := ![x, y, z]
  have hε : Function.Injective ε := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ε]
  have hrange : Set.range ε = J := by
    rw [hJeq]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [ε]
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  let e01 : Bool := decide (A x y ≠ 0)
  let e12 : Bool := decide (A y z ≠ 0)
  let e02 : Bool := decide (A x z ≠ 0)
  let I' : Fin 3 → Bool := fun i => decide (ε i ∈ I)
  have hkey : ∀ i j : Fin 3, cx3 e01 e12 e02 i j =
      if ε i = ε j then 1
      else if decide (A (ε i) (ε j) ≠ 0) then 3 else 2 := by
    intro i j
    have hyx : (A y x ≠ 0) = (A x y ≠ 0) := propext (plh_symm_ne hA y x)
    have hzy : (A z y ≠ 0) = (A y z ≠ 0) := propext (plh_symm_ne hA z y)
    have hzx : (A z x ≠ 0) = (A x z ≠ 0) := propext (plh_symm_ne hA z x)
    fin_cases i <;> fin_cases j <;>
      simp [e01, e12, e02, ε, cx3, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz,
        hyx, hzy, hzx] <;>
      (split_ifs <;> simp_all)
  have hπJ : ∀ i, ε i ∈ I → ∃ j, ε j = π (ε i) := by
    intro i hi
    have hmem : π (ε i) ∈ Set.range ε := by
      rw [hrange]
      exact hIJ (hπI (ε i) hi)
    exact hmem
  let π' : Fin 3 → Fin 3 := fun i => if h : ε i ∈ I then (hπJ i h).choose else i
  have hπ' : ∀ i, ε i ∈ I → ε (π' i) = π (ε i) := by
    intro i hi
    dsimp only [π']
    rw [dif_pos hi]
    exact (hπJ i hi).choose_spec
  have hvalid : Valid3 e01 e12 e02 I' π' := by
    unfold Valid3
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      have hxy0 : A x y ≠ 0 := of_decide_eq_true (show decide (A x y ≠ 0) = true from h1)
      have hyz0 : A y z ≠ 0 := of_decide_eq_true (show decide (A y z ≠ 0) = true from h2)
      have hxz0 : A x z ≠ 0 := of_decide_eq_true (show decide (A x z ≠ 0) = true from h3)
      exact hxz0 (hA.notri y x z (Ne.symm hxy) hyz hxz
        ((plh_symm_ne hA y x).mpr hxy0) hyz0)
    · intro i hi
      have hIi : ε i ∈ I := of_decide_eq_true (show decide (ε i ∈ I) = true from hi)
      have hmem : ε (π' i) ∈ I := by rw [hπ' i hIi]; exact hπI (ε i) hIi
      show decide (ε (π' i) ∈ I) = true
      exact decide_eq_true hmem
    · intro i hi
      have hIi : ε i ∈ I := of_decide_eq_true (show decide (ε i ∈ I) = true from hi)
      have hπi : ε (π' i) ∈ I := by rw [hπ' i hIi]; exact hπI (ε i) hIi
      apply hε
      calc ε (π' (π' i)) = π (ε (π' i)) := hπ' (π' i) hπi
        _ = π (π (ε i)) := by rw [hπ' i hIi]
        _ = ε i := hππ (ε i) hIi
    · intro i j hi hj
      have hIi : ε i ∈ I := of_decide_eq_true (show decide (ε i ∈ I) = true from hi)
      have hIj : ε j ∈ I := of_decide_eq_true (show decide (ε j ∈ I) = true from hj)
      rw [hkey (π' i) (π' j), hkey i j, hπ' i hIi, hπ' j hIj]
      by_cases hij : i = j
      · subst hij; simp
      · have hεij : ε i ≠ ε j := fun h => hij (hε h)
        have hπij : π (ε i) ≠ π (ε j) := fun h =>
          hεij (by rw [← hππ (ε i) hIi, ← hππ (ε j) hIj, h])
        have hdec : decide (A (π (ε i)) (π (ε j)) ≠ 0)
            = decide (A (ε i) (ε j) ≠ 0) :=
          decide_eq_decide.mpr (hπA (ε i) hIi (ε j) hIj hεij)
        rw [if_neg hπij, if_neg hεij, hdec]
  obtain ⟨c, hcmem, σ₀, hσ₀, hmatch⟩ := classify3 e01 e12 e02 I' π' hvalid
  let σ : Fin 3 → Fin n := fun i => ε (σ₀ i)
  have hσinj : Function.Injective σ := hε.comp (perms3_injective σ₀ hσ₀)
  have hσrange : Set.range σ = J := by
    have hcomp : σ = ε ∘ σ₀ := rfl
    rw [hcomp, Set.range_comp, (perms3_surjective σ₀ hσ₀).range_eq, Set.image_univ, hrange]
  refine ⟨c, σ, hcmem, hmatch.1, hσinj, hσrange, ?_, ?_, ?_⟩
  · intro i j hij
    have hσ₀ij : σ₀ i ≠ σ₀ j := fun h => hij ((perms3_injective σ₀ hσ₀) h)
    have hεij : ε (σ₀ i) ≠ ε (σ₀ j) := fun h => hσ₀ij (hε h)
    have hc : c.coxN i j = (if decide (A (σ i) (σ j) ≠ 0) then 3 else 2) := by
      rw [← hmatch.2.1 i j hij, hkey (σ₀ i) (σ₀ j), if_neg hεij]
    rcases hA.sl (σ i) (σ j) (fun h => hij (hσinj h)) with h0 | hneg
    · have hc2 : c.coxN i j = 2 := by rw [hc, if_neg (by rw [h0]; decide)]
      rw [h0, if_neg (by rw [hc2]; decide)]
    · have hc3 : c.coxN i j = 3 := by rw [hc, if_pos (by rw [hneg]; decide)]
      rw [hneg, if_pos hc3]
  · intro i
    rw [← hmatch.2.2.1 i]
    dsimp only [I', σ]
    rw [decide_eq_true_iff]
  · intro i hi
    have hIi : I' (σ₀ i) = true := by
      change decide (ε (σ₀ i) ∈ I) = true
      exact decide_eq_true hi
    obtain ⟨j, hjval, hjσ⟩ := hmatch.2.2.2 i hIi
    refine ⟨j, hjval, ?_⟩
    calc σ j = ε (σ₀ j) := rfl
      _ = ε (π' (σ₀ i)) := by rw [hjσ]
      _ = π (ε (σ₀ i)) := hπ' (σ₀ i) hi
      _ = π (σ i) := rfl

theorem exists_code_matches2 (hA : SLDiagram A) {J I : Set (Fin n)} (hIJ : I ⊆ J)
    {π : Fin n → Fin n} (hπI : ∀ i ∈ I, π i ∈ I) (hππ : ∀ i ∈ I, π (π i) = i)
    (hπA : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (A (π i) (π j) ≠ 0 ↔ A i j ≠ 0)) (hJ : J.ncard = 2) :
    ∃ (c : PhanCode) (σ : Fin 2 → Fin n), c ∈ codes2 ∧ c.rank = 2 ∧ Function.Injective σ ∧
      Set.range σ = J ∧
      (∀ i j : Fin 2, i ≠ j → A (σ i) (σ j) = if c.coxN i j = 3 then -1 else 0) ∧
      (∀ i : Fin 2, σ i ∈ I ↔ c.coreN i = true) ∧
      ∀ i : Fin 2, σ i ∈ I → ∃ j : Fin 2, j.val = c.permN i ∧ σ j = π (σ i) := by
  classical
  obtain ⟨x, y, hxy, hJeq⟩ := Set.ncard_eq_two.mp hJ
  let ε : Fin 2 → Fin n := ![x, y]
  have hε : Function.Injective ε := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ε]
  have hrange : Set.range ε = J := by
    rw [hJeq]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [ε]
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  let e01 : Bool := decide (A x y ≠ 0)
  let I' : Fin 2 → Bool := fun i => decide (ε i ∈ I)
  have hkey : ∀ i j : Fin 2, cx2 e01 i j =
      if ε i = ε j then 1
      else if decide (A (ε i) (ε j) ≠ 0) then 3 else 2 := by
    intro i j
    have hyx : (A y x ≠ 0) = (A x y ≠ 0) := propext (plh_symm_ne hA y x)
    fin_cases i <;> fin_cases j <;>
      simp [e01, ε, cx2, Matrix.cons_val_zero, Matrix.cons_val_one, hxy, Ne.symm hxy,
        hyx] <;>
      (split_ifs <;> simp_all)
  have hπJ : ∀ i, ε i ∈ I → ∃ j, ε j = π (ε i) := by
    intro i hi
    have hmem : π (ε i) ∈ Set.range ε := by
      rw [hrange]
      exact hIJ (hπI (ε i) hi)
    exact hmem
  let π' : Fin 2 → Fin 2 := fun i => if h : ε i ∈ I then (hπJ i h).choose else i
  have hπ' : ∀ i, ε i ∈ I → ε (π' i) = π (ε i) := by
    intro i hi
    dsimp only [π']
    rw [dif_pos hi]
    exact (hπJ i hi).choose_spec
  have hvalid : Valid2 e01 I' π' := by
    unfold Valid2
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hIi : ε i ∈ I := of_decide_eq_true (show decide (ε i ∈ I) = true from hi)
      have hmem : ε (π' i) ∈ I := by rw [hπ' i hIi]; exact hπI (ε i) hIi
      show decide (ε (π' i) ∈ I) = true
      exact decide_eq_true hmem
    · intro i hi
      have hIi : ε i ∈ I := of_decide_eq_true (show decide (ε i ∈ I) = true from hi)
      have hπi : ε (π' i) ∈ I := by rw [hπ' i hIi]; exact hπI (ε i) hIi
      apply hε
      calc ε (π' (π' i)) = π (ε (π' i)) := hπ' (π' i) hπi
        _ = π (π (ε i)) := by rw [hπ' i hIi]
        _ = ε i := hππ (ε i) hIi
    · intro i j hi hj
      have hIi : ε i ∈ I := of_decide_eq_true (show decide (ε i ∈ I) = true from hi)
      have hIj : ε j ∈ I := of_decide_eq_true (show decide (ε j ∈ I) = true from hj)
      rw [hkey (π' i) (π' j), hkey i j, hπ' i hIi, hπ' j hIj]
      by_cases hij : i = j
      · subst hij; simp
      · have hεij : ε i ≠ ε j := fun h => hij (hε h)
        have hπij : π (ε i) ≠ π (ε j) := fun h =>
          hεij (by rw [← hππ (ε i) hIi, ← hππ (ε j) hIj, h])
        have hdec : decide (A (π (ε i)) (π (ε j)) ≠ 0)
            = decide (A (ε i) (ε j) ≠ 0) :=
          decide_eq_decide.mpr (hπA (ε i) hIi (ε j) hIj hεij)
        rw [if_neg hπij, if_neg hεij, hdec]
  obtain ⟨c, hcmem, σ₀, hσ₀, hmatch⟩ := classify2 e01 I' π' hvalid
  let σ : Fin 2 → Fin n := fun i => ε (σ₀ i)
  have hσinj : Function.Injective σ := hε.comp (perms2_injective σ₀ hσ₀)
  have hσrange : Set.range σ = J := by
    have hcomp : σ = ε ∘ σ₀ := rfl
    rw [hcomp, Set.range_comp, (perms2_surjective σ₀ hσ₀).range_eq, Set.image_univ, hrange]
  refine ⟨c, σ, hcmem, hmatch.1, hσinj, hσrange, ?_, ?_, ?_⟩
  · intro i j hij
    have hσ₀ij : σ₀ i ≠ σ₀ j := fun h => hij ((perms2_injective σ₀ hσ₀) h)
    have hεij : ε (σ₀ i) ≠ ε (σ₀ j) := fun h => hσ₀ij (hε h)
    have hc : c.coxN i j = (if decide (A (σ i) (σ j) ≠ 0) then 3 else 2) := by
      rw [← hmatch.2.1 i j hij, hkey (σ₀ i) (σ₀ j), if_neg hεij]
    rcases hA.sl (σ i) (σ j) (fun h => hij (hσinj h)) with h0 | hneg
    · have hc2 : c.coxN i j = 2 := by rw [hc, if_neg (by rw [h0]; decide)]
      rw [h0, if_neg (by rw [hc2]; decide)]
    · have hc3 : c.coxN i j = 3 := by rw [hc, if_pos (by rw [hneg]; decide)]
      rw [hneg, if_pos hc3]
  · intro i
    rw [← hmatch.2.2.1 i]
    dsimp only [I', σ]
    rw [decide_eq_true_iff]
  · intro i hi
    have hIi : I' (σ₀ i) = true := by
      change decide (ε (σ₀ i) ∈ I) = true
      exact decide_eq_true hi
    obtain ⟨j, hjval, hjσ⟩ := hmatch.2.2.2 i hIi
    refine ⟨j, hjval, ?_⟩
    calc σ j = ε (σ₀ j) := rfl
      _ = ε (π' (σ₀ i)) := by rw [hjσ]
      _ = π (ε (σ₀ i)) := hπ' (σ₀ i) hi
      _ = π (σ i) := rfl

theorem exists_code_matches (hA : SLDiagram A) {J I : Set (Fin n)} (hIJ : I ⊆ J)
    {π : Fin n → Fin n} (hπI : ∀ i ∈ I, π i ∈ I) (hππ : ∀ i ∈ I, π (π i) = i)
    (hπA : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (A (π i) (π j) ≠ 0 ↔ A i j ≠ 0))
    (hJ : J.ncard = 2 ∨ J.ncard = 3) :
    ∃ (c : PhanCode) (σ : Fin J.ncard → Fin n), (J.ncard = 3 → c ∈ codes3) ∧
      (J.ncard = 2 → c ∈ codes2) ∧ c.rank = J.ncard ∧ Function.Injective σ ∧
      Set.range σ = J ∧
      (∀ i j : Fin J.ncard, i ≠ j → A (σ i) (σ j) = if c.coxN i j = 3 then -1 else 0) ∧
      (∀ i : Fin J.ncard, σ i ∈ I ↔ c.coreN i = true) ∧
      ∀ i : Fin J.ncard, σ i ∈ I → ∃ j : Fin J.ncard, j.val = c.permN i ∧ σ j = π (σ i) := by
  classical
  rcases hJ with hJ | hJ
  · rw [hJ]
    obtain ⟨c, σ, hmem, hrest⟩ := exists_code_matches2 hA hIJ hπI hππ hπA hJ
    exact ⟨c, σ, fun h => absurd h (by decide), fun _ => hmem, hrest⟩
  · rw [hJ]
    obtain ⟨c, σ, hmem, hrest⟩ := exists_code_matches3 hA hIJ hπI hππ hπA hJ
    exact ⟨c, σ, fun _ => hmem, fun h => absurd h (by decide), hrest⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
