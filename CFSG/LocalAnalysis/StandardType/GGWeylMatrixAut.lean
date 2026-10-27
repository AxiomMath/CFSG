module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit

public section

namespace CFSG.StandardType

private def nbr {n : ℕ} (N : CoxeterMatrix (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j ≠ i ∧ N i j ≠ 2

private theorem mem_nbr {n : ℕ} {N : CoxeterMatrix (Fin n)} {i j : Fin n} :
    j ∈ nbr N i ↔ j ≠ i ∧ N i j ≠ 2 := by
  simp [nbr]

private theorem nbr_map {n : ℕ} {N : CoxeterMatrix (Fin n)} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, N (σ i) (σ j) = N i j) (i : Fin n) :
    (nbr N i).image σ = nbr N (σ i) := by
  ext j
  rw [Finset.mem_image]
  simp only [mem_nbr]
  constructor
  · rintro ⟨a, ⟨hai, hNa⟩, rfl⟩
    refine ⟨fun h => hai (σ.injective h), ?_⟩
    rw [hσ i a]
    exact hNa
  · intro ⟨hji, hNj⟩
    refine ⟨σ.symm j, ⟨?_, ?_⟩, by simp⟩
    · intro h
      exact hji (by simpa using congrArg σ h)
    · have hEq : N i (σ.symm j) = N (σ i) j := by
        rw [← hσ i (σ.symm j)]
        simp
      rw [hEq]
      exact hNj

private theorem nbr_card_eq {n : ℕ} {N : CoxeterMatrix (Fin n)} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, N (σ i) (σ j) = N i j) (i : Fin n) :
    (nbr N (σ i)).card = (nbr N i).card := by
  rw [← nbr_map hσ i]
  exact Finset.card_image_of_injective _ σ.injective

private theorem apply_eq_self_of_nbrs {n : ℕ} {N : CoxeterMatrix (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i j, N (σ i) (σ j) = N i j) {i j : Fin n}
    (hi : σ i = i) (hj : j ∈ nbr N i)
    (hother : ∀ k ∈ nbr N i, k ≠ j → σ k = k) : σ j = j := by
  obtain ⟨hji, hNij⟩ := mem_nbr.mp hj
  have hmem : σ j ∈ nbr N i := by
    rw [mem_nbr]
    refine ⟨?_, ?_⟩
    · intro h
      exact hji (σ.injective (by rw [h, hi]))
    · rw [← hi, hσ i j]
      exact hNij
  by_contra hne
  exact hne (σ.injective (hother (σ j) hmem hne))

private def IsPathMatrix {n : ℕ} (N : CoxeterMatrix (Fin n)) : Prop :=
  ∀ i j : Fin n, i ≠ j → (N i j ≠ 2 ↔ (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)

private def autCheck {n : ℕ} (N : CoxeterMatrix (Fin n))
    (σ : Equiv.Perm (Fin n)) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    N (σ i) (σ j) == N i j

private theorem autCheck_iff {n : ℕ} {N : CoxeterMatrix (Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    autCheck N σ = true ↔ ∀ i j, N (σ i) (σ j) = N i j := by
  simp [autCheck, List.all_eq_true, List.mem_finRange]

private theorem isPathMatrix_A (n : ℕ) : IsPathMatrix (CoxeterMatrix.A n) := by
  intro i j hij
  simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
  split_ifs with h
  · exact iff_of_true (by norm_num) (by omega)
  · exact iff_of_false (by norm_num) (by omega)

private theorem B_eq_two_iff_A_eq_two (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.B n i j = 2 ↔ CoxeterMatrix.A n i j = 2 := by
  simp only [CoxeterMatrix.A, CoxeterMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

private theorem isPathMatrix_B (n : ℕ) : IsPathMatrix (CoxeterMatrix.B n) := by
  intro i j hij
  rw [show (CoxeterMatrix.B n i j ≠ 2) ↔ (CoxeterMatrix.A n i j ≠ 2) from
    not_congr (B_eq_two_iff_A_eq_two n i j)]
  exact isPathMatrix_A n i j hij

private theorem isPathMatrix_F4 : IsPathMatrix (CoxeterMatrix.F₄) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.F₄, Matrix.of_apply, Matrix.cons_val']

private theorem isPathMatrix_G2 : IsPathMatrix (CoxeterMatrix.G₂) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']

private theorem nbr_zero {n : ℕ} {N : CoxeterMatrix (Fin n)} (hpath : IsPathMatrix N)
    (hn : 2 ≤ n) :
    nbr N ⟨0, by omega⟩ = {⟨1, by omega⟩} := by
  ext j
  rw [mem_nbr]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hj0, hNj⟩
    have h := (hpath ⟨0, by omega⟩ j (by simpa using hj0.symm)).mp hNj
    have hj1 : (j : ℕ) = 1 := by
      simp only [zero_add] at h
      omega
    exact Fin.ext (by simpa using hj1)
  · intro hj
    subst hj
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · exact (hpath ⟨0, by omega⟩ ⟨1, by omega⟩ (by
          intro h; have := congrArg Fin.val h; simp only at this; omega)).mpr
        (Or.inl (by simp only))

private theorem one_lt_nbr_card_of_interior {n : ℕ} {N : CoxeterMatrix (Fin n)}
    (hpath : IsPathMatrix N) {j : Fin n} (hj0 : 0 < (j : ℕ)) (hj1 : (j : ℕ) + 1 < n) :
    1 < (nbr N j).card := by
  let p : Fin n := ⟨(j : ℕ) - 1, by omega⟩
  let s : Fin n := ⟨(j : ℕ) + 1, hj1⟩
  have hp : p ∈ nbr N j := by
    rw [mem_nbr]
    have hjp : j ≠ p := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [p] at hv
      omega
    refine ⟨hjp.symm, (hpath j p hjp).mpr (Or.inr ?_)⟩
    dsimp [p]
    omega
  have hs : s ∈ nbr N j := by
    rw [mem_nbr]
    have hjs : j ≠ s := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [s] at hv
      omega
    refine ⟨hjs.symm, (hpath j s hjs).mpr (Or.inl ?_)⟩
    dsimp [s]
  have hps : p ≠ s := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p, s] at hv
    omega
  exact Finset.one_lt_card.mpr ⟨p, hp, s, hs, hps⟩

private theorem eq_zero_or_last_of_nbr_card_one {n : ℕ} {N : CoxeterMatrix (Fin n)}
    (hpath : IsPathMatrix N) (hn : 2 ≤ n) {j : Fin n}
    (hj : (nbr N j).card = 1) :
    j = ⟨0, by omega⟩ ∨ j = ⟨n - 1, by omega⟩ := by
  have hnot : ¬ (0 < (j : ℕ) ∧ (j : ℕ) + 1 < n) := by
    rintro ⟨hj0, hj1⟩
    have := one_lt_nbr_card_of_interior hpath hj0 hj1
    omega
  have hval : (j : ℕ) = 0 ∨ (j : ℕ) = n - 1 := by omega
  rcases hval with h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Fin.ext (by simpa using h))

private theorem eq_one_of_fixes_zero {n : ℕ} {N : CoxeterMatrix (Fin n)}
    (hpath : IsPathMatrix N) (hn : 2 ≤ n) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, N (σ i) (σ j) = N i j)
    (h0 : σ ⟨0, by omega⟩ = ⟨0, by omega⟩) : σ = 1 := by
  have hmain : ∀ (k : ℕ) (i : Fin n), (i : ℕ) < k → σ i = i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hi
      by_cases hi0 : (i : ℕ) = 0
      · have hi_eq : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi0)
        rw [hi_eq, h0]
      · have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
        let p : Fin n := ⟨(i : ℕ) - 1, by omega⟩
        have hpi : i ≠ p := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [p] at hv
          omega
        have hpσ : σ p = p := ih (i : ℕ) hi p (by
          dsimp [p]
          omega)
        have hN : N (σ i) p ≠ 2 := by
          have hconj := hσ i p
          rw [hpσ] at hconj
          rw [hconj]
          exact (hpath i p hpi).mpr (Or.inr (by dsimp [p]; omega))
        have hxi : σ i ≠ p := by
          intro h
          exact hpi (σ.injective (h.trans hpσ.symm))
        rcases (hpath (σ i) p hxi).mp hN with hcase | hcase
        ·
          have hval : (σ i : ℕ) + 1 = (i : ℕ) - 1 := by
            have hc := hcase
            dsimp [p] at hc
            omega
          by_cases hi2 : (i : ℕ) = 1
          · omega
          · have hi2' : 2 ≤ (i : ℕ) := by omega
            let q : Fin n := ⟨(i : ℕ) - 2, by omega⟩
            have hqσ : σ q = q := ih (i : ℕ) hi q (by
              dsimp [q]
              omega)
            have hxq : σ i = q := by
              apply Fin.ext
              dsimp [q]
              omega
            have hiq : i = q := σ.injective (hxq.trans hqσ.symm)
            have hv := congrArg Fin.val hiq
            dsimp [q] at hv
            omega
        · have hval : (i : ℕ) = (σ i : ℕ) := by
            have hc := hcase
            dsimp [p] at hc
            omega
          exact Fin.ext (by omega)
  exact Equiv.ext fun i => hmain n i i.isLt

private theorem path_card_le_two {n : ℕ} {N : CoxeterMatrix (Fin n)}
    (hpath : IsPathMatrix N) :
    Nat.card {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j} ≤ 2 := by
  by_cases hn : 2 ≤ n
  · let z : Fin n := ⟨0, by omega⟩
    let l : Fin n := ⟨n - 1, by omega⟩
    have hinj : Function.Injective
        (fun σ : {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j} =>
          (σ.1 z : Fin n)) := by
      rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ heq
      have hτinv : ∀ i j, N (τ.symm i) (τ.symm j) = N i j := by
        intro i j
        obtain ⟨a, rfl⟩ := τ.surjective i
        obtain ⟨b, rfl⟩ := τ.surjective j
        simpa using (hτ a b).symm
      have hρ : ∀ i j, N ((σ.trans τ.symm) i) ((σ.trans τ.symm) j) = N i j := by
        intro i j
        simp only [Equiv.trans_apply]
        rw [hτinv, hσ i j]
      have heq' : σ z = τ z := heq
      have h0 : (σ.trans τ.symm) z = z := by
        simp only [Equiv.trans_apply]
        rw [heq', Equiv.symm_apply_apply]
      have hρ1 : σ.trans τ.symm = 1 := eq_one_of_fixes_zero hpath hn hρ h0
      refine Subtype.ext (Equiv.ext fun i => ?_)
      have hsymm : τ.symm (σ i) = i := by
        have := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) hρ1) i
        simpa using this
      simpa using congrArg τ hsymm
    have himage : ∀ σ : {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j},
        σ.1 z = z ∨ σ.1 z = l := by
      rintro ⟨σ, hσ⟩
      have hcard : (nbr N (σ z)).card = (nbr N z).card := nbr_card_eq hσ z
      have hz : nbr N z = {⟨1, by omega⟩} := by
        simpa only [z] using nbr_zero hpath hn
      rw [hz] at hcard
      have hcard1 : (nbr N (σ z)).card = 1 := by simpa using hcard
      rcases eq_zero_or_last_of_nbr_card_one hpath hn hcard1 with h | h
      · exact Or.inl h
      · exact Or.inr h
    let S : Set (Fin n) := {j | j = z ∨ j = l}
    have hS : Nat.card ↥S ≤ 2 := by
      have hsurj : Function.Surjective
          (fun b : Bool => (⟨if b then z else l, by
            by_cases hb : b
            · simp [S, hb]
            · simp [S, hb]⟩ : ↥S)) := by
        rintro ⟨j, hj | hj⟩
        · exact ⟨true, Subtype.ext (by simp [hj])⟩
        · exact ⟨false, Subtype.ext (by simp [hj])⟩
      calc Nat.card ↥S ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
        _ = 2 := by simp
    calc Nat.card {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j}
        ≤ Nat.card ↥S :=
          Nat.card_le_card_of_injective
            (fun σ => (⟨σ.1 z, himage σ⟩ : ↥S))
            (fun σ τ h => hinj (Subtype.ext_iff.mp h))
      _ ≤ 2 := hS
  · have hn1 : n ≤ 1 := by omega
    have hfin : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
    have hsub : Subsingleton {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j} :=
      ⟨fun a b => Subtype.ext (Equiv.ext fun i => Subsingleton.elim _ _)⟩
    have hle1 : Nat.card {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j} ≤ 1 := by
      have h := Nat.card_le_card_of_injective
        (fun _ : {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j} => ())
        (fun a b _ => hsub.elim a b)
      simp
    exact hle1.trans (by norm_num)

private theorem card_autPerm_reindex {n : ℕ} {N : CoxeterMatrix (Fin n)} {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Fin n ≃ ι) :
    Nat.card {σ : ι ≃ ι // ∀ i j, (N.reindex e) (σ i) (σ j) = (N.reindex e) i j}
      = Nat.card {τ : Fin n ≃ Fin n // ∀ i j, N (τ i) (τ j) = N i j} := by
  classical
  refine Nat.card_congr ?_
  refine Equiv.subtypeEquiv e.symm.permCongr ?_
  intro σ
  constructor
  · intro hσ i j
    simpa [Equiv.permCongr_apply, CoxeterMatrix.reindex_apply] using hσ (e i) (e j)
  · intro hσ i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    simpa [Equiv.permCongr_apply, CoxeterMatrix.reindex_apply] using hσ a b

private theorem card_autPerm_le_of_reindex {n : ℕ} {N : CoxeterMatrix (Fin n)} {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Fin n ≃ ι)
    {k : ℕ} (h : Nat.card {τ : Fin n ≃ Fin n // ∀ i j, N (τ i) (τ j) = N i j} ≤ k) :
    Nat.card {σ : ι ≃ ι // ∀ i j, (N.reindex e) (σ i) (σ j) = (N.reindex e) i j} ≤ k := by
  rw [card_autPerm_reindex e]
  exact h

private def coxInt {n : ℕ} (N : CoxeterMatrix (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (N i j : ℤ)

private theorem eq_one_of_sepB_cox {n : ℕ} {N : CoxeterMatrix (Fin n)} {K : ℕ}
    (h : CFSG.HardMathSupport.Timmesfeld.RootAut.sepB (coxInt N) K = true)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i j, N (σ i) (σ j) = N i j) : σ = 1 :=
  CFSG.HardMathSupport.Timmesfeld.RootAut.eq_one_of_sepB h
    (fun i j => by simp only [coxInt, Matrix.of_apply, hσ i j])

private theorem subsingleton_of_sepB_cox {n : ℕ} {N : CoxeterMatrix (Fin n)} {K : ℕ}
    (h : CFSG.HardMathSupport.Timmesfeld.RootAut.sepB (coxInt N) K = true) :
    Subsingleton {σ : Equiv.Perm (Fin n) // ∀ i j, N (σ i) (σ j) = N i j} :=
  ⟨fun a b => Subtype.ext (by
    rw [eq_one_of_sepB_cox h a.2, eq_one_of_sepB_cox h b.2])⟩

private theorem E7_card_le_one :
    Nat.card {σ : Equiv.Perm (Fin 7) //
      ∀ i j, CoxeterMatrix.E₇ (σ i) (σ j) = CoxeterMatrix.E₇ i j} ≤ 1 := by
  have hsep : CFSG.HardMathSupport.Timmesfeld.RootAut.sepB (coxInt CoxeterMatrix.E₇) 14 = true := by
    decide +kernel
  have hsub := subsingleton_of_sepB_cox hsep
  have hle1 : Nat.card {σ : Equiv.Perm (Fin 7) //
      ∀ i j, CoxeterMatrix.E₇ (σ i) (σ j) = CoxeterMatrix.E₇ i j} ≤ 1 := by
    have h := Nat.card_le_card_of_injective
      (fun _ : {σ : Equiv.Perm (Fin 7) //
        ∀ i j, CoxeterMatrix.E₇ (σ i) (σ j) = CoxeterMatrix.E₇ i j} => ())
      (fun a b _ => hsub.elim a b)
    simpa using h
  exact hle1

private theorem E8_card_le_one :
    Nat.card {σ : Equiv.Perm (Fin 8) //
      ∀ i j, CoxeterMatrix.E₈ (σ i) (σ j) = CoxeterMatrix.E₈ i j} ≤ 1 := by
  have hsep : CFSG.HardMathSupport.Timmesfeld.RootAut.sepB (coxInt CoxeterMatrix.E₈) 16 = true := by
    decide +kernel
  have hsub := subsingleton_of_sepB_cox hsep
  have hle1 : Nat.card {σ : Equiv.Perm (Fin 8) //
      ∀ i j, CoxeterMatrix.E₈ (σ i) (σ j) = CoxeterMatrix.E₈ i j} ≤ 1 := by
    have h := Nat.card_le_card_of_injective
      (fun _ : {σ : Equiv.Perm (Fin 8) //
        ∀ i j, CoxeterMatrix.E₈ (σ i) (σ j) = CoxeterMatrix.E₈ i j} => ())
      (fun a b _ => hsub.elim a b)
    simpa using h
  exact hle1

private def DAdj (n : ℕ) (i j : Fin n) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 2 < n) ∨
    (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
      (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
        (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n))

private theorem D_eq_zero_iff {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    CartanMatrix.D n i j = 0 ↔ ¬ DAdj n i j := by
  unfold CartanMatrix.D
  simp only [Matrix.of_apply]
  rw [if_neg hij, if_neg (by omega : ¬ n ≤ 2)]
  unfold DAdj
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h1, h2]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3, h4]
  · simp [h1, h2, h3, h4]

private theorem D_adj_iff {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ggCoxeterMatrixD n i j ≠ 2 ↔ DAdj n i j := by
  rw [ggCoxeterMatrixD_apply, if_neg hij]
  have hD := D_eq_zero_iff hn hij
  by_cases h : DAdj n i j
  · have hne : CartanMatrix.D n i j ≠ 0 := by
      intro h0
      exact (hD).mp h0 h
    simp [hne, h]
  · have hzero : CartanMatrix.D n i j = 0 := (hD).mpr h
    simp [hzero, h]

private theorem mem_nbr_D {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} :
    j ∈ nbr (ggCoxeterMatrixD n) i ↔ j ≠ i ∧ DAdj n i j := by
  rw [mem_nbr]
  constructor
  · rintro ⟨hij, h2⟩
    exact ⟨hij, (D_adj_iff hn hij.symm).mp h2⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, (D_adj_iff hn hij.symm).mpr h⟩

private theorem D_nbr_chain {n : ℕ} (hn : 5 ≤ n) {i : Fin n}
    (hi0 : 1 ≤ (i : ℕ)) (hin : (i : ℕ) + 1 ≤ n - 3) :
    nbr (ggCoxeterMatrixD n) i = {⟨(i : ℕ) - 1, by omega⟩, ⟨(i : ℕ) + 1, by omega⟩} := by
  ext j
  rw [mem_nbr_D (by omega : 4 ≤ n)]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold DAdj
  simp [Fin.ext_iff]
  omega

private theorem D_nbr_fork {n : ℕ} (hn : 5 ≤ n) :
    nbr (ggCoxeterMatrixD n) ⟨n - 3, by omega⟩ =
      {⟨n - 4, by omega⟩, ⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} := by
  ext j
  rw [mem_nbr_D (by omega : 4 ≤ n)]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  unfold DAdj
  simp [Fin.ext_iff]
  omega

private theorem D_nbr_right {n : ℕ} (hn : 4 ≤ n) :
    nbr (ggCoxeterMatrixD n) ⟨n - 2, by omega⟩ = {⟨n - 3, by omega⟩} := by
  ext j
  rw [mem_nbr_D hn]
  simp only [Finset.mem_singleton, Fin.ext_iff]
  unfold DAdj
  simp [Fin.ext_iff]
  omega

private theorem D_nbr_left {n : ℕ} (hn : 4 ≤ n) :
    nbr (ggCoxeterMatrixD n) ⟨n - 1, by omega⟩ = {⟨n - 3, by omega⟩} := by
  ext j
  rw [mem_nbr_D hn]
  simp only [Finset.mem_singleton, Fin.ext_iff]
  unfold DAdj
  simp [Fin.ext_iff]
  omega

private theorem D_card_chain {n : ℕ} (hn : 5 ≤ n) {i : Fin n}
    (hi0 : 1 ≤ (i : ℕ)) (hin : (i : ℕ) + 1 ≤ n - 3) :
    (nbr (ggCoxeterMatrixD n) i).card = 2 := by
  rw [D_nbr_chain hn hi0 hin]
  refine Finset.card_pair_eq_two_iff.mpr ?_
  apply Fin.ne_of_val_ne
  simp

private theorem D_card_fork {n : ℕ} (hn : 5 ≤ n) :
    (nbr (ggCoxeterMatrixD n) ⟨n - 3, by omega⟩).card = 3 := by
  rw [D_nbr_fork hn, Finset.card_eq_three]
  refine ⟨⟨n - 4, by omega⟩, ⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩, ?_, ?_, ?_, rfl⟩
  · apply Fin.ne_of_val_ne; simp; omega
  · apply Fin.ne_of_val_ne; simp; omega
  · apply Fin.ne_of_val_ne; simp; omega

private theorem D_card_right {n : ℕ} (hn : 4 ≤ n) :
    (nbr (ggCoxeterMatrixD n) ⟨n - 2, by omega⟩).card = 1 := by
  rw [D_nbr_right hn]
  simp

private theorem D_card_left {n : ℕ} (hn : 4 ≤ n) :
    (nbr (ggCoxeterMatrixD n) ⟨n - 1, by omega⟩).card = 1 := by
  rw [D_nbr_left hn]
  simp

private theorem D_eq_fork_of_card_three {n : ℕ} (hn : 5 ≤ n) {j : Fin n}
    (hj : (nbr (ggCoxeterMatrixD n) j).card = 3) : j = ⟨n - 3, by omega⟩ := by
  by_contra hne
  have hlt : (j : ℕ) < n := j.isLt
  have hvalne : (j : ℕ) ≠ n - 3 := by
    intro h
    exact hne (Fin.ext (by simpa using h))
  have hcases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨
      (2 ≤ (j : ℕ) ∧ (j : ℕ) ≤ n - 4) ∨ (j : ℕ) = n - 2 ∨ (j : ℕ) = n - 1 := by
    omega
  rcases hcases with h0 | h1 | hchain | hright | hleft
  · have hj0 : j = ⟨0, by omega⟩ := Fin.ext h0
    have hzero : (nbr (ggCoxeterMatrixD n) ⟨0, by omega⟩).card = 1 := by
      have hset : nbr (ggCoxeterMatrixD n) ⟨0, by omega⟩ = {⟨1, by omega⟩} := by
        ext k
        rw [mem_nbr_D (by omega : 4 ≤ n)]
        simp only [Finset.mem_singleton, Fin.ext_iff]
        unfold DAdj
        simp
        omega
      rw [hset]
      simp
    rw [hj0, hzero] at hj
    omega
  · have hj1 : j = ⟨1, by omega⟩ := Fin.ext h1
    rw [hj1, D_card_chain hn (i := ⟨1, by omega⟩) (by simp) (by omega)] at hj
    omega
  · rw [D_card_chain hn (i := j) (by omega) (by omega)] at hj
    omega
  · rw [show j = ⟨n - 2, by omega⟩ from Fin.ext hright, D_card_right (by omega : 4 ≤ n)] at hj
    omega
  · rw [show j = ⟨n - 1, by omega⟩ from Fin.ext hleft, D_card_left (by omega : 4 ≤ n)] at hj
    omega

private theorem D_fixes_top {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j)
    (hc : σ ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩) :
    σ ⟨n - 4, by omega⟩ = ⟨n - 4, by omega⟩ := by
  let c : Fin n := ⟨n - 3, by omega⟩
  let t : Fin n := ⟨n - 4, by omega⟩
  have hc' : σ c = c := by simpa [c] using hc
  have hcval : (c : ℕ) = n - 3 := rfl
  have htval : (t : ℕ) = n - 4 := rfl
  have htmem : t ∈ nbr (ggCoxeterMatrixD n) c := by
    rw [mem_nbr_D (by omega : 4 ≤ n)]
    refine ⟨?_, ?_⟩
    · intro h
      have hv : (t : ℕ) = (c : ℕ) := congrArg Fin.val h
      rw [htval, hcval] at hv
      omega
    · unfold DAdj
      rw [hcval, htval]
      omega
  have hσt_mem : σ t ∈ nbr (ggCoxeterMatrixD n) c := by
    have h : σ t ∈ nbr (ggCoxeterMatrixD n) (σ c) := by
      rw [mem_nbr]
      refine ⟨?_, ?_⟩
      · intro hEq
        have htne : t ≠ c := by
          intro h
          have hv : (t : ℕ) = (c : ℕ) := congrArg Fin.val h
          rw [htval, hcval] at hv
          omega
        exact htne (σ.injective (by rw [hEq, hc']))
      · rw [hσ c t]
        exact (mem_nbr.mp htmem).2
    simpa [hc'] using h
  rw [D_nbr_fork hn] at hσt_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσt_mem
  have hcard : (nbr (ggCoxeterMatrixD n) (σ t)).card = 2 := by
    rw [nbr_card_eq hσ t]
    exact D_card_chain hn (i := t) (by rw [htval]; omega) (by rw [htval]; omega)
  rcases hσt_mem with h | h | h
  · exact h
  · rw [h, D_card_right (by omega : 4 ≤ n)] at hcard
    omega
  · rw [h, D_card_left (by omega : 4 ≤ n)] at hcard
    omega

private theorem D_fixes_down {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j)
    (hc : σ ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩)
    (htop : σ ⟨n - 4, by omega⟩ = ⟨n - 4, by omega⟩) :
    ∀ d : ℕ, d ≤ n - 4 →
      σ ⟨n - 4 - d, by omega⟩ = ⟨n - 4 - d, by omega⟩ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · simpa using htop
    · let a : Fin n := ⟨n - 3 - d, by omega⟩
      let i : Fin n := ⟨n - 4 - d, by omega⟩
      have haval : (a : ℕ) = n - 3 - d := rfl
      have hival : (i : ℕ) = n - 4 - d := rfl
      have ha0 : 1 ≤ (a : ℕ) := by rw [haval]; omega
      have han : (a : ℕ) + 1 ≤ n - 3 := by rw [haval]; omega
      have hia : (i : ℕ) + 1 = (a : ℕ) := by rw [hival, haval]; omega
      have haσ : σ a = a := by
        have hd1 : d - 1 ≤ n - 4 := by omega
        have h := ih (d - 1) (by omega) hd1
        have h' : (⟨n - 4 - (d - 1), by omega⟩ : Fin n) = a := by
          apply Fin.ext
          change n - 4 - (d - 1) = (a : ℕ)
          rw [haval]
          omega
        rwa [h'] at h
      have hotherσ : σ ⟨(a : ℕ) + 1, by omega⟩ = ⟨(a : ℕ) + 1, by omega⟩ := by
        by_cases hd1 : d = 1
        · subst hd1
          have hcent : (⟨(a : ℕ) + 1, by omega⟩ : Fin n) = ⟨n - 3, by omega⟩ := by
            apply Fin.ext
            change (a : ℕ) + 1 = n - 3
            rw [haval]
            omega
          rw [hcent]
          exact hc
        · have hd2 : 2 ≤ d := by omega
          have hdle : d - 2 ≤ n - 4 := by omega
          have h := ih (d - 2) (by omega) hdle
          have h' : (⟨n - 4 - (d - 2), by omega⟩ : Fin n) =
              ⟨(a : ℕ) + 1, by omega⟩ := by
            apply Fin.ext
            change n - 4 - (d - 2) = (a : ℕ) + 1
            rw [haval]
            omega
          rwa [h'] at h
      have hji : i ∈ nbr (ggCoxeterMatrixD n) a := by
        rw [mem_nbr]
        refine ⟨?_, ?_⟩
        · intro hEq
          have hv : (i : ℕ) = (a : ℕ) := congrArg Fin.val hEq
          rw [hival, haval] at hv
          omega
        · rw [D_adj_iff (by omega : 4 ≤ n) (by
            intro hEq
            have hv : (a : ℕ) = (i : ℕ) := congrArg Fin.val hEq
            rw [hival, haval] at hv
            omega)]
          unfold DAdj
          rw [hival, haval]
          omega
      have hother : ∀ k ∈ nbr (ggCoxeterMatrixD n) a, k ≠ i → σ k = k := by
        intro k hk hki
        rw [D_nbr_chain hn ha0 han] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with hk | hk
        · exfalso
          apply hki
          rw [hk]
          apply Fin.ext
          change (a : ℕ) - 1 = (i : ℕ)
          rw [haval, hival]
          omega
        · rw [hk]
          exact hotherσ
      have h := apply_eq_self_of_nbrs hσ haσ hji hother
      simpa [i] using h

private theorem dCard_le_two {n : ℕ} (hn : 5 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j} ≤ 2 := by
  let c : Fin n := ⟨n - 3, by omega⟩
  let t : Fin n := ⟨n - 4, by omega⟩
  let r : Fin n := ⟨n - 2, by omega⟩
  let s : Fin n := ⟨n - 1, by omega⟩
  have hcval : (c : ℕ) = n - 3 := rfl
  have htval : (t : ℕ) = n - 4 := rfl
  have hrval : (r : ℕ) = n - 2 := rfl
  have hsval : (s : ℕ) = n - 1 := rfl
  have hspine : ∀ σ : {σ : Equiv.Perm (Fin n) //
      ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j},
      ∀ i : Fin n, i.val ≤ n - 3 → σ.1 i = i := by
    rintro ⟨σ, hσ⟩ i hi
    have hc : σ c = c := by
      apply D_eq_fork_of_card_three hn
      rw [nbr_card_eq hσ c, D_card_fork hn]
    have htop : σ t = t := by
      apply D_fixes_top hn hσ
      simpa [c] using hc
    have hfixc : σ ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by simpa [c] using hc
    have hfixt : σ ⟨n - 4, by omega⟩ = ⟨n - 4, by omega⟩ := by simpa [t] using htop
    by_cases hi3 : (i : ℕ) = n - 3
    · have hic : i = c := by
        apply Fin.ext
        rw [hi3, hcval]
      rw [hic]
      exact hc
    · have hi4 : (i : ℕ) ≤ n - 4 := by omega
      have h := D_fixes_down hn hσ hfixc hfixt (n - 4 - (i : ℕ)) (by omega)
      have hi_eq : (⟨n - 4 - (n - 4 - (i : ℕ)), by omega⟩ : Fin n) = i := by
        apply Fin.ext
        change n - 4 - (n - 4 - (i : ℕ)) = (i : ℕ)
        omega
      rwa [hi_eq] at h
  have hcases : ∀ σ : {σ : Equiv.Perm (Fin n) //
      ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j},
      σ.1 = 1 ∨ σ.1 = Equiv.swap r s := by
    rintro ⟨σ, hσ⟩
    have hsp := hspine ⟨σ, hσ⟩
    have hleafmap : ∀ x : Fin n, x = r ∨ x = s → σ x = r ∨ σ x = s := by
      intro x hx
      by_contra hcon
      push Not at hcon
      have hxspine : (σ x).val ≤ n - 3 := by
        by_contra h
        have hval : (σ x).val = n - 2 ∨ (σ x).val = n - 1 := by
          have := (σ x).isLt
          omega
        rcases hval with hv | hv
        · exact hcon.1 (Fin.ext (by rw [hrval]; omega))
        · exact hcon.2 (Fin.ext (by rw [hsval]; omega))
      have hfix : σ (σ x) = σ x := hsp (σ x) hxspine
      have hxfix : σ x = x := σ.injective hfix
      rcases hx with hx | hx
      · exact hcon.1 (hxfix.trans hx)
      · exact hcon.2 (hxfix.trans hx)
    have hle := hleafmap r (Or.inl rfl)
    rcases hle with hr | hr
    · left
      ext i
      by_cases hi : i.val ≤ n - 3
      · rw [hsp i hi]; rfl
      · have hival : i.val = n - 2 ∨ i.val = n - 1 := by omega
        rcases hival with h | h
        · have hir : i = r := Fin.ext h
          rw [hir, hr]; rfl
        · have his : i = s := Fin.ext h
          rw [his]
          have hsr : σ s = s := by
            rcases hleafmap s (Or.inr rfl) with hs | hs
            · exfalso
              have hEq : σ s = σ r := hs.trans hr.symm
              have hsr' : s = r := σ.injective hEq
              have hv : (s : ℕ) = (r : ℕ) := congrArg Fin.val hsr'
              rw [hsval, hrval] at hv
              omega
            · exact hs
          rw [hsr]; rfl
    · right
      ext i
      by_cases hi : i.val ≤ n - 3
      · rw [hsp i hi]
        exact congrArg Fin.val (Equiv.swap_apply_of_ne_of_ne
          (by intro h; have hv : (i : ℕ) = (r : ℕ) := congrArg Fin.val h; rw [hrval] at hv; omega)
          (by intro h; have hv : (i : ℕ) = (s : ℕ) := congrArg Fin.val h; rw [hsval] at hv; omega)).symm
      · have hival : i.val = n - 2 ∨ i.val = n - 1 := by omega
        rcases hival with h | h
        · have hir : i = r := Fin.ext h
          rw [hir, hr, Equiv.swap_apply_left]
        · have his : i = s := Fin.ext h
          rw [his]
          have hsr : σ s = r := by
            rcases hleafmap s (Or.inr rfl) with hs | hs
            · exact hs
            · exfalso
              have hEq : σ s = σ r := hs.trans hr.symm
              have hsr' : s = r := σ.injective hEq
              have hv : (s : ℕ) = (r : ℕ) := congrArg Fin.val hsr'
              rw [hsval, hrval] at hv
              omega
          rw [hsr, Equiv.swap_apply_right]
  have hswap_ne : (Equiv.swap r s : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    have hs_eq_r : s = r := by
      simpa using congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) h) r
    have hv : (s : ℕ) = (r : ℕ) := congrArg Fin.val hs_eq_r
    rw [hsval, hrval] at hv
    omega
  have hinj : Function.Injective
      (fun σ : {σ : Equiv.Perm (Fin n) //
        ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j} =>
        (if σ.1 = 1 then true else false)) := by
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ hb
    change (if σ = 1 then true else false) = (if τ = 1 then true else false) at hb
    rcases hcases ⟨σ, hσ⟩ with hσ1 | hσs
    · rcases hcases ⟨τ, hτ⟩ with hτ1 | hτs
      · have hσ1' : σ = 1 := hσ1
        have hτ1' : τ = 1 := hτ1
        exact Subtype.ext (hσ1'.trans hτ1'.symm)
      · have hσ1' : σ = 1 := hσ1
        have hτs' : τ = Equiv.swap r s := hτs
        rw [hσ1', hτs'] at hb
        simp [hswap_ne] at hb
    · rcases hcases ⟨τ, hτ⟩ with hτ1 | hτs
      · have hσs' : σ = Equiv.swap r s := hσs
        have hτ1' : τ = 1 := hτ1
        rw [hσs', hτ1'] at hb
        simp [hswap_ne] at hb
      · have hσs' : σ = Equiv.swap r s := hσs
        have hτs' : τ = Equiv.swap r s := hτs
        exact Subtype.ext (hσs'.trans hτs'.symm)
  have hle2 : Nat.card {σ : Equiv.Perm (Fin n) //
      ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j} ≤ 2 := by
    have h := Nat.card_le_card_of_injective
      (fun σ : {σ : Equiv.Perm (Fin n) //
        ∀ i j, ggCoxeterMatrixD n (σ i) (σ j) = ggCoxeterMatrixD n i j} =>
        (if σ.1 = 1 then true else false)) hinj
    simpa using h
  exact hle2

private theorem E6_card_le_two :
    Nat.card {σ : Equiv.Perm (Fin 6) //
      ∀ i j, CoxeterMatrix.E₆ (σ i) (σ j) = CoxeterMatrix.E₆ i j} ≤ 2 := by
  have hcheck : Fintype.card {σ : Equiv.Perm (Fin 6) //
      autCheck CoxeterMatrix.E₆ σ = true} ≤ 2 := by
    decide +kernel
  calc Nat.card {σ : Equiv.Perm (Fin 6) //
        ∀ i j, CoxeterMatrix.E₆ (σ i) (σ j) = CoxeterMatrix.E₆ i j}
      = Nat.card {σ : Equiv.Perm (Fin 6) // autCheck CoxeterMatrix.E₆ σ = true} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun _ => autCheck_iff.symm))
    _ = Fintype.card {σ : Equiv.Perm (Fin 6) // autCheck CoxeterMatrix.E₆ σ = true} :=
        Nat.card_eq_fintype_card
    _ ≤ 2 := hcheck

private theorem D4_card_le_six :
    Nat.card {σ : Equiv.Perm (Fin 4) //
      ∀ i j, ggCoxeterMatrixD 4 (σ i) (σ j) = ggCoxeterMatrixD 4 i j} ≤ 6 := by
  have hcheck : Fintype.card {σ : Equiv.Perm (Fin 4) //
      autCheck (ggCoxeterMatrixD 4) σ = true} ≤ 6 := by
    decide +kernel
  calc Nat.card {σ : Equiv.Perm (Fin 4) //
        ∀ i j, ggCoxeterMatrixD 4 (σ i) (σ j) = ggCoxeterMatrixD 4 i j}
      = Nat.card {σ : Equiv.Perm (Fin 4) // autCheck (ggCoxeterMatrixD 4) σ = true} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun _ => autCheck_iff.symm))
    _ = Fintype.card {σ : Equiv.Perm (Fin 4) // autCheck (ggCoxeterMatrixD 4) σ = true} :=
        Nat.card_eq_fintype_card
    _ ≤ 6 := hcheck

theorem GGIsWeylMatrix.card_autPerm_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hD4 : ¬ ∃ e : Fin 4 ≃ ι, M = (ggCoxeterMatrixD 4).reindex e) :
    Nat.card {σ : ι ≃ ι // ∀ i j, M (σ i) (σ j) = M i j} ≤ 2 := by
  classical
  rcases hM with ⟨n, e, _, hA | ⟨_, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
    ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · obtain rfl := hA
    exact card_autPerm_le_of_reindex e (path_card_le_two (isPathMatrix_A n))
  · obtain rfl := hB
    exact card_autPerm_le_of_reindex e (path_card_le_two (isPathMatrix_B n))
  · by_cases h4 : n = 4
    · subst n
      exact (hD4 ⟨e,hD⟩).elim
    · obtain rfl := hD
      exact card_autPerm_le_of_reindex e (dCard_le_two (by omega))
  · obtain rfl := hE6
    exact card_autPerm_le_of_reindex e E6_card_le_two
  · obtain rfl := hE7
    exact card_autPerm_le_of_reindex e (E7_card_le_one.trans (by norm_num))
  · obtain rfl := hE8
    exact card_autPerm_le_of_reindex e (E8_card_le_one.trans (by norm_num))
  · obtain rfl := hF4
    exact card_autPerm_le_of_reindex e (path_card_le_two isPathMatrix_F4)
  · obtain rfl := hG2
    exact card_autPerm_le_of_reindex e (path_card_le_two isPathMatrix_G2)

theorem GGIsWeylMatrix.card_autPerm_le_six {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) :
    Nat.card {σ : ι ≃ ι // ∀ i j, M (σ i) (σ j) = M i j} ≤ 6 := by
  classical
  rcases hM with ⟨n, e, _, hA | ⟨_, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
    ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · obtain rfl := hA
    exact card_autPerm_le_of_reindex e ((path_card_le_two (isPathMatrix_A n)).trans (by norm_num))
  · obtain rfl := hB
    exact card_autPerm_le_of_reindex e ((path_card_le_two (isPathMatrix_B n)).trans (by norm_num))
  · obtain rfl := hD
    by_cases h4 : n = 4
    · subst h4
      exact card_autPerm_le_of_reindex e D4_card_le_six
    · exact card_autPerm_le_of_reindex e ((dCard_le_two (by omega)).trans (by norm_num))
  · obtain rfl := hE6
    exact card_autPerm_le_of_reindex e (E6_card_le_two.trans (by norm_num))
  · obtain rfl := hE7
    exact card_autPerm_le_of_reindex e (E7_card_le_one.trans (by norm_num))
  · obtain rfl := hE8
    exact card_autPerm_le_of_reindex e (E8_card_le_one.trans (by norm_num))
  · obtain rfl := hF4
    exact card_autPerm_le_of_reindex e ((path_card_le_two isPathMatrix_F4).trans (by norm_num))
  · obtain rfl := hG2
    exact card_autPerm_le_of_reindex e ((path_card_le_two isPathMatrix_G2).trans (by norm_num))

end CFSG.StandardType

end
