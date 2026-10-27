module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphScaled

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08DiagPerm (p : ℕ) {ι : Type} (C : Matrix ι ι ℤ) (π : ι ≃ ι) : Prop :=
  ∀ i j, ((C (π i) (π j) : ℤ) : ZMod p) = ((C i j : ℤ) : ZMod p)

private def ggQ2s08b1a_AdjA (n : ℕ) (i j : Fin n) : Prop :=
  i = j ∨ (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)

private theorem ggQ2s08b1a_A_two_iff (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.A n i j = 2 ↔ ¬ ggQ2s08b1a_AdjA n i j := by
  simp only [CoxeterMatrix.A, Matrix.of_apply, ggQ2s08b1a_AdjA]
  split_ifs <;> omega

private theorem ggQ2s08b1a_B_eq_A (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.B n i j = 2 ↔ CoxeterMatrix.A n i j = 2 := by
  simp only [CoxeterMatrix.A, CoxeterMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggQ2s08b1a_B_two_iff (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.B n i j = 2 ↔ ¬ ggQ2s08b1a_AdjA n i j :=
  (ggQ2s08b1a_B_eq_A n i j).trans (ggQ2s08b1a_A_two_iff n i j)

private theorem ggQ2s08b1a_A_le_four (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.A n i j ≤ 4 := by
  by_cases hij : i = j
  · subst hij; simp [CoxeterMatrix.A]
  · simp only [CoxeterMatrix.A, Matrix.of_apply, hij, if_false]
    split_ifs <;> omega

private theorem ggQ2s08b1a_B_le_four (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.B n i j ≤ 4 := by
  by_cases hij : i = j
  · subst hij; simp [CoxeterMatrix.B]
  · simp only [CoxeterMatrix.B, Matrix.of_apply, hij, if_false]
    split_ifs <;> omega

private lemma ggQ2s08b1a_cast_eq_zero {z : ℤ}
    (hz : z = 2 ∨ z = 0 ∨ z = -1 ∨ z = -2) : ((z : ZMod 3) = 0) ↔ z = 0 := by
  rcases hz with h | h | h | h <;> subst h <;> decide

private theorem ggQ2s08b1a_entry {ι : Type*} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) (hMv : ∀ i j, M i j ≤ 4) (i j : ι) :
    C i j = 2 ∨ C i j = 0 ∨ C i j = -1 ∨ C i j = -2 := by
  by_cases hij : i = j
  · subst hij; exact Or.inl (hC.1 i)
  · rcases hC.entries hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨h6, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
    · exfalso
      have hle := hMv i j
      omega

private theorem ggQ2s08b1a_adj_of_diagPerm {ι : Type} {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) {Adj : ι → ι → Prop}
    (hM2 : ∀ i j, M i j = 2 ↔ ¬ Adj i j)
    (hMv : ∀ i j, M i j ≤ 4)
    {π : ι ≃ ι} (hπ : GGQ2S08DiagPerm 3 C π) :
    ∀ i j, Adj (π i) (π j) ↔ Adj i j := by
  have hentry := ggQ2s08b1a_entry hC hMv
  have hcast0 : ∀ x y, C x y = 0 ↔ ((C x y : ℤ) : ZMod 3) = 0 := fun x y =>
    (ggQ2s08b1a_cast_eq_zero (hentry x y)).symm
  have hzero : ∀ x y, C x y = 0 ↔ ¬ Adj x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have hAdj : Adj x x := by
        by_contra h
        have h2 := (hM2 x x).mpr h
        rw [M.diagonal] at h2
        exact (by norm_num : (1 : ℕ) ≠ 2) h2
      rw [hC.1]
      simp [hAdj]
    · have hCM : C x y = 0 ↔ M x y = 2 := by
        rcases hC.entries hxy with ⟨h2, h1, -⟩ | ⟨h3, h1, -⟩ | ⟨h4, h1⟩ | ⟨h6, h1⟩
        · exact ⟨fun _ => h2, fun _ => h1⟩
        · exact ⟨fun hc => by rw [h1] at hc; omega, fun hm => by rw [h3] at hm; omega⟩
        · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
            exact ⟨fun hc => by rw [h1] at hc; omega, fun hm => by rw [h4] at hm; omega⟩
        · exfalso
          have hle := hMv x y
          omega
      rw [hCM]
      exact hM2 x y
  intro i j
  have hthis : C (π i) (π j) = 0 ↔ C i j = 0 := by
    rw [hcast0 (π i) (π j), hcast0 i j, hπ i j]
  have hp : ¬ Adj (π i) (π j) ↔ ¬ Adj i j := by
    rw [← hzero (π i) (π j), ← hzero i j]
    exact hthis
  exact not_iff_not.mp hp

private theorem ggQ2s08b1a_seq_linear (x : ℕ → ℕ) (N : ℕ)
    (hstep : ∀ i, i + 1 ≤ N → x (i + 1) = x i + 1 ∨ x i = x (i + 1) + 1)
    (hinj : ∀ i j, i ≤ N → j ≤ N → x i = x j → i = j) :
    (∀ i, i ≤ N → x i = x 0 + i) ∨ (∀ i, i ≤ N → x 0 = x i + i) := by
  have hU : ∀ m, m ≤ N →
      (∀ i, i ≤ m → x i = x 0 + i) ∨ (∀ i, i ≤ m → x 0 = x i + i) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        exact Or.inl (fun i hi => by rw [Nat.le_zero.mp hi]; ring)
      · have hrec : m - 1 < m := by omega
        have hN : m - 1 ≤ N := by omega
        have hidx : m - 1 + 1 = m := by omega
        rcases ih (m - 1) hrec hN with hleft | hright
        · rcases hstep (m - 1) (by omega) with hs | hs
          · rw [hidx] at hs
            refine Or.inl fun i hi => ?_
            rcases lt_or_eq_of_le hi with hi' | hieq
            · exact hleft i (by omega)
            · rw [hieq]
              have h1 : x (m - 1) = x 0 + (m - 1) := hleft (m - 1) le_rfl
              omega
          · rw [hidx] at hs
            by_cases hm1 : m = 1
            · subst hm1
              refine Or.inr fun i hi => ?_
              rcases lt_or_eq_of_le hi with hi' | hieq
              · have : i = 0 := by omega
                subst this; ring
              · rw [hieq]; simpa using hs
            · exfalso
              have hm2 : 2 ≤ m := by omega
              have h1 : x (m - 1) = x 0 + (m - 1) := hleft (m - 1) le_rfl
              have h3 : x (m - 2) = x 0 + (m - 2) := hleft (m - 2) (by omega)
              have heq : x m = x (m - 2) := by omega
              exact (by omega : m ≠ m - 2) (hinj m (m - 2) hm (by omega) heq)
        · rcases hstep (m - 1) (by omega) with hs | hs
          · rw [hidx] at hs
            by_cases hm1 : m = 1
            · subst hm1
              refine Or.inl fun i hi => ?_
              rcases lt_or_eq_of_le hi with hi' | hieq
              · have : i = 0 := by omega
                subst this; ring
              · rw [hieq]; simpa using hs
            · exfalso
              have hm2 : 2 ≤ m := by omega
              have h1 : x 0 = x (m - 1) + (m - 1) := hright (m - 1) le_rfl
              have h3 : x 0 = x (m - 2) + (m - 2) := hright (m - 2) (by omega)
              have heq : x m = x (m - 2) := by omega
              exact (by omega : m ≠ m - 2) (hinj m (m - 2) hm (by omega) heq)
          · rw [hidx] at hs
            refine Or.inr fun i hi => ?_
            rcases lt_or_eq_of_le hi with hi' | hieq
            · exact hright i (by omega)
            · rw [hieq]
              have h2 : x 0 = x (m - 1) + (m - 1) := hright (m - 1) le_rfl
              omega
  exact hU N le_rfl

private theorem ggQ2s08b1a_path_aut {n : ℕ} (hn : 2 ≤ n) {σ : Fin n ≃ Fin n}
    (hσ : ∀ i j, ggQ2s08b1a_AdjA n (σ i) (σ j) ↔ ggQ2s08b1a_AdjA n i j) :
    σ = 1 ∨ σ = Fin.revPerm := by
  let x : ℕ → ℕ := fun i => if h : i < n then (σ ⟨i, h⟩ : ℕ) else 0
  have hx : ∀ i : Fin n, x i.val = (σ i : ℕ) := by
    intro i
    simp only [x]
    rw [dif_pos i.isLt]
  have hstep : ∀ i, i + 1 ≤ n - 1 → x (i + 1) = x i + 1 ∨ x i = x (i + 1) + 1 := by
    intro i hi
    have hi1 : i < n := by omega
    have hi2 : i + 1 < n := by omega
    have hadj : ggQ2s08b1a_AdjA n (⟨i, hi1⟩ : Fin n) ⟨i + 1, hi2⟩ := by
      right; left; simp
    have h := (hσ ⟨i, hi1⟩ ⟨i + 1, hi2⟩).mpr hadj
    have hne : σ ⟨i, hi1⟩ ≠ σ ⟨i + 1, hi2⟩ := fun h0 => by
      have h1 := σ.injective h0
      simp only [Fin.mk.injEq] at h1
      omega
    have h1 : x i = (σ ⟨i, hi1⟩ : ℕ) := hx ⟨i, hi1⟩
    have h2 : x (i + 1) = (σ ⟨i + 1, hi2⟩ : ℕ) := by
      simpa using hx ⟨i + 1, hi2⟩
    rw [h1, h2]
    rcases h with h0 | h0 | h0
    · exact absurd h0 hne
    · exact Or.inl h0.symm
    · exact Or.inr h0.symm
  have hinj : ∀ i j, i ≤ n - 1 → j ≤ n - 1 → x i = x j → i = j := by
    intro i j hi hj h
    have hi' : i < n := by omega
    have hj' : j < n := by omega
    have h1 : x i = (σ ⟨i, hi'⟩ : ℕ) := hx ⟨i, hi'⟩
    have h2 : x j = (σ ⟨j, hj'⟩ : ℕ) := hx ⟨j, hj'⟩
    rw [h1, h2] at h
    have h3 : (⟨i, hi'⟩ : Fin n) = ⟨j, hj'⟩ := σ.injective (Fin.ext h)
    simpa using congrArg Fin.val h3
  rcases ggQ2s08b1a_seq_linear x (n - 1) hstep hinj with hleft | hright
  · left
    have h0 : x 0 = 0 := by
      have hN : x (n - 1) = x 0 + (n - 1) := hleft (n - 1) le_rfl
      have hxN : x (n - 1) = (σ ⟨n - 1, by omega⟩ : ℕ) := hx ⟨n - 1, by omega⟩
      have hlt : (σ ⟨n - 1, by omega⟩ : ℕ) < n := (σ ⟨n - 1, by omega⟩).isLt
      have hx0 : x 0 = (σ ⟨0, by omega⟩ : ℕ) := by
        simp only [x]
        rw [dif_pos (by omega)]
      have hx0lt : x 0 < n := by rw [hx0]; exact (σ ⟨0, by omega⟩).isLt
      omega
    refine Equiv.ext (fun i => Fin.ext ?_)
    have hi : i.val ≤ n - 1 := by omega
    have hxi : x i.val = x 0 + i.val := hleft i.val hi
    rw [h0, hx i] at hxi
    change (σ i : ℕ) = i.val
    omega
  · right
    have h0 : x 0 = n - 1 := by
      have hN : x 0 = x (n - 1) + (n - 1) := hright (n - 1) le_rfl
      have hxN : x (n - 1) = (σ ⟨n - 1, by omega⟩ : ℕ) := hx ⟨n - 1, by omega⟩
      have hlt : (σ ⟨n - 1, by omega⟩ : ℕ) < n := (σ ⟨n - 1, by omega⟩).isLt
      have hx0 : x 0 = (σ ⟨0, by omega⟩ : ℕ) := by
        simp only [x]
        rw [dif_pos (by omega)]
      have hx0lt : x 0 < n := by rw [hx0]; exact (σ ⟨0, by omega⟩).isLt
      omega
    refine Equiv.ext (fun i => Fin.ext ?_)
    have hi : i.val ≤ n - 1 := by omega
    have hxi : x 0 = x i.val + i.val := hright i.val hi
    rw [h0, hx i] at hxi
    rw [Fin.revPerm_apply, Fin.val_rev]
    omega

private theorem ggQ2s08b1a_card_le_two {ι : Type} {C : Matrix ι ι ℤ} {ρ : ι ≃ ι}
    (h : ∀ π : ι ≃ ι, GGQ2S08DiagPerm 3 C π → π = 1 ∨ π = ρ) :
    Nat.card {π : ι ≃ ι // GGQ2S08DiagPerm 3 C π} ≤ 2 := by
  classical
  have hinj : Function.Injective
      (fun π : {π : ι ≃ ι // GGQ2S08DiagPerm 3 C π} =>
        (if π.1 = 1 then (0 : Fin 2) else 1)) := by
    intro π τ heq
    dsimp only at heq
    have hπ := h π.1 π.2
    have hτ := h τ.1 τ.2
    by_cases hp : π.1 = 1
    · have hp' : (if π.1 = 1 then (0 : Fin 2) else 1) = 0 := if_pos hp
      rw [hp'] at heq
      have hq : τ.1 = 1 := by
        by_contra hq
        have hq' : (if τ.1 = 1 then (0 : Fin 2) else 1) = 1 := if_neg hq
        rw [hq'] at heq
        exact absurd heq (by decide)
      exact Subtype.ext (hp.trans hq.symm)
    · have hp' : (if π.1 = 1 then (0 : Fin 2) else 1) = 1 := if_neg hp
      rw [hp'] at heq
      have hq : ¬ τ.1 = 1 := by
        intro hq
        have hq' : (if τ.1 = 1 then (0 : Fin 2) else 1) = 0 := if_pos hq
        rw [hq'] at heq
        exact absurd heq (by decide)
      exact Subtype.ext ((hπ.resolve_left hp).trans (hτ.resolve_left hq).symm)
  calc Nat.card {π : ι ≃ ι // GGQ2S08DiagPerm 3 C π} ≤ Nat.card (Fin 2) :=
        Nat.card_le_card_of_injective _ hinj
    _ = 2 := Nat.card_fin 2

private theorem ggQ2s08b1a_path_card_le {n : ℕ} (hn : 2 ≤ n)
    {M : CoxeterMatrix (Fin n)} {C : Matrix (Fin n) (Fin n) ℤ} (hC : GGIntCartan M C)
    (hM2 : ∀ i j, M i j = 2 ↔ ¬ ggQ2s08b1a_AdjA n i j)
    (hMv : ∀ i j, M i j ≤ 4) :
    Nat.card {σ : Fin n ≃ Fin n // GGQ2S08DiagPerm 3 C σ} ≤ 2 :=
  ggQ2s08b1a_card_le_two fun σ hσ =>
    ggQ2s08b1a_path_aut hn (ggQ2s08b1a_adj_of_diagPerm hC hM2 hMv hσ)

private theorem ggQ2s08b1a_D_card_le {n : ℕ} (hn : 6 ≤ n) {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : GGIntCartan (ggCoxeterMatrixD n) C) :
    Nat.card {σ : Fin n ≃ Fin n // GGQ2S08DiagPerm 3 C σ} ≤ 2 := by
  refine ggQ2s08b1a_card_le_two (ρ := Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩) ?_
  intro π hπ
  have hone := ggAtMostOneMultipleEdge_D n
  rcases hC.eq_or_eq_transpose (ggIntCartan_D n) hone with hD | hD
  · have hscaled : ∀ i j, (1 : ZMod 3) * (CartanMatrix.D n i j : ZMod 3) =
        1 * (CartanMatrix.D n (π i) (π j) : ZMod 3) := by
      intro i j
      have h := hπ i j
      rw [hD] at h
      simpa using h.symm
    exact (ggQ2g_scaledD n hn π (fun _ => 1) (fun _ => by decide) hscaled).2
  · have hscaled : ∀ i j, (1 : ZMod 3) * (CartanMatrix.D n i j : ZMod 3) =
        1 * (CartanMatrix.D n (π i) (π j) : ZMod 3) := by
      intro i j
      have h := hπ j i
      rw [hD] at h
      simp only [Matrix.transpose_apply] at h
      simpa using h.symm
    exact (ggQ2g_scaledD n hn π (fun _ => 1) (fun _ => by decide) hscaled).2

private theorem ggQ2s08b1a_card_le_of_equiv {r : ℕ} {ι : Type} {C : Matrix ι ι ℤ}
    (e : Fin r ≃ ι)
    (hbound : Nat.card {σ : Fin r ≃ Fin r //
        GGQ2S08DiagPerm 3 (Matrix.reindex e.symm e.symm C) σ} ≤ 2) :
    Nat.card {π : ι ≃ ι // GGQ2S08DiagPerm 3 C π} ≤ 2 := by
  have hiff : ∀ π : ι ≃ ι, GGQ2S08DiagPerm 3 C π →
      GGQ2S08DiagPerm 3 (Matrix.reindex e.symm e.symm C) ((e.trans π).trans e.symm) := by
    intro π h i j
    have h' := h (e i) (e j)
    simpa [GGQ2S08DiagPerm, Matrix.reindex_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_symm] using h'
  have hinj : Function.Injective
      (fun π : {π : ι ≃ ι // GGQ2S08DiagPerm 3 C π} =>
        (⟨(e.trans π.1).trans e.symm, hiff π.1 π.2⟩ :
          {σ : Fin r ≃ Fin r // GGQ2S08DiagPerm 3 (Matrix.reindex e.symm e.symm C) σ})) := by
    intro π τ h
    have h2 : (e.trans π.1).trans e.symm = (e.trans τ.1).trans e.symm :=
      congrArg Subtype.val h
    have h3 : π.1 = τ.1 := by
      refine Equiv.ext (fun a => ?_)
      obtain ⟨x, rfl⟩ := e.surjective a
      have hx := congrFun (congrArg DFunLike.coe h2) x
      simpa [Equiv.trans_apply] using hx
    exact Subtype.ext h3
  exact (Nat.card_le_card_of_injective _ hinj).trans hbound

theorem ggQ2s08_diagPerm_card_le {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} (hM : GGQ2LabelWeyl lab M)
    {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) :
    Nat.card {π : ι ≃ ι // GGQ2S08DiagPerm 3 C π} ≤ 2 := by
  obtain ⟨-, htag, hrank⟩ := hlab
  have hr : 2 ≤ lab.rank := by omega
  have hr6 : 6 ≤ lab.rank := by omega
  rcases htag with htag | htag | htag | htag | htag
  · have hM' := hM
    simp only [GGQ2LabelWeyl, htag] at hM'
    obtain ⟨e, hMe⟩ := hM'
    have hpoint : ∀ i j : Fin lab.rank,
        (M.reindex e.symm) i j = CoxeterMatrix.A lab.rank i j := by
      intro i j
      rw [CoxeterMatrix.reindex_apply, hMe, CoxeterMatrix.reindex_apply]
      simp
    refine ggQ2s08b1a_card_le_of_equiv e (ggQ2s08b1a_path_card_le hr
      (GGIntCartan.reindex (e := e.symm) hC) ?_ ?_)
    · intro i j; rw [hpoint i j]; exact ggQ2s08b1a_A_two_iff _ i j
    · intro i j; rw [hpoint i j]; exact ggQ2s08b1a_A_le_four _ i j
  · have hM' := hM
    simp only [GGQ2LabelWeyl, htag] at hM'
    obtain ⟨e, hMe⟩ := hM'
    have hpoint : ∀ i j : Fin lab.rank,
        (M.reindex e.symm) i j = CoxeterMatrix.B lab.rank i j := by
      intro i j
      rw [CoxeterMatrix.reindex_apply, hMe, CoxeterMatrix.reindex_apply]
      simp
    refine ggQ2s08b1a_card_le_of_equiv e (ggQ2s08b1a_path_card_le hr
      (GGIntCartan.reindex (e := e.symm) hC) ?_ ?_)
    · intro i j; rw [hpoint i j]; exact ggQ2s08b1a_B_two_iff _ i j
    · intro i j; rw [hpoint i j]; exact ggQ2s08b1a_B_le_four _ i j
  · have hM' := hM
    simp only [GGQ2LabelWeyl, htag] at hM'
    obtain ⟨e, hMe⟩ := hM'
    have hpoint : ∀ i j : Fin lab.rank,
        (M.reindex e.symm) i j = CoxeterMatrix.B lab.rank i j := by
      intro i j
      rw [CoxeterMatrix.reindex_apply, hMe, CoxeterMatrix.reindex_apply]
      simp
    refine ggQ2s08b1a_card_le_of_equiv e (ggQ2s08b1a_path_card_le hr
      (GGIntCartan.reindex (e := e.symm) hC) ?_ ?_)
    · intro i j; rw [hpoint i j]; exact ggQ2s08b1a_B_two_iff _ i j
    · intro i j; rw [hpoint i j]; exact ggQ2s08b1a_B_le_four _ i j
  · have hM' := hM
    simp only [GGQ2LabelWeyl, htag] at hM'
    obtain ⟨e, hMe⟩ := hM'
    have hMeq : M.reindex e.symm = ggCoxeterMatrixD lab.rank := by
      rw [hMe]
      ext i j
      rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
      simp
    have hC'' : GGIntCartan (ggCoxeterMatrixD lab.rank)
        (Matrix.reindex e.symm e.symm C) := by
      rw [← hMeq]
      exact GGIntCartan.reindex (e := e.symm) hC
    exact ggQ2s08b1a_card_le_of_equiv e (ggQ2s08b1a_D_card_le hr6 hC'')
  · have hM' := hM
    simp only [GGQ2LabelWeyl, htag] at hM'
    obtain ⟨e, hMe⟩ := hM'
    have hMeq : M.reindex e.symm = ggCoxeterMatrixD lab.rank := by
      rw [hMe]
      ext i j
      rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
      simp
    have hC'' : GGIntCartan (ggCoxeterMatrixD lab.rank)
        (Matrix.reindex e.symm e.symm C) := by
      rw [← hMeq]
      exact GGIntCartan.reindex (e := e.symm) hC
    exact ggQ2s08b1a_card_le_of_equiv e (ggQ2s08b1a_D_card_le hr6 hC'')

end CFSG.StandardType

end
