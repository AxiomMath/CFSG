module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.Quasithin.A94.F6Comb

abbrev M5 : Type := Matrix (Fin 5) (Fin 5) (ZMod 2)

@[expose] def IsUp (N : M5) : Prop := ∀ i j : Fin 5, j ≤ i → N i j = 0

@[expose] def gm (N M : M5) : M5 := N + M + N * M

@[expose] def pv (N : M5) : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 := (N 0 1, N 1 2, N 2 3, N 3 4)

@[expose] def qv (N : M5) : ZMod 2 × ZMod 2 := (N 0 2, N 2 4)

@[expose] def NA0 : Finset (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :=
  {(0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (1, 0, 1, 0),
    (1, 0, 0, 1), (0, 1, 0, 1)}

@[expose] def sub2 (𝒩 : Finset M5) : Finset M5 := 𝒩.filter (fun N => pv N = 0)

@[expose] def sub3 (𝒩 : Finset M5) : Finset M5 := (sub2 𝒩).filter (fun N => qv N = 0)

@[expose] def Sv (𝒩 : Finset M5) : Finset (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) := 𝒩.image pv

@[expose] def Rv (𝒩 : Finset M5) : Finset (ZMod 2 × ZMod 2) := (sub2 𝒩).image qv

theorem mat_add_self (N : M5) : N + N = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem gm_assoc (N M K : M5) : gm (gm N M) K = gm N (gm M K) := by
  unfold gm
  noncomm_ring

private theorem gm_zero_left (N : M5) : gm 0 N = N := by
  unfold gm
  simp

private theorem gm_self {N : M5} (h : N * N = 0) : gm N N = 0 := by
  unfold gm
  simp [h, mat_add_self]

private theorem gm_invol_cancel {r X : M5} (h : r * r = 0) : gm r (gm r X) = X := by
  rw [← gm_assoc, gm_self h, gm_zero_left]

private theorem mul_01 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 0 1 = 0 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_12 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 1 2 = 0 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_23 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 2 3 = 0 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_34 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 3 4 = 0 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_02 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 0 2 = N 0 1 * M 1 2 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_13 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 1 3 = N 1 2 * M 2 3 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_24 {N M : M5} (hN : IsUp N) (hM : IsUp M) : (N * M) 2 4 = N 2 3 * M 3 4 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_03 {N M : M5} (hN : IsUp N) (hM : IsUp M) :
    (N * M) 0 3 = N 0 1 * M 1 3 + N 0 2 * M 2 3 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_14 {N M : M5} (hN : IsUp N) (hM : IsUp M) :
    (N * M) 1 4 = N 1 2 * M 2 4 + N 1 3 * M 3 4 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem mul_04 {N M : M5} (hN : IsUp N) (hM : IsUp M) :
    (N * M) 0 4 = N 0 1 * M 1 4 + N 0 2 * M 2 4 + N 0 3 * M 3 4 := by
  have hN' : ∀ i j : Fin 5, j ≤ i → N i j = 0 := hN
  have hM' : ∀ i j : Fin 5, j ≤ i → M i j = 0 := hM
  simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_five, hN', hM']

private theorem ext_up {N M : M5} (hN : IsUp N) (hM : IsUp M)
    (h1 : N 0 1 = M 0 1) (h2 : N 1 2 = M 1 2) (h3 : N 2 3 = M 2 3) (h4 : N 3 4 = M 3 4)
    (h5 : N 0 2 = M 0 2) (h6 : N 1 3 = M 1 3) (h7 : N 2 4 = M 2 4) (h8 : N 0 3 = M 0 3)
    (h9 : N 1 4 = M 1 4) (h10 : N 0 4 = M 0 4) : N = M := by
  ext i j
  by_cases hij : j ≤ i
  · rw [hN i j hij, hM i j hij]
  · simp only [not_le] at hij
    fin_cases i <;> fin_cases j <;> first
      | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7 | exact h8
      | exact h9 | exact h10 | exact absurd hij (by decide)

private theorem pv_zero_iff (N : M5) :
    pv N = 0 ↔ N 0 1 = 0 ∧ N 1 2 = 0 ∧ N 2 3 = 0 ∧ N 3 4 = 0 := by
  simp [pv, Prod.ext_iff]

private theorem pv_gm {N M : M5} (hN : IsUp N) (hM : IsUp M) : pv (gm N M) = pv N + pv M := by
  have h1 := mul_01 hN hM
  have h2 := mul_12 hN hM
  have h3 := mul_23 hN hM
  have h4 := mul_34 hN hM
  simp only [pv, gm, Prod.mk_add_mk, Matrix.add_apply, h1, h2, h3, h4, add_zero]

private theorem qv_gm {N M : M5} (hN : IsUp N) (hM : IsUp M) (hpN : pv N = 0) (hpM : pv M = 0) :
    qv (gm N M) = qv N + qv M := by
  obtain ⟨a1, -, c1, -⟩ := (pv_zero_iff N).1 hpN
  have e1 : (N * M) 0 2 = 0 := by rw [mul_02 hN hM, a1, zero_mul]
  have e2 : (N * M) 2 4 = 0 := by rw [mul_24 hN hM, c1, zero_mul]
  simp [qv, gm, e1, e2]

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

private theorem pv_add_self (x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : x + x = 0 := by
  obtain ⟨a, b, c, d⟩ := x
  simp [zmod2_add_self]

private theorem qv_add_self (x : ZMod 2 × ZMod 2) : x + x = 0 := by
  obtain ⟨a, b⟩ := x
  simp [zmod2_add_self]

private theorem mem_NA0 : ∀ a b c d : ZMod 2, a * b = 0 → b * c = 0 → c * d = 0 →
    (a, b, c, d) ∈ NA0 := by
  decide

set_option maxRecDepth 100000 in
private theorem card_closed_le_four : ∀ T ∈ NA0.powerset,
    (∀ x ∈ T, ∀ y ∈ T, x + y ∈ T) → T.card ≤ 4 := by
  decide +kernel

private theorem card_pairs_le_two : ∀ R : Finset (ZMod 2 × ZMod 2),
    (∀ u ∈ R, ∀ v ∈ R, u.1 * v.2 = v.1 * u.2) → R.card ≤ 2 := by
  decide

private theorem card_constr_le_four : ∀ a d : ZMod 2, (a ≠ 0 ∨ d ≠ 0) →
    ((Finset.univ : Finset (ZMod 2 × ZMod 2 × ZMod 2)).filter
      (fun x => a * x.2.1 = x.1 * d)).card ≤ 4 := by
  decide

private theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem zmod2_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x
  decide

private theorem zmod2_mul_eq_zero {a y d : ZMod 2} (h1 : a * y = 0) (h2 : y * d = 0)
    (h3 : a ≠ 0 ∨ d ≠ 0) : y = 0 := by
  revert a y d
  decide

private theorem mem_sub2 {𝒩 : Finset M5} {N : M5} : N ∈ sub2 𝒩 ↔ N ∈ 𝒩 ∧ pv N = 0 :=
  Finset.mem_filter

private theorem mem_sub3 {𝒩 : Finset M5} {N : M5} : N ∈ sub3 𝒩 ↔ N ∈ sub2 𝒩 ∧ qv N = 0 :=
  Finset.mem_filter

private theorem card_le_mul_of_rep {β : Type} [DecidableEq β] (𝒜 B : Finset M5) (φ : M5 → β)
    (hsq : ∀ N ∈ 𝒜, N * N = 0)
    (hB : ∀ N ∈ 𝒜, ∀ r ∈ 𝒜, φ r = φ N → gm r N ∈ B) :
    𝒜.card ≤ (𝒜.image φ).card * B.card := by
  classical
  rw [← Finset.card_product]
  have hrep : ∀ N ∈ 𝒜, Function.invFunOn φ (𝒜 : Set M5) (φ N) ∈ 𝒜 ∧
      φ (Function.invFunOn φ (𝒜 : Set M5) (φ N)) = φ N := by
    intro N hN
    have h := Function.invFunOn_pos (f := φ) (s := (𝒜 : Set M5))
      ⟨N, Finset.mem_coe.2 hN, rfl⟩
    exact ⟨Finset.mem_coe.1 h.1, h.2⟩
  refine Finset.card_le_card_of_injOn
    (fun N => (φ N, gm (Function.invFunOn φ (𝒜 : Set M5) (φ N)) N)) ?_ ?_
  · intro N hN
    have hN' : N ∈ 𝒜 := Finset.mem_coe.1 hN
    obtain ⟨hr, hφr⟩ := hrep N hN'
    exact Finset.mem_coe.2 (Finset.mem_product.2
      ⟨Finset.mem_image.2 ⟨N, hN', rfl⟩, hB N hN' _ hr hφr⟩)
  · intro N hN M hM hNM
    have hN' : N ∈ 𝒜 := Finset.mem_coe.1 hN
    have hM' : M ∈ 𝒜 := Finset.mem_coe.1 hM
    simp only [Prod.mk.injEq] at hNM
    obtain ⟨hφ, hg⟩ := hNM
    have hr : Function.invFunOn φ (𝒜 : Set M5) (φ N) =
        Function.invFunOn φ (𝒜 : Set M5) (φ M) := by rw [hφ]
    have hg2 : gm (Function.invFunOn φ (𝒜 : Set M5) (φ N)) N =
        gm (Function.invFunOn φ (𝒜 : Set M5) (φ N)) M := by
      rw [hg, hr]
    have hsqr := hsq _ (hrep N hN').1
    calc N = gm (Function.invFunOn φ (𝒜 : Set M5) (φ N))
          (gm (Function.invFunOn φ (𝒜 : Set M5) (φ N)) N) :=
            (gm_invol_cancel hsqr).symm
      _ = gm (Function.invFunOn φ (𝒜 : Set M5) (φ N))
          (gm (Function.invFunOn φ (𝒜 : Set M5) (φ N)) M) := by rw [hg2]
      _ = M := gm_invol_cancel hsqr

private theorem card_le_mul_S {𝒩 : Finset M5} (hup : ∀ N ∈ 𝒩, IsUp N)
    (hgm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, gm N M ∈ 𝒩) (hsq : ∀ N ∈ 𝒩, N * N = 0) :
    𝒩.card ≤ (Sv 𝒩).card * (sub2 𝒩).card := by
  refine card_le_mul_of_rep 𝒩 (sub2 𝒩) pv hsq ?_
  intro N hN r hr hpr
  refine mem_sub2.2 ⟨hgm r hr N hN, ?_⟩
  rw [pv_gm (hup r hr) (hup N hN), hpr, pv_add_self]

private theorem card_le_mul_R {𝒩 : Finset M5} (hup : ∀ N ∈ 𝒩, IsUp N)
    (hgm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, gm N M ∈ 𝒩) (hsq : ∀ N ∈ 𝒩, N * N = 0) :
    (sub2 𝒩).card ≤ (Rv 𝒩).card * (sub3 𝒩).card := by
  refine card_le_mul_of_rep (sub2 𝒩) (sub3 𝒩) qv ?_ ?_
  · intro N hN
    exact hsq N (mem_sub2.1 hN).1
  · intro N hN r hr hqr
    have hNm := mem_sub2.1 hN
    have hrm := mem_sub2.1 hr
    have hpg : pv (gm r N) = 0 := by
      rw [pv_gm (hup r hrm.1) (hup N hNm.1), hrm.2, hNm.2, add_zero]
    refine mem_sub3.2 ⟨mem_sub2.2 ⟨hgm r hrm.1 N hNm.1, hpg⟩, ?_⟩
    rw [qv_gm (hup r hrm.1) (hup N hNm.1) hrm.2 hNm.2, hqr, qv_add_self]

private theorem sub3_card_le (𝒩 : Finset M5) (hup : ∀ N ∈ 𝒩, IsUp N) : (sub3 𝒩).card ≤ 16 := by
  have hz : ∀ N ∈ sub3 𝒩, N 0 1 = 0 ∧ N 1 2 = 0 ∧ N 2 3 = 0 ∧ N 3 4 = 0 ∧
      N 0 2 = 0 ∧ N 2 4 = 0 := by
    intro N hN
    obtain ⟨h2, hq⟩ := mem_sub3.1 hN
    obtain ⟨-, hp⟩ := mem_sub2.1 h2
    obtain ⟨a, b, c, d⟩ := (pv_zero_iff N).1 hp
    have hq' : N 0 2 = 0 ∧ N 2 4 = 0 := by simpa [qv, Prod.ext_iff] using hq
    exact ⟨a, b, c, d, hq'.1, hq'.2⟩
  calc (sub3 𝒩).card
      ≤ (Finset.univ : Finset (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)).card := by
        refine Finset.card_le_card_of_injOn (fun N => (N 1 3, N 0 3, N 1 4, N 0 4)) ?_ ?_
        · intro N _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro N hN M hM hNM
          have hN' : N ∈ sub3 𝒩 := Finset.mem_coe.1 hN
          have hM' : M ∈ sub3 𝒩 := Finset.mem_coe.1 hM
          simp only [Prod.mk.injEq] at hNM
          obtain ⟨e13, e03, e14, e04⟩ := hNM
          obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hz N hN'
          obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hz M hM'
          have hNu : IsUp N := hup N (mem_sub2.1 (mem_sub3.1 hN').1).1
          have hMu : IsUp M := hup M (mem_sub2.1 (mem_sub3.1 hM').1).1
          exact ext_up hNu hMu (n1.trans m1.symm) (n2.trans m2.symm) (n3.trans m3.symm)
            (n4.trans m4.symm) (n5.trans m5.symm) (by rw [e13]) (n6.trans m6.symm)
            e03 e14 e04
    _ = 16 := by simp [Finset.card_univ, Fintype.card_prod, ZMod.card]

private theorem Rv_card_le_two {𝒩 : Finset M5} (hup : ∀ N ∈ 𝒩, IsUp N)
    (hcomm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, N * M = M * N) : (Rv 𝒩).card ≤ 2 := by
  refine card_pairs_le_two _ ?_
  intro u hu v hv
  obtain ⟨N, hN, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hv
  have hNm := mem_sub2.1 hN
  have hMm := mem_sub2.1 hM
  have h04 := congrArg (fun X : M5 => X 0 4) (hcomm N hNm.1 M hMm.1)
  rw [mul_04 (hup N hNm.1) (hup M hMm.1), mul_04 (hup M hMm.1) (hup N hNm.1)] at h04
  obtain ⟨n1, -, -, n4⟩ := (pv_zero_iff N).1 hNm.2
  obtain ⟨m1, -, -, m4⟩ := (pv_zero_iff M).1 hMm.2
  rw [n1, m1, n4, m4] at h04
  simpa [qv] using h04

private theorem sub3_entries {𝒩 : Finset M5} {N : M5} (hN : N ∈ sub3 𝒩) :
    N 0 1 = 0 ∧ N 1 2 = 0 ∧ N 2 3 = 0 ∧ N 3 4 = 0 ∧ N 0 2 = 0 ∧ N 2 4 = 0 := by
  obtain ⟨h2, hq⟩ := mem_sub3.1 hN
  obtain ⟨-, hp⟩ := mem_sub2.1 h2
  obtain ⟨a, b, c, d⟩ := (pv_zero_iff N).1 hp
  have hq' : N 0 2 = 0 ∧ N 2 4 = 0 := by simpa [qv, Prod.ext_iff] using hq
  exact ⟨a, b, c, d, hq'.1, hq'.2⟩

private theorem sub3_card_le_four {𝒩 : Finset M5} (hup : ∀ N ∈ 𝒩, IsUp N)
    (hcomm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, N * M = M * N) {N : M5} (hN : N ∈ 𝒩)
    (hnz : N 0 1 ≠ 0 ∨ N 3 4 ≠ 0) : (sub3 𝒩).card ≤ 4 := by
  have hYprop : ∀ Y ∈ sub3 𝒩, Y 1 3 = 0 ∧ N 0 1 * Y 1 4 = Y 0 3 * N 3 4 := by
    intro Y hYmem
    obtain ⟨y01, y12, y23, y34, y02, y24⟩ := sub3_entries hYmem
    have hY1 : Y ∈ 𝒩 := (mem_sub2.1 (mem_sub3.1 hYmem).1).1
    have hc := hcomm N hN Y hY1
    have hα := congrArg (fun X : M5 => X 0 3) hc
    have hβ := congrArg (fun X : M5 => X 1 4) hc
    have hγ := congrArg (fun X : M5 => X 0 4) hc
    rw [mul_03 (hup N hN) (hup Y hY1), mul_03 (hup Y hY1) (hup N hN)] at hα
    rw [mul_14 (hup N hN) (hup Y hY1), mul_14 (hup Y hY1) (hup N hN)] at hβ
    rw [mul_04 (hup N hN) (hup Y hY1), mul_04 (hup Y hY1) (hup N hN)] at hγ
    rw [y01, y02, y23] at hα
    rw [y12, y24, y34] at hβ
    rw [y01, y02, y24, y34] at hγ
    simp only [mul_zero, zero_mul, add_zero, zero_add] at hα hβ hγ
    have h13 : Y 1 3 = 0 := zmod2_mul_eq_zero hα hβ.symm hnz
    exact ⟨h13, hγ⟩
  calc (sub3 𝒩).card
      ≤ ((Finset.univ : Finset (ZMod 2 × ZMod 2 × ZMod 2)).filter
          (fun x => N 0 1 * x.2.1 = x.1 * N 3 4)).card := by
        refine Finset.card_le_card_of_injOn (fun Y => (Y 0 3, Y 1 4, Y 0 4)) ?_ ?_
        · intro Y hY
          have hY' : Y ∈ sub3 𝒩 := Finset.mem_coe.1 hY
          exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, (hYprop Y hY').2⟩)
        · intro Y hY Y' hY' hYY'
          have hY1 : Y ∈ sub3 𝒩 := Finset.mem_coe.1 hY
          have hY2 : Y' ∈ sub3 𝒩 := Finset.mem_coe.1 hY'
          simp only [Prod.mk.injEq] at hYY'
          obtain ⟨e03, e14, e04⟩ := hYY'
          obtain ⟨a1, a2, a3, a4, a5, a6⟩ := sub3_entries hY1
          obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sub3_entries hY2
          have hu : IsUp Y := hup Y (mem_sub2.1 (mem_sub3.1 hY1).1).1
          have hu' : IsUp Y' := hup Y' (mem_sub2.1 (mem_sub3.1 hY2).1).1
          exact ext_up hu hu' (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm)
            (a4.trans b4.symm) (a5.trans b5.symm) ((hYprop Y hY1).1.trans (hYprop Y' hY2).1.symm)
            (a6.trans b6.symm) e03 e14 e04
    _ ≤ 4 := card_constr_le_four _ _ hnz

private theorem Sv_card_le_four {𝒩 : Finset M5} (hup : ∀ N ∈ 𝒩, IsUp N)
    (hgm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, gm N M ∈ 𝒩) (hsq : ∀ N ∈ 𝒩, N * N = 0) :
    (Sv 𝒩).card ≤ 4 := by
  refine card_closed_le_four (Sv 𝒩) ?_ ?_
  · rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.1 hx
    have hu := hup N hN
    have e02 : N 0 1 * N 1 2 = 0 := by
      have h' : (N * N) 0 2 = 0 := by rw [hsq N hN]; rfl
      rwa [mul_02 hu hu] at h'
    have e13 : N 1 2 * N 2 3 = 0 := by
      have h' : (N * N) 1 3 = 0 := by rw [hsq N hN]; rfl
      rwa [mul_13 hu hu] at h'
    have e24 : N 2 3 * N 3 4 = 0 := by
      have h' : (N * N) 2 4 = 0 := by rw [hsq N hN]; rfl
      rwa [mul_24 hu hu] at h'
    exact mem_NA0 _ _ _ _ e02 e13 e24
  · intro x hx y hy
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hy
    rw [← pv_gm (hup N hN) (hup M hM)]
    exact Finset.mem_image.2 ⟨gm N M, hgm N hN M hM, rfl⟩

theorem classify (𝒩 : Finset M5) (hup : ∀ N ∈ 𝒩, IsUp N)
    (hgm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, gm N M ∈ 𝒩)
    (hcomm : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, N * M = M * N)
    (hsq : ∀ N ∈ 𝒩, N * N = 0) (hcard : 𝒩.card = 64) :
    (∀ N ∈ 𝒩, N 0 1 = 0 ∧ N 2 3 = 0 ∧ N 3 4 = 0 ∧ N 2 4 = 0) ∨
      (∀ N ∈ 𝒩, N 0 1 = 0 ∧ N 1 2 = 0 ∧ N 3 4 = 0 ∧ N 0 2 = 0) := by
  have hS4 : (Sv 𝒩).card ≤ 4 := Sv_card_le_four hup hgm hsq
  have hR2 : (Rv 𝒩).card ≤ 2 := Rv_card_le_two hup hcomm
  have hT16 : (sub3 𝒩).card ≤ 16 := sub3_card_le 𝒩 hup
  have hS : 64 ≤ (Sv 𝒩).card * (sub2 𝒩).card := by
    rw [← hcard]
    exact card_le_mul_S hup hgm hsq
  have hR : (sub2 𝒩).card ≤ (Rv 𝒩).card * (sub3 𝒩).card := card_le_mul_R hup hgm hsq
  have hA : ∀ N ∈ 𝒩, N 0 1 = 0 ∧ N 3 4 = 0 := by
    intro N hN
    by_contra hcon
    have hnz : N 0 1 ≠ 0 ∨ N 3 4 ≠ 0 := by
      by_contra h'
      exact hcon ⟨not_not.1 (fun h => h' (Or.inl h)), not_not.1 (fun h => h' (Or.inr h))⟩
    have h4 := sub3_card_le_four hup hcomm hN hnz
    have h32 : (Sv 𝒩).card * (sub2 𝒩).card ≤ 4 * (2 * 4) :=
      le_trans (Nat.mul_le_mul hS4 (le_trans hR (Nat.mul_le_mul hR2 h4))) (le_refl _)
    omega
  have hBC : (∃ N ∈ 𝒩, N 1 2 ≠ 0) ∨ (∃ N ∈ 𝒩, N 2 3 ≠ 0) := by
    by_contra hcon
    have h12 : ∀ N ∈ 𝒩, N 1 2 = 0 := fun N hN => by
      by_contra h
      exact hcon (Or.inl ⟨N, hN, h⟩)
    have h23 : ∀ N ∈ 𝒩, N 2 3 = 0 := fun N hN => by
      by_contra h
      exact hcon (Or.inr ⟨N, hN, h⟩)
    have hsub : 𝒩 ⊆ sub2 𝒩 := by
      intro N hN
      exact mem_sub2.2 ⟨hN, (pv_zero_iff N).2 ⟨(hA N hN).1, h12 N hN, h23 N hN, (hA N hN).2⟩⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (sub2 𝒩).card ≤ 2 * 16 := le_trans hR (Nat.mul_le_mul hR2 hT16)
    omega
  by_cases hb : ∃ N ∈ 𝒩, N 1 2 ≠ 0
  ·
    left
    obtain ⟨N₁, hN₁, hb1⟩ := hb
    have hN₁1 : N₁ 1 2 = 1 := zmod2_eq_one hb1
    have hu₁ := hup N₁ hN₁
    have hsq13 : N₁ 1 2 * N₁ 2 3 = 0 := by
      have h' : (N₁ * N₁) 1 3 = 0 := by rw [hsq N₁ hN₁]; rfl
      rwa [mul_13 hu₁ hu₁] at h'
    have hN₁23 : N₁ 2 3 = 0 := by
      rw [hN₁1] at hsq13
      simpa using hsq13
    have hc0 : ∀ M ∈ 𝒩, M 2 3 = 0 := by
      intro M hM
      by_contra hcM
      have hM1 : M 2 3 = 1 := zmod2_eq_one hcM
      have h13 := congrArg (fun X : M5 => X 1 3) (hcomm N₁ hN₁ M hM)
      rw [mul_13 hu₁ (hup M hM), mul_13 (hup M hM) hu₁, hN₁1, hM1, hN₁23, mul_zero] at h13
      simp at h13
    have hS2 : Sv 𝒩 ⊆ {0, (0, 1, 0, 0)} := by
      intro x hx
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hx
      have hpM : pv M = (0, M 1 2, 0, 0) := by
        simp [pv, (hA M hM).1, hc0 M hM, (hA M hM).2]
      rw [hpM]
      rcases zmod2_cases (M 1 2) with h | h
      · rw [h]; simp
      · rw [h]; simp
    have hSc : (Sv 𝒩).card ≤ 2 := le_trans (Finset.card_le_card hS2) Finset.card_le_two
    have h32 : (Sv 𝒩).card * (sub2 𝒩).card ≤ 2 * (sub2 𝒩).card :=
      Nat.mul_le_mul_right _ hSc
    have hsub2 : 32 ≤ (sub2 𝒩).card := by omega
    have hw : ∃ w ∈ sub2 𝒩, qv w ≠ 0 := by
      by_contra hcon
      have hsub : sub2 𝒩 ⊆ sub3 𝒩 := by
        intro w hw
        refine mem_sub3.2 ⟨hw, ?_⟩
        by_contra hq
        exact hcon ⟨w, hw, hq⟩
      have h1 := Finset.card_le_card hsub
      omega
    obtain ⟨w, hw, hqw⟩ := hw
    have hwm := mem_sub2.1 hw
    have hwu : IsUp w := hup w hwm.1
    obtain ⟨w1, w2, w3, w4⟩ := (pv_zero_iff w).1 hwm.2
    have hw24 : w 2 4 = 0 := by
      have h14 := congrArg (fun X : M5 => X 1 4) (hcomm N₁ hN₁ w hwm.1)
      rw [mul_14 hu₁ hwu, mul_14 hwu hu₁, hN₁1, w4, w2, (hA N₁ hN₁).2] at h14
      simpa using h14
    have hw02 : w 0 2 = 1 := by
      have h0 : w 0 2 ≠ 0 := by
        intro h0
        exact hqw (by simp [qv, h0, hw24])
      exact zmod2_eq_one h0
    have hc24 : ∀ M ∈ 𝒩, M 2 4 = 0 := by
      intro M hM
      have h04 := congrArg (fun X : M5 => X 0 4) (hcomm M hM w hwm.1)
      rw [mul_04 (hup M hM) hwu, mul_04 hwu (hup M hM)] at h04
      simp only [(hA M hM).1, (hA M hM).2, w1, w4, hw02, hw24, mul_zero, zero_mul, add_zero,
        zero_add, mul_one, one_mul] at h04
      exact h04.symm
    exact fun M hM => ⟨(hA M hM).1, hc0 M hM, (hA M hM).2, hc24 M hM⟩
  ·
    right
    have hb0 : ∀ M ∈ 𝒩, M 1 2 = 0 := fun M hM => by
      by_contra h
      exact hb ⟨M, hM, h⟩
    obtain ⟨N₂, hN₂, hc2⟩ : ∃ N ∈ 𝒩, N 2 3 ≠ 0 := by
      rcases hBC with h | h
      · exact absurd h hb
      · exact h
    have hc1 : N₂ 2 3 = 1 := zmod2_eq_one hc2
    have hu₂ := hup N₂ hN₂
    have hS2 : Sv 𝒩 ⊆ {0, (0, 0, 1, 0)} := by
      intro x hx
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hx
      have hpM : pv M = (0, 0, M 2 3, 0) := by
        simp [pv, (hA M hM).1, hb0 M hM, (hA M hM).2]
      rw [hpM]
      rcases zmod2_cases (M 2 3) with h | h
      · rw [h]; simp
      · rw [h]; simp
    have hSc : (Sv 𝒩).card ≤ 2 := le_trans (Finset.card_le_card hS2) Finset.card_le_two
    have h32 : (Sv 𝒩).card * (sub2 𝒩).card ≤ 2 * (sub2 𝒩).card :=
      Nat.mul_le_mul_right _ hSc
    have hsub2 : 32 ≤ (sub2 𝒩).card := by omega
    have hw : ∃ w ∈ sub2 𝒩, qv w ≠ 0 := by
      by_contra hcon
      have hsub : sub2 𝒩 ⊆ sub3 𝒩 := by
        intro w hw
        refine mem_sub3.2 ⟨hw, ?_⟩
        by_contra hq
        exact hcon ⟨w, hw, hq⟩
      have h1 := Finset.card_le_card hsub
      omega
    obtain ⟨w, hw, hqw⟩ := hw
    have hwm := mem_sub2.1 hw
    have hwu : IsUp w := hup w hwm.1
    obtain ⟨w1, w2, w3, w4⟩ := (pv_zero_iff w).1 hwm.2
    have hw02 : w 0 2 = 0 := by
      have h03 := congrArg (fun X : M5 => X 0 3) (hcomm N₂ hN₂ w hwm.1)
      rw [mul_03 hu₂ hwu, mul_03 hwu hu₂] at h03
      simp only [(hA N₂ hN₂).1, w1, w3, hc1, mul_zero, zero_mul, add_zero, zero_add,
        mul_one] at h03
      exact h03.symm
    have hw24 : w 2 4 = 1 := by
      have h0 : w 2 4 ≠ 0 := by
        intro h0
        exact hqw (by simp [qv, hw02, h0])
      exact zmod2_eq_one h0
    have hc02 : ∀ M ∈ 𝒩, M 0 2 = 0 := by
      intro M hM
      have h04 := congrArg (fun X : M5 => X 0 4) (hcomm M hM w hwm.1)
      rw [mul_04 (hup M hM) hwu, mul_04 hwu (hup M hM)] at h04
      simp only [(hA M hM).1, (hA M hM).2, w1, w4, hw02, hw24, mul_zero, zero_mul, add_zero,
        zero_add, mul_one] at h04
      exact h04
    exact fun M hM => ⟨(hA M hM).1, hb0 M hM, (hA M hM).2, hc02 M hM⟩

end CFSG.Quasithin.A94.F6Comb
