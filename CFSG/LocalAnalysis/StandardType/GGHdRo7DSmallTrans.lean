module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallAux

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmTransAux_mul_sign {a b : ZMod 3} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  apply CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero
  exact mul_ne_zero (by rcases ha with h | h <;> simp [h])
    (by rcases hb with h | h <;> simp [h])

private lemma hdRo7DSmTransAux_inv_sign {a : ZMod 3} (ha : a = 1 ∨ a = -1) :
    a⁻¹ = 1 ∨ a⁻¹ = -1 := by
  apply CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero
  exact inv_ne_zero (by rcases ha with h | h <;> simp [h])

private lemma hdRo7DSmTransAux_prod_sign {ι : Type*} [Fintype ι] {f : ι → ZMod 3}
    (hf : ∀ i, f i = 1 ∨ f i = -1) : (∏ i, f i = 1 ∨ ∏ i, f i = -1) := by
  apply CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
    rcases hf i with h | h <;> simp [h])

private lemma hdRo7DSmTransAux_decompFin_zero {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.decomposeFin.symm (0, τ) : Equiv.Perm (Fin (n + 1))) 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 τ

private lemma hdRo7DSmTransAux_decompFin_succ {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    (Equiv.Perm.decomposeFin.symm (0, τ) : Equiv.Perm (Fin (n + 1))) i.succ = (τ i).succ := by
  rw [Equiv.Perm.decomposeFin_symm_apply_succ]
  simp

private lemma hdRo7DSmTransAux_decompFin_symm_zero {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.decomposeFin.symm (0, τ) : Equiv.Perm (Fin (n + 1))).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, hdRo7DSmTransAux_decompFin_zero]

private lemma hdRo7DSmTransAux_decompFin_symm_succ {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i : Fin n) :
    (Equiv.Perm.decomposeFin.symm (0, τ) : Equiv.Perm (Fin (n + 1))).symm i.succ =
      (τ.symm i).succ := by
  rw [Equiv.symm_apply_eq, hdRo7DSmTransAux_decompFin_succ, Equiv.apply_symm_apply]

private lemma hdRo7DSmTransAux_dspDecompFin {n : ℕ} (τ : Equiv.Perm (Fin n))
    {d : Fin n → ZMod 3} (hd : ∀ i, d i = 1 ∨ d i = -1) (hpd : ∏ i, d i = 1) :
    DSPData (Equiv.Perm.decomposeFin.symm (0, τ)) (Fin.cons (α := fun _ => ZMod 3) 1 d) := by
  refine ⟨hdRo7DSmTransAux_decompFin_zero τ, Fin.cons_zero (α := fun _ => ZMod 3) 1 d, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨y, rfl⟩
    · exact Or.inl (Fin.cons_zero (α := fun _ => ZMod 3) 1 d)
    · exact hd y
  · rw [Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ, hpd]

private lemma hdRo7DSmTransAux_dAct_eq {n : ℕ} {h g' : DV n} (h0 : h 0 = g' 0)
    (τ : Equiv.Perm (Fin n)) (d : Fin n → ZMod 3)
    (hd : ∀ i, d i * h i.succ = g' (τ i).succ) :
    dAct (Equiv.Perm.decomposeFin.symm (0, τ)) (Fin.cons (α := fun _ => ZMod 3) 1 d) h = g' := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨y, rfl⟩
  · rw [dAct, hdRo7DSmTransAux_decompFin_symm_zero, Fin.cons_zero, h0]
    simp
  · rw [dAct, hdRo7DSmTransAux_decompFin_symm_succ, Fin.cons_succ, hd,
      Equiv.apply_symm_apply]


private lemma hdRo7DSmTransAux_d_full {n : ℕ} {h g' : DV n} (h0 : h 0 ≠ 0)
    (h0g' : h 0 = g' 0) (τ : Equiv.Perm (Fin n)) (hne : ∀ i : Fin n, h i.succ ≠ 0)
    (hmem : ∀ i : Fin n, g' (τ i).succ ≠ 0) (hsign : dSgn h = dSgn g') :
    ∃ d : Fin n → ZMod 3, (∀ i, d i = 1 ∨ d i = -1) ∧
      (∀ i, d i * h i.succ = g' (τ i).succ) ∧ (∏ i, d i = 1) := by
  let d : Fin n → ZMod 3 := fun i => g' (τ i).succ * h i.succ
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i
    exact hdRo7DSmTransAux_mul_sign
      (CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero (hmem i))
      (CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero (hne i))
  · intro i
    dsimp [d]
    rw [mul_assoc, CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_sq (hne i), mul_one]
  · have hGeq : (∏ i : Fin n, g' (τ i).succ) = ∏ i : Fin n, g' i.succ :=
      Equiv.prod_comp τ (fun i : Fin n => g' i.succ)
    have hprod : (∏ i : Fin n, d i) = (∏ i : Fin n, g' i.succ) * (∏ i : Fin n, h i.succ) := by
      dsimp [d]
      rw [Finset.prod_mul_distrib, hGeq]
    have hsg : h 0 ^ n * (∏ i : Fin n, h i.succ) = g' 0 ^ n * (∏ i : Fin n, g' i.succ) := by
      have hh := hsign
      unfold dSgn at hh
      simpa [Finset.prod_mul_distrib, Finset.prod_const] using hh
    rw [← h0g'] at hsg
    have hHG : (∏ i : Fin n, h i.succ) = ∏ i : Fin n, g' i.succ :=
      mul_left_cancel₀ (pow_ne_zero n h0) hsg
    calc (∏ i : Fin n, d i) = (∏ i : Fin n, g' i.succ) * (∏ i : Fin n, h i.succ) := hprod
      _ = (∏ i : Fin n, h i.succ) * (∏ i : Fin n, h i.succ) := by rw [← hHG]
      _ = 1 := by
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_eq_one
              (fun i _ => CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_sq (hne i))

private lemma hdRo7DSmTransAux_d_notfull {n : ℕ} {h g' : DV n}
    (τ : Equiv.Perm (Fin n))
    (hmem : ∀ i : Fin n, g' (τ i).succ ≠ 0 ↔ h i.succ ≠ 0)
    (t : Fin n) (ht : h t.succ = 0) :
    ∃ d : Fin n → ZMod 3, (∀ i, d i = 1 ∨ d i = -1) ∧
      (∀ i, d i * h i.succ = g' (τ i).succ) ∧ (∏ i, d i = 1) := by
  let A : Fin n → ZMod 3 := fun i => if h i.succ ≠ 0 then g' (τ i).succ * h i.succ else 1
  let P : ZMod 3 := ∏ i, A i
  let d : Fin n → ZMod 3 := fun i => A i * (if i = t then P⁻¹ else 1)
  have hA_sign : ∀ i, A i = 1 ∨ A i = -1 := by
    intro i
    dsimp [A]
    by_cases hi : h i.succ ≠ 0
    · rw [if_pos hi]
      exact hdRo7DSmTransAux_mul_sign
        (CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero ((hmem i).mpr hi))
        (CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero hi)
    · rw [if_neg hi]; exact Or.inl rfl
  have hP_sign : P = 1 ∨ P = -1 := hdRo7DSmTransAux_prod_sign hA_sign
  have hP_ne : P ≠ 0 := by rcases hP_sign with h | h <;> simp [h]
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i
    dsimp [d]
    refine hdRo7DSmTransAux_mul_sign (hA_sign i) ?_
    by_cases hit : i = t
    · rw [if_pos hit]; exact hdRo7DSmTransAux_inv_sign hP_sign
    · rw [if_neg hit]; exact Or.inl rfl
  · intro i
    dsimp [d]
    by_cases hi : h i.succ ≠ 0
    · have hit : i ≠ t := by rintro rfl; exact hi ht
      rw [if_neg hit, mul_one]
      dsimp [A]
      rw [if_pos hi, mul_assoc, CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_sq hi, mul_one]
    · have hgi : g' (τ i).succ = 0 := by
        have : ¬ (g' (τ i).succ ≠ 0) := by rw [hmem i]; exact hi
        simpa using this
      have hzero : h i.succ = 0 := by simpa using hi
      simp [hgi, hzero]
  · have hprodA : (∏ i, A i) = P := rfl
    have hprodB : (∏ i, if i = t then P⁻¹ else 1) = P⁻¹ := by
      rw [Finset.prod_ite_eq']
      simp
    calc (∏ i, d i) = (∏ i, A i) * (∏ i, if i = t then P⁻¹ else 1) := by
          dsimp [d]
          rw [Finset.prod_mul_distrib]
      _ = P * P⁻¹ := by rw [hprodA, hprodB]
      _ = 1 := mul_inv_cancel₀ hP_ne


private lemma hdRo7DSmTransAux_ext {n : ℕ} {h g : DV n} (h0 : h 0 ≠ 0) (g0 : g 0 ≠ 0)
    (hsupp : dSupp h = dSupp g) (hsgn : dSupp h = n → dSgn h = dSgn g) :
    ∃ σ c, DSPData σ c ∧ (dAct σ c h = g ∨ dAct σ c h = -g) := by
  let s : ZMod 3 := h 0 * g 0
  let g' : DV n := s • g
  have hs_ne : s ≠ 0 := mul_ne_zero h0 g0
  have hg'0 : g' 0 = h 0 := by
    dsimp [g', s]
    rw [mul_assoc, CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_sq g0, mul_one]
  have hSupp_g' : dSupp g' = dSupp g := by
    dsimp [g', dSupp]
    congr 1
    apply Finset.filter_congr
    intro i _
    exact ⟨fun hh => (mul_ne_zero_iff.mp hh).2, fun hh => mul_ne_zero_iff.mpr ⟨hs_ne, hh⟩⟩
  have hSgn_g' : dSgn g' = dSgn g := by
    have hs' : s = 1 ∨ s = -1 :=
      CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero hs_ne
    rcases hs' with hs1 | hs1
    · dsimp [g']; rw [hs1, one_smul]
    · dsimp [g']; rw [hs1]
      unfold dSgn
      apply Finset.prod_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  let S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0)
  let Sg : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => g' i.succ ≠ 0)
  have hcard : S.card = Sg.card := by
    show dSupp h = dSupp g'
    rw [hsupp, hSupp_g']
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S Sg hcard
  have hmem : ∀ i : Fin n, g' (τ i).succ ≠ 0 ↔ h i.succ ≠ 0 := by
    intro i
    have hi : τ i ∈ Sg ↔ i ∈ S := by
      rw [← hτ]
      simp
    simpa [S, Sg] using hi
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, τ)
  have hs_cases : s = 1 ∨ s = -1 :=
    CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero hs_ne
  have hstep : ∀ d : Fin n → ZMod 3, (∀ i, d i = 1 ∨ d i = -1) →
      (∀ i, d i * h i.succ = g' (τ i).succ) → (∏ i : Fin n, d i = 1) →
      ∃ σ c, DSPData σ c ∧ (dAct σ c h = g ∨ dAct σ c h = -g) := by
    intro d hdsign hdact hpd
    refine ⟨σ, Fin.cons (α := fun _ => ZMod 3) 1 d,
      hdRo7DSmTransAux_dspDecompFin τ hdsign hpd, ?_⟩
    have hg'a : dAct σ (Fin.cons (α := fun _ => ZMod 3) 1 d) h = g' :=
      hdRo7DSmTransAux_dAct_eq hg'0.symm τ d hdact
    rcases hs_cases with hs1 | hs1
    · left
      have hg'g : g' = g := by dsimp [g']; rw [hs1, one_smul]
      rw [hg'a, hg'g]
    · right
      have hg'g : g' = -g := by dsimp [g']; rw [hs1, neg_one_smul]
      rw [hg'a, hg'g]
  by_cases hfull : S = Finset.univ
  · have hne : ∀ i : Fin n, h i.succ ≠ 0 := by
      intro i
      have hi : i ∈ S := by rw [hfull]; exact Finset.mem_univ i
      simpa [S] using hi
    have hmem' : ∀ i : Fin n, g' (τ i).succ ≠ 0 := fun i => (hmem i).mpr (hne i)
    have hdh : dSupp h = n := by
      have hc : S.card = n := by rw [hfull]; simp
      simpa [dSupp, S] using hc
    have hsign : dSgn h = dSgn g' := (hsgn hdh).trans hSgn_g'.symm
    obtain ⟨d, hdsign, hdact, hpd⟩ :=
      hdRo7DSmTransAux_d_full h0 hg'0.symm τ hne hmem' hsign
    exact hstep d hdsign hdact hpd
  · have hex : ∃ t : Fin n, h t.succ = 0 := by
      by_contra hc
      apply hfull
      rw [Finset.eq_univ_iff_forall]
      intro i
      by_contra hi
      exact hc ⟨i, by simpa [S] using hi⟩
    obtain ⟨t, ht⟩ := hex
    obtain ⟨d, hdsign, hdact, hpd⟩ := hdRo7DSmTransAux_d_notfull τ hmem t ht
    exact hstep d hdsign hdact hpd


private lemma hdRo7DSmTransAux_supp_single {n : ℕ} (h : DV n) (h0 : h 0 = 0)
    (hs : dSupp h = 1) : ∃ a : Fin n, h a.succ ≠ 0 ∧ ∀ k : Fin (n + 1), k ≠ a.succ → h k = 0 := by
  rw [dSupp] at hs
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hs
  refine ⟨a, ?_, ?_⟩
  · have hm : a ∈ Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0) := by rw [ha]; simp
    simpa using hm
  · intro k hk
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · exact h0
    · have hja : j ≠ a := by rintro rfl; exact hk rfl
      have hnot : j ∉ Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0) := by
        rw [ha]; simp [hja]
      have : ¬ (h j.succ ≠ 0) := by simpa using hnot
      simpa using this

private lemma hdRo7DSmTransAux_dAct_smul_dE {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (a : ZMod 3) (i : Fin (n + 1)) :
    dAct σ c (a • dE n i) = (c i * a) • dE n (σ i) := by
  funext j
  by_cases h : j = σ i
  · subst h
    simp [dAct, dE, Pi.single, Equiv.symm_apply_apply]
  · have hne : σ.symm j ≠ i := fun hh =>
        h (by rw [← Equiv.apply_symm_apply σ j, hh])
    simp [dAct, dE, Pi.single, h, hne]

private lemma hdRo7DSmTransAux_int {n : ℕ} {h g : DV n} (h0 : h 0 = 0) (g0 : g 0 = 0)
    (hh : dSupp h = 1) (hg : dSupp g = 1) :
    ∃ σ c, DSPData σ c ∧ (dAct σ c h = g ∨ dAct σ c h = -g) := by
  obtain ⟨a, ha, hsupp⟩ := hdRo7DSmTransAux_supp_single h h0 hh
  obtain ⟨b, hb, gsupp⟩ := hdRo7DSmTransAux_supp_single g g0 hg
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap a.succ b.succ
  let c : Fin (n + 1) → ZMod 3 := fun _ => 1
  refine ⟨σ, c, ?_, ?_⟩
  · refine ⟨?_, rfl, fun i => Or.inl rfl, ?_⟩
    · show (Equiv.swap a.succ b.succ) 0 = 0
      exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm
    · show ∏ i : Fin (n + 1), (1 : ZMod 3) = 1
      simp
  · have hσsymm : σ.symm = σ := by simp [σ, Equiv.symm_swap]
    have hσa : σ a.succ = b.succ := by simp [σ]
    have h_eq : h = h a.succ • dE n a.succ := by
      funext k
      by_cases hk : k = a.succ
      · subst hk; simp [dE]
      · simp [dE, hk, hsupp k hk]
    have g_eq : g = g b.succ • dE n b.succ := by
      funext k
      by_cases hk : k = b.succ
      · subst hk; simp [dE]
      · simp [dE, hk, gsupp k hk]
    have hA_sq : h a.succ * h a.succ = 1 := CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_sq ha
    have gB_sq : g b.succ * g b.succ = 1 := CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_sq hb
    have hact : dAct σ c h = h a.succ • dE n b.succ := by
      calc dAct σ c h = dAct σ c (h a.succ • dE n a.succ) := by rw [← h_eq]
        _ = (c a.succ * h a.succ) • dE n (σ a.succ) :=
            hdRo7DSmTransAux_dAct_smul_dE σ c (h a.succ) a.succ
        _ = h a.succ • dE n b.succ := by simp [c, hσa]
    have hsmul : (h a.succ * g b.succ) • g = h a.succ • dE n b.succ := by
      calc (h a.succ * g b.succ) • g
          = (h a.succ * g b.succ) • (g b.succ • dE n b.succ) :=
              congrArg (fun x => (h a.succ * g b.succ) • x) g_eq
        _ = ((h a.succ * g b.succ) * g b.succ) • dE n b.succ := by rw [smul_smul]
        _ = h a.succ • dE n b.succ := by rw [mul_assoc, gB_sq, mul_one]
    have heq : dAct σ c h = (h a.succ * g b.succ) • g := by rw [hact, hsmul]
    rcases CFSG.StandardType.HdRo7C.hdRo7CSmallAux_zmod3_ne_zero
      (mul_ne_zero ha hb) with hs | hs
    · left; rw [heq, hs, one_smul]
    · right; rw [heq, hs, neg_one_smul]

theorem dSmTrans_holds : DSmTransLeaf := by
  constructor
  · intro n h g h0 g0 hsupp hsgn
    exact hdRo7DSmTransAux_ext h0 g0 hsupp hsgn
  · intro n h g h0 g0 hh hg
    exact hdRo7DSmTransAux_int h0 g0 hh hg

end CFSG.StandardType.HdRo7D.Small
