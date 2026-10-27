module

public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Hyp

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ}

namespace MonoN0Hyp

private theorem monoSwap_isSign_ne_zero {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) :
    s i ≠ 0 := by
  rcases hs i with h | h <;> rw [h] <;> decide

private theorem monoSwap_commute_mat_iff {A B : GL (Fin (n + 1)) (ZMod 3)} :
    Commute A B ↔ Commute (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
      (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by
  constructor
  · intro h
    show (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
        (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
      (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
    rw [← Units.val_mul, ← Units.val_mul, h]
  · intro h
    exact Units.ext h

private theorem monoSwap_commute_coordRefl {a b : Fin (n + 1)}
    {A B : GL (Fin (n + 1)) (ZMod 3)}
    (hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl a)
    (hB : (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl b) : Commute A B := by
  rw [monoSwap_commute_mat_iff, hA, hB]
  exact coordRefl_commute a b

private theorem monoSwap_commute_of_monoN0 {T q : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hq : (q : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n) : Commute q T := by
  rw [monoSwap_commute_mat_iff, hT]
  exact commute_coordRefl_zero_of_mem_monoN0 hq

private theorem monoSwap_orbN_single {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) {p : Fin (n + 1)} (hp : p ≠ 0) (hp1 : OrbN Xg (Pi.single p 1))
    {c : Fin (n + 1)} (hc : c ≠ 0) : OrbN Xg (Pi.single c 1) := by
  have h0 : Equiv.swap p c 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hp) (Ne.symm hc)
  have hv := h.orbN_spMat hp1 (s := fun _ => 1) (fun _ => Or.inl rfl) h0
  have heq : spMat (Equiv.swap p c) (fun _ => (1 : ZMod 3)) *ᵥ (Pi.single p 1) =
      Pi.single c 1 := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply']
    funext i
    simp [spMat_apply, Equiv.swap_apply_left, Pi.single_apply]
  rwa [heq] at hv

private theorem monoSwap_exists_conj_coordRefl {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {p : Fin (n + 1)} (hp : p ≠ 0) (hp1 : OrbN Xg (Pi.single p 1))
    {c : Fin (n + 1)} (hc : c ≠ 0) :
    ∃ C ∈ Xg, ((C * T * C⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c ∧
      (C : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single c 1 := by
  have hv := monoSwap_orbN_single h hp hp1 hc
  obtain ⟨C, hCX, haxis, hconj⟩ :=
    h.exists_conj_coordRefl hT hc (c := 1) one_ne_zero (by simpa using hv)
  exact ⟨C, hCX, hconj, by simpa using haxis⟩

private theorem monoSwap_orbN_wt_two {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) {δ : ZMod 3} (hδ : δ ≠ 0)
    {q : GL (Fin (n + 1)) (ZMod 3)}
    (hqR : ∃ A ∈ Xg, q = A * T * A⁻¹)
    (hqmat : (q : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b δ)
    {w : Fin (n + 1) → ZMod 3} (hw0 : w 0 = 0) (hw2 : wt w = 2) : OrbN Xg w := by
  obtain ⟨A, hAX, hq⟩ := hqR
  have hmono : (q : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    rw [hqmat]
    exact swapRefl_mem_monoN0 ha hb hδ
  have hcomm : Commute q T := monoSwap_commute_of_monoN0 hT hmono
  have hne : q ≠ T := by
    intro hEq
    have hmat : (q : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [hEq]
    rw [hqmat, hT] at hmat
    exact (coordRefl_ne_swapRefl hab (0 : Fin (n + 1)) δ) hmat.symm
  have h0 : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    refine h.zero_of_commute hT hAX ?_ ?_
    · rw [← hq]; exact hcomm
    · rw [← hq]; exact hne
  rcases h.conj_cases hT hAX h0 with
    ⟨c, hc0, hconj, hc⟩ | ⟨a₁, b₁, ha₁, hb₁, hab₁, δ₁, hδ₁, hconj, c, hc, haxis⟩
  · rw [← hq] at hconj
    exact absurd (hconj.symm.trans hqmat) (coordRefl_ne_swapRefl hab c δ)
  · have hwt : wt ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) = 2 := by
      rw [haxis, wt_smul_single_sub_smul hab₁ hc hδ₁]
    refine h.orbN_of_wt_eq_zero ⟨A, hAX, rfl⟩ h0 hw0 ?_
    rw [hwt, hw2]

private theorem monoSwap_exists_twin {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) {δ : ZMod 3} (hδ : δ ≠ 0)
    {q : GL (Fin (n + 1)) (ZMod 3)} (hqR : ∃ A ∈ Xg, q = A * T * A⁻¹)
    (hqmat : (q : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b δ) :
    ∃ A ∈ Xg, ((A * T * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b (-δ) := by
  have hneg : -δ ≠ 0 := neg_ne_zero.mpr hδ
  have hw0 : (Pi.single a 1 - (-δ) • Pi.single b 1 : Fin (n + 1) → ZMod 3) 0 = 0 := by
    simp [Pi.single_eq_of_ne (Ne.symm ha), Pi.single_eq_of_ne (Ne.symm hb)]
  have hw2 : wt (Pi.single a 1 - (-δ) • Pi.single b 1 : Fin (n + 1) → ZMod 3) = 2 := by
    simpa using wt_smul_single_sub_smul hab (c := 1) one_ne_zero hneg
  have hv := monoSwap_orbN_wt_two h hT ha hb hab hδ hqR hqmat hw0 hw2
  obtain ⟨A, hAX, haxis, hconj⟩ :=
    h.exists_conj_swapRefl hT ha hb hab (c := 1) one_ne_zero hneg (by simpa using hv)
  exact ⟨A, hAX, hconj⟩

private theorem monoSwap_commute_swap_neg {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) {T : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) {δ : ZMod 3} (hδ : δ ≠ 0)
    {q : GL (Fin (n + 1)) (ZMod 3)}
    (hqmat : (q : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b δ)
    {r : GL (Fin (n + 1)) (ZMod 3)} (hrR : ∃ B ∈ Xg, r = B * T * B⁻¹)
    (hrT : Commute r T) (hrq : Commute r q)
    {q' : GL (Fin (n + 1)) (ZMod 3)}
    (hq'mat : (q' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b (-δ)) :
    Commute r q' := by
  obtain ⟨B, hBX, hrB⟩ := hrR
  have hneg : -δ ≠ 0 := neg_ne_zero.mpr hδ
  by_cases hrTeq : r = T
  · rw [hrTeq]
    have hmono : (q' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
      rw [hq'mat]
      exact swapRefl_mem_monoN0 ha hb hneg
    exact (monoSwap_commute_of_monoN0 hT hmono).symm
  · have h0 : ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
      refine h.zero_of_commute hT hBX ?_ ?_
      · rw [← hrB]; exact hrT
      · rw [← hrB]; exact hrTeq
    rcases h.conj_cases hT hBX h0 with
      ⟨c, hc0, hconj, hc⟩ | ⟨a₁, b₁, ha₁, hb₁, hab₁, δ₁, hδ₁, hconj, c, hc, hcaxis⟩
    · have hrmat : (r : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl c := by
        rw [hrB]; exact hconj
      have h1 : Commute r q ↔ c ≠ a ∧ c ≠ b := by
        rw [monoSwap_commute_mat_iff, hrmat, hqmat, coordRefl_commute_swapRefl_iff hab hδ]
      have h2 : Commute r q' ↔ c ≠ a ∧ c ≠ b := by
        rw [monoSwap_commute_mat_iff, hrmat, hq'mat,
          coordRefl_commute_swapRefl_iff hab hneg]
      exact h2.mpr (h1.mp hrq)
    · have hrmat : (r : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
          swapRefl a₁ b₁ δ₁ := by
        rw [hrB]; exact hconj
      have h1 : Commute r q ↔ (a₁ = a ∧ b₁ = b) ∨ (a₁ = b ∧ b₁ = a) ∨
          (a₁ ≠ a ∧ a₁ ≠ b ∧ b₁ ≠ a ∧ b₁ ≠ b) := by
        rw [monoSwap_commute_mat_iff, hrmat, hqmat, swapRefl_commute_iff hab₁ hab hδ₁ hδ]
      have h2 : Commute r q' ↔ (a₁ = a ∧ b₁ = b) ∨ (a₁ = b ∧ b₁ = a) ∨
          (a₁ ≠ a ∧ a₁ ≠ b ∧ b₁ ≠ a ∧ b₁ ≠ b) := by
        rw [monoSwap_commute_mat_iff, hrmat, hq'mat,
          swapRefl_commute_iff hab₁ hab hδ₁ hneg]
      exact h2.mpr (h1.mp hrq)

private theorem monoSwap_spMat_conj_coordRefl {σ : Equiv.Perm (Fin (n + 1))}
    (hσ : σ * σ = 1) (b : Fin (n + 1)) :
    spMat σ 1 * coordRefl b * spMat σ 1 = coordRefl (σ b) := by
  have hσb : ∀ x, σ (σ x) = x := by
    intro x
    have h := congrFun (congrArg (fun f : Equiv.Perm (Fin (n + 1)) =>
      (f : Fin (n + 1) → Fin (n + 1))) hσ) x
    simpa [Equiv.Perm.mul_apply] using h
  have hP : ∀ j : Fin (n + 1),
      (spMat σ 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single j 1 =
        Pi.single (σ j) 1 := by
    intro j
    rw [Matrix.mulVec_single_one, Matrix.col_apply']
    funext k
    simp [spMat_apply, Pi.single_apply]
  have hcol : ∀ a : Fin (n + 1),
      (coordRefl a : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (Pi.single a (1 : ZMod 3) : Fin (n + 1) → ZMod 3) =
        -(Pi.single a (1 : ZMod 3) : Fin (n + 1) → ZMod 3) := by
    intro a
    rw [coordRefl_mulVec]
    funext k
    by_cases hk : k = a
    · subst hk
      rw [if_pos rfl, Pi.single_eq_same, Pi.neg_apply, Pi.single_eq_same]
      decide
    · rw [if_neg hk, Pi.single_eq_of_ne hk, Pi.neg_apply, Pi.single_eq_of_ne hk]
      exact neg_zero.symm
  have hmul : ∀ (a c : Fin (n + 1)), c ≠ a →
      (coordRefl a : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          (Pi.single c (1 : ZMod 3) : Fin (n + 1) → ZMod 3) =
        (Pi.single c (1 : ZMod 3) : Fin (n + 1) → ZMod 3) := by
    intro a c hc
    rw [coordRefl_mulVec]
    funext k
    by_cases hk : k = a
    · subst hk
      rw [if_pos rfl, Pi.single_eq_of_ne (Ne.symm hc)]
      decide
    · rw [if_neg hk]
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP i]
  by_cases hi : σ i = b
  · have hib : i = σ b := by rw [← hσb i, hi]
    rw [hi, hcol b, Matrix.mulVec_neg, hP b, hib, hcol (σ b)]
  · have hib : i ≠ σ b := by
      intro hh
      apply hi
      rw [hh, hσb b]
    rw [hmul b (σ i) hi, hP (σ i), hσb i, hmul (σ b) i hib]

private theorem monoSwap_wt_col {G' : GL (Fin (n + 1)) (ZMod 3)} {m : Fin (n + 1)}
    {Tm : GL (Fin (n + 1)) (ZMod 3)}
    (hTmmat : (Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl m)
    {l : Fin (n + 1)}
    (hQmat : ((G' * Tm * G'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl l) :
    wt ((G' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) = 1 := by
  have haxis := conj_coordRefl_mulVec_axis (a := m) hTmmat G'
  rw [hQmat] at haxis
  have hzero : ∀ i, i ≠ l →
      ((G' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) i = 0 := by
    intro i hi
    have h2 := congrFun haxis i
    rw [coordRefl_mulVec] at h2
    simp only [hi, if_false, Pi.neg_apply] at h2
    exact zmod3_eq_zero_of_eq_neg h2
  have hvne : ((G' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) ≠ 0 := by
    refine gl_mulVec_ne_zero G' ?_
    intro he
    simpa using congrFun he m
  have hvl : ((G' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) l ≠ 0 := by
    intro h0
    apply hvne
    funext i
    by_cases hi : i = l
    · subst i
      exact h0
    · exact hzero i hi
  have hv_eq : ((G' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) =
      (((G' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) l) •
        Pi.single l 1 := by
    funext i
    by_cases hi : i = l
    · subst i
      simp
    · rw [hzero i hi]
      simp [hi]
  rw [hv_eq, wt_smul_single hvl l]

private theorem monoSwap_false_of_u_swap {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) (hn : 4 ≤ n) {p : Fin (n + 1)} (hp : p ≠ 0)
    (hp1 : OrbN Xg (Pi.single p 1)) {T Tp u g : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hTp : (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl p)
    (hgX : g ∈ Xg) (hTpEq : Tp = g * T * g⁻¹) (huEq : g * u * g⁻¹ = T)
    (huR : ∃ A ∈ Xg, u = A * T * A⁻¹) {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) {δ : ZMod 3} (hδ : δ ≠ 0)
    (humat : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b δ) : False := by
  have hmono : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n := by
    rw [humat]
    exact swapRefl_mem_monoN0 ha hb hδ
  have huT : Commute u T := monoSwap_commute_of_monoN0 hT hmono
  have huNe : u ≠ T := by
    intro hEq
    have hm : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [hEq]
    rw [humat, hT] at hm
    exact (coordRefl_ne_swapRefl hab (0 : Fin (n + 1)) δ) hm.symm
  obtain ⟨A', hA'X, hA'mat⟩ := monoSwap_exists_twin h hT ha hb hab hδ huR humat
  let u' : GL (Fin (n + 1)) (ZMod 3) := A' * T * A'⁻¹
  have hu'mat : (u' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b (-δ) :=
    hA'mat
  let p' : GL (Fin (n + 1)) (ZMod 3) := g * u' * g⁻¹
  have hp'T : Commute p' T := by
    have h2 := (monoSwap_commute_swap_neg h hT ha hb hab hδ humat huR huT
      (Commute.refl u) hu'mat).conj g
    rw [huEq] at h2
    change Commute (g * u' * g⁻¹) T
    exact h2.symm
  have hTR : ∃ C ∈ Xg, T = C * T * C⁻¹ := ⟨1, Xg.one_mem, by group⟩
  have hp'Tp : Commute p' Tp := by
    have h2 := (monoSwap_commute_swap_neg h hT ha hb hab hδ humat hTR
      (Commute.refl T) huT.symm hu'mat).conj g
    rw [← hTpEq] at h2
    change Commute (g * u' * g⁻¹) Tp
    exact h2.symm
  have hp'neT : p' ≠ T := by
    intro hEq
    have hu'eq : u' = u := by
      have h2 : g⁻¹ * p' * g = g⁻¹ * T * g := by rw [hEq]
      have h3 : g⁻¹ * p' * g = u' := by
        change g⁻¹ * (g * u' * g⁻¹) * g = u'
        group
      have h4 : g⁻¹ * T * g = u := by rw [← huEq]; group
      rw [h3, h4] at h2
      exact h2
    have hm : swapRefl a b (-δ) = swapRefl a b δ := by
      rw [← hu'mat, hu'eq, humat]
    exact swapRefl_ne_neg hab hδ hm.symm
  have hp'neTp : p' ≠ Tp := by
    intro hEq
    have hu'eq : u' = T := by
      have h2 : g⁻¹ * p' * g = g⁻¹ * Tp * g := by rw [hEq]
      have h3 : g⁻¹ * p' * g = u' := by
        change g⁻¹ * (g * u' * g⁻¹) * g = u'
        group
      have h4 : g⁻¹ * Tp * g = T := by rw [hTpEq]; group
      rw [h3, h4] at h2
      exact h2
    have hm : swapRefl a b (-δ) = coordRefl 0 := by
      rw [← hu'mat, hu'eq, hT]
    exact (coordRefl_ne_swapRefl hab (0 : Fin (n + 1)) (-δ)) hm.symm
  have claim : ∀ r : GL (Fin (n + 1)) (ZMod 3), (∃ B ∈ Xg, r = B * T * B⁻¹) →
      Commute r T → Commute r Tp → Commute r p' := by
    intro r hrR hrT hrTp
    obtain ⟨B, hBX, hrB⟩ := hrR
    have hr'R : ∃ B' ∈ Xg, g⁻¹ * r * g = B' * T * B'⁻¹ := by
      refine ⟨g⁻¹ * B, Xg.mul_mem (Xg.inv_mem hgX) hBX, ?_⟩
      rw [hrB]; group
    have hr'T : Commute (g⁻¹ * r * g) T := by
      have h2 := hrTp.conj g⁻¹
      have h3 : g⁻¹ * Tp * (g⁻¹)⁻¹ = T := by rw [inv_inv, hTpEq]; group
      rw [h3] at h2
      simpa [inv_inv] using h2
    have hr'u : Commute (g⁻¹ * r * g) u := by
      have h2 := hrT.conj g⁻¹
      have h3 : g⁻¹ * T * (g⁻¹)⁻¹ = u := by rw [inv_inv, ← huEq]; group
      rw [h3] at h2
      simpa [inv_inv] using h2
    have h2 := (monoSwap_commute_swap_neg h hT ha hb hab hδ humat hr'R hr'T hr'u hu'mat).conj g
    have h3 : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
    rw [h3] at h2
    change Commute r p'
    exact h2
  have hAtX : g * A' ∈ Xg := Xg.mul_mem hgX hA'X
  have hp'form : (g * A') * T * (g * A')⁻¹ = p' := by
    change (g * A') * T * (g * A')⁻¹ = g * (A' * T * A'⁻¹) * g⁻¹
    group
  have h0 : ((((g * A') : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    refine h.zero_of_commute hT hAtX ?_ ?_
    · rw [hp'form]; exact hp'T
    · rw [hp'form]; exact hp'neT
  have hcases := h.conj_cases hT hAtX h0
  rw [hp'form] at hcases
  rcases hcases with ⟨c, hc0, hcmat, -, -, -⟩ |
      ⟨a₁, b₁, ha₁, _, hab₁, ε, hε, hmat, -, -, -⟩
  · have hcp : c ≠ p := by
      intro hcp
      apply hp'neTp
      exact Units.ext (by rw [hcmat, hcp, hTp])
    have h4 : ({0, p, c} : Finset (Fin (n + 1))).card ≤ 3 := by
      have h1 := Finset.card_insert_le (0 : Fin (n + 1)) ({p, c} : Finset (Fin (n + 1)))
      have h2 := Finset.card_insert_le p ({c} : Finset (Fin (n + 1)))
      have h3 : ({c} : Finset (Fin (n + 1))).card = 1 := Finset.card_singleton c
      omega
    have hlt : ({0, p, c} : Finset (Fin (n + 1))).card <
        (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, -, hjnot⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (s := {0, p, c}) (t := Finset.univ) hlt
    have hj0 : j ≠ 0 := fun hh => hjnot (by simp [hh])
    have hjp : j ≠ p := fun hh => hjnot (by simp [hh])
    have hjc : j ≠ c := fun hh => hjnot (by simp [hh])
    have hcj : c ≠ j := Ne.symm hjc
    have hw0 : (Pi.single c 1 - (1 : ZMod 3) • Pi.single j 1 : Fin (n + 1) → ZMod 3) 0 = 0 := by
      simp [Pi.single_eq_of_ne (Ne.symm hc0), Pi.single_eq_of_ne (Ne.symm hj0)]
    have hw2 : wt (Pi.single c 1 - (1 : ZMod 3) • Pi.single j 1 : Fin (n + 1) → ZMod 3) = 2 := by
      simpa using wt_smul_single_sub_smul hcj (c := 1) one_ne_zero one_ne_zero
    have hv := monoSwap_orbN_wt_two h hT ha hb hab hδ huR humat hw0 hw2
    obtain ⟨Ar, hArX, -, harmat⟩ :=
      h.exists_conj_swapRefl hT hc0 hj0 hcj (c := 1) one_ne_zero one_ne_zero (by simpa using hv)
    let r : GL (Fin (n + 1)) (ZMod 3) := Ar * T * Ar⁻¹
    have hrmat : (r : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl c j 1 := harmat
    have hrR : ∃ B ∈ Xg, r = B * T * B⁻¹ := ⟨Ar, hArX, rfl⟩
    have hrT : Commute r T := by
      rw [monoSwap_commute_mat_iff, hrmat, hT, Commute.symm_iff,
        coordRefl_commute_swapRefl_iff hcj one_ne_zero]
      exact ⟨Ne.symm hc0, Ne.symm hj0⟩
    have hrTp : Commute r Tp := by
      rw [monoSwap_commute_mat_iff, hrmat, hTp, Commute.symm_iff,
        coordRefl_commute_swapRefl_iff hcj one_ne_zero]
      exact ⟨Ne.symm hcp, Ne.symm hjp⟩
    have hcomm := claim r hrR hrT hrTp
    have hbad : Commute (swapRefl c j 1) (coordRefl c) := by
      have h2 := monoSwap_commute_mat_iff.mp hcomm
      rwa [hrmat, hcmat] at h2
    rw [Commute.symm_iff, coordRefl_commute_swapRefl_iff hcj one_ne_zero] at hbad
    exact hbad.1 rfl
  · obtain ⟨Cr, hCrX, hCrmat, -⟩ := monoSwap_exists_conj_coordRefl h hT hp hp1 ha₁
    let r : GL (Fin (n + 1)) (ZMod 3) := Cr * T * Cr⁻¹
    have hrmat : (r : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl a₁ := hCrmat
    have hrR : ∃ B ∈ Xg, r = B * T * B⁻¹ := ⟨Cr, hCrX, rfl⟩
    have hrT : Commute r T := monoSwap_commute_coordRefl hrmat hT
    have hrTp : Commute r Tp := monoSwap_commute_coordRefl hrmat hTp
    have hcomm := claim r hrR hrT hrTp
    have hbad : Commute (coordRefl a₁) (swapRefl a₁ b₁ ε) := by
      have h2 := monoSwap_commute_mat_iff.mp hcomm
      rwa [hrmat, hmat] at h2
    rw [coordRefl_commute_swapRefl_iff hab₁ hε] at hbad
    exact hbad.1 rfl

private theorem monoSwap_exists_interchange {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) (hn : 4 ≤ n) {p : Fin (n + 1)} (hp : p ≠ 0)
    (hp1 : OrbN Xg (Pi.single p 1)) {T Tp : GL (Fin (n + 1)) (ZMod 3)} (hTX : T ∈ Xg)
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hTpX : Tp ∈ Xg) (hTp : (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl p)
    {g : GL (Fin (n + 1)) (ZMod 3)} (hgX : g ∈ Xg)
    (hge0 : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single p 1)
    (hgT : g * T * g⁻¹ = Tp) :
    ∃ g' ∈ Xg, g' * T * g'⁻¹ = Tp ∧ g' * Tp * g'⁻¹ = T ∧
      (g' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single p 1 := by
  have huR : ∃ A ∈ Xg, (g⁻¹ * T * (g⁻¹)⁻¹) = A * T * A⁻¹ := ⟨g⁻¹, Xg.inv_mem hgX, rfl⟩
  have huEq : g * (g⁻¹ * T * (g⁻¹)⁻¹) * g⁻¹ = T := by group
  have huT : Commute (g⁻¹ * T * (g⁻¹)⁻¹) T := by
    have h2 := (monoSwap_commute_coordRefl hTp hT).conj g⁻¹
    have h3 : g⁻¹ * Tp * (g⁻¹)⁻¹ = T := by rw [inv_inv, ← hgT]; group
    rw [h3] at h2
    simpa [inv_inv] using h2.symm
  have huNe : (g⁻¹ * T * (g⁻¹)⁻¹) ≠ T := by
    intro hEq
    have h1 : T = Tp := by
      have h2 : g * (g⁻¹ * T * (g⁻¹)⁻¹) * g⁻¹ = g * T * g⁻¹ := by rw [hEq]
      rw [huEq, hgT] at h2
      exact h2
    have hm : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [h1]
    rw [hT, hTp] at hm
    exact hp (coordRefl_injective hm).symm
  have hu0 : (((g⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    refine h.zero_of_commute hT (Xg.inv_mem hgX) ?_ ?_
    · exact huT
    · exact huNe
  rcases h.conj_cases hT (Xg.inv_mem hgX) hu0 with
    ⟨a, ha0, humat, -, -, -⟩ | ⟨a, b, ha, hb, hab, δ, hδ, humat, -, -, -⟩
  · have hσ0 : Equiv.swap a p 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ha0) (Ne.symm hp)
    obtain ⟨m, hmX, hmmat⟩ := h.sub (spMat (Equiv.swap a p) 1)
      ⟨_, fun _ => 1, fun _ => Or.inl rfl, hσ0, rfl⟩
    have hmm : m * m = 1 := by
      refine Units.ext ?_
      rw [Units.val_mul, hmmat]
      exact spMat_mul_self (Equiv.swap a p) 1 (Equiv.swap_mul_self a p) (fun j => by simp)
    have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmm
    have hmMem : (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoN0 n :=
      ⟨_, fun _ => 1, fun _ => Or.inl rfl, hσ0, hmmat⟩
    have hmT : Commute m T := monoSwap_commute_of_monoN0 hT hmMem
    have hmT' : m * T * m⁻¹ = T := by
      calc m * T * m⁻¹ = T * m * m⁻¹ := by rw [hmT]
        _ = T := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hmTp : m * Tp * m⁻¹ = g⁻¹ * T * (g⁻¹)⁻¹ := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hminv, hmmat, hTp, humat]
      rw [monoSwap_spMat_conj_coordRefl (Equiv.swap_mul_self a p) p,
        Equiv.swap_apply_right]
    refine ⟨g * m, Xg.mul_mem hgX hmX, ?_, ?_, ?_⟩
    · change g * m * T * (g * m)⁻¹ = Tp
      rw [show g * m * T * (g * m)⁻¹ = g * (m * T * m⁻¹) * g⁻¹ by group, hmT', hgT]
    · change g * m * Tp * (g * m)⁻¹ = T
      rw [show g * m * Tp * (g * m)⁻¹ = g * (m * Tp * m⁻¹) * g⁻¹ by group, hmTp, huEq]
    · have hm0 : (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
          Pi.single 0 1 := by
        rw [hmmat, Matrix.mulVec_single_one, Matrix.col_apply']
        funext i
        simp [spMat_apply, hσ0, Pi.single_apply]
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hm0, hge0]
  · exact (monoSwap_false_of_u_swap h hn hp hp1 hT hTp hgX hgT.symm huEq huR ha hb hab hδ
      humat).elim

private theorem monoSwap_image_coordRefl {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) (hn : 4 ≤ n) {p : Fin (n + 1)} (hp : p ≠ 0)
    (hp1 : OrbN Xg (Pi.single p 1)) {T Tp g' : GL (Fin (n + 1)) (ZMod 3)}
    (hT : (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl 0)
    (hTp : (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl p)
    (hg'X : g' ∈ Xg) (hg'T : g' * T * g'⁻¹ = Tp) (hg'Tp : g' * Tp * g'⁻¹ = T)
    {k : Fin (n + 1)} (hk0 : k ≠ 0) (hkp : k ≠ p) {Tk : GL (Fin (n + 1)) (ZMod 3)}
    (hTk : (Tk : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl k)
    (hTkR : ∃ C ∈ Xg, Tk = C * T * C⁻¹) :
    ∃ l, ((g' * Tk * g'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl l := by
  by_contra hnot
  obtain ⟨C0, hC0X, hC0⟩ := hTkR
  have hqR : ∃ B ∈ Xg, g' * Tk * g'⁻¹ = B * T * B⁻¹ := by
    refine ⟨g' * C0, Xg.mul_mem hg'X hC0X, ?_⟩
    rw [hC0]; group
  have hqTp : Commute (g' * Tk * g'⁻¹) Tp := by
    have h2 := (monoSwap_commute_coordRefl hT hTk).conj g'
    rw [hg'T] at h2
    exact h2.symm
  have hqT : Commute (g' * Tk * g'⁻¹) T := by
    have h2 := (monoSwap_commute_coordRefl hTp hTk).conj g'
    rw [hg'Tp] at h2
    exact h2.symm
  have hqneT : g' * Tk * g'⁻¹ ≠ T := by
    intro hEq
    have h1 : Tk = Tp := by
      have h2 : g'⁻¹ * (g' * Tk * g'⁻¹) * g' = g'⁻¹ * T * g' := by rw [hEq]
      have h3 : g'⁻¹ * (g' * Tk * g'⁻¹) * g' = Tk := by group
      have h4 : g'⁻¹ * T * g' = Tp := by rw [← hg'Tp]; group
      rw [h3, h4] at h2
      exact h2
    have hm : (Tk : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [h1]
    rw [hTk, hTp] at hm
    exact hkp (coordRefl_injective hm)
  have hqneTp : g' * Tk * g'⁻¹ ≠ Tp := by
    intro hEq
    have h1 : Tk = T := by
      have h2 : g'⁻¹ * (g' * Tk * g'⁻¹) * g' = g'⁻¹ * Tp * g' := by rw [hEq]
      have h3 : g'⁻¹ * (g' * Tk * g'⁻¹) * g' = Tk := by group
      have h4 : g'⁻¹ * Tp * g' = T := by rw [← hg'T]; group
      rw [h3, h4] at h2
      exact h2
    have hm : (Tk : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
        (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [h1]
    rw [hTk, hT] at hm
    exact hk0 (coordRefl_injective hm)
  have hqR' : ∃ B ∈ Xg, g' * Tk * g'⁻¹ = B * T * B⁻¹ := hqR
  obtain ⟨B, hBX, hBq⟩ := hqR
  have hq0 : ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
    refine h.zero_of_commute hT hBX ?_ ?_
    · rw [← hBq]; exact hqT
    · rw [← hBq]; exact hqneT
  have hcases := h.conj_cases hT hBX hq0
  rw [← hBq] at hcases
  rcases hcases with ⟨l, hl0, hlmat, -, -, -⟩ | ⟨a, b, ha, hb, hab, δ, hδ, hmat, -, -, -⟩
  · exact hnot ⟨l, hlmat⟩
  · obtain ⟨A', hA'X, hA'mat⟩ := monoSwap_exists_twin h hT ha hb hab hδ hqR' hmat
    let q' : GL (Fin (n + 1)) (ZMod 3) := A' * T * A'⁻¹
    have hq'mat : (q' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl a b (-δ) :=
      hA'mat
    let t' : GL (Fin (n + 1)) (ZMod 3) := g'⁻¹ * q' * g'
    have hTR : ∃ C ∈ Xg, T = C * T * C⁻¹ := ⟨1, Xg.one_mem, by group⟩
    have hq'T : Commute q' T :=
      (monoSwap_commute_swap_neg h hT ha hb hab hδ hmat hTR (Commute.refl T) hqT.symm
        hq'mat).symm
    have hq'q : Commute q' (g' * Tk * g'⁻¹) :=
      (monoSwap_commute_swap_neg h hT ha hb hab hδ hmat hqR' hqT (Commute.refl _)
        hq'mat).symm
    have hq'Tp : Commute q' Tp := by
      have hTpR : ∃ C ∈ Xg, Tp = C * T * C⁻¹ := ⟨g', hg'X, hg'T.symm⟩
      exact (monoSwap_commute_swap_neg h hT ha hb hab hδ hmat hTpR
        (monoSwap_commute_coordRefl hTp hT) hqTp.symm hq'mat).symm
    have ht'T : Commute t' T := by
      have h2 := hq'Tp.conj g'⁻¹
      have h3 : g'⁻¹ * Tp * (g'⁻¹)⁻¹ = T := by rw [inv_inv, ← hg'T]; group
      rw [h3] at h2
      simpa [t', inv_inv] using h2
    have ht'Tp : Commute t' Tp := by
      have h2 := hq'T.conj g'⁻¹
      have h3 : g'⁻¹ * T * (g'⁻¹)⁻¹ = Tp := by rw [inv_inv, ← hg'Tp]; group
      rw [h3] at h2
      simpa [t', inv_inv] using h2
    have ht'Tk : Commute t' Tk := by
      have h2 := hq'q.conj g'⁻¹
      have h3 : g'⁻¹ * (g' * Tk * g'⁻¹) * (g'⁻¹)⁻¹ = Tk := by rw [inv_inv]; group
      rw [h3] at h2
      simpa [t', inv_inv] using h2
    have ht'neT : t' ≠ T := by
      intro hEq
      have hq'eq : q' = Tp := by
        have h2 : g' * t' * g'⁻¹ = g' * T * g'⁻¹ := by rw [hEq]
        have h3 : g' * t' * g'⁻¹ = q' := by
          change g' * (g'⁻¹ * q' * g') * g'⁻¹ = q'
          group
        rw [h3, hg'T] at h2
        exact h2
      have hm : (q' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
          (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [hq'eq]
      rw [hq'mat, hTp] at hm
      exact (coordRefl_ne_swapRefl hab p (-δ)) hm.symm
    have ht'neTp : t' ≠ Tp := by
      intro hEq
      have hq'eq : q' = T := by
        have h2 : g' * t' * g'⁻¹ = g' * Tp * g'⁻¹ := by rw [hEq]
        have h3 : g' * t' * g'⁻¹ = q' := by
          change g' * (g'⁻¹ * q' * g') * g'⁻¹ = q'
          group
        rw [h3, hg'Tp] at h2
        exact h2
      have hm : (q' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
          (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [hq'eq]
      rw [hq'mat, hT] at hm
      exact (coordRefl_ne_swapRefl hab (0 : Fin (n + 1)) (-δ)) hm.symm
    have ht'neTk : t' ≠ Tk := by
      intro hEq
      have hq'eq : q' = g' * Tk * g'⁻¹ := by
        have h2 : g' * t' * g'⁻¹ = g' * Tk * g'⁻¹ := by rw [hEq]
        have h3 : g' * t' * g'⁻¹ = q' := by
          change g' * (g'⁻¹ * q' * g') * g'⁻¹ = q'
          group
        rw [h3] at h2
        exact h2
      have hm : (q' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) =
          ((g' * Tk * g'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) := by rw [hq'eq]
      rw [hq'mat, hmat] at hm
      exact swapRefl_ne_neg hab hδ hm.symm
    have ht'form : (g'⁻¹ * A') * T * (g'⁻¹ * A')⁻¹ = t' := by
      change (g'⁻¹ * A') * T * (g'⁻¹ * A')⁻¹ = g'⁻¹ * (A' * T * A'⁻¹) * g'
      group
    have hAt'X : g'⁻¹ * A' ∈ Xg := Xg.mul_mem (Xg.inv_mem hg'X) hA'X
    have ht'0 : ((((g'⁻¹ * A') : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 := by
      refine h.zero_of_commute hT hAt'X ?_ ?_
      · rw [ht'form]; exact ht'T
      · rw [ht'form]; exact ht'neT
    have claim : ∀ r : GL (Fin (n + 1)) (ZMod 3), (∃ Br ∈ Xg, r = Br * T * Br⁻¹) →
        Commute r T → Commute r Tp → Commute r Tk → Commute r t' := by
      intro r hrR hrT hrTp hrTk
      obtain ⟨Br, hBrX, hrBr⟩ := hrR
      have hr'R : ∃ B' ∈ Xg, g' * r * g'⁻¹ = B' * T * B'⁻¹ := by
        refine ⟨g' * Br, Xg.mul_mem hg'X hBrX, ?_⟩
        rw [hrBr]; group
      have hr'T : Commute (g' * r * g'⁻¹) T := by
        have h2 := hrTp.conj g'
        rw [hg'Tp] at h2
        exact h2
      have hr'q : Commute (g' * r * g'⁻¹) (g' * Tk * g'⁻¹) := by
        have h2 := hrTk.conj g'
        exact h2
      have h2 := (monoSwap_commute_swap_neg h hT ha hb hab hδ hmat hr'R hr'T hr'q
        hq'mat).conj g'⁻¹
      have h3 : g'⁻¹ * (g' * r * g'⁻¹) * (g'⁻¹)⁻¹ = r := by group
      rw [h3] at h2
      simpa [t', inv_inv] using h2
    have ht'cases := h.conj_cases hT hAt'X ht'0
    rw [ht'form] at ht'cases
    rcases ht'cases with ⟨l, hl0, hlmat, -, -, -⟩ |
        ⟨a₂, b₂, ha₂, _, hab₂, ε, hε, hmat₂, -, -, -⟩
    · have hl0' : l ≠ 0 := by
        intro hh
        apply ht'neT
        exact Units.ext (by rw [hlmat, hh, hT])
      have hlp' : l ≠ p := by
        intro hh
        apply ht'neTp
        exact Units.ext (by rw [hlmat, hh, hTp])
      have hlk' : l ≠ k := by
        intro hh
        apply ht'neTk
        exact Units.ext (by rw [hlmat, hh, hTk])
      have h4 : ({0, p, k, l} : Finset (Fin (n + 1))).card ≤ 4 := by
        have h1 := Finset.card_insert_le (0 : Fin (n + 1)) ({p, k, l} : Finset (Fin (n + 1)))
        have h2 := Finset.card_insert_le p ({k, l} : Finset (Fin (n + 1)))
        have h3 := Finset.card_insert_le k ({l} : Finset (Fin (n + 1)))
        have h5 : ({l} : Finset (Fin (n + 1))).card = 1 := Finset.card_singleton l
        omega
      have hlt : ({0, p, k, l} : Finset (Fin (n + 1))).card <
          (Finset.univ : Finset (Fin (n + 1))).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨j, -, hjnot⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card (s := {0, p, k, l}) (t := Finset.univ) hlt
      have hj0 : j ≠ 0 := fun hh => hjnot (by simp [hh])
      have hjp : j ≠ p := fun hh => hjnot (by simp [hh])
      have hjk : j ≠ k := fun hh => hjnot (by simp [hh])
      have hjl : j ≠ l := fun hh => hjnot (by simp [hh])
      have hlj : l ≠ j := Ne.symm hjl
      have hw0 : (Pi.single l 1 - (1 : ZMod 3) • Pi.single j 1 : Fin (n + 1) → ZMod 3) 0 = 0 := by
        simp [Pi.single_eq_of_ne (Ne.symm hl0'), Pi.single_eq_of_ne (Ne.symm hj0)]
      have hw2 : wt (Pi.single l 1 - (1 : ZMod 3) • Pi.single j 1 : Fin (n + 1) → ZMod 3) = 2 := by
        simpa using wt_smul_single_sub_smul hlj (c := 1) one_ne_zero one_ne_zero
      have hv := monoSwap_orbN_wt_two h hT ha hb hab hδ hqR' hmat hw0 hw2
      obtain ⟨Ar, hArX, -, harmat⟩ :=
        h.exists_conj_swapRefl hT hl0' hj0 hlj (c := 1) one_ne_zero one_ne_zero (by simpa using hv)
      let r : GL (Fin (n + 1)) (ZMod 3) := Ar * T * Ar⁻¹
      have hrmat : (r : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = swapRefl l j 1 := harmat
      have hrR : ∃ B ∈ Xg, r = B * T * B⁻¹ := ⟨Ar, hArX, rfl⟩
      have hrT : Commute r T := by
        rw [monoSwap_commute_mat_iff, hrmat, hT, Commute.symm_iff,
          coordRefl_commute_swapRefl_iff hlj one_ne_zero]
        exact ⟨Ne.symm hl0', Ne.symm hj0⟩
      have hrTp : Commute r Tp := by
        rw [monoSwap_commute_mat_iff, hrmat, hTp, Commute.symm_iff,
          coordRefl_commute_swapRefl_iff hlj one_ne_zero]
        exact ⟨Ne.symm hlp', Ne.symm hjp⟩
      have hrTk : Commute r Tk := by
        rw [monoSwap_commute_mat_iff, hrmat, hTk, Commute.symm_iff,
          coordRefl_commute_swapRefl_iff hlj one_ne_zero]
        exact ⟨Ne.symm hlk', Ne.symm hjk⟩
      have hcomm := claim r hrR hrT hrTp hrTk
      have hbad : Commute (swapRefl l j 1) (coordRefl l) := by
        have h2 := monoSwap_commute_mat_iff.mp hcomm
        rwa [hrmat, hlmat] at h2
      rw [Commute.symm_iff, coordRefl_commute_swapRefl_iff hlj one_ne_zero] at hbad
      exact hbad.1 rfl
    · obtain ⟨Cr, hCrX, hCrmat, -⟩ := monoSwap_exists_conj_coordRefl h hT hp hp1 ha₂
      let r : GL (Fin (n + 1)) (ZMod 3) := Cr * T * Cr⁻¹
      have hrmat : (r : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl a₂ := hCrmat
      have hrR : ∃ B ∈ Xg, r = B * T * B⁻¹ := ⟨Cr, hCrX, rfl⟩
      have hrT : Commute r T := monoSwap_commute_coordRefl hrmat hT
      have hrTp : Commute r Tp := monoSwap_commute_coordRefl hrmat hTp
      have hrTk : Commute r Tk := monoSwap_commute_coordRefl hrmat hTk
      have hcomm := claim r hrR hrT hrTp hrTk
      have hbad : Commute (coordRefl a₂) (swapRefl a₂ b₂ ε) := by
        have h2 := monoSwap_commute_mat_iff.mp hcomm
        rwa [hrmat, hmat₂] at h2
      rw [coordRefl_commute_swapRefl_iff hab₂ hε] at hbad
      exact hbad.1 rfl
variable {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} (h : MonoN0Hyp Xg)
include h

theorem exists_swap_mem (hn : 4 ≤ n) {p : Fin (n + 1)} (hp : p ≠ 0)
    (hp1 : OrbN Xg (Pi.single p 1)) :
    ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat (Equiv.swap 0 p) 1 := by
  obtain ⟨T, hTX, hT⟩ := h.exists_coordRefl (0 : Fin (n + 1))
  obtain ⟨g, hgX, hge0, hgTmat⟩ :=
    h.exists_conj_coordRefl hT hp (c := 1) one_ne_zero (by simpa using hp1)
  have hge0' : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single p 1 := by simpa using hge0
  let Tp : GL (Fin (n + 1)) (ZMod 3) := g * T * g⁻¹
  have hTpX : Tp ∈ Xg := Xg.mul_mem (Xg.mul_mem hgX hTX) (Xg.inv_mem hgX)
  have hTp : (Tp : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = coordRefl p := hgTmat
  have hgT : g * T * g⁻¹ = Tp := rfl
  obtain ⟨g', hg'X, hg'T, hg'Tp, hg'e0⟩ :=
    monoSwap_exists_interchange h hn hp hp1 hTX hT hTpX hTp hgX hge0' hgT
  have hwt : ∀ m : Fin (n + 1),
      wt ((g' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single m 1) = 1 := by
    intro m
    by_cases hm0 : m = 0
    · subst m
      refine monoSwap_wt_col (G' := g') (Tm := T) (m := 0) (l := p) hT ?_
      rw [hg'T]
      exact hTp
    by_cases hmp : m = p
    · subst m
      refine monoSwap_wt_col (G' := g') (Tm := Tp) (m := p) (l := (0 : Fin (n + 1))) hTp ?_
      rw [hg'Tp]
      exact hT
    · obtain ⟨Tk, hTkX, hTk⟩ := h.exists_coordRefl m
      have hTkR : ∃ C ∈ Xg, Tk = C * T * C⁻¹ := by
        obtain ⟨C, hCX, hCconj, -⟩ :=
          monoSwap_exists_conj_coordRefl h hT hp hp1 (c := m) hm0
        exact ⟨C, hCX, Units.ext (by rw [hTk, hCconj])⟩
      obtain ⟨l, hl⟩ := monoSwap_image_coordRefl h hn hp hp1 hT hTp hg'X hg'T hg'Tp
        (k := m) hm0 hmp hTk hTkR
      exact monoSwap_wt_col (G' := g') (Tm := Tk) (m := m) (l := l) hTk hl
  obtain ⟨τ, s, hs, -, hgs⟩ := mem_spSet_of_wt_col (A := g') hwt
  have hτ0 : τ 0 = p := by
    have h1 : (spMat τ s : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) = Pi.single p 1 := by
      rw [← hgs]
      exact hg'e0
    rw [spMat_mulVec] at h1
    have h2 := congrFun h1 (τ 0)
    simp only [Equiv.symm_apply_apply, Pi.single_eq_same, mul_one] at h2
    by_cases hne : τ 0 = p
    · exact hne
    · exfalso
      rw [Pi.single_eq_of_ne hne] at h2
      rcases hs 0 with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)
  set ρ : Equiv.Perm (Fin (n + 1)) := τ.symm * Equiv.swap 0 p with hρdef
  have hρ0 : ρ 0 = 0 := by
    rw [hρdef, Equiv.Perm.mul_apply, Equiv.swap_apply_left, ← hτ0, Equiv.symm_apply_apply]
  let r : Fin (n + 1) → ZMod 3 := fun j => s (ρ j)
  have hrSign : IsSign r := fun j => hs (ρ j)
  have hρmem : spMat ρ r ∈ monoN0 n := ⟨ρ, r, hrSign, hρ0, rfl⟩
  obtain ⟨C, hCX, hCmat⟩ := h.sub (spMat ρ r) hρmem
  have hprod : spMat τ s * spMat ρ r = spMat (Equiv.swap 0 p) 1 := by
    rw [spMat_mul]
    have hperm : τ * ρ = Equiv.swap 0 p := by
      rw [hρdef]
      ext x
      simp [Equiv.Perm.mul_apply]
    rw [hperm]
    have hfun : (fun j => s (ρ j) * r j) = fun _ => (1 : ZMod 3) := by
      funext j
      exact mul_self_of_ne_zero (monoSwap_isSign_ne_zero hs (ρ j))
    rw [hfun]
    rfl
  refine ⟨g' * C, Xg.mul_mem hg'X hCX, ?_⟩
  rw [Units.val_mul, hgs, hCmat]
  exact hprod


theorem fk_sub {p : Fin (n + 1)} (hp : p ≠ 0)
    (hA : ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat (Equiv.swap 0 p) 1)
    {σ : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ZMod 3} (hs : IsSign s) :
    ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s := by
  obtain ⟨A0, hA0X, hA0⟩ := hA
  by_cases hσ : σ 0 = 0
  · obtain ⟨C, hCX, hC⟩ := h.sub (spMat σ s) ⟨σ, s, hs, hσ, rfl⟩
    exact ⟨C, hCX, hC⟩
  · have hq : σ 0 ≠ 0 := hσ
    have hsw0 : Equiv.swap p (σ 0) 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hp) (Ne.symm hq)
    have hρ0 : (Equiv.swap 0 p * Equiv.swap p (σ 0) * σ) 0 = 0 := by
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have hperm : Equiv.swap p (σ 0) * Equiv.swap 0 p *
        (Equiv.swap 0 p * Equiv.swap p (σ 0) * σ) = σ := by
      calc Equiv.swap p (σ 0) * Equiv.swap 0 p *
            (Equiv.swap 0 p * Equiv.swap p (σ 0) * σ)
          = Equiv.swap p (σ 0) * (Equiv.swap 0 p *
              (Equiv.swap 0 p * (Equiv.swap p (σ 0) * σ))) := by
            simp only [mul_assoc]
        _ = Equiv.swap p (σ 0) *
              ((Equiv.swap 0 p * Equiv.swap 0 p) * (Equiv.swap p (σ 0) * σ)) := by
            rw [← mul_assoc (Equiv.swap 0 p) (Equiv.swap 0 p) (Equiv.swap p (σ 0) * σ)]
        _ = Equiv.swap p (σ 0) * (Equiv.swap p (σ 0) * σ) := by
            rw [Equiv.swap_mul_self, one_mul]
        _ = σ := Equiv.swap_mul_self_mul p (σ 0) σ
    obtain ⟨B, hBX, hB⟩ := h.sub (spMat (Equiv.swap p (σ 0)) 1)
      ⟨_, fun _ => 1, fun _ => Or.inl rfl, hsw0, rfl⟩
    obtain ⟨C, hCX, hC⟩ := h.sub (spMat (Equiv.swap 0 p * Equiv.swap p (σ 0) * σ) s)
      ⟨_, s, hs, hρ0, rfl⟩
    refine ⟨B * A0 * C, Xg.mul_mem (Xg.mul_mem hBX hA0X) hCX, ?_⟩
    rw [Units.val_mul, Units.val_mul, hB, hA0, hC]
    rw [spMat_mul, spMat_mul, hperm]
    congr 1
    funext j
    simp

end MonoN0Hyp

end CFSG.StandardType.FrameRoute.FS81
