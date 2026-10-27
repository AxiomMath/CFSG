module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open Matrix

private lemma ggQ2ge_fin_ne (n a b : ℕ) (ha : a < n) (hb : b < n) (h : a ≠ b) :
    (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := by
  intro hh
  exact h (by simpa [Fin.ext_iff] using hh)

private lemma ggQ2ge_D_left {k : ℕ} (hk : 2 ≤ k) :
    CartanMatrix.D (2 * k) ⟨2 * k - 3, by omega⟩ ⟨2 * k - 4, by omega⟩ = -1 := by
  unfold CartanMatrix.D
  simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> omega

private lemma ggQ2ge_D_mid {k : ℕ} (hk : 2 ≤ k) :
    CartanMatrix.D (2 * k) ⟨2 * k - 3, by omega⟩ ⟨2 * k - 2, by omega⟩ = -1 := by
  unfold CartanMatrix.D
  simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> omega

private lemma ggQ2ge_D_right {k : ℕ} (hk : 2 ≤ k) :
    CartanMatrix.D (2 * k) ⟨2 * k - 3, by omega⟩ ⟨2 * k - 1, by omega⟩ = -1 := by
  unfold CartanMatrix.D
  simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> omega

private lemma ggQ2ge_A_char (n : ℕ) : ∀ x y : Fin n, x ≠ y →
    CartanMatrix.A n x y ≠ 0 → x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  unfold CartanMatrix.A at h
  simp only [Matrix.of_apply] at h
  split_ifs at h with h1 h2
  · exact absurd h1 hxy
  · exact h2
  · exact absurd rfl h

private lemma ggQ2ge_B_char (n : ℕ) : ∀ x y : Fin n, x ≠ y →
    CartanMatrix.B n x y ≠ 0 → x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  unfold CartanMatrix.B at h
  simp only [Matrix.of_apply] at h
  split_ifs at h with h1 h2 h3 h4
  · exact absurd h1 hxy
  · exact Or.inl h2
  · exact Or.inl h2
  · exact Or.inr h4
  · exact absurd rfl h

private lemma ggQ2ge_C_char (n : ℕ) : ∀ x y : Fin n, x ≠ y →
    CartanMatrix.C n x y ≠ 0 → x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  unfold CartanMatrix.C at h
  simp only [Matrix.of_apply] at h
  split_ifs at h with h1 h2 h3 h4
  · exact absurd h1 hxy
  · exact Or.inl h2
  · exact Or.inr h3
  · exact Or.inr h3
  · exact absurd rfl h

private lemma ggQ2ge_F4_char : ∀ x y : Fin 4, x ≠ y → CartanMatrix.F₄ x y ≠ 0 →
    x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  fin_cases x <;> fin_cases y <;> revert h hxy <;> decide +kernel

private lemma ggQ2ge_F4t_char : ∀ x y : Fin 4, x ≠ y →
    (fun i j => CartanMatrix.F₄ j i) x y ≠ 0 →
    x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  fin_cases x <;> fin_cases y <;> revert h hxy <;> decide +kernel

private lemma ggQ2ge_G2_char : ∀ x y : Fin 2, x ≠ y → CartanMatrix.G₂ x y ≠ 0 →
    x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  fin_cases x <;> fin_cases y <;> revert h hxy <;> decide +kernel

private lemma ggQ2ge_G2t_char : ∀ x y : Fin 2, x ≠ y →
    (fun i j => CartanMatrix.G₂ j i) x y ≠ 0 →
    x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  intro x y hxy h
  fin_cases x <;> fin_cases y <;> revert h hxy <;> decide +kernel

private def ggQ2ge_NoThree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ x y z w : Fin n, y ≠ x → z ≠ x → w ≠ x → y ≠ z → y ≠ w → z ≠ w →
    M x y ≠ 0 → M x z ≠ 0 → M x w ≠ 0 → False

private lemma ggQ2ge_ABC_no_three {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ x y : Fin n, x ≠ y → M x y ≠ 0 → x.val + 1 = y.val ∨ y.val + 1 = x.val) :
    ggQ2ge_NoThree M := by
  rintro x y z w hyx hzx hwx hyz hyw hzw hxy hxz hxw
  have hy := hM x y (Ne.symm hyx) hxy
  have hz := hM x z (Ne.symm hzx) hxz
  have hw := hM x w (Ne.symm hwx) hxw
  rcases hy with hy | hy <;> rcases hz with hz | hz <;> rcases hw with hw | hw <;>
    first
      | exact hyz (Fin.ext (by omega))
      | exact hyw (Fin.ext (by omega))
      | exact hzw (Fin.ext (by omega))

private lemma ggQ2ge_F4_no_three : ggQ2ge_NoThree CartanMatrix.F₄ :=
  ggQ2ge_ABC_no_three _ ggQ2ge_F4_char

private lemma ggQ2ge_F4t_no_three : ggQ2ge_NoThree (fun i j => CartanMatrix.F₄ j i) :=
  ggQ2ge_ABC_no_three _ ggQ2ge_F4t_char

private lemma ggQ2ge_G2_no_three : ggQ2ge_NoThree CartanMatrix.G₂ :=
  ggQ2ge_ABC_no_three _ ggQ2ge_G2_char

private lemma ggQ2ge_G2t_no_three : ggQ2ge_NoThree (fun i j => CartanMatrix.G₂ j i) :=
  ggQ2ge_ABC_no_three _ ggQ2ge_G2t_char

private theorem ggQ2ge_card_eq {ι : Type} [Fintype ι] [DecidableEq ι] {e₀ : ι} {k : ℕ}
    (f : Fin (2 * k) ≃ {i // i ≠ e₀}) : Fintype.card ι = 2 * k + 1 := by
  have h1 : Fintype.card {i : ι // i ≠ e₀} = Fintype.card ι - 1 := by
    have := Fintype.card_subtype_compl (fun i : ι => i = e₀)
    simp only [Fintype.card_subtype_eq] at this
    simpa using this
  have h2 : Fintype.card (Fin (2 * k)) = Fintype.card {i : ι // i ≠ e₀} :=
    Fintype.card_congr f
  rw [Fintype.card_fin] at h2
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨e₀⟩
  omega

private theorem ggQ2ge_D_four {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℤ)
    (e₀ : ι) {k : ℕ} (hk : 2 ≤ k) (f : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hf : ∀ i j, C (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    ∃ a b c d : ι, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      C a b ≠ 0 ∧ C a c ≠ 0 ∧ C a d ≠ 0 := by
  refine ⟨f ⟨2 * k - 3, by omega⟩, f ⟨2 * k - 4, by omega⟩, f ⟨2 * k - 2, by omega⟩,
    f ⟨2 * k - 1, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    exact (ggQ2ge_fin_ne (2 * k) (2 * k - 3) (2 * k - 4) (by omega) (by omega) (by omega))
      (f.injective (Subtype.ext hh))
  · intro hh
    exact (ggQ2ge_fin_ne (2 * k) (2 * k - 3) (2 * k - 2) (by omega) (by omega) (by omega))
      (f.injective (Subtype.ext hh))
  · intro hh
    exact (ggQ2ge_fin_ne (2 * k) (2 * k - 3) (2 * k - 1) (by omega) (by omega) (by omega))
      (f.injective (Subtype.ext hh))
  · intro hh
    exact (ggQ2ge_fin_ne (2 * k) (2 * k - 4) (2 * k - 2) (by omega) (by omega) (by omega))
      (f.injective (Subtype.ext hh))
  · intro hh
    exact (ggQ2ge_fin_ne (2 * k) (2 * k - 4) (2 * k - 1) (by omega) (by omega) (by omega))
      (f.injective (Subtype.ext hh))
  · intro hh
    exact (ggQ2ge_fin_ne (2 * k) (2 * k - 2) (2 * k - 1) (by omega) (by omega) (by omega))
      (f.injective (Subtype.ext hh))
  · rw [hf ⟨2 * k - 3, by omega⟩ ⟨2 * k - 4, by omega⟩, ggQ2ge_D_left hk]
    norm_num
  · rw [hf ⟨2 * k - 3, by omega⟩ ⟨2 * k - 2, by omega⟩, ggQ2ge_D_mid hk]
    norm_num
  · rw [hf ⟨2 * k - 3, by omega⟩ ⟨2 * k - 1, by omega⟩, ggQ2ge_D_right hk]
    norm_num

private lemma ggQ2ge_transport_contra {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : ggQ2ge_NoThree M) {ι : Type} (C : Matrix ι ι ℤ) (e : Fin n ≃ ι)
    (he : ∀ i j, C (e i) (e j) = M i j) {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hCab : C a b ≠ 0) (hCac : C a c ≠ 0) (hCad : C a d ≠ 0) : False := by
  refine hM (e.symm a) (e.symm b) (e.symm c) (e.symm d)
    (fun h => hab (e.symm.injective h).symm) (fun h => hac (e.symm.injective h).symm)
    (fun h => had (e.symm.injective h).symm) (fun h => hbc (e.symm.injective h))
    (fun h => hbd (e.symm.injective h)) (fun h => hcd (e.symm.injective h))
    ?_ ?_ ?_
  · rw [← he (e.symm a) (e.symm b)]; simpa using hCab
  · rw [← he (e.symm a) (e.symm c)]; simpa using hCac
  · rw [← he (e.symm a) (e.symm d)]; simpa using hCad

private lemma ggQ2ge_E7_nbrs3 : ∀ y : Fin 7, y ≠ (3 : Fin 7) →
    CartanMatrix.E 7 3 y ≠ 0 → y = 1 ∨ y = 2 ∨ y = 4 := by
  intro y hy h
  fin_cases y <;> revert hy h <;> decide +kernel

private lemma ggQ2ge_E7_nbrs4 : ∀ y : Fin 7, y ≠ (4 : Fin 7) →
    CartanMatrix.E 7 4 y ≠ 0 → y = 3 ∨ y = 5 := by
  intro y hy h
  fin_cases y <;> revert hy h <;> decide +kernel

private lemma ggQ2ge_E7_nbrs5 : ∀ y : Fin 7, y ≠ (5 : Fin 7) →
    CartanMatrix.E 7 5 y ≠ 0 → y = 4 ∨ y = 6 := by
  intro y hy h
  fin_cases y <;> revert hy h <;> decide +kernel

private lemma ggQ2ge_E7_nbrs1 : ∀ y : Fin 7, y ≠ (1 : Fin 7) →
    CartanMatrix.E 7 1 y ≠ 0 → y = 3 := by
  intro y hy h
  fin_cases y <;> revert hy h <;> decide +kernel

private lemma ggQ2ge_E7_nbrs2 : ∀ y : Fin 7, y ≠ (2 : Fin 7) →
    CartanMatrix.E 7 2 y ≠ 0 → y = 0 ∨ y = 3 := by
  intro y hy h
  fin_cases y <;> revert hy h <;> decide +kernel

private lemma ggQ2ge_E7_nbrs0 : ∀ y : Fin 7, y ≠ (0 : Fin 7) →
    CartanMatrix.E 7 0 y ≠ 0 → y = 2 := by
  intro y hy h
  fin_cases y <;> revert hy h <;> decide +kernel

private lemma ggQ2ge_E7_deg3 (x : Fin 7)
    (h : ∃ y1 y2 y3 : Fin 7, y1 ≠ x ∧ y2 ≠ x ∧ y3 ≠ x ∧
      y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 ∧ CartanMatrix.E 7 x y1 ≠ 0 ∧
      CartanMatrix.E 7 x y2 ≠ 0 ∧ CartanMatrix.E 7 x y3 ≠ 0) : x = 3 := by
  revert h
  fin_cases x <;> decide +kernel

private lemma ggQ2ge_E7_unique (x : Fin 7)
    (h : ∃ y, (y ≠ x ∧ CartanMatrix.E 7 x y ≠ 0) ∧
      (∀ z : Fin 7, z ≠ x ∧ CartanMatrix.E 7 x z ≠ 0 → z = y)) :
    x = 0 ∨ x = 1 ∨ x = 6 := by
  revert h
  fin_cases x <;> decide +kernel

private lemma ggQ2ge_unique_e7 {ι : Type} (C : Matrix ι ι ℤ) (e : Fin 7 ≃ ι)
    (he : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) {c : ι}
    (h : ∃! d : ι, d ≠ c ∧ C c d ≠ 0) :
    ∃ y : Fin 7, (y ≠ e.symm c ∧ CartanMatrix.E 7 (e.symm c) y ≠ 0) ∧
      ∀ z : Fin 7, z ≠ e.symm c ∧ CartanMatrix.E 7 (e.symm c) z ≠ 0 → z = y := by
  obtain ⟨d, hd, huniq⟩ := h
  refine ⟨e.symm d, ⟨?_, ?_⟩, ?_⟩
  · intro hh
    exact hd.1 (e.symm.injective hh)
  · have hthis : C c d = CartanMatrix.E 7 (e.symm c) (e.symm d) := by
      have := he (e.symm c) (e.symm d)
      simpa using this
    rw [← hthis]; exact hd.2
  · intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hzc : e z ≠ c := by
      intro hh
      exact hz1 (e.injective (by rw [hh, Equiv.apply_symm_apply]))
    have hCz : C c (e z) ≠ 0 := by
      have hthis : C c (e z) = CartanMatrix.E 7 (e.symm c) z := by
        have := he (e.symm c) z
        simpa using this
      rw [hthis]; exact hz2
    have := huniq (e z) ⟨hzc, hCz⟩
    calc z = e.symm (e z) := (Equiv.symm_apply_apply e z).symm
      _ = e.symm d := by rw [this]

theorem ggQ2g_no_D_complement {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℤ) (e₀ : ι)
    {k : ℕ} (hk : 2 ≤ k) (f : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hf : ∀ i j, C (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    (¬ ∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ ((∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
        (2 ≤ n ∧ ((∀ i j, C (e i) (e j) = CartanMatrix.B n i j) ∨
          (∀ i j, C (e i) (e j) = CartanMatrix.C n i j))))) ∧
    (¬ ∃ e : Fin 6 ≃ ι, ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) ∧
    (¬ ∃ e : Fin 8 ≃ ι, ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j) ∧
    (¬ ∃ e : Fin 4 ≃ ι, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧
    (¬ ∃ e : Fin 2 ≃ ι, (∀ i j, C (e i) (e j) = CartanMatrix.G₂ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.G₂ j i)) := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hCab, hCac, hCad⟩ :=
    ggQ2ge_D_four C e₀ hk f hf
  have hcard : Fintype.card ι = 2 * k + 1 := ggQ2ge_card_eq f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨n, e, hn, hA | ⟨hn2, hB | hC⟩⟩
    · exact ggQ2ge_transport_contra (ggQ2ge_ABC_no_three (CartanMatrix.A n) (ggQ2ge_A_char n))
        C e hA hab hac had hbc hbd hcd hCab hCac hCad
    · exact ggQ2ge_transport_contra (ggQ2ge_ABC_no_three (CartanMatrix.B n) (ggQ2ge_B_char n))
        C e hB hab hac had hbc hbd hcd hCab hCac hCad
    · exact ggQ2ge_transport_contra (ggQ2ge_ABC_no_three (CartanMatrix.C n) (ggQ2ge_C_char n))
        C e hC hab hac had hbc hbd hcd hCab hCac hCad
  · rintro ⟨e, he⟩
    have h6 : Fintype.card ι = 6 := by rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · rintro ⟨e, he⟩
    have h8 : Fintype.card ι = 8 := by rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · rintro ⟨e, hF | hFt⟩
    · exact ggQ2ge_transport_contra ggQ2ge_F4_no_three C e hF hab hac had hbc hbd hcd
        hCab hCac hCad
    · exact ggQ2ge_transport_contra ggQ2ge_F4t_no_three C e hFt hab hac had hbc hbd hcd
        hCab hCac hCad
  · rintro ⟨e, hG | hGt⟩
    · exact ggQ2ge_transport_contra ggQ2ge_G2_no_three C e hG hab hac had hbc hbd hcd
        hCab hCac hCad
    · exact ggQ2ge_transport_contra ggQ2ge_G2t_no_three C e hGt hab hac had hbc hbd hcd
        hCab hCac hCad

theorem ggQ2g_classE7 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℤ) (e : Fin 7 ≃ ι)
    (he : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) (e₀ c : ι) (hce : c ≠ e₀)
    (hcl : ∃! d, d ≠ c ∧ C c d ≠ 0) {k : ℕ} (hk : 2 ≤ k) (f : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hf : ∀ i j, C (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    k = 3 ∧ e₀ = e 0 ∧ (c = e 1 ∨ c = e 6) := by
  have hcard : Fintype.card ι = 2 * k + 1 := ggQ2ge_card_eq f
  have h7 : Fintype.card ι = 7 := by rw [← Fintype.card_congr e, Fintype.card_fin]
  have hk3 : k = 3 := by omega
  subst k
  let g : Fin 6 → Fin 7 := fun i => e.symm (f i)
  have hg_inj : Function.Injective g := by
    intro i j h
    change e.symm (f i) = e.symm (f j) at h
    have h1 : (f i : ι) = (f j : ι) := e.symm.injective h
    exact f.injective (Subtype.ext h1)
  have hg : ∀ i j : Fin 6, CartanMatrix.E 7 (g i) (g j) = CartanMatrix.D 6 i j := by
    intro i j
    change CartanMatrix.E 7 (e.symm (f i)) (e.symm (f j)) = CartanMatrix.D 6 i j
    rw [← he (e.symm (f i)) (e.symm (f j))]
    simpa using hf i j
  have hg3 : g 3 = 3 := by
    refine ggQ2ge_E7_deg3 (g 3) ⟨g 2, g 4, g 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hg_inj.ne (by decide)
    · exact hg_inj.ne (by decide)
    · exact hg_inj.ne (by decide)
    · exact hg_inj.ne (by decide)
    · exact hg_inj.ne (by decide)
    · exact hg_inj.ne (by decide)
    · rw [hg 3 2]; decide
    · rw [hg 3 4]; decide
    · rw [hg 3 5]; decide
  have hg2 : g 2 = 4 := by
    have hmem : g 2 = 1 ∨ g 2 = 2 ∨ g 2 = 4 := by
      refine ggQ2ge_E7_nbrs3 (g 2) ?_ ?_
      · intro h
        exact (hg_inj.ne (show (2 : Fin 6) ≠ 3 by decide)) (by rw [h, hg3])
      · rw [← hg3, hg 3 2]; decide
    rcases hmem with h | h | h
    · exfalso
      have h1n : g 1 ≠ 1 := by
        have := hg_inj.ne (show (1 : Fin 6) ≠ 2 by decide)
        rwa [h] at this
      have hE1 : CartanMatrix.E 7 1 (g 1) ≠ 0 := by
        have h' : CartanMatrix.E 7 (g 2) (g 1) ≠ 0 := by rw [hg 2 1]; decide
        rwa [h] at h'
      have h13 : g 1 = 3 := ggQ2ge_E7_nbrs1 (g 1) h1n hE1
      have hne : g 1 ≠ g 3 := hg_inj.ne (show (1 : Fin 6) ≠ 3 by decide)
      rw [hg3] at hne
      exact hne h13
    · exfalso
      have h1n : g 1 ≠ 2 := by
        have := hg_inj.ne (show (1 : Fin 6) ≠ 2 by decide)
        rwa [h] at this
      have hE1 : CartanMatrix.E 7 2 (g 1) ≠ 0 := by
        have h' : CartanMatrix.E 7 (g 2) (g 1) ≠ 0 := by rw [hg 2 1]; decide
        rwa [h] at h'
      have hmem1 : g 1 = 0 ∨ g 1 = 3 := ggQ2ge_E7_nbrs2 (g 1) h1n hE1
      have hg1 : g 1 = 0 := by
        rcases hmem1 with h1 | h1
        · exact h1
        · exfalso
          have hne : g 1 ≠ g 3 := hg_inj.ne (show (1 : Fin 6) ≠ 3 by decide)
          rw [hg3] at hne
          exact hne h1
      have h0n : g 0 ≠ 0 := by
        have := hg_inj.ne (show (0 : Fin 6) ≠ 1 by decide)
        rwa [hg1] at this
      have hE0 : CartanMatrix.E 7 0 (g 0) ≠ 0 := by
        have h' : CartanMatrix.E 7 (g 1) (g 0) ≠ 0 := by rw [hg 1 0]; decide
        rwa [hg1] at h'
      have hg0 : g 0 = 2 := ggQ2ge_E7_nbrs0 (g 0) h0n hE0
      have h02 : g 0 ≠ g 2 := hg_inj.ne (show (0 : Fin 6) ≠ 2 by decide)
      rw [h] at h02
      exact h02 hg0
    · exact h
  have hg1 : g 1 = 5 := by
    have h14 : g 1 ≠ 4 := by
      have := hg_inj.ne (show (1 : Fin 6) ≠ 2 by decide)
      rwa [hg2] at this
    have hE : CartanMatrix.E 7 4 (g 1) ≠ 0 := by
      have h' : CartanMatrix.E 7 (g 2) (g 1) ≠ 0 := by rw [hg 2 1]; decide
      rwa [hg2] at h'
    have h35 : g 1 = 3 ∨ g 1 = 5 := ggQ2ge_E7_nbrs4 (g 1) h14 hE
    rcases h35 with h | h
    · exfalso
      have hne : g 1 ≠ g 3 := hg_inj.ne (show (1 : Fin 6) ≠ 3 by decide)
      rw [hg3] at hne
      exact hne h
    · exact h
  have hg0 : g 0 = 6 := by
    have h05 : g 0 ≠ 5 := by
      have := hg_inj.ne (show (0 : Fin 6) ≠ 1 by decide)
      rwa [hg1] at this
    have hE : CartanMatrix.E 7 5 (g 0) ≠ 0 := by
      have h' : CartanMatrix.E 7 (g 1) (g 0) ≠ 0 := by rw [hg 1 0]; decide
      rwa [hg1] at h'
    have h46 : g 0 = 4 ∨ g 0 = 6 := ggQ2ge_E7_nbrs5 (g 0) h05 hE
    rcases h46 with h | h
    · exfalso
      have h02 : g 0 ≠ g 2 := hg_inj.ne (show (0 : Fin 6) ≠ 2 by decide)
      rw [hg2] at h02
      exact h02 h
    · exact h
  have hg4 : g 4 = 1 ∨ g 4 = 2 := by
    have h43 : g 4 ≠ 3 := by
      have := hg_inj.ne (show (4 : Fin 6) ≠ 3 by decide)
      rwa [hg3] at this
    have hE : CartanMatrix.E 7 3 (g 4) ≠ 0 := by
      have h' : CartanMatrix.E 7 (g 3) (g 4) ≠ 0 := by rw [hg 3 4]; decide
      rwa [hg3] at h'
    rcases ggQ2ge_E7_nbrs3 (g 4) h43 hE with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h42 : g 4 ≠ g 2 := hg_inj.ne (show (4 : Fin 6) ≠ 2 by decide)
      rw [hg2] at h42
      exact h42 h
  have hg5 : g 5 = 1 ∨ g 5 = 2 := by
    have h53 : g 5 ≠ 3 := by
      have := hg_inj.ne (show (5 : Fin 6) ≠ 3 by decide)
      rwa [hg3] at this
    have hE : CartanMatrix.E 7 3 (g 5) ≠ 0 := by
      have h' : CartanMatrix.E 7 (g 3) (g 5) ≠ 0 := by rw [hg 3 5]; decide
      rwa [hg3] at h'
    rcases ggQ2ge_E7_nbrs3 (g 5) h53 hE with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h52 : g 5 ≠ g 2 := hg_inj.ne (show (5 : Fin 6) ≠ 2 by decide)
      rw [hg2] at h52
      exact h52 h
  have h0 : (0 : Fin 7) ∉ Set.range g := by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [hg0, hg1, hg2, hg3, hg4, hg5]
  have he0 : e₀ = e 0 := by
    by_contra hne
    have hmem : (0 : Fin 7) ∈ Set.range g := by
      refine ⟨f.symm ⟨e 0, Ne.symm hne⟩, ?_⟩
      change e.symm (f (f.symm ⟨e 0, Ne.symm hne⟩)) = 0
      rw [Equiv.apply_symm_apply]
      simpa using Equiv.symm_apply_apply e 0
    exact h0 hmem
  have hc : c = e 1 ∨ c = e 6 := by
    have hcl' := ggQ2ge_unique_e7 C e he hcl
    rcases ggQ2ge_E7_unique (e.symm c) hcl' with h | h | h
    · exfalso
      have hc0 : c = e 0 := by
        calc c = e (e.symm c) := (e.apply_symm_apply c).symm
          _ = e 0 := by rw [h]
      exact hce (hc0.trans he0.symm)
    · left
      calc c = e (e.symm c) := (e.apply_symm_apply c).symm
        _ = e 1 := by rw [h]
    · right
      calc c = e (e.symm c) := (e.apply_symm_apply c).symm
        _ = e 6 := by rw [h]
  exact ⟨rfl, he0, hc⟩

end CFSG.StandardType

end


