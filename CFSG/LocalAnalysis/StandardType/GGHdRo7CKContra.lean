module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CKContraAux_coord_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (i k : Fin (n + 1)) :
    b.coord k (b i) = (if i = k then 1 else 0) := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

private lemma hdRo7CKContraAux_coord_smul_basis {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (k i : Fin (n + 1)) (c : ZMod 3) :
    b.coord k (c • b i) = c * (if i = k then 1 else 0) := by
  rw [map_smul, hdRo7CKContraAux_coord_basis, smul_eq_mul]

private lemma hdRo7CKContraAux_coord_v_zero {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (c : ZMod 3)
    (k : Fin (n + 1)) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk2 : k ≠ 2) :
    b.coord k (c • b 0 + b 1 + b 2 : V) = 0 := by
  rw [map_add, map_add, hdRo7CKContraAux_coord_smul_basis, hdRo7CKContraAux_coord_basis,
    hdRo7CKContraAux_coord_basis]
  rw [if_neg (Ne.symm hk0), if_neg (Ne.symm hk1), if_neg (Ne.symm hk2)]
  ring

private lemma hdRo7CKContraAux_coord_v_zero0 {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (k : Fin (n + 1)) (hk1 : k ≠ 1) (hk2 : k ≠ 2) :
    b.coord k (b 1 + b 2 : V) = 0 := by
  rw [map_add, hdRo7CKContraAux_coord_basis, hdRo7CKContraAux_coord_basis]
  rw [if_neg (Ne.symm hk1), if_neg (Ne.symm hk2)]
  ring

private lemma hdRo7CKContraAux_coord_signed {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : V ≃ₗ[ZMod 3] V) (c : ZMod 3) (σ : Equiv.Perm (Fin (n + 1)))
    (c' : Fin (n + 1) → ZMod 3) (happly : ∀ i, a (b i) = c' i • b (σ i))
    (k : Fin (n + 1)) :
    b.coord k (a (c • b 0 + b 1 + b 2)) =
      c * c' 0 * (if σ 0 = k then 1 else 0) + c' 1 * (if σ 1 = k then 1 else 0) +
        c' 2 * (if σ 2 = k then 1 else 0) := by
  simp only [map_add, map_smul, happly, hdRo7CKContraAux_coord_smul_basis,
    hdRo7CKContraAux_coord_basis, smul_eq_mul]
  ring

private lemma hdRo7CKContraAux_coord_at_sigma0 {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : V ≃ₗ[ZMod 3] V) (c : ZMod 3) (σ : Equiv.Perm (Fin (n + 1)))
    (c' : Fin (n + 1) → ZMod 3) (happly : ∀ i, a (b i) = c' i • b (σ i))
    (h10 : σ 1 ≠ σ 0) (h20 : σ 2 ≠ σ 0) :
    b.coord (σ 0) (a (c • b 0 + b 1 + b 2)) = c * c' 0 := by
  rw [hdRo7CKContraAux_coord_signed b a c σ c' happly (σ 0)]
  rw [if_pos rfl, if_neg h10, if_neg h20]
  ring

private lemma hdRo7CKContraAux_coord_at_sigma1 {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : V ≃ₗ[ZMod 3] V) (c : ZMod 3) (σ : Equiv.Perm (Fin (n + 1)))
    (c' : Fin (n + 1) → ZMod 3) (happly : ∀ i, a (b i) = c' i • b (σ i))
    (h01 : σ 0 ≠ σ 1) (h21 : σ 2 ≠ σ 1) :
    b.coord (σ 1) (a (c • b 0 + b 1 + b 2)) = c' 1 := by
  rw [hdRo7CKContraAux_coord_signed b a c σ c' happly (σ 1)]
  rw [if_neg h01, if_pos rfl, if_neg h21]
  ring

private lemma hdRo7CKContraAux_coord_at_sigma2 {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : V ≃ₗ[ZMod 3] V) (c : ZMod 3) (σ : Equiv.Perm (Fin (n + 1)))
    (c' : Fin (n + 1) → ZMod 3) (happly : ∀ i, a (b i) = c' i • b (σ i))
    (h02 : σ 0 ≠ σ 2) (h12 : σ 1 ≠ σ 2) :
    b.coord (σ 2) (a (c • b 0 + b 1 + b 2)) = c' 2 := by
  rw [hdRo7CKContraAux_coord_signed b a c σ c' happly (σ 2)]
  rw [if_neg h02, if_neg h12, if_pos rfl]
  ring

private lemma hdRo7CKContraAux_fin_zero_ne_one (n : ℕ) (hn : 1 ≤ n) :
    (0 : Fin (n + 1)) ≠ 1 := by
  apply Fin.ne_of_val_ne
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
  exact Nat.zero_ne_one

private lemma hdRo7CKContraAux_fin_zero_ne_two (n : ℕ) (hn : 2 ≤ n) :
    (0 : Fin (n + 1)) ≠ 2 := by
  apply Fin.ne_of_val_ne
  rw [Fin.val_zero, Fin.coe_ofNat_eq_mod (n + 1) 2,
    Nat.mod_eq_of_lt (by omega : 2 < n + 1)]
  exact (by decide : (0:ℕ) ≠ 2)

private lemma hdRo7CKContraAux_fin_one_ne_two (n : ℕ) (hn : 2 ≤ n) :
    (1 : Fin (n + 1)) ≠ 2 := by
  apply Fin.ne_of_val_ne
  rw [Fin.val_one', Fin.coe_ofNat_eq_mod (n + 1) 2,
    Nat.mod_eq_of_lt (by omega : 1 < n + 1), Nat.mod_eq_of_lt (by omega : 2 < n + 1)]
  exact (by decide : (1:ℕ) ≠ 2)

private def hdRo7CKContraAux_S (n : ℕ) (c : ZMod 3) : Finset (Fin (n + 1)) :=
  if c = 0 then ({1, 2} : Finset (Fin (n + 1))) else ({0, 1, 2} : Finset (Fin (n + 1)))

private lemma hdRo7CKContraAux_perm_preserves {n : ℕ} (hn : 5 ≤ n) {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (a : V ≃ₗ[ZMod 3] V) (c : ZMod 3) (σ : Equiv.Perm (Fin (n + 1)))
    (c' : Fin (n + 1) → ZMod 3) (hc' : ∀ i, c' i = 1 ∨ c' i = -1)
    (happly : ∀ i, a (b i) = c' i • b (σ i))
    (hfix : a (c • b 0 + b 1 + b 2) = c • b 0 + b 1 + b 2) :
    ∀ i, i ∈ hdRo7CKContraAux_S n c → σ i ∈ hdRo7CKContraAux_S n c := by
  have hc'0 : c' 0 ≠ 0 := by rcases hc' 0 with h | h <;> rw [h] <;> decide
  have hc'1 : c' 1 ≠ 0 := by rcases hc' 1 with h | h <;> rw [h] <;> decide
  have hc'2 : c' 2 ≠ 0 := by rcases hc' 2 with h | h <;> rw [h] <;> decide
  have h01 : σ 0 ≠ σ 1 := fun h =>
    hdRo7CKContraAux_fin_zero_ne_one n (by omega) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h =>
    hdRo7CKContraAux_fin_zero_ne_two n (by omega) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h =>
    hdRo7CKContraAux_fin_one_ne_two n (by omega) (σ.injective h)
  have h21 : σ 2 ≠ σ 1 := Ne.symm h12
  intro i hi
  rw [hdRo7CKContraAux_S] at hi ⊢
  by_cases hc : c = 0
  · rw [if_pos hc] at hi ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    rcases hi with rfl | rfl
    · by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      obtain ⟨hk1, hk2⟩ := hcon
      have hzero : b.coord (σ 1) (a (c • b 0 + b 1 + b 2)) = 0 := by
        rw [hfix, hc]
        simpa using hdRo7CKContraAux_coord_v_zero0 b (σ 1) hk1 hk2
      rw [hdRo7CKContraAux_coord_at_sigma1 b a c σ c' happly h01 h21] at hzero
      exact hc'1 hzero
    · by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      obtain ⟨hk1, hk2⟩ := hcon
      have hzero : b.coord (σ 2) (a (c • b 0 + b 1 + b 2)) = 0 := by
        rw [hfix, hc]
        simpa using hdRo7CKContraAux_coord_v_zero0 b (σ 2) hk1 hk2
      rw [hdRo7CKContraAux_coord_at_sigma2 b a c σ c' happly h02 h12] at hzero
      exact hc'2 hzero
  · rw [if_neg hc] at hi ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    rcases hi with rfl | rfl | rfl
    · by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      obtain ⟨hk0, hk1, hk2⟩ := hcon
      have hzero : b.coord (σ 0) (a (c • b 0 + b 1 + b 2)) = 0 := by
        rw [hfix]
        exact hdRo7CKContraAux_coord_v_zero b c (σ 0) hk0 hk1 hk2
      rw [hdRo7CKContraAux_coord_at_sigma0 b a c σ c' happly (Ne.symm h01)
        (Ne.symm h02)] at hzero
      exact (mul_ne_zero hc hc'0) hzero
    · by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      obtain ⟨hk0, hk1, hk2⟩ := hcon
      have hzero : b.coord (σ 1) (a (c • b 0 + b 1 + b 2)) = 0 := by
        rw [hfix]
        exact hdRo7CKContraAux_coord_v_zero b c (σ 1) hk0 hk1 hk2
      rw [hdRo7CKContraAux_coord_at_sigma1 b a c σ c' happly h01 h21] at hzero
      exact hc'1 hzero
    · by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      obtain ⟨hk0, hk1, hk2⟩ := hcon
      have hzero : b.coord (σ 2) (a (c • b 0 + b 1 + b 2)) = 0 := by
        rw [hfix]
        exact hdRo7CKContraAux_coord_v_zero b c (σ 2) hk0 hk1 hk2
      rw [hdRo7CKContraAux_coord_at_sigma2 b a c σ c' happly h02 h12] at hzero
      exact hc'2 hzero

private lemma hdRo7CKContraAux_image_eq {n : ℕ} (S : Finset (Fin (n + 1)))
    (σ : Equiv.Perm (Fin (n + 1))) (h : ∀ i ∈ S, σ i ∈ S) : S.image σ = S := by
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact h i hi
  · rw [Finset.card_image_of_injective S σ.injective]

private lemma hdRo7CKContraAux_mem_iff_of_image_eq {n : ℕ} (S : Finset (Fin (n + 1)))
    (σ : Equiv.Perm (Fin (n + 1))) (h : S.image σ = S) :
    ∀ x, (σ x ∈ S) ↔ (x ∈ S) := by
  intro x
  constructor
  · intro hx
    rw [← h] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hyx⟩
    rwa [σ.injective hyx] at hy
  · intro hx
    rw [← h]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

private noncomputable def hdRo7CKContraAux_toPerm {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V) :
    Equiv.Perm (Fin (n + 1)) := by
  classical
  exact if h : C2Full 3 b a then Classical.choose h else 1

private noncomputable def hdRo7CKContraAux_toSign {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V) :
    Fin (n + 1) → ZMod 3 := by
  classical
  exact if h : C2Full 3 b a then Classical.choose (Classical.choose_spec h) else 1

private lemma hdRo7CKContraAux_toPerm_apply {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (h : C2Full 3 b a) :
    hdRo7CKContraAux_toPerm b a = Classical.choose h := by
  classical
  rw [hdRo7CKContraAux_toPerm, dif_pos h]

private lemma hdRo7CKContraAux_toSign_apply {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (h : C2Full 3 b a) :
    hdRo7CKContraAux_toSign b a = Classical.choose (Classical.choose_spec h) := by
  classical
  rw [hdRo7CKContraAux_toSign, dif_pos h]

private lemma hdRo7CKContraAux_toSign_mem {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (h : C2Full 3 b a) :
    ∀ i, hdRo7CKContraAux_toSign b a i = 1 ∨ hdRo7CKContraAux_toSign b a i = -1 := by
  intro i
  rw [hdRo7CKContraAux_toSign_apply b a h]
  exact (Classical.choose_spec (Classical.choose_spec h)).1 i

private lemma hdRo7CKContraAux_apply {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (h : C2Full 3 b a) :
    ∀ i, a (b i) = hdRo7CKContraAux_toSign b a i • b (hdRo7CKContraAux_toPerm b a i) := by
  intro i
  rw [hdRo7CKContraAux_toSign_apply b a h, hdRo7CKContraAux_toPerm_apply b a h]
  exact (Classical.choose_spec (Classical.choose_spec h)).2 i

private lemma hdRo7CKContraAux_ext {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {a₁ a₂ : V ≃ₗ[ZMod 3] V}
    (h1 : C2Full 3 b a₁) (h2 : C2Full 3 b a₂)
    (hσ : hdRo7CKContraAux_toPerm b a₁ = hdRo7CKContraAux_toPerm b a₂)
    (hc' : hdRo7CKContraAux_toSign b a₁ = hdRo7CKContraAux_toSign b a₂) : a₁ = a₂ := by
  apply b.ext'
  intro i
  rw [hdRo7CKContraAux_apply b a₁ h1 i, hdRo7CKContraAux_apply b a₂ h2 i, hσ, hc']

private lemma hdRo7CKContraAux_sign_eq_of_decide {u v : ZMod 3}
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (h : decide (u = 1) = decide (v = 1)) : u = v := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv]
  · rw [hu, hv] at h; exact absurd h (by decide)
  · rw [hu, hv] at h; exact absurd h (by decide)
  · rw [hu, hv]

private lemma hdRo7CKContraAux_toSign_eq_of_decide {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {a₁ a₂ : V ≃ₗ[ZMod 3] V}
    (h1 : C2Full 3 b a₁) (h2 : C2Full 3 b a₂)
    (h : (fun i => decide (hdRo7CKContraAux_toSign b a₁ i = 1)) =
      (fun i => decide (hdRo7CKContraAux_toSign b a₂ i = 1))) :
    hdRo7CKContraAux_toSign b a₁ = hdRo7CKContraAux_toSign b a₂ := by
  funext i
  exact hdRo7CKContraAux_sign_eq_of_decide (hdRo7CKContraAux_toSign_mem b a₁ h1 i)
    (hdRo7CKContraAux_toSign_mem b a₂ h2 i) (congrFun h i)

private noncomputable def hdRo7CKContraAux_restrict {n : ℕ} (S : Finset (Fin (n + 1)))
    (σ : Equiv.Perm (Fin (n + 1))) (h : S.image σ = S) :
    Equiv.Perm ↥(S : Set (Fin (n + 1))) × Equiv.Perm ↥((S : Set (Fin (n + 1)))ᶜ) :=
  let hiff := hdRo7CKContraAux_mem_iff_of_image_eq S σ h
  (σ.subtypePerm hiff, σ.subtypePerm (p := fun x => x ∉ S) fun x => (hiff x).not)

private lemma hdRo7CKContraAux_restrict_injective {n : ℕ} (S : Finset (Fin (n + 1))) :
    Function.Injective (fun p : {σ : Equiv.Perm (Fin (n + 1)) // S.image σ = S} =>
      hdRo7CKContraAux_restrict S p.1 p.2) := by
  intro p q hpq
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ S
  · have h1 : (hdRo7CKContraAux_restrict S p.1 p.2).1 = (hdRo7CKContraAux_restrict S q.1 q.2).1 :=
      congrArg Prod.fst hpq
    dsimp only [hdRo7CKContraAux_restrict] at h1
    have hpt := DFunLike.congr_fun h1 ⟨x, hx⟩
    rw [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypePerm_apply] at hpt
    exact congrArg Subtype.val hpt
  · have h2 : (hdRo7CKContraAux_restrict S p.1 p.2).2 = (hdRo7CKContraAux_restrict S q.1 q.2).2 :=
      congrArg Prod.snd hpq
    dsimp only [hdRo7CKContraAux_restrict] at h2
    have hpt := DFunLike.congr_fun h2 ⟨x, hx⟩
    rw [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypePerm_apply] at hpt
    exact congrArg Subtype.val hpt

private lemma hdRo7CKContraAux_arith_three (n : ℕ) (hn : 5 ≤ n) :
    6 * (n - 2).factorial * 2 ^ (n + 1) < 2 ^ n * n.factorial := by
  have hfac1 : n.factorial = n * (n - 1).factorial := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  have hfac2 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  have hnl : 12 < n * (n - 1) := by
    have := Nat.mul_le_mul hn (show 4 ≤ n - 1 by omega)
    omega
  have hpos : 0 < 2 ^ n * (n - 2).factorial :=
    mul_pos (Nat.pow_pos (by norm_num)) (Nat.factorial_pos _)
  rw [hfac1, hfac2, hpow]
  nlinarith [hpos]

private lemma hdRo7CKContraAux_arith_two (n : ℕ) (hn : 5 ≤ n) :
    2 * (n - 1).factorial * 2 ^ (n + 1) < 2 ^ n * n.factorial := by
  have hfac1 : n.factorial = n * (n - 1).factorial := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  have hnl : 4 < n := by omega
  have hpos : 0 < 2 ^ n * (n - 1).factorial :=
    mul_pos (Nat.pow_pos (by norm_num)) (Nat.factorial_pos _)
  rw [hfac1, hpow]
  nlinarith [hpos]

theorem c2_kcontra_holds : C2KContraLeaf := by
  intro hN hR p _ hp n hn V _ _ b AK AL A c hAK hAKA hALA hStab hNoT hfix hgen hcard
  subst p
  have hrefl_full : ∀ r ∈ AL, GGLinRefl r → C2Full 3 b r := by
    intro r hrAL hrrefl
    rcases hR 3 rfl n hn V b A
        (fun a ha => hAKA ((hAK a).mpr ha))
        (fun a haA hafix => hN 3 rfl n hn V b a
          (hStab a haA hafix) hafix)
        hNoT r (hALA hrAL) hrrefl with hsp | hsign | hswap
    · obtain ⟨σ, c', _, _, hc', happly⟩ := hsp
      exact ⟨σ, c', hc', happly⟩
    · refine ⟨1, fun i => if i = 0 then -1 else 1, ?_, ?_⟩
      · intro i; by_cases hi : i = 0 <;> simp [hi]
      · intro i
        by_cases hi : i = 0
        · subst hi
          simp [Equiv.Perm.one_apply, hsign.1]
        · simp [hi, Equiv.Perm.one_apply, hsign.2 i hi]
    · obtain ⟨i, ε, hi0, hε, h0, hi, hrest⟩ := hswap
      refine ⟨Equiv.swap 0 i, fun j => if j = 0 then ε else if j = i then ε else 1, ?_, ?_⟩
      · intro j
        dsimp only
        by_cases hj0 : j = 0
        · rw [if_pos hj0]; exact hε
        · rw [if_neg hj0]
          by_cases hji : j = i
          · rw [if_pos hji]; exact hε
          · rw [if_neg hji]; exact Or.inl rfl
      · intro j
        by_cases hj0 : j = 0
        · subst hj0
          simp [h0]
        · by_cases hji : j = i
          · subst hji
            simp [hi, hi0]
          · simp [hrest j hj0 hji, hj0, hji, Equiv.swap_apply_of_ne_of_ne hj0 hji]
  have hAL_full : ∀ a ∈ AL, C2Full 3 b a := by
    rw [hgen]
    intro a ha
    have hmem : a ∈ CFSG.StandardType.OrthF3.ggOrthSignedPerms b :=
      (Subgroup.closure_le (CFSG.StandardType.OrthF3.ggOrthSignedPerms b)).mpr (fun r hr => hrefl_full r hr.1 hr.2) ha
    exact hmem
  haveI : Fintype V := Module.fintypeOfFintype b
  haveI : Finite V := Finite.of_fintype V
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (fun v => congrFun h v))
  haveI : Finite ↥AL := Subtype.finite
  let S : Finset (Fin (n + 1)) := hdRo7CKContraAux_S n c
  have hS_mem : ∀ i, i ∈ S ↔ i ∈ hdRo7CKContraAux_S n c := fun i => Iff.rfl
  let f : ↥AL → {σ : Equiv.Perm (Fin (n + 1)) // S.image σ = S} ×
      (Fin (n + 1) → Bool) := fun x =>
    let hx := hAL_full x.1 x.2
    ⟨⟨hdRo7CKContraAux_toPerm b x.1,
        hdRo7CKContraAux_image_eq S _
          (hdRo7CKContraAux_perm_preserves hn b x.1 c _ _
            (hdRo7CKContraAux_toSign_mem b x.1 hx)
            (hdRo7CKContraAux_apply b x.1 hx) (hfix x.1 x.2))⟩,
      fun i => decide (hdRo7CKContraAux_toSign b x.1 i = 1)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hσ : hdRo7CKContraAux_toPerm b x.1 = hdRo7CKContraAux_toPerm b y.1 := by
      have := congrArg (fun q => (q.1 : Equiv.Perm (Fin (n + 1)))) hxy
      simpa using this
    have hb : (fun i => decide (hdRo7CKContraAux_toSign b x.1 i = 1)) =
        (fun i => decide (hdRo7CKContraAux_toSign b y.1 i = 1)) := by
      have := congrArg Prod.snd hxy
      simpa using this
    exact Subtype.ext (hdRo7CKContraAux_ext b (hAL_full x.1 x.2) (hAL_full y.1 y.2) hσ
      (hdRo7CKContraAux_toSign_eq_of_decide b (hAL_full x.1 x.2) (hAL_full y.1 y.2) hb))
  have hcard1 : Nat.card ↥AL ≤
      Nat.card ({σ : Equiv.Perm (Fin (n + 1)) // S.image σ = S} ×
        (Fin (n + 1) → Bool)) :=
    Nat.card_le_card_of_injective f hf
  have hcardg : Nat.card {σ : Equiv.Perm (Fin (n + 1)) // S.image σ = S} ≤
      Nat.card (Equiv.Perm ↥(S : Set (Fin (n + 1)))) *
        Nat.card (Equiv.Perm ↥((S : Set (Fin (n + 1)))ᶜ)) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ (hdRo7CKContraAux_restrict_injective S)
  have hQ : Nat.card (Fin (n + 1) → Bool) = 2 ^ (n + 1) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_fin, Fintype.card_bool]
  have hPermS : Nat.card (Equiv.Perm ↥(S : Set (Fin (n + 1)))) = (S.card).factorial := by
    rw [Nat.card_perm]
    change (Nat.card {x // x ∈ (S : Set (Fin (n + 1)))}).factorial = (S.card).factorial
    rw [Nat.subtype_card (p := fun x => x ∈ (S : Set (Fin (n + 1)))) S (fun x => Iff.rfl)]
  have hPermSc : Nat.card (Equiv.Perm ↥((S : Set (Fin (n + 1)))ᶜ)) = ((Sᶜ).card).factorial := by
    rw [Nat.card_perm]
    change (Nat.card {x // x ∈ ((S : Set (Fin (n + 1)))ᶜ)}).factorial = ((Sᶜ).card).factorial
    rw [Nat.subtype_card (p := fun x => x ∈ ((S : Set (Fin (n + 1)))ᶜ)) (Sᶜ)
      (fun x => Finset.mem_compl)]
  have hcardS : S.card = if c = 0 then 2 else 3 := by
    dsimp only [S]
    rw [hdRo7CKContraAux_S]
    split_ifs with hc
    · rw [Finset.card_insert_of_notMem
          (by simpa using hdRo7CKContraAux_fin_one_ne_two n (by omega)),
        Finset.card_singleton]
    · rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hdRo7CKContraAux_fin_zero_ne_one n (by omega),
              hdRo7CKContraAux_fin_zero_ne_two n (by omega)⟩),
        Finset.card_insert_of_notMem (by simpa using hdRo7CKContraAux_fin_one_ne_two n (by omega)),
        Finset.card_singleton]
  have hcardSc : (Sᶜ).card = if c = 0 then n - 1 else n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hcardS]
    split_ifs with hc
    · omega
    · omega
  have hAL_le : Nat.card AL ≤ (S.card).factorial * ((Sᶜ).card).factorial * 2 ^ (n + 1) := by
    calc Nat.card AL
        ≤ Nat.card ({σ : Equiv.Perm (Fin (n + 1)) // S.image σ = S} ×
            (Fin (n + 1) → Bool)) := hcard1
      _ = Nat.card {σ : Equiv.Perm (Fin (n + 1)) // S.image σ = S} *
            Nat.card (Fin (n + 1) → Bool) := Nat.card_prod _ _
      _ ≤ (Nat.card (Equiv.Perm ↥(S : Set (Fin (n + 1)))) *
            Nat.card (Equiv.Perm ↥((S : Set (Fin (n + 1)))ᶜ))) * 2 ^ (n + 1) := by
          exact Nat.mul_le_mul hcardg (le_of_eq hQ)
      _ = (S.card).factorial * ((Sᶜ).card).factorial * 2 ^ (n + 1) := by
          rw [hPermS, hPermSc]
  have hfin : Nat.card AL < 2 ^ n * n.factorial := by
    refine lt_of_le_of_lt hAL_le ?_
    by_cases hc : c = 0
    · rw [if_pos hc] at hcardS hcardSc
      rw [hcardS, hcardSc]
      norm_num
      exact hdRo7CKContraAux_arith_two n hn
    · rw [if_neg hc] at hcardS hcardSc
      rw [hcardS, hcardSc]
      norm_num
      exact hdRo7CKContraAux_arith_three n hn
  exact (not_lt_of_ge hcard) hfin

end CFSG.StandardType.HdRo7C
