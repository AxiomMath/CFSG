module

public import CFSG.Quasithin.EmptyFaithful.A38c6Defs
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.A38c6

open CFSG.Quasithin CFSG.Quasithin.A38c5.Fm
open Equiv

private def clPts (B : Finset (Fin 8)) (i : Fin 6) : Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  if B = {0, 1, 2, 3} then
    ![(0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2), (4, 5, 6, 7), (4, 6, 5, 7), (4, 7, 5, 6)] i
  else if B = {0, 1, 4, 5} then
    ![(0, 1, 4, 5), (0, 4, 1, 5), (0, 5, 1, 4), (2, 3, 6, 7), (2, 6, 3, 7), (2, 7, 3, 6)] i
  else
    ![(0, 1, 6, 7), (0, 6, 1, 7), (0, 7, 1, 6), (2, 3, 4, 5), (2, 4, 3, 5), (2, 5, 3, 4)] i

private def clOf (B : Finset (Fin 8)) (i : Fin 6) : P8 :=
  swap (clPts B i).1 (clPts B i).2.1 * swap (clPts B i).2.2.1 (clPts B i).2.2.2

private def ClsOk4 (B : Finset (Fin 8)) (a b c d : Fin 8) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    (({a, b, c, d} : Finset (Fin 8)) = B ∨ ({a, b, c, d} : Finset (Fin 8)) = Bᶜ)

private def ClsIn4 (B : Finset (Fin 8)) (a b c d : Fin 8) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ((a ∈ B ∧ b ∈ B ∧ c ∈ B ∧ d ∈ B) ∨ (a ∉ B ∧ b ∉ B ∧ c ∉ B ∧ d ∉ B))

set_option maxRecDepth 100000 in
private theorem cls_cl_valid : ∀ B ∈ blocks3, ∀ i : Fin 6,
    ClsOk4 B (clPts B i).1 (clPts B i).2.1 (clPts B i).2.2.1 (clPts B i).2.2.2 := by
  unfold ClsOk4
  decide +kernel

set_option maxRecDepth 100000 in
private theorem cls_dts_core : ∀ B ∈ blocks3, ∀ a b c d : Fin 8, ClsIn4 B a b c d →
    ∃ i : Fin 6, swap a b * swap c d = clOf B i := by
  unfold ClsIn4
  decide +kernel

private theorem cls_card_blocks3 : ∀ B ∈ blocks3, B.card = 4 := by decide +kernel

private theorem cls_zero_mem : ∀ B ∈ blocks3, (0 : Fin 8) ∈ B := by decide +kernel

private theorem cls_dts_union {B : Finset (Fin 8)} (hB : B ∈ blocks3) (g : P8) :
    g ∈ dts B ∪ dts Bᶜ ↔ ∃ i : Fin 6, g = clOf B i := by
  constructor
  · intro hg
    have key : ∀ S : Finset (Fin 8), (S = B ∨ S = Bᶜ) → ∀ g ∈ dts S,
        ∃ i : Fin 6, g = clOf B i := by
      rintro S hS g ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, hS', rfl⟩
      refine cls_dts_core B hB a b c d ⟨h1, h2, h3, h4, h5, h6, ?_⟩
      have ha : a ∈ S := by rw [← hS']; simp
      have hb : b ∈ S := by rw [← hS']; simp
      have hc : c ∈ S := by rw [← hS']; simp
      have hd : d ∈ S := by rw [← hS']; simp
      rcases hS with rfl | rfl
      · exact Or.inl ⟨ha, hb, hc, hd⟩
      · simp only [Finset.mem_compl] at ha hb hc hd
        exact Or.inr ⟨ha, hb, hc, hd⟩
    rcases hg with hg | hg
    · exact key B (Or.inl rfl) g hg
    · exact key Bᶜ (Or.inr rfl) g hg
  · rintro ⟨i, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := cls_cl_valid B hB i
    rcases h7 with h7 | h7
    · exact Or.inl ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, h7, rfl⟩
    · exact Or.inr ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, h7, rfl⟩

private theorem cls_mem_Vsub {B : Finset (Fin 8)} (hB : B ∈ blocks3) {g : P8} :
    g ∈ Vsub B ↔ (∀ i : Fin 6, g * clOf B i = clOf B i * g) ∧ ∀ x, g x ∈ B ↔ x ∈ B := by
  rw [mem_Vsub]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h i
    exact h _ ((cls_dts_union hB _).2 ⟨i, rfl⟩)
  · intro h c hc
    obtain ⟨i, rfl⟩ := (cls_dts_union hB c).1 hc
    exact h i

private theorem cls_rk_of_card {A V : Subgroup P8} {n : ℕ} (hA : Nat.card ↥A = 2 ^ (n + 1))
    (hV : Nat.card ↥(A ⊓ V) = 2 ^ n) : rk ↥A = rk ↥(A ⊓ V) + 1 := by
  unfold rk
  rw [hA, hV, padicValNat.prime_pow, padicValNat.prime_pow]

private theorem cls_swap_core : ∀ B ∈ blocks3, ∀ a b : Fin 8, a ≠ b →
    ¬ ((∀ i : Fin 6, swap a b * clOf B i = clOf B i * swap a b) ∧
      ∀ x, swap a b x ∈ B ↔ x ∈ B) := by
  decide +kernel

private theorem cls_swap_not_mem {B : Finset (Fin 8)} (hB : B ∈ blocks3) {a b : Fin 8}
    (hab : a ≠ b) : Equiv.swap a b ∉ Vsub B := by
  rw [cls_mem_Vsub hB]
  exact cls_swap_core B hB a b hab

theorem rk_zpowers_swap {B : Finset (Fin 8)} (hB : B ∈ blocks3) {a b : Fin 8} (hab : a ≠ b)
    (hA : Subgroup.zpowers (Equiv.swap a b) ≤ PStab B) :
    rk ↥(Subgroup.zpowers (Equiv.swap a b)) =
      rk ↥(Subgroup.zpowers (Equiv.swap a b) ⊓ Vsub B) + 1 := by
  have _ := hA
  have h2 : Nat.card ↥(Subgroup.zpowers (Equiv.swap a b)) = 2 := by
    rw [Nat.card_zpowers]
    exact Equiv.Perm.IsSwap.orderOf ⟨a, b, hab, rfl⟩
  have hdvd : Nat.card ↥(Subgroup.zpowers (Equiv.swap a b) ⊓ Vsub B) ∣ 2 :=
    h2 ▸ Subgroup.card_dvd_of_le inf_le_left
  have h1 : Nat.card ↥(Subgroup.zpowers (Equiv.swap a b) ⊓ Vsub B) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers (Equiv.swap a b) ⊓ Vsub B = Subgroup.zpowers (Equiv.swap a b) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      have hmem : Equiv.swap a b ∈ Subgroup.zpowers (Equiv.swap a b) ⊓ Vsub B := by
        rw [heq]; exact Subgroup.mem_zpowers _
      exact cls_swap_not_mem hB hab hmem.2
  exact cls_rk_of_card (n := 0) (by simpa using h2) (by simpa using h1)

private def ClsOkVal (B : Finset (Fin 8)) (i x : Fin 8) : Prop := x ≠ i ∧ (x ∈ B ↔ i ∈ B)

private instance (B : Finset (Fin 8)) (i x : Fin 8) : Decidable (ClsOkVal B i x) := by
  unfold ClsOkVal; infer_instance

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
private theorem cls_fpf_core : ∀ B ∈ blocks3,
    ∀ x0 : Fin 8, ClsOkVal B 0 x0 →
    ∀ x1 : Fin 8, ClsOkVal B 1 x1 → (x0 = 1 ↔ x1 = 0) →
    ∀ x2 : Fin 8, ClsOkVal B 2 x2 → (x0 = 2 ↔ x2 = 0) → (x1 = 2 ↔ x2 = 1) →
    ∀ x3 : Fin 8, ClsOkVal B 3 x3 → (x0 = 3 ↔ x3 = 0) → (x1 = 3 ↔ x3 = 1) → (x2 = 3 ↔ x3 = 2) →
    ∀ x4 : Fin 8, ClsOkVal B 4 x4 → (x0 = 4 ↔ x4 = 0) → (x1 = 4 ↔ x4 = 1) → (x2 = 4 ↔ x4 = 2) →
      (x3 = 4 ↔ x4 = 3) →
    ∀ x5 : Fin 8, ClsOkVal B 5 x5 → (x0 = 5 ↔ x5 = 0) → (x1 = 5 ↔ x5 = 1) → (x2 = 5 ↔ x5 = 2) →
      (x3 = 5 ↔ x5 = 3) → (x4 = 5 ↔ x5 = 4) →
    ∀ x6 : Fin 8, ClsOkVal B 6 x6 → (x0 = 6 ↔ x6 = 0) → (x1 = 6 ↔ x6 = 1) → (x2 = 6 ↔ x6 = 2) →
      (x3 = 6 ↔ x6 = 3) → (x4 = 6 ↔ x6 = 4) → (x5 = 6 ↔ x6 = 5) →
    ∀ x7 : Fin 8, ClsOkVal B 7 x7 → (x0 = 7 ↔ x7 = 0) → (x1 = 7 ↔ x7 = 1) → (x2 = 7 ↔ x7 = 2) →
      (x3 = 7 ↔ x7 = 3) → (x4 = 7 ↔ x7 = 4) → (x5 = 7 ↔ x7 = 5) → (x6 = 7 ↔ x7 = 6) →
    ∀ i : Fin 6, ∀ y : Fin 8,
      ![x0, x1, x2, x3, x4, x5, x6, x7] (clOf B i y) =
        clOf B i (![x0, x1, x2, x3, x4, x5, x6, x7] y) := by
  decide +kernel

private theorem cls_fpf_mem {B : Finset (Fin 8)} (hB : B ∈ blocks3) {g : P8} (hg2 : g * g = 1)
    (hfp : ∀ x, g x ≠ x) (hpres : ∀ x, g x ∈ B ↔ x ∈ B) : g ∈ Vsub B := by
  have hinv : ∀ i j : Fin 8, g i = j ↔ g j = i := by
    have h : ∀ x, g (g x) = x := fun x => by
      have := congrArg (fun p : P8 => p x) hg2
      simpa using this
    intro i j
    constructor
    · rintro rfl
      exact h i
    · rintro rfl
      exact h j
  rw [cls_mem_Vsub hB]
  refine ⟨fun i => ?_, hpres⟩
  have hf : ⇑g = ![g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] := by
    funext y
    fin_cases y <;> rfl
  have key := cls_fpf_core B hB (g 0) ⟨hfp 0, hpres 0⟩
    (g 1) ⟨hfp 1, hpres 1⟩ (hinv 0 1)
    (g 2) ⟨hfp 2, hpres 2⟩ (hinv 0 2) (hinv 1 2)
    (g 3) ⟨hfp 3, hpres 3⟩ (hinv 0 3) (hinv 1 3) (hinv 2 3)
    (g 4) ⟨hfp 4, hpres 4⟩ (hinv 0 4) (hinv 1 4) (hinv 2 4) (hinv 3 4)
    (g 5) ⟨hfp 5, hpres 5⟩ (hinv 0 5) (hinv 1 5) (hinv 2 5) (hinv 3 5) (hinv 4 5)
    (g 6) ⟨hfp 6, hpres 6⟩ (hinv 0 6) (hinv 1 6) (hinv 2 6) (hinv 3 6) (hinv 4 6) (hinv 5 6)
    (g 7) ⟨hfp 7, hpres 7⟩ (hinv 0 7) (hinv 1 7) (hinv 2 7) (hinv 3 7) (hinv 4 7) (hinv 5 7)
      (hinv 6 7) i
  rw [← hf] at key
  exact Equiv.ext fun y => key y

theorem rk_regE8 {B : Finset (Fin 8)} (hB : B ∈ blocks3) {A : Subgroup P8} (hA : IsRegE8 A)
    (hAB : A ≤ PStab B) : rk ↥A = rk ↥(A ⊓ Vsub B) + 1 := by
  obtain ⟨-, -, hsq, hcard, hreg⟩ := hA
  have h0B : (0 : Fin 8) ∈ B := cls_zero_mem B hB
  have hmem : ∀ a ∈ A, a 0 ∈ B → a ∈ Vsub B := by
    intro a ha ha0
    have hpres : ∀ x, a x ∈ B ↔ x ∈ B := by
      rcases hAB ha with h | h
      · exact h
      · exact absurd ((h 0).1 ha0) (not_not.2 h0B)
    by_cases hfix : ∃ x, a x = x
    · obtain ⟨x, hx⟩ := hfix
      obtain ⟨u, -, hu⟩ := hreg x x
      have ha1 : a = 1 := by
        rw [hu a ⟨ha, hx⟩, ← hu 1 ⟨A.one_mem, rfl⟩]
      rw [ha1]
      exact Subgroup.one_mem _
    · push Not at hfix
      exact cls_fpf_mem hB (hsq a ha) hfix hpres
  have hV : Nat.card ↥(A ⊓ Vsub B) = 4 := by
    let f : ↥(A ⊓ Vsub B) → ↥B := fun g =>
      ⟨(g : P8) 0, ((mem_Vsub.1 g.2.2).2 0).2 h0B⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨g, hgA, hgV⟩ ⟨h, hhA, hhV⟩ hgh
        have h0 : g 0 = h 0 := congrArg Subtype.val hgh
        obtain ⟨u, -, hu⟩ := hreg 0 (g 0)
        have e1 := hu g ⟨hgA, rfl⟩
        have e2 := hu h ⟨hhA, h0.symm⟩
        exact Subtype.ext (e1.trans e2.symm)
      · rintro ⟨j, hj⟩
        obtain ⟨a, ⟨haA, ha0⟩, -⟩ := hreg 0 j
        exact ⟨⟨a, haA, hmem a haA (ha0 ▸ hj)⟩, Subtype.ext ha0⟩
    rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact cls_card_blocks3 B hB
  exact cls_rk_of_card (n := 2) (by rw [hcard]; norm_num) (by rw [hV]; norm_num)

private theorem cls_dts_conj (γ : P8) {S : Finset (Fin 8)} {c : P8} (hc : c ∈ dts S) :
    γ * c * γ⁻¹ ∈ dts (S.map γ.toEmbedding) := by
  obtain ⟨a, b, c', d, h1, h2, h3, h4, h5, h6, hS, rfl⟩ := hc
  refine ⟨γ a, γ b, γ c', γ d, γ.injective.ne h1, γ.injective.ne h2, γ.injective.ne h3,
    γ.injective.ne h4, γ.injective.ne h5, γ.injective.ne h6, ?_, ?_⟩
  · rw [← hS]
    simp [Finset.map_insert]
  · rw [Equiv.swap_apply_apply γ a b, Equiv.swap_apply_apply γ c' d]
    group

private theorem cls_dts_conj_iff (γ : P8) (S : Finset (Fin 8)) (c : P8) :
    γ * c * γ⁻¹ ∈ dts (S.map γ.toEmbedding) ↔ c ∈ dts S := by
  refine ⟨fun h => ?_, cls_dts_conj γ⟩
  have h1 := cls_dts_conj γ⁻¹ h
  have h2 : (S.map γ.toEmbedding).map (γ⁻¹).toEmbedding = S := by
    ext x
    simp [Finset.mem_map_equiv, Equiv.Perm.inv_def]
  rw [h2] at h1
  simpa [mul_assoc] using h1

private theorem cls_compl_map (γ : P8) (S : Finset (Fin 8)) :
    (S.map γ.toEmbedding)ᶜ = Sᶜ.map γ.toEmbedding := by
  ext x
  simp [Finset.mem_map_equiv]

private theorem cls_mem_map (γ : P8) (S : Finset (Fin 8)) (x : Fin 8) :
    x ∈ S.map γ.toEmbedding ↔ γ⁻¹ x ∈ S := by
  simp [Finset.mem_map_equiv, Equiv.Perm.inv_def]

private theorem cls_mem_Vsub_conj (γ : P8) (S : Finset (Fin 8)) (h : P8) :
    γ * h * γ⁻¹ ∈ Vsub (S.map γ.toEmbedding) ↔ h ∈ Vsub S := by
  rw [mem_Vsub, mem_Vsub, cls_compl_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c hc => ?_, fun x => ?_⟩
    · have hc' : γ * c * γ⁻¹ ∈ dts (S.map γ.toEmbedding) ∪ dts (Sᶜ.map γ.toEmbedding) := by
        rcases hc with hc | hc
        · exact Or.inl (cls_dts_conj γ hc)
        · exact Or.inr (cls_dts_conj γ hc)
      have := h1 _ hc'
      calc h * c = γ⁻¹ * (γ * h * γ⁻¹ * (γ * c * γ⁻¹)) * γ := by group
        _ = γ⁻¹ * (γ * c * γ⁻¹ * (γ * h * γ⁻¹)) * γ := by rw [this]
        _ = c * h := by group
    · have := h2 (γ x)
      simpa [cls_mem_map] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun c hc => ?_, fun x => ?_⟩
    · have e : γ * (γ⁻¹ * c * γ) * γ⁻¹ = c := by group
      have hc' : γ⁻¹ * c * γ ∈ dts S ∪ dts Sᶜ := by
        rcases hc with hc | hc
        · exact Or.inl ((cls_dts_conj_iff γ S _).1 (by rwa [e]))
        · exact Or.inr ((cls_dts_conj_iff γ Sᶜ _).1 (by rwa [e]))
      have := h1 _ hc'
      calc γ * h * γ⁻¹ * c = γ * (h * (γ⁻¹ * c * γ)) * γ⁻¹ := by group
        _ = γ * ((γ⁻¹ * c * γ) * h) * γ⁻¹ := by rw [this]
        _ = c * (γ * h * γ⁻¹) := by group
    · have := h2 (γ⁻¹ x)
      simpa [cls_mem_map] using this

private theorem cls_Vsub_compl (B : Finset (Fin 8)) : Vsub Bᶜ = Vsub B := by
  ext g
  rw [mem_Vsub, mem_Vsub, compl_compl, Set.union_comm]
  refine and_congr Iff.rfl (forall_congr' fun x => ?_)
  simp only [Finset.mem_compl, not_iff_not]

private theorem cls_mem_cjP {γ g : P8} {X : Subgroup P8} : g ∈ cjP γ X ↔ γ⁻¹ * g * γ ∈ X := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : γ⁻¹ * ((MulAut.conj γ).toMonoidHom h) * γ = h := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hh
  · intro h
    refine ⟨γ⁻¹ * g * γ, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private def clsDm (m : Fin 16) : P8 :=
  (if m.val % 2 = 1 then swap (0 : Fin 8) 1 else 1) *
    (if m.val / 2 % 2 = 1 then swap (2 : Fin 8) 3 else 1) *
    (if m.val / 4 % 2 = 1 then swap (4 : Fin 8) 5 else 1) *
    (if m.val / 8 % 2 = 1 then swap (6 : Fin 8) 7 else 1)

private theorem cls_dm_mem (m : Fin 16) : clsDm m ∈ D8 := by
  have h0 : swap (0 : Fin 8) 1 ∈ D8 := Subgroup.subset_closure (by simp)
  have h1 : swap (2 : Fin 8) 3 ∈ D8 := Subgroup.subset_closure (by simp)
  have h2 : swap (4 : Fin 8) 5 ∈ D8 := Subgroup.subset_closure (by simp)
  have h3 : swap (6 : Fin 8) 7 ∈ D8 := Subgroup.subset_closure (by simp)
  unfold clsDm
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;> split_ifs <;>
    first | exact one_mem _ | assumption

private theorem cls_dm_mul : ∀ m m' : Fin 16, ∃ m'' : Fin 16, clsDm m * clsDm m' = clsDm m'' := by
  decide +kernel

private theorem cls_dm_inv : ∀ m : Fin 16, (clsDm m)⁻¹ = clsDm m := by decide +kernel

private theorem cls_exists_dm {σ : P8} (hσ : σ ∈ D8) : ∃ m : Fin 16, σ = clsDm m := by
  unfold D8 at hσ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨4, by decide +kernel⟩
    · exact ⟨8, by decide +kernel⟩
  | one => exact ⟨0, by decide +kernel⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact cls_dm_mul m m'
  | inv x _ hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m, cls_dm_inv m⟩

private def clsXfin : Finset P8 :=
  (Finset.univ.filter (fun m : Fin 16 => Equiv.Perm.sign (clsDm m) = 1)).image clsDm

private theorem cls_mem_X (σ : P8) : σ ∈ D8 ⊓ alternatingGroup (Fin 8) ↔ σ ∈ clsXfin := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨m, rfl⟩ := cls_exists_dm h1
    exact Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Equiv.Perm.mem_alternatingGroup.1 h2⟩, rfl⟩
  · intro h
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 h
    exact ⟨cls_dm_mem m, Equiv.Perm.mem_alternatingGroup.2 (Finset.mem_filter.1 hm).2⟩

private theorem cls_card_Xfin : clsXfin.card = 8 := by decide +kernel

private theorem cls_card_X : Nat.card ↥(D8 ⊓ alternatingGroup (Fin 8)) = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight cls_mem_X), Nat.card_eq_fintype_card,
    Fintype.card_coe, cls_card_Xfin]

private def ClsVD (B : Finset (Fin 8)) (σ : P8) : Prop :=
  (∀ i : Fin 6, σ * clOf B i = clOf B i * σ) ∧ ∀ x, σ x ∈ B ↔ x ∈ B

private instance (B : Finset (Fin 8)) (σ : P8) : Decidable (ClsVD B σ) := by
  unfold ClsVD; infer_instance

private theorem cls_card_Xfin_V : ∀ B ∈ blocks3, (clsXfin.filter (ClsVD B)).card = 4 := by
  decide +kernel

private theorem cls_card_XV {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    Nat.card ↥(D8 ⊓ alternatingGroup (Fin 8) ⊓ Vsub B) = 4 := by
  have hmem : ∀ σ, σ ∈ D8 ⊓ alternatingGroup (Fin 8) ⊓ Vsub B ↔ σ ∈ clsXfin.filter (ClsVD B) := by
    intro σ
    rw [Finset.mem_filter, Subgroup.mem_inf, cls_mem_X, cls_mem_Vsub hB]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card, Fintype.card_coe]
  exact cls_card_Xfin_V B hB

private def ClsPS (g : P8) (B : Finset (Fin 8)) : Prop :=
  (∀ x, g x ∈ B ↔ x ∈ B) ∨ (∀ x, g x ∈ B ↔ x ∉ B)

private instance (g : P8) (B : Finset (Fin 8)) : Decidable (ClsPS g B) := by
  unfold ClsPS; infer_instance

set_option maxRecDepth 100000 in
private theorem cls_classify : ∀ B' : Finset (Fin 8), B'.card = 4 →
    ClsPS (swap 0 1 * swap 2 3) B' → ClsPS (swap 2 3 * swap 4 5) B' →
    ClsPS (swap 4 5 * swap 6 7) B' → B' ∈ blocks3 ∨ B'ᶜ ∈ blocks3 := by
  decide +kernel

private theorem cls_three_mem : swap (0 : Fin 8) 1 * swap 2 3 ∈ clsXfin ∧
    swap (2 : Fin 8) 3 * swap 4 5 ∈ clsXfin ∧ swap (4 : Fin 8) 5 * swap 6 7 ∈ clsXfin := by
  decide +kernel

theorem rk_cjP_DL {B : Finset (Fin 8)} (hB : B ∈ blocks3) (γ : P8)
    (hA : cjP γ (D8 ⊓ alternatingGroup (Fin 8)) ≤ PStab B) :
    rk ↥(cjP γ (D8 ⊓ alternatingGroup (Fin 8))) =
      rk ↥(cjP γ (D8 ⊓ alternatingGroup (Fin 8)) ⊓ Vsub B) + 1 := by
  set X : Subgroup P8 := D8 ⊓ alternatingGroup (Fin 8) with hX
  set B' : Finset (Fin 8) := B.map γ⁻¹.toEmbedding with hB'
  have hB'mem : ∀ x, x ∈ B' ↔ γ x ∈ B := fun x => by
    rw [hB', cls_mem_map, inv_inv]
  have hBB' : B'.map γ.toEmbedding = B := by
    ext x
    rw [cls_mem_map, hB'mem, perm_apply_inv]
  have hcardB' : B'.card = 4 := by
    rw [hB', Finset.card_map]
    exact cls_card_blocks3 B hB
  have hPS : ∀ σ ∈ clsXfin, ClsPS σ B' := by
    intro σ hσ
    have hσX : σ ∈ X := (cls_mem_X σ).2 hσ
    have hmem : γ * σ * γ⁻¹ ∈ cjP γ X := cls_mem_cjP.2 (by simpa [mul_assoc] using hσX)
    rcases hA hmem with h | h
    · left
      intro x
      rw [hB'mem, hB'mem]
      have := h (γ x)
      simpa using this
    · right
      intro x
      rw [hB'mem, hB'mem]
      have := h (γ x)
      simpa using this
  obtain ⟨B'', hB''3, hVB⟩ : ∃ B'' ∈ blocks3, Vsub B' = Vsub B'' := by
    rcases cls_classify B' hcardB' (hPS _ cls_three_mem.1) (hPS _ cls_three_mem.2.1)
        (hPS _ cls_three_mem.2.2) with h | h
    · exact ⟨B', h, rfl⟩
    · exact ⟨B'ᶜ, h, (cls_Vsub_compl B').symm⟩
  have hinj : Function.Injective (MulAut.conj γ).toMonoidHom := fun a b hab =>
    (MulAut.conj γ).injective hab
  have hcard1 : Nat.card ↥(cjP γ X) = 8 := by
    unfold cjP
    rw [Subgroup.card_map_of_injective hinj]
    exact cls_card_X
  have hVA : cjP γ X ⊓ Vsub B = cjP γ (X ⊓ Vsub B') := by
    ext g
    have hconj := cls_mem_Vsub_conj γ B' (γ⁻¹ * g * γ)
    rw [hBB', show γ * (γ⁻¹ * g * γ) * γ⁻¹ = g by group] at hconj
    constructor
    · rintro ⟨h1, h2⟩
      exact cls_mem_cjP.2 ⟨cls_mem_cjP.1 h1, hconj.1 h2⟩
    · intro h
      have h' := cls_mem_cjP.1 h
      exact ⟨cls_mem_cjP.2 h'.1, hconj.2 h'.2⟩
  have hcard2 : Nat.card ↥(cjP γ X ⊓ Vsub B) = 4 := by
    rw [hVA]
    unfold cjP
    rw [Subgroup.card_map_of_injective hinj, hVB]
    exact cls_card_XV hB''3
  exact cls_rk_of_card (n := 2) (by rw [hcard1]; norm_num) (by rw [hcard2]; norm_num)

end CFSG.Quasithin.A38c6
