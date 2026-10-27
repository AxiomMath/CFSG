module

public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4PatE6 {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (CK : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ) :
    Prop :=
  ∃ (a₁ a₂ : Λa) (c c' : Fin 6), a₁ ≠ a₂ ∧ GGDepED4Leaf c ∧ GGDepED4Leaf c' ∧ c ≠ c' ∧
    (∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then -1 else 0) ∧
        CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then -1 else 0) ∧
        CK (Sum.inr a₂) (Sum.inl j) = (if j.1 = c' then -1 else 0) ∧
        CK (Sum.inl j) (Sum.inr a₂) = (if j.1 = c' then -1 else 0)) ∧
    CK (Sum.inr a₁) (Sum.inr a₂) = 0 ∧ CK (Sum.inr a₂) (Sum.inr a₁) = 0 ∧
    CK (Sum.inr a₁) (Sum.inr a₁) = 2 ∧ CK (Sum.inr a₂) (Sum.inr a₂) = 2

@[expose] def GGDepED4PatD6 {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (CK : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ) :
    Prop :=
  ∃ (a₁ a₂ : Λa) (c : Fin 6), a₁ ≠ a₂ ∧ GGDepED4Leaf c ∧
    (∀ j : {c : Fin 6 // GGDepED4In c},
      CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then -1 else 0) ∧
        CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then -1 else 0) ∧
        CK (Sum.inr a₂) (Sum.inl j) = 0 ∧ CK (Sum.inl j) (Sum.inr a₂) = 0) ∧
    CK (Sum.inr a₁) (Sum.inr a₂) = -1 ∧ CK (Sum.inr a₂) (Sum.inr a₁) = -1 ∧
    CK (Sum.inr a₁) (Sum.inr a₁) = 2 ∧ CK (Sum.inr a₂) (Sum.inr a₂) = 2

private instance lr6p6_decPredIn : DecidablePred GGDepED4In :=
  fun c => by unfold GGDepED4In; infer_instance

private def lr6p6_tA (n : ℕ) (i j : Fin n) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def lr6p6_tB6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) then 4
  else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def lr6p6_tD6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 3 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 3)
  then 3 else 2

private def lr6p6_tE6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
  then 3 else 2

private theorem lr6p6_a6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.A 6 p.1 p.2 = lr6p6_tA 6 p.1 p.2 := by
  decide

private theorem lr6p6_b6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.B 6 p.1 p.2 = lr6p6_tB6 p.1 p.2 := by
  decide

private theorem lr6p6_d6_apply :
    ∀ p : Fin 6 × Fin 6, ggCoxeterMatrixD 6 p.1 p.2 = lr6p6_tD6 p.1 p.2 := by
  decide

private theorem lr6p6_e6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.E₆ p.1 p.2 = lr6p6_tE6 p.1 p.2 := by
  decide

private def lr6p6_emb : Fin 4 → Fin 6 := ![1, 2, 3, 4]

private lemma lr6p6_emb_inj : Function.Injective lr6p6_emb := by decide

private def lr6p6_P (i j : Fin 4) : ℕ :=
  lr6p6_tE6 (lr6p6_emb i) (lr6p6_emb j)

private def lr6p6_g (a0 a1 a2 a3 : Fin 6) : Fin 4 → Fin 6 := ![a0, a1, a2, a3]

private lemma lr6p6_g_apply (f : Fin 4 → Fin 6) (i : Fin 4) :
    lr6p6_g (f 0) (f 1) (f 2) (f 3) i = f i := by
  fin_cases i <;> rfl

private lemma lr6p6_tD6_symm : ∀ i j : Fin 6, lr6p6_tD6 i j = lr6p6_tD6 j i := by decide

private theorem lr6p6_tD6_cls_tuple :
    ∀ a0 a1 a2 a3 : Fin 6,
      (∀ i j : Fin 4, lr6p6_tD6 (lr6p6_g a0 a1 a2 a3 i) (lr6p6_g a0 a1 a2 a3 j)
        = lr6p6_P i j) →
      ∀ t1 t2 : Fin 6, (∀ i : Fin 4, t1 ≠ lr6p6_g a0 a1 a2 a3 i) →
        (∀ i : Fin 4, t2 ≠ lr6p6_g a0 a1 a2 a3 i) → t1 ≠ t2 →
        (∃ k : Fin 4, (k = 0 ∨ k = 1 ∨ k = 3) ∧
            (∀ i : Fin 4, lr6p6_tD6 t1 (lr6p6_g a0 a1 a2 a3 i) = if i = k then 3 else 2) ∧
            (∀ i : Fin 4, lr6p6_tD6 t2 (lr6p6_g a0 a1 a2 a3 i) = 2) ∧
            lr6p6_tD6 t1 t2 = 3) ∨
        (∃ k : Fin 4, (k = 0 ∨ k = 1 ∨ k = 3) ∧
            (∀ i : Fin 4, lr6p6_tD6 t2 (lr6p6_g a0 a1 a2 a3 i) = if i = k then 3 else 2) ∧
            (∀ i : Fin 4, lr6p6_tD6 t1 (lr6p6_g a0 a1 a2 a3 i) = 2) ∧
            lr6p6_tD6 t1 t2 = 3) := by
  unfold lr6p6_g lr6p6_P lr6p6_emb
  decide +kernel

private theorem lr6p6_tD6_cls :
    ∀ f : Fin 4 → Fin 6, Function.Injective f →
      (∀ i j, lr6p6_tD6 (f i) (f j) = lr6p6_P i j) →
      ∀ t1 t2 : Fin 6, (∀ i, t1 ≠ f i) → (∀ i, t2 ≠ f i) → t1 ≠ t2 →
        (∃ k : Fin 4, (k = 0 ∨ k = 1 ∨ k = 3) ∧
            (∀ i : Fin 4, lr6p6_tD6 t1 (f i) = if i = k then 3 else 2) ∧
            (∀ i : Fin 4, lr6p6_tD6 t2 (f i) = 2) ∧
            lr6p6_tD6 t1 t2 = 3) ∨
        (∃ k : Fin 4, (k = 0 ∨ k = 1 ∨ k = 3) ∧
            (∀ i : Fin 4, lr6p6_tD6 t2 (f i) = if i = k then 3 else 2) ∧
            (∀ i : Fin 4, lr6p6_tD6 t1 (f i) = 2) ∧
            lr6p6_tD6 t1 t2 = 3) := by
  intro f _ hpat t1 t2 ht1 ht2 hne
  have hpat' : ∀ i j : Fin 4,
      lr6p6_tD6 (lr6p6_g (f 0) (f 1) (f 2) (f 3) i)
        (lr6p6_g (f 0) (f 1) (f 2) (f 3) j) = lr6p6_P i j := by
    intro i j
    rw [lr6p6_g_apply f i, lr6p6_g_apply f j]
    exact hpat i j
  have ht1' : ∀ i : Fin 4, t1 ≠ lr6p6_g (f 0) (f 1) (f 2) (f 3) i :=
    fun i h => ht1 i (h.trans (lr6p6_g_apply f i))
  have ht2' : ∀ i : Fin 4, t2 ≠ lr6p6_g (f 0) (f 1) (f 2) (f 3) i :=
    fun i h => ht2 i (h.trans (lr6p6_g_apply f i))
  rcases lr6p6_tD6_cls_tuple (f 0) (f 1) (f 2) (f 3) hpat' t1 t2 ht1' ht2' hne with
    ⟨k, hk, r1, r2, hadj⟩ | ⟨k, hk, r1, r2, hadj⟩
  · left
    refine ⟨k, hk, ?_, ?_, hadj⟩
    · intro i; rw [← lr6p6_g_apply f i]; exact r1 i
    · intro i; rw [← lr6p6_g_apply f i]; exact r2 i
  · right
    refine ⟨k, hk, ?_, ?_, hadj⟩
    · intro i; rw [← lr6p6_g_apply f i]; exact r1 i
    · intro i; rw [← lr6p6_g_apply f i]; exact r2 i

private theorem lr6p6_no_tA6_tuple :
    ¬ (∃ a0 a1 a2 a3 : Fin 6,
      ∀ i j : Fin 4, lr6p6_tA 6 (lr6p6_g a0 a1 a2 a3 i) (lr6p6_g a0 a1 a2 a3 j)
        = lr6p6_P i j) := by
  unfold lr6p6_g lr6p6_P lr6p6_emb
  decide +kernel

private theorem lr6p6_no_tB6_tuple :
    ¬ (∃ a0 a1 a2 a3 : Fin 6,
      ∀ i j : Fin 4, lr6p6_tB6 (lr6p6_g a0 a1 a2 a3 i) (lr6p6_g a0 a1 a2 a3 j)
        = lr6p6_P i j) := by
  unfold lr6p6_g lr6p6_P lr6p6_emb
  decide +kernel

private theorem lr6p6_no_tA6 :
    ¬ (∃ f : Fin 4 → Fin 6, Function.Injective f ∧
      ∀ i j, lr6p6_tA 6 (f i) (f j) = lr6p6_P i j) := by
  rintro ⟨f, -, hpat⟩
  apply lr6p6_no_tA6_tuple
  refine ⟨f 0, f 1, f 2, f 3, ?_⟩
  intro i j
  rw [lr6p6_g_apply f i, lr6p6_g_apply f j]
  exact hpat i j

private theorem lr6p6_no_tB6 :
    ¬ (∃ f : Fin 4 → Fin 6, Function.Injective f ∧
      ∀ i j, lr6p6_tB6 (f i) (f j) = lr6p6_P i j) := by
  rintro ⟨f, -, hpat⟩
  apply lr6p6_no_tB6_tuple
  refine ⟨f 0, f 1, f 2, f 3, ?_⟩
  intro i j
  rw [lr6p6_g_apply f i, lr6p6_g_apply f j]
  exact hpat i j

private def lr6p6_embJ : Fin 4 → {c : Fin 6 // GGDepED4In c} :=
  fun i => ⟨lr6p6_emb i, by fin_cases i <;> (unfold GGDepED4In; decide)⟩

private lemma lr6p6_embJ_inj : Function.Injective lr6p6_embJ := by
  intro a b h
  exact lr6p6_emb_inj (congrArg Subtype.val h)

private lemma lr6p6_J_val (j : {c : Fin 6 // GGDepED4In c}) :
    j.1 = 1 ∨ j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 4 := by
  revert j
  decide +kernel

private lemma lr6p6_J_exists (j : {c : Fin 6 // GGDepED4In c}) :
    ∃ i : Fin 4, lr6p6_embJ i = j := by
  obtain ⟨v, hv⟩ := j
  rcases lr6p6_J_val ⟨v, hv⟩ with h | h | h | h
  · exact ⟨0, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨1, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨2, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨3, Subtype.ext (by rw [h]; rfl)⟩

lemma lr6p6_cartanE6_off (i j : Fin 6) (hij : i ≠ j) :
    CartanMatrix.E 6 i j = 0 ∨ CartanMatrix.E 6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

lemma lr6p6_coxeterE6_off (i j : Fin 6) (hij : i ≠ j) :
    CoxeterMatrix.E₆ i j = if CartanMatrix.E 6 i j = 0 then 2 else 3 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma lr6p6_mod3_zero_three {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 3) (hcn : c < 0) (hcn' : c' < 0)
    (he : e = 0 ∨ e = -1) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((3 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases he with rfl | rfl
  · rcases int_neg_pair_of_mul_eq (Or.inr rfl) hcn hcn' h with ⟨hc1, -⟩ | ⟨hc3, -⟩
    · rw [hc1] at hc
      norm_num at hc
    · have hc'1 : c' = -1 := by nlinarith [h, hc3]
      rw [hc'1] at hc'
      norm_num at hc'
  · exact absurd hcc (by decide)

private lemma lr6p6_mod3_zero_two {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 2) (he : e = 0) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc', he] at hcc
  exact absurd hcc (by decide)

private lemma lr6p6_mod3_neg_two_three {c c' : ℤ} {k : ℤ}
    (hc : (c : ZMod 3) = ((-1 : ℤ) : ZMod 3)) (hc' : (c' : ZMod 3) = ((-1 : ℤ) : ZMod 3))
    (h : c * c' = k) (hk : k = 2 ∨ k = 3) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((k : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases hk with rfl | rfl <;> exact absurd hcc (by decide)

lemma lr6p6_MJ {ι : Type*} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {emb : {c : Fin 6 // GGDepED4In c} → ι}
    (hemb : Function.Injective emb)
    (hJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (C (emb i) (emb j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3)) :
    ∀ i j : {c : Fin 6 // GGDepED4In c},
      M (emb i) (emb j) = CoxeterMatrix.E₆ i.1 j.1 := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal (emb i), (CoxeterMatrix.E₆).diagonal i.1]
  · have hne : emb i ≠ emb j := fun h => hij (hemb h)
    have hkl : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hJij := hJ i j
    have hJji : (C (emb j) (emb i) : ZMod 3) = ((CartanMatrix.E 6) i.1 j.1 : ZMod 3) := by
      have hs : CartanMatrix.E 6 j.1 i.1 = CartanMatrix.E 6 i.1 j.1 :=
        congrFun (congrFun (CartanMatrix.E_transpose 6) i.1) j.1
      rw [hJ j i, hs]
    have hcase := hC.2 (emb i) (emb j) hne
    rw [lr6p6_coxeterE6_off i.1 j.1 hkl]
    rcases lr6p6_cartanE6_off i.1 j.1 hkl with he | he
    · rw [if_pos he]
      rcases hcase with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exact hm
      · exfalso
        rw [h1, he] at hJij
        norm_num at hJij
      · exfalso
        exact lr6p6_mod3_zero_two hJij hJji h1 he
      · exfalso
        exact lr6p6_mod3_zero_three hJij hJji h1 h2 h3 (Or.inl he)
    · rw [if_neg (by omega)]
      rcases hcase with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exfalso
        rw [h1, he] at hJij
        norm_num at hJij
      · exact hm
      · exfalso
        exact lr6p6_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inl rfl)
      · exfalso
        exact lr6p6_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inr rfl)

lemma lr6p6_cartan_of_two {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h2 : M u v = 2) :
    C u v = 0 ∧ C v u = 0 := by
  rcases hC.entries huv with ⟨-, h1, h2'⟩ | ⟨hm, -, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
  · exact ⟨h1, h2'⟩
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega

lemma lr6p6_cartan_of_three {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h3 : M u v = 3) :
    C u v = -1 ∧ C v u = -1 := by
  rcases hC.entries huv with ⟨hm, -, -⟩ | ⟨-, h1, h2'⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [h3] at hm; omega
  · exact ⟨h1, h2'⟩
  · rw [h3] at hm; omega
  · rw [h3] at hm; omega

theorem ggDepED4_pattern6 {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)}
    {CK : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3)) :
    GGDepED4PatE6 CK ∨ GGDepED4PatD6 CK := by
  classical
  have hMA : ∀ i j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl i) (Sum.inl j) = CoxeterMatrix.E₆ i.1 j.1 :=
    lr6p6_MJ hCK (emb := Sum.inl) (fun _ _ h => Sum.inl.inj h) (fun i j => hJ i j)
  have hcardJ : Fintype.card {c : Fin 6 // GGDepED4In c} = 4 := by
    have hbij : Function.Bijective lr6p6_embJ := ⟨lr6p6_embJ_inj, lr6p6_J_exists⟩
    have h := Fintype.card_congr (Equiv.ofBijective lr6p6_embJ hbij)
    rw [Fintype.card_fin] at h
    exact h.symm
  have hcardLa : Fintype.card Λa = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hΛa
  have hcardι : Fintype.card ({c : Fin 6 // GGDepED4In c} ⊕ Λa) = 6 := by
    rw [Fintype.card_sum, hcardJ, hcardLa]
  obtain ⟨a₁, a₂, hne, -⟩ := Nat.card_eq_two_iff.mp hΛa
  have hWKy := hWK
  rcases hWK with ⟨n, e, hn, hcase⟩ | ⟨e, hE⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · have hn6 : n = 6 := by
      have h := Fintype.card_congr e
      rw [Fintype.card_fin] at h
      omega
    subst n
    let ψ : {c : Fin 6 // GGDepED4In c} → Fin 6 := fun j => e.symm (Sum.inl j)
    let tt : Λa → Fin 6 := fun a => e.symm (Sum.inr a)
    let f : Fin 4 → Fin 6 := fun i => ψ (lr6p6_embJ i)
    have hf_inj : Function.Injective f := by
      intro x y h
      exact lr6p6_embJ_inj (Sum.inl.inj (e.symm.injective h))
    rcases hcase with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · exfalso
      have hpattern : ∀ i j : Fin 4, lr6p6_tA 6 (f i) (f j) = lr6p6_P i j := by
        intro i j
        have h1 : MK (Sum.inl (lr6p6_embJ i)) (Sum.inl (lr6p6_embJ j)) =
            CoxeterMatrix.A 6 (f i) (f j) := by
          rw [hA, CoxeterMatrix.reindex_apply]
        calc lr6p6_tA 6 (f i) (f j)
            = CoxeterMatrix.A 6 (f i) (f j) := (lr6p6_a6_apply (f i, f j)).symm
          _ = MK (Sum.inl (lr6p6_embJ i)) (Sum.inl (lr6p6_embJ j)) := h1.symm
          _ = CoxeterMatrix.E₆ (lr6p6_embJ i).1 (lr6p6_embJ j).1 := hMA _ _
          _ = lr6p6_tE6 (lr6p6_emb i) (lr6p6_emb j) :=
              lr6p6_e6_apply (lr6p6_emb i, lr6p6_emb j)
          _ = lr6p6_P i j := rfl
      exact lr6p6_no_tA6 ⟨f, hf_inj, hpattern⟩
    · exfalso
      have hpattern : ∀ i j : Fin 4, lr6p6_tB6 (f i) (f j) = lr6p6_P i j := by
        intro i j
        have h1 : MK (Sum.inl (lr6p6_embJ i)) (Sum.inl (lr6p6_embJ j)) =
            CoxeterMatrix.B 6 (f i) (f j) := by
          rw [hB, CoxeterMatrix.reindex_apply]
        calc lr6p6_tB6 (f i) (f j)
            = CoxeterMatrix.B 6 (f i) (f j) := (lr6p6_b6_apply (f i, f j)).symm
          _ = MK (Sum.inl (lr6p6_embJ i)) (Sum.inl (lr6p6_embJ j)) := h1.symm
          _ = CoxeterMatrix.E₆ (lr6p6_embJ i).1 (lr6p6_embJ j).1 := hMA _ _
          _ = lr6p6_tE6 (lr6p6_emb i) (lr6p6_emb j) :=
              lr6p6_e6_apply (lr6p6_emb i, lr6p6_emb j)
          _ = lr6p6_P i j := rfl
      exact lr6p6_no_tB6 ⟨f, hf_inj, hpattern⟩
    · have hpattern : ∀ i j : Fin 4, lr6p6_tD6 (f i) (f j) = lr6p6_P i j := by
        intro i j
        have h1 : MK (Sum.inl (lr6p6_embJ i)) (Sum.inl (lr6p6_embJ j)) =
            ggCoxeterMatrixD 6 (f i) (f j) := by
          rw [hD, CoxeterMatrix.reindex_apply]
        calc lr6p6_tD6 (f i) (f j)
            = ggCoxeterMatrixD 6 (f i) (f j) := (lr6p6_d6_apply (f i, f j)).symm
          _ = MK (Sum.inl (lr6p6_embJ i)) (Sum.inl (lr6p6_embJ j)) := h1.symm
          _ = CoxeterMatrix.E₆ (lr6p6_embJ i).1 (lr6p6_embJ j).1 := hMA _ _
          _ = lr6p6_tE6 (lr6p6_emb i) (lr6p6_emb j) :=
              lr6p6_e6_apply (lr6p6_emb i, lr6p6_emb j)
          _ = lr6p6_P i j := rfl
      have hrow : ∀ (a : Λa) (k : Fin 4),
          (∀ i : Fin 4, lr6p6_tD6 (tt a) (f i) = if i = k then 3 else 2) →
          ∀ j : {c : Fin 6 // GGDepED4In c},
            CK (Sum.inr a) (Sum.inl j) = (if j.1 = lr6p6_emb k then -1 else 0) ∧
              CK (Sum.inl j) (Sum.inr a) = (if j.1 = lr6p6_emb k then -1 else 0) := by
        intro a k hkrow j
        obtain ⟨i, hi⟩ := lr6p6_J_exists j
        have hfi : f i = ψ j := by rw [← hi]
        have hM : MK (Sum.inr a) (Sum.inl j) = if i = k then 3 else 2 := by
          calc MK (Sum.inr a) (Sum.inl j)
              = ggCoxeterMatrixD 6 (tt a) (ψ j) := by rw [hD, CoxeterMatrix.reindex_apply]
            _ = lr6p6_tD6 (tt a) (ψ j) := lr6p6_d6_apply (tt a, ψ j)
            _ = lr6p6_tD6 (tt a) (f i) := by rw [hfi]
            _ = if i = k then 3 else 2 := hkrow i
        have hiff : (j = lr6p6_embJ k) ↔ (i = k) := by
          rw [← hi]
          exact ⟨fun h => lr6p6_embJ_inj h, fun h => by rw [h]⟩
        have hiffc : (j = lr6p6_embJ k) ↔ (j.1 = lr6p6_emb k) := by
          rw [Subtype.ext_iff]
          rfl
        have hM' : MK (Sum.inr a) (Sum.inl j) = if j.1 = lr6p6_emb k then 3 else 2 := by
          rw [hM]
          by_cases hik : i = k
          · have hjk : j.1 = lr6p6_emb k := hiffc.mp (hiff.mpr hik)
            rw [if_pos hik, if_pos hjk]
          · have hjk : ¬ j.1 = lr6p6_emb k := fun h => hik (hiff.mp (hiffc.mpr h))
            rw [if_neg hik, if_neg hjk]
        by_cases hjk : j.1 = lr6p6_emb k
        · have h3 : MK (Sum.inr a) (Sum.inl j) = 3 := by rw [hM', if_pos hjk]
          have hres := lr6p6_cartan_of_three hCK (Sum.inr_ne_inl) h3
          rw [if_pos hjk]
          exact hres
        · have h2 : MK (Sum.inr a) (Sum.inl j) = 2 := by rw [hM', if_neg hjk]
          have hres := lr6p6_cartan_of_two hCK (Sum.inr_ne_inl) h2
          rw [if_neg hjk]
          exact hres
      have hrow0 : ∀ (a : Λa),
          (∀ i : Fin 4, lr6p6_tD6 (tt a) (f i) = 2) →
          ∀ j : {c : Fin 6 // GGDepED4In c},
            CK (Sum.inr a) (Sum.inl j) = 0 ∧ CK (Sum.inl j) (Sum.inr a) = 0 := by
        intro a hkrow j
        obtain ⟨i, hi⟩ := lr6p6_J_exists j
        have hfi : ψ j = f i := by rw [← hi]
        have hM : MK (Sum.inr a) (Sum.inl j) = 2 := by
          have h1 : MK (Sum.inr a) (Sum.inl j) =
              ggCoxeterMatrixD 6 (tt a) (ψ j) := by rw [hD, CoxeterMatrix.reindex_apply]
          rw [h1, lr6p6_d6_apply (tt a, ψ j), hfi]
          exact hkrow i
        exact lr6p6_cartan_of_two hCK (Sum.inr_ne_inl) hM
      have hbuild : ∀ (x y : Λa) (k : Fin 4), (k = 0 ∨ k = 1 ∨ k = 3) →
          (∀ i : Fin 4, lr6p6_tD6 (tt x) (f i) = if i = k then 3 else 2) →
          (∀ i : Fin 4, lr6p6_tD6 (tt y) (f i) = 2) →
          lr6p6_tD6 (tt x) (tt y) = 3 → x ≠ y → GGDepED4PatD6 CK := by
        intro x y k hk hx hy hxy hxyne
        have h1 := hrow x k hx
        have h2 := hrow0 y hy
        have hMxy : MK (Sum.inr x) (Sum.inr y) = 3 := by
          calc MK (Sum.inr x) (Sum.inr y)
              = ggCoxeterMatrixD 6 (tt x) (tt y) := by rw [hD, CoxeterMatrix.reindex_apply]
            _ = lr6p6_tD6 (tt x) (tt y) := lr6p6_d6_apply (tt x, tt y)
            _ = 3 := hxy
        have h12 := lr6p6_cartan_of_three hCK (fun h => hxyne (Sum.inr.inj h)) hMxy
        refine ⟨x, y, lr6p6_emb k, hxyne, ?_, ?_, h12.1, h12.2, ?_, ?_⟩
        · rcases hk with rfl | rfl | rfl <;> (unfold GGDepED4Leaf; decide)
        · intro j
          exact ⟨(h1 j).1, (h1 j).2, (h2 j).1, (h2 j).2⟩
        · exact hCK.1 (Sum.inr x)
        · exact hCK.1 (Sum.inr y)
      rcases lr6p6_tD6_cls f hf_inj hpattern (tt a₁) (tt a₂)
          (fun i h => Sum.inr_ne_inl (e.symm.injective h))
          (fun i h => Sum.inr_ne_inl (e.symm.injective h))
          (fun h => hne (Sum.inr.inj (e.symm.injective h))) with hcls | hcls
      · obtain ⟨k, hk, hrow1, hrow2, hnadj⟩ := hcls
        exact Or.inr (hbuild a₁ a₂ k hk hrow1 hrow2 hnadj hne)
      · obtain ⟨k, hk, hrow2, hrow1, hnadj⟩ := hcls
        exact Or.inr (hbuild a₂ a₁ k hk hrow2 hrow1
          (by rw [lr6p6_tD6_symm (tt a₂) (tt a₁)]; exact hnadj)
          (fun h => hne h.symm))
  · exact Or.inl (ggDepED4_pattern2 hΛa hWKy hCK ⟨e, hE⟩ hJ)
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin] at h
    omega

end CFSG.StandardType

end
