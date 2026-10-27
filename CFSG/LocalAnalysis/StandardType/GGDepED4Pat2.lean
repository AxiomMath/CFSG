module

public import CFSG.LocalAnalysis.StandardType.GGDepED4Defs
public import CFSG.LocalAnalysis.StandardType.GGDepEPattern

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nD4Q_tE6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
  then 3 else 2

private theorem l05nD4Q_e6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.E₆ p.1 p.2 = l05nD4Q_tE6 p.1 p.2 := by
  decide

private def l05nD4Q_emb : Fin 4 → Fin 6 := ![1, 2, 3, 4]

private lemma l05nD4Q_emb_inj : Function.Injective l05nD4Q_emb := by decide

private def l05nD4Q_P (i j : Fin 4) : ℕ :=
  l05nD4Q_tE6 (l05nD4Q_emb i) (l05nD4Q_emb j)

private theorem l05nD4Q_cls :
    ∀ f : Fin 4 → Fin 6, Function.Injective f →
      (∀ i j, l05nD4Q_tE6 (f i) (f j) = l05nD4Q_P i j) →
      ∀ t1 t2 : Fin 6, (∀ i, t1 ≠ f i) → (∀ i, t2 ≠ f i) → t1 ≠ t2 →
        ∃ k k' : Fin 4, (k = 0 ∨ k = 1 ∨ k = 3) ∧ (k' = 0 ∨ k' = 1 ∨ k' = 3) ∧ k ≠ k' ∧
          (∀ i, l05nD4Q_tE6 t1 (f i) = if i = k then 3 else 2) ∧
          (∀ i, l05nD4Q_tE6 t2 (f i) = if i = k' then 3 else 2) ∧
          l05nD4Q_tE6 t1 t2 = 2 := by
  decide +kernel

private instance l05nD4Q_decPredIn : DecidablePred GGDepED4In :=
  fun c => by unfold GGDepED4In; infer_instance

private def l05nD4Q_embJ : Fin 4 → {c : Fin 6 // GGDepED4In c} :=
  fun i => ⟨l05nD4Q_emb i, by fin_cases i <;> (unfold GGDepED4In; decide)⟩

private lemma l05nD4Q_embJ_inj : Function.Injective l05nD4Q_embJ := by
  intro a b h
  exact l05nD4Q_emb_inj (congrArg Subtype.val h)

private lemma l05nD4Q_J_val (j : {c : Fin 6 // GGDepED4In c}) :
    j.1 = 1 ∨ j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 4 := by
  revert j
  decide +kernel

private lemma l05nD4Q_J_exists (j : {c : Fin 6 // GGDepED4In c}) :
    ∃ i : Fin 4, l05nD4Q_embJ i = j := by
  obtain ⟨v, hv⟩ := j
  rcases l05nD4Q_J_val ⟨v, hv⟩ with h | h | h | h
  · exact ⟨0, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨1, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨2, Subtype.ext (by rw [h]; rfl)⟩
  · exact ⟨3, Subtype.ext (by rw [h]; rfl)⟩

private lemma l05nD4Q_cartanE6_off (i j : Fin 6) (hij : i ≠ j) :
    CartanMatrix.E 6 i j = 0 ∨ CartanMatrix.E 6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma l05nD4Q_coxeterE6_off (i j : Fin 6) (hij : i ≠ j) :
    CoxeterMatrix.E₆ i j = if CartanMatrix.E 6 i j = 0 then 2 else 3 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma l05nD4Q_mod3_zero_three {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
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

private lemma l05nD4Q_mod3_zero_two {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 2) (he : e = 0) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc', he] at hcc
  exact absurd hcc (by decide)

private lemma l05nD4Q_mod3_neg_two_three {c c' : ℤ} {k : ℤ}
    (hc : (c : ZMod 3) = ((-1 : ℤ) : ZMod 3)) (hc' : (c' : ZMod 3) = ((-1 : ℤ) : ZMod 3))
    (h : c * c' = k) (hk : k = 2 ∨ k = 3) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((k : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases hk with rfl | rfl <;> exact absurd hcc (by decide)

private lemma l05nD4Q_MJ {ι : Type*} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
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
    rw [l05nD4Q_coxeterE6_off i.1 j.1 hkl]
    rcases l05nD4Q_cartanE6_off i.1 j.1 hkl with he | he
    · rw [if_pos he]
      rcases hcase with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exact hm
      · exfalso
        rw [h1, he] at hJij
        norm_num at hJij
      · exfalso
        exact l05nD4Q_mod3_zero_two hJij hJji h1 he
      · exfalso
        exact l05nD4Q_mod3_zero_three hJij hJji h1 h2 h3 (Or.inl he)
    · rw [if_neg (by omega)]
      rcases hcase with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exfalso
        rw [h1, he] at hJij
        norm_num at hJij
      · exact hm
      · exfalso
        exact l05nD4Q_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inl rfl)
      · exfalso
        exact l05nD4Q_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inr rfl)

private lemma l05nD4Q_cartan_of_two {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h2 : M u v = 2) :
    C u v = 0 ∧ C v u = 0 := by
  rcases hC.entries huv with ⟨-, h1, h2'⟩ | ⟨hm, -, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
  · exact ⟨h1, h2'⟩
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega

private lemma l05nD4Q_cartan_of_three {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h3 : M u v = 3) :
    C u v = -1 ∧ C v u = -1 := by
  rcases hC.entries huv with ⟨hm, -, -⟩ | ⟨-, h1, h2'⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [h3] at hm; omega
  · exact ⟨h1, h2'⟩
  · rw [h3] at hm; omega
  · rw [h3] at hm; omega

theorem ggDepED4_pattern2 {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa)}
    {CK : Matrix ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ({c : Fin 6 // GGDepED4In c} ⊕ Λa) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hE : ∃ eK : Fin 6 ≃ ({c : Fin 6 // GGDepED4In c} ⊕ Λa), MK = CoxeterMatrix.E₆.reindex eK)
    (hJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK (Sum.inl i) (Sum.inl j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3)) :
    ∃ (a₁ a₂ : Λa) (c c' : Fin 6), a₁ ≠ a₂ ∧ GGDepED4Leaf c ∧ GGDepED4Leaf c' ∧ c ≠ c' ∧
      (∀ j : {c : Fin 6 // GGDepED4In c},
        CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then -1 else 0) ∧
          CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then -1 else 0) ∧
          CK (Sum.inr a₂) (Sum.inl j) = (if j.1 = c' then -1 else 0) ∧
          CK (Sum.inl j) (Sum.inr a₂) = (if j.1 = c' then -1 else 0)) ∧
      CK (Sum.inr a₁) (Sum.inr a₂) = 0 ∧ CK (Sum.inr a₂) (Sum.inr a₁) = 0 ∧
      CK (Sum.inr a₁) (Sum.inr a₁) = 2 ∧ CK (Sum.inr a₂) (Sum.inr a₂) = 2 := by
  obtain ⟨eK, hEeq⟩ := hE
  have hMJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      MK (Sum.inl i) (Sum.inl j) = CoxeterMatrix.E₆ i.1 j.1 :=
    l05nD4Q_MJ hCK (emb := Sum.inl) (fun _ _ h => Sum.inl.inj h) (fun i j => hJ i j)
  obtain ⟨a₁, a₂, hne, huniv⟩ := Nat.card_eq_two_iff.mp hΛa
  let ψ : {c : Fin 6 // GGDepED4In c} → Fin 6 := fun j => eK.symm (Sum.inl j)
  let tt : Λa → Fin 6 := fun a => eK.symm (Sum.inr a)
  let f : Fin 4 → Fin 6 := fun i => ψ (l05nD4Q_embJ i)
  have hf_inj : Function.Injective f := by
    intro a b h
    exact l05nD4Q_embJ_inj (Sum.inl.inj (eK.symm.injective h))
  have hpattern : ∀ i j : Fin 4, l05nD4Q_tE6 (f i) (f j) = l05nD4Q_P i j := by
    intro i j
    have h1 : MK (Sum.inl (l05nD4Q_embJ i)) (Sum.inl (l05nD4Q_embJ j)) =
        CoxeterMatrix.E₆ (f i) (f j) := by
      rw [hEeq, CoxeterMatrix.reindex_apply]
    calc l05nD4Q_tE6 (f i) (f j)
        = CoxeterMatrix.E₆ (f i) (f j) := (l05nD4Q_e6_apply (f i, f j)).symm
      _ = MK (Sum.inl (l05nD4Q_embJ i)) (Sum.inl (l05nD4Q_embJ j)) := h1.symm
      _ = CoxeterMatrix.E₆ (l05nD4Q_embJ i).1 (l05nD4Q_embJ j).1 := hMJ _ _
      _ = l05nD4Q_tE6 (l05nD4Q_emb i) (l05nD4Q_emb j) :=
            l05nD4Q_e6_apply (l05nD4Q_emb i, l05nD4Q_emb j)
      _ = l05nD4Q_P i j := rfl
  obtain ⟨k, k', hk, hk', hkk', hrow1, hrow2, hnadj⟩ :=
    l05nD4Q_cls f hf_inj hpattern (tt a₁) (tt a₂)
      (fun i h => Sum.inr_ne_inl (eK.symm.injective h))
      (fun i h => Sum.inr_ne_inl (eK.symm.injective h))
      (fun h => hne (Sum.inr.inj (eK.symm.injective h)))
  have hrow : ∀ (a : Λa) (k : Fin 4),
      (∀ i : Fin 4, l05nD4Q_tE6 (tt a) (f i) = if i = k then 3 else 2) →
      ∀ j : {c : Fin 6 // GGDepED4In c},
        CK (Sum.inr a) (Sum.inl j) = (if j.1 = l05nD4Q_emb k then -1 else 0) ∧
        CK (Sum.inl j) (Sum.inr a) = (if j.1 = l05nD4Q_emb k then -1 else 0) := by
    intro a k hkrow j
    obtain ⟨i, hi⟩ := l05nD4Q_J_exists j
    have hfi : f i = ψ j := by rw [← hi]
    have hM : MK (Sum.inr a) (Sum.inl j) = if i = k then 3 else 2 := by
      calc MK (Sum.inr a) (Sum.inl j)
          = CoxeterMatrix.E₆ (tt a) (ψ j) := by rw [hEeq, CoxeterMatrix.reindex_apply]
        _ = l05nD4Q_tE6 (tt a) (ψ j) := l05nD4Q_e6_apply (tt a, ψ j)
        _ = l05nD4Q_tE6 (tt a) (f i) := by rw [hfi]
        _ = if i = k then 3 else 2 := hkrow i
    have hiff : (j = l05nD4Q_embJ k) ↔ (i = k) := by
      rw [← hi]
      exact ⟨fun h => l05nD4Q_embJ_inj h, fun h => by rw [h]⟩
    have hiffc : (j = l05nD4Q_embJ k) ↔ (j.1 = l05nD4Q_emb k) := by
      rw [Subtype.ext_iff]
      rfl
    have hM' : MK (Sum.inr a) (Sum.inl j) = if j.1 = l05nD4Q_emb k then 3 else 2 := by
      rw [hM]
      by_cases hik : i = k
      · have hjk : j.1 = l05nD4Q_emb k := hiffc.mp (hiff.mpr hik)
        rw [if_pos hik, if_pos hjk]
      · have hjk : ¬ j.1 = l05nD4Q_emb k := fun h => hik (hiff.mp (hiffc.mpr h))
        rw [if_neg hik, if_neg hjk]
    by_cases hjk : j.1 = l05nD4Q_emb k
    · have h3 : MK (Sum.inr a) (Sum.inl j) = 3 := by rw [hM', if_pos hjk]
      have hres := l05nD4Q_cartan_of_three hCK (Sum.inr_ne_inl) h3
      rw [if_pos hjk]; exact hres
    · have h2 : MK (Sum.inr a) (Sum.inl j) = 2 := by rw [hM', if_neg hjk]
      have hres := l05nD4Q_cartan_of_two hCK (Sum.inr_ne_inl) h2
      rw [if_neg hjk]; exact hres
  have h1 := hrow a₁ k hrow1
  have h2 := hrow a₂ k' hrow2
  have hM12 : MK (Sum.inr a₁) (Sum.inr a₂) = 2 := by
    rw [hEeq, CoxeterMatrix.reindex_apply, l05nD4Q_e6_apply (tt a₁, tt a₂), hnadj]
  have h12 := l05nD4Q_cartan_of_two hCK (fun h => hne (Sum.inr.inj h)) hM12
  refine ⟨a₁, a₂, l05nD4Q_emb k, l05nD4Q_emb k', hne, ?_, ?_, ?_, ?_, h12.1, h12.2, ?_, ?_⟩
  · rcases hk with rfl | rfl | rfl <;> (unfold GGDepED4Leaf; decide)
  · rcases hk' with rfl | rfl | rfl <;> (unfold GGDepED4Leaf; decide)
  · exact fun h => hkk' (l05nD4Q_emb_inj h)
  · intro j
    exact ⟨(h1 j).1, (h1 j).2, (h2 j).1, (h2 j).2⟩
  · exact hCK.1 (Sum.inr a₁)
  · exact hCK.1 (Sum.inr a₂)

end CFSG.StandardType

end
