module

public import CFSG.LocalAnalysis.StandardType.GGDepED4Defs
public import CFSG.LocalAnalysis.StandardType.GGDepEPattern
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nD4P_tE6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
  then 3 else 2

private def l05nD4P_tA5 (i j : Fin 5) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nD4P_tB5 (i j : Fin 5) : ℕ :=
  if i = j then 1
  else if (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) then 4
  else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nD4P_tD5 (i j : Fin 5) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2)
  then 3 else 2

private theorem l05nD4P_a5_apply :
    ∀ p : Fin 5 × Fin 5, CoxeterMatrix.A 5 p.1 p.2 = l05nD4P_tA5 p.1 p.2 := by decide

private theorem l05nD4P_b5_apply :
    ∀ p : Fin 5 × Fin 5, CoxeterMatrix.B 5 p.1 p.2 = l05nD4P_tB5 p.1 p.2 := by decide

private theorem l05nD4P_d5_apply :
    ∀ p : Fin 5 × Fin 5, ggCoxeterMatrixD 5 p.1 p.2 = l05nD4P_tD5 p.1 p.2 := by decide

private theorem l05nD4P_e6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.E₆ p.1 p.2 = l05nD4P_tE6 p.1 p.2 := by decide

private def l05nD4P_emb (i : Fin 4) : Fin 6 := ⟨i.val + 1, by omega⟩

private lemma l05nD4P_emb_inj : Function.Injective l05nD4P_emb := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [l05nD4P_emb] at this
  omega

private abbrev l05nD4P_J := {c : Fin 6 // GGDepED4In c}

private def l05nD4P_posEquiv : Fin 4 ≃ l05nD4P_J where
  toFun i := ⟨l05nD4P_emb i, by
    have h := i.isLt
    simp only [GGDepED4In]
    constructor
    · intro hh
      have h2 : i.val + 1 = 0 := by simpa [l05nD4P_emb] using congrArg Fin.val hh
      omega
    · intro hh
      have h2 : i.val + 1 = 5 := by simpa [l05nD4P_emb] using congrArg Fin.val hh
      omega⟩
  invFun j := ⟨j.1.val - 1, by
    have h := j.2
    simp only [GGDepED4In] at h
    have := j.1.isLt
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp [l05nD4P_emb]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have h := j.2
    simp only [GGDepED4In] at h
    have := j.1.isLt
    simp [l05nD4P_emb]
    omega

private lemma l05nD4P_posEquiv_val (i : Fin 4) :
    (l05nD4P_posEquiv i).1 = l05nD4P_emb i := rfl

private def l05nD4P_P (i j : Fin 4) : ℕ := l05nD4P_tE6 (l05nD4P_emb i) (l05nD4P_emb j)

private def l05nD4P_g (a0 a1 a2 a3 : Fin 5) : Fin 4 → Fin 5 := ![a0, a1, a2, a3]

private lemma l05nD4P_g_apply (f : Fin 4 → Fin 5) (i : Fin 4) :
    l05nD4P_g (f 0) (f 1) (f 2) (f 3) i = f i := by fin_cases i <;> rfl

private def l05nD4P_cond (k : Fin 4) : Prop := k.val = 0 ∨ k.val = 1 ∨ k.val = 3

private def l05nD4P_concl (tab : Fin 5 → Fin 5 → ℕ) (cond : Fin 4 → Prop)
    (a0 a1 a2 a3 : Fin 5) (t : Fin 5) : Prop :=
  ∃ k : Fin 4, cond k ∧ ∀ i : Fin 4,
    tab t (l05nD4P_g a0 a1 a2 a3 i) = if i = k then 3 else 2

private theorem l05nD4P_cls_A5 :
    ∀ a0 a1 a2 a3 : Fin 5,
      (∀ i j : Fin 4, l05nD4P_tA5 (l05nD4P_g a0 a1 a2 a3 i) (l05nD4P_g a0 a1 a2 a3 j)
        = l05nD4P_P i j) →
      ∀ t : Fin 5, (∀ i : Fin 4, t ≠ l05nD4P_g a0 a1 a2 a3 i) →
        l05nD4P_concl l05nD4P_tA5 l05nD4P_cond a0 a1 a2 a3 t := by
  unfold l05nD4P_concl l05nD4P_cond l05nD4P_P l05nD4P_emb l05nD4P_g
  decide +kernel

private theorem l05nD4P_cls_B5 :
    ∀ a0 a1 a2 a3 : Fin 5,
      (∀ i j : Fin 4, l05nD4P_tB5 (l05nD4P_g a0 a1 a2 a3 i) (l05nD4P_g a0 a1 a2 a3 j)
        = l05nD4P_P i j) →
      ∀ t : Fin 5, (∀ i : Fin 4, t ≠ l05nD4P_g a0 a1 a2 a3 i) →
        l05nD4P_concl l05nD4P_tB5 l05nD4P_cond a0 a1 a2 a3 t := by
  unfold l05nD4P_concl l05nD4P_cond l05nD4P_P l05nD4P_emb l05nD4P_g
  decide +kernel

private theorem l05nD4P_cls_D5 :
    ∀ a0 a1 a2 a3 : Fin 5,
      (∀ i j : Fin 4, l05nD4P_tD5 (l05nD4P_g a0 a1 a2 a3 i) (l05nD4P_g a0 a1 a2 a3 j)
        = l05nD4P_P i j) →
      ∀ t : Fin 5, (∀ i : Fin 4, t ≠ l05nD4P_g a0 a1 a2 a3 i) →
        l05nD4P_concl l05nD4P_tD5 l05nD4P_cond a0 a1 a2 a3 t := by
  unfold l05nD4P_concl l05nD4P_cond l05nD4P_P l05nD4P_emb l05nD4P_g
  decide +kernel

private lemma l05nD4P_cartanE6_off (i j : Fin 6) (hij : i ≠ j) :
    CartanMatrix.E 6 i j = 0 ∨ CartanMatrix.E 6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma l05nD4P_cartanE6_symm (i j : Fin 6) :
    CartanMatrix.E 6 i j = CartanMatrix.E 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private lemma l05nD4P_coxeterE6_off (i j : Fin 6) (hij : i ≠ j) :
    CoxeterMatrix.E₆ i j = if CartanMatrix.E 6 i j = 0 then 2 else 3 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma l05nD4P_mul_eq_three {a b : ℤ} (ha : a < 0) (hb : b < 0) (h : a * b = 3) :
    a = -1 ∨ a = -3 := by
  have hb1 : b ≤ -1 := by omega
  have hge : -3 ≤ a := by nlinarith [h, ha, hb1]
  have hle : a ≤ -1 := by omega
  interval_cases a <;> omega

private lemma l05nD4P_mod3_zero_three {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 3) (hcn : c < 0) (hcn' : c' < 0)
    (he : e = 0 ∨ e = -1) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((3 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases he with rfl | rfl
  · rcases l05nD4P_mul_eq_three hcn hcn' h with hc1 | hc3
    · rw [hc1] at hc; norm_num at hc
    · have hc'1 : c' = -1 := by nlinarith [h, hc3]
      rw [hc'1] at hc'; norm_num at hc'
  · exact absurd hcc (by decide)

private lemma l05nD4P_mod3_zero_two {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 2) (he : e = 0) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc', he] at hcc
  exact absurd hcc (by decide)

private lemma l05nD4P_mod3_neg_two_three {c c' : ℤ} {k : ℤ}
    (hc : (c : ZMod 3) = ((-1 : ℤ) : ZMod 3)) (hc' : (c' : ZMod 3) = ((-1 : ℤ) : ZMod 3))
    (h : c * c' = k) (hk : k = 2 ∨ k = 3) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((k : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases hk with rfl | rfl <;> exact absurd hcc (by decide)

private lemma l05nD4P_MJ_E6 {M : CoxeterMatrix (Option (Fin 4))}
    {C : Matrix (Option (Fin 4)) (Option (Fin 4)) ℤ} (hC : GGIntCartan M C)
    (hJ : ∀ i j : Fin 4, (C (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (l05nD4P_emb i) (l05nD4P_emb j) : ZMod 3)) :
    ∀ i j : Fin 4, M (some i) (some j) =
      CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal (some i), (CoxeterMatrix.E₆).diagonal (l05nD4P_emb i)]
  · have hne : (some i : Option (Fin 4)) ≠ some j := by simp [hij]
    have hkl : l05nD4P_emb i ≠ l05nD4P_emb j := fun h => hij (l05nD4P_emb_inj h)
    have hJij := hJ i j
    have hJji : (C (some j) (some i) : ZMod 3) =
        ((CartanMatrix.E 6) (l05nD4P_emb i) (l05nD4P_emb j) : ZMod 3) := by
      rw [hJ j i, l05nD4P_cartanE6_symm (l05nD4P_emb j) (l05nD4P_emb i)]
    have hcase := hC.2 (some i) (some j) hne
    rw [l05nD4P_coxeterE6_off (l05nD4P_emb i) (l05nD4P_emb j) hkl]
    rcases l05nD4P_cartanE6_off (l05nD4P_emb i) (l05nD4P_emb j) hkl with he | he
    · rw [if_pos he]
      rcases hcase with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exact hm
      · exfalso; rw [h1, he] at hJij; norm_num at hJij
      · exfalso; exact l05nD4P_mod3_zero_two hJij hJji h1 he
      · exfalso; exact l05nD4P_mod3_zero_three hJij hJji h1 h2 h3 (Or.inl he)
    · rw [if_neg (by omega)]
      rcases hcase with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exfalso; rw [h1, he] at hJij; norm_num at hJij
      · exact hm
      · exfalso
        exact l05nD4P_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inl rfl)
      · exfalso
        exact l05nD4P_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inr rfl)

private lemma l05nD4P_row {tab : Fin 5 → Fin 5 → ℕ} {T : CoxeterMatrix (Fin 5)}
    (hT : ∀ p : Fin 5 × Fin 5, T p.1 p.2 = tab p.1 p.2)
    {P : Fin 4 → Fin 4 → ℕ} {cond : Fin 4 → Prop}
    (he6 : ∀ i j : Fin 4, CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j) = P i j)
    (hfin : ∀ a0 a1 a2 a3 : Fin 5,
      (∀ i j : Fin 4, tab (l05nD4P_g a0 a1 a2 a3 i) (l05nD4P_g a0 a1 a2 a3 j) = P i j) →
      ∀ t : Fin 5, (∀ i : Fin 4, t ≠ l05nD4P_g a0 a1 a2 a3 i) →
        l05nD4P_concl tab cond a0 a1 a2 a3 t)
    {M : CoxeterMatrix (Option (Fin 4))} {eT : Fin 5 ≃ Option (Fin 4)}
    (hMe : M = T.reindex eT)
    (hMA : ∀ i j : Fin 4, M (some i) (some j) =
      CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j)) :
    ∃ k : Fin 4, cond k ∧ ∀ i : Fin 4, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin 4 → Fin 5 := fun i => eT.symm (some i)
  let t : Fin 5 := eT.symm none
  have ht : ∀ i : Fin 4, t ≠ f i := by
    intro i h
    have h' : (none : Option (Fin 4)) = some i := eT.symm.injective (by simpa [t, f] using h)
    simp at h'
  let g : Fin 4 → Fin 5 := l05nD4P_g (f 0) (f 1) (f 2) (f 3)
  have hg : ∀ i : Fin 4, g i = f i := l05nD4P_g_apply f
  have hP : ∀ i j : Fin 4, tab (g i) (g j) = P i j := by
    intro i j
    rw [hg i, hg j]
    calc tab (f i) (f j) = T (f i) (f j) := (hT (f i, f j)).symm
      _ = M (some i) (some j) :=
          (show T (f i) (f j) = M (some i) (some j) by
            rw [hMe, CoxeterMatrix.reindex_apply])
      _ = CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j) := hMA i j
      _ = P i j := he6 i j
  have ht' : ∀ i : Fin 4, t ≠ g i := fun i h => ht i (h.trans (hg i))
  obtain ⟨k, hk, hrow⟩ := hfin (f 0) (f 1) (f 2) (f 3) hP t ht'
  refine ⟨k, hk, fun i => ?_⟩
  have h1 : M none (some i) = tab t (f i) := by
    rw [hMe, CoxeterMatrix.reindex_apply, hT (t, f i)]
  have h2 : tab t (f i) = tab t (g i) := by rw [hg i]
  exact h1.trans (h2.trans (hrow i))

private lemma l05nD4P_cartan_of_two {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h2 : M u v = 2) :
    C u v = 0 ∧ C v u = 0 := by
  rcases hC.2 u v huv with ⟨-, h1, h2'⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · exact ⟨h1, h2'⟩
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega

private lemma l05nD4P_cartan_of_three {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h3 : M u v = 3) :
    C u v = -1 ∧ C v u = -1 := by
  rcases hC.2 u v huv with ⟨hm, -, -⟩ | ⟨-, h1, h2'⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · rw [h3] at hm; omega
  · exact ⟨h1, h2'⟩
  · rw [h3] at hm; omega
  · rw [h3] at hm; omega

private lemma l05nD4P_setup
    {MK : CoxeterMatrix (Option l05nD4P_J)}
    {CK : Matrix (Option l05nD4P_J) (Option l05nD4P_J) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : l05nD4P_J, (CK (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) i.1 j.1 : ZMod 3)) :
    ∃ (M : CoxeterMatrix (Option (Fin 4)))
      (C : Matrix (Option (Fin 4)) (Option (Fin 4)) ℤ),
      M = MK.reindex (Equiv.optionCongr l05nD4P_posEquiv).symm ∧
      GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        (∀ i j : Fin 4, (C (some i) (some j) : ZMod 3) =
          ((CartanMatrix.E 6) (l05nD4P_emb i) (l05nD4P_emb j) : ZMod 3)) ∧
        (∀ i j : Fin 4, M (some i) (some j) =
          CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j)) ∧
        (∀ i : Fin 4, C none (some i) = CK none (some (l05nD4P_posEquiv i))) ∧
        (∀ i : Fin 4, C (some i) none = CK (some (l05nD4P_posEquiv i)) none) := by
  let σ : Option (Fin 4) ≃ Option l05nD4P_J := Equiv.optionCongr l05nD4P_posEquiv
  let M : CoxeterMatrix (Option (Fin 4)) := MK.reindex σ.symm
  let C : Matrix (Option (Fin 4)) (Option (Fin 4)) ℤ := fun o o' => CK (σ o) (σ o')
  have hW : GGIsWeylMatrix M := l05nDP4_weyl_reindex hWK σ.symm
  have hC : GGIntCartan M C := by
    simpa only [M, C] using l05nBL_intCartan_reindex hCK σ
  have hJ' : ∀ i j : Fin 4, (C (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (l05nD4P_emb i) (l05nD4P_emb j) : ZMod 3) := by
    intro i j
    have h := hJ (l05nD4P_posEquiv i) (l05nD4P_posEquiv j)
    have h1 : C (some i) (some j) =
        CK (some (l05nD4P_posEquiv i)) (some (l05nD4P_posEquiv j)) := by
      show CK (σ (some i)) (σ (some j)) =
        CK (some (l05nD4P_posEquiv i)) (some (l05nD4P_posEquiv j))
      simp [σ, Equiv.optionCongr_apply]
    rw [h1, h, l05nD4P_posEquiv_val i, l05nD4P_posEquiv_val j]
  have hMA : ∀ i j : Fin 4, M (some i) (some j) =
      CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j) := l05nD4P_MJ_E6 hC hJ'
  have hcn : ∀ i : Fin 4, C none (some i) = CK none (some (l05nD4P_posEquiv i)) := by
    intro i
    show CK (σ none) (σ (some i)) = CK none (some (l05nD4P_posEquiv i))
    simp [σ, Equiv.optionCongr_apply]
  have hnc : ∀ i : Fin 4, C (some i) none = CK (some (l05nD4P_posEquiv i)) none := by
    intro i
    show CK (σ (some i)) (σ none) = CK (some (l05nD4P_posEquiv i)) none
    simp [σ, Equiv.optionCongr_apply]
  exact ⟨M, C, rfl, hW, hC, hJ', hMA, hcn, hnc⟩

private lemma l05nD4P_weyl_row {M : CoxeterMatrix (Option (Fin 4))}
    (hW : GGIsWeylMatrix M)
    (hMA : ∀ i j : Fin 4, M (some i) (some j) =
      CoxeterMatrix.E₆ (l05nD4P_emb i) (l05nD4P_emb j)) :
    ∃ k : Fin 4, l05nD4P_cond k ∧ ∀ i : Fin 4, M none (some i) = if i = k then 3 else 2 := by
  rw [GGIsWeylMatrix] at hW
  rcases hW with ⟨n, eT, hn, hcase⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ |
    ⟨eT, hMe⟩
  · have hn5 : n = 5 := by
      have hcard := Fintype.card_congr eT
      simp [Fintype.card_fin, Fintype.card_option] at hcard
      omega
    subst hn5
    rcases hcase with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · exact l05nD4P_row (T := CoxeterMatrix.A 5) (tab := l05nD4P_tA5)
        (by intro p; exact l05nD4P_a5_apply p) (P := l05nD4P_P) (cond := l05nD4P_cond)
        (by intro i j; exact l05nD4P_e6_apply (l05nD4P_emb i, l05nD4P_emb j))
        l05nD4P_cls_A5 hA hMA
    · exact l05nD4P_row (T := CoxeterMatrix.B 5) (tab := l05nD4P_tB5)
        (by intro p; exact l05nD4P_b5_apply p) (P := l05nD4P_P) (cond := l05nD4P_cond)
        (by intro i j; exact l05nD4P_e6_apply (l05nD4P_emb i, l05nD4P_emb j))
        l05nD4P_cls_B5 hB hMA
    · exact l05nD4P_row (T := ggCoxeterMatrixD 5) (tab := l05nD4P_tD5)
        (by intro p; exact l05nD4P_d5_apply p) (P := l05nD4P_P) (cond := l05nD4P_cond)
        (by intro i j; exact l05nD4P_e6_apply (l05nD4P_emb i, l05nD4P_emb j))
        l05nD4P_cls_D5 hD hMA
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard

theorem ggDepED4_pattern1 {MK : CoxeterMatrix (Option {c : Fin 6 // GGDepED4In c})}
    {CK : Matrix (Option {c : Fin 6 // GGDepED4In c}) (Option {c : Fin 6 // GGDepED4In c}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin 6 // GGDepED4In c},
      (CK (some i) (some j) : ZMod 3) = (CartanMatrix.E 6 i.1 j.1 : ZMod 3)) :
    ∃ c0 : Fin 6, GGDepED4Leaf c0 ∧ ∀ i : {c : Fin 6 // GGDepED4In c},
      CK none (some i) = (if i.1 = c0 then -1 else 0) ∧
        CK (some i) none = (if i.1 = c0 then -1 else 0) := by
  obtain ⟨M, C, -, hW, hC, hJ', hMA, hcn, hnc⟩ := l05nD4P_setup hWK hCK hJ
  obtain ⟨k, hk, hrowk⟩ := l05nD4P_weyl_row hW hMA
  have hCrow : ∀ i : Fin 4, C none (some i) = (if i = k then (-1 : ℤ) else 0) ∧
      C (some i) none = (if i = k then (-1 : ℤ) else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      have h3 : M none (some i) = 3 := by rw [hrowk i, if_pos rfl]
      simpa using l05nD4P_cartan_of_three hC (by simp) h3
    · have h2 : M none (some i) = 2 := by rw [hrowk i, if_neg hik]
      simpa [hik] using l05nD4P_cartan_of_two hC (by simp) h2
  refine ⟨l05nD4P_emb k, ?_, fun i => ?_⟩
  · have hk' : k.val = 0 ∨ k.val = 1 ∨ k.val = 3 := hk
    rcases hk' with h | h | h
    · left; apply Fin.ext; simp [l05nD4P_emb]; omega
    · right; left; apply Fin.ext; simp [l05nD4P_emb]; omega
    · right; right; apply Fin.ext; simp [l05nD4P_emb]; omega
  · set j : Fin 4 := l05nD4P_posEquiv.symm i with hj
    have hji : l05nD4P_posEquiv j = i := Equiv.apply_symm_apply l05nD4P_posEquiv i
    have hes : i.1 = l05nD4P_emb j := by
      rw [← hji]
      exact l05nD4P_posEquiv_val j
    have hiff : (i.1 = l05nD4P_emb k) ↔ (j = k) := by
      rw [hes]
      exact ⟨fun h => l05nD4P_emb_inj h, fun h => by rw [h]⟩
    have h1 : CK none (some i) = (if j = k then (-1 : ℤ) else 0) := by
      rw [← hji, ← hcn j]
      exact (hCrow j).1
    have h2 : CK (some i) none = (if j = k then (-1 : ℤ) else 0) := by
      rw [← hji, ← hnc j]
      exact (hCrow j).2
    refine ⟨?_, ?_⟩
    · rw [h1]
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos (hiff.mpr hjk)]
      · rw [if_neg hjk, if_neg (fun h => hjk (hiff.mp h))]
    · rw [h2]
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos (hiff.mpr hjk)]
      · rw [if_neg hjk, if_neg (fun h => hjk (hiff.mp h))]

end CFSG.StandardType

end
