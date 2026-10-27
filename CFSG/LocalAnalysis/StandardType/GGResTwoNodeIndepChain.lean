module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import TauCeti.GroupTheory.Coxeter.Matrix
public import CFSG.YGroups.Y443.Native.Hom

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l6si_chainS {n : ℕ} (P : Fin n → Prop) :
    {i : Fin n // P i} → {i : Fin n // P i} → Prop :=
  fun u v => u ≠ v ∧ (CoxeterMatrix.A n).M u.1 v.1 ≠ 2

private lemma l6si_M_ne_two_iff {n : ℕ} {u v : Fin n} (huv : (u : ℕ) ≠ (v : ℕ)) :
    (CoxeterMatrix.A n).M u v ≠ 2 ↔ ((u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h (TauCeti.coxeterMatrixA_eq_two (by omega))
  · intro h
    have h3 := TauCeti.coxeterMatrixA_eq_three (m := n) (i := u) (j := v) h
    omega

private lemma l6si_lt_congr {k u v : ℕ} (hu : u ≠ k) (hv : v ≠ k)
    (h : u + 1 = v ∨ v + 1 = u) : (u < k ↔ v < k) := by
  omega

private lemma l6si_refltrans_map {α β : Type} {r : α → α → Prop} {p : β → β → Prop} (f : α → β)
    (h : ∀ a b, r a b → p (f a) (f b)) : ∀ {a b}, Relation.ReflTransGen r a b →
      Relation.ReflTransGen p (f a) (f b) := by
  intro a b hab
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h _ _ hbc)

private lemma l6si_sep {n : ℕ} {P : Fin n → Prop}
    (hconn : ∀ u v : {i : Fin n // P i},
      Relation.ReflTransGen (l6si_chainS P) u v)
    {k u v : Fin n} (hk : ¬ P k) (hu : P u) (hv : P v)
    (huk : (u : ℕ) < (k : ℕ)) (hkv : (k : ℕ) < (v : ℕ)) : False := by
  have hpath := hconn ⟨u, hu⟩ ⟨v, hv⟩
  have hstep : ∀ a b : {i : Fin n // P i}, l6si_chainS P a b →
      (((a : Fin n) : ℕ) < (k : ℕ) → ((b : Fin n) : ℕ) < (k : ℕ)) := by
    intro a b hab ha
    have hane : ((a : Fin n) : ℕ) ≠ (k : ℕ) := fun h => hk (Fin.ext h ▸ a.2)
    have hbne : ((b : Fin n) : ℕ) ≠ (k : ℕ) := fun h => hk (Fin.ext h ▸ b.2)
    have hdist : ((a : Fin n) : ℕ) ≠ ((b : Fin n) : ℕ) :=
      fun h => hab.1 (Subtype.ext (Fin.ext h))
    have hadj : ((a : Fin n) : ℕ) + 1 = ((b : Fin n) : ℕ) ∨
        ((b : Fin n) : ℕ) + 1 = ((a : Fin n) : ℕ) :=
      (l6si_M_ne_two_iff hdist).mp hab.2
    exact (l6si_lt_congr hane hbne hadj).mp ha
  have key : ∀ b : {i : Fin n // P i},
      Relation.ReflTransGen (l6si_chainS P) ⟨u, hu⟩ b → ((b : Fin n) : ℕ) < (k : ℕ) := by
    intro b hb
    induction hb with
    | refl => simpa using huk
    | tail hab hbc ih => exact hstep _ _ hbc ih
  have hvk : ((v : Fin n) : ℕ) < (k : ℕ) := key ⟨v, hv⟩ hpath
  omega

theorem ggChainA_deleted_interval {n : ℕ} (hn : 3 ≤ n) {Λ : Type} (e : Fin n ≃ Λ) (b₁ b₂ : Λ)
    (hb : b₁ ≠ b₂) (hconn : GGDeletedConnected2 ((CoxeterMatrix.A n).reindex e) b₁ b₂) :
    ∃ s ≤ 2, ∀ i : Fin n, (e i ≠ b₁ ∧ e i ≠ b₂) ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (n - 2) := by
  let P : Fin n → Prop := fun i => e i ≠ b₁ ∧ e i ≠ b₂
  let i₁ : Fin n := e.symm b₁
  let i₂ : Fin n := e.symm b₂
  have hi₁ : e i₁ = b₁ := by simp [i₁]
  have hi₂ : e i₂ = b₂ := by simp [i₂]
  have hP₁ : ¬ P i₁ := by simp [P, hi₁]
  have hP₂ : ¬ P i₂ := by simp [P, hi₂]
  have hi_ne : i₁ ≠ i₂ := by
    intro h
    exact hb (by rw [← hi₁, ← hi₂, h])
  have hPne : ∀ i : Fin n, P i ↔ (i ≠ i₁ ∧ i ≠ i₂) := by
    intro i
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 ((congrArg e h).trans hi₁),
        fun h => h2 ((congrArg e h).trans hi₂)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (e.injective (h.trans hi₁.symm)),
        fun h => h2 (e.injective (h.trans hi₂.symm))⟩
  have hPv : ∀ i : Fin n, P i ↔ ((i : ℕ) ≠ (i₁ : ℕ) ∧ (i : ℕ) ≠ (i₂ : ℕ)) := by
    intro i
    rw [hPne i]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (Fin.ext h), fun h => h2 (Fin.ext h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (congrArg Fin.val h), fun h => h2 (congrArg Fin.val h)⟩
  have hconnFin : ∀ u v : {i : Fin n // P i},
      Relation.ReflTransGen (l6si_chainS P) u v := by
    intro u v
    let E : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ≃ {i : Fin n // P i} :=
      { toFun := fun x => ⟨e.symm x.1, by simpa [P] using x.2⟩
        invFun := fun y => ⟨e y.1, by simpa [P] using y.2⟩
        left_inv := fun x => by apply Subtype.ext; simp
        right_inv := fun y => by apply Subtype.ext; simp }
    have hpath := hconn (E.symm u) (E.symm v)
    have hstepE : ∀ x y : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
        (x ≠ y ∧ ((CoxeterMatrix.A n).reindex e).M x.1 y.1 ≠ 2) →
        l6si_chainS P (E x) (E y) := by
      intro x y hxy
      refine ⟨fun h => hxy.1 (E.injective h), ?_⟩
      have h2 := hxy.2
      rw [CoxeterMatrix.reindex_apply] at h2
      simpa [E, l6si_chainS] using h2
    have hmap := l6si_refltrans_map (fun x => E x) hstepE hpath
    simpa using hmap
  have hne_val : (i₁ : ℕ) ≠ (i₂ : ℕ) := fun h => hi_ne (Fin.ext h)
  have hex : ∃ a c : ℕ, a < c ∧
      (((i₁ : ℕ) = a ∧ (i₂ : ℕ) = c) ∨ ((i₁ : ℕ) = c ∧ (i₂ : ℕ) = a)) := by
    refine ⟨min (i₁ : ℕ) (i₂ : ℕ), max (i₁ : ℕ) (i₂ : ℕ), ?_, ?_⟩
    · rcases le_total (i₁ : ℕ) (i₂ : ℕ) with h | h
      · rw [Nat.min_eq_left h, Nat.max_eq_right h]
        exact lt_of_le_of_ne h hne_val
      · rw [Nat.min_eq_right h, Nat.max_eq_left h]
        exact lt_of_le_of_ne h (Ne.symm hne_val)
    · rcases le_total (i₁ : ℕ) (i₂ : ℕ) with h | h
      · left
        exact ⟨(Nat.min_eq_left h).symm, (Nat.max_eq_right h).symm⟩
      · right
        exact ⟨(Nat.max_eq_left h).symm, (Nat.min_eq_right h).symm⟩
  obtain ⟨a, c, hac, hminmax⟩ := hex
  have hc_lt : c < n := by
    rcases hminmax with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · rw [← hc]; exact i₂.isLt
    · rw [← ha]; exact i₁.isLt
  have ha_lt : a < n := lt_trans hac hc_lt
  have ha_le_i1 : a ≤ (i₁ : ℕ) := by
    rcases hminmax with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · rw [ha]
    · rw [ha]; exact le_of_lt hac
  have ha_le_i2 : a ≤ (i₂ : ℕ) := by
    rcases hminmax with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · rw [hc]; exact le_of_lt hac
    · rw [hc]
  have hi1_le_c : (i₁ : ℕ) ≤ c := by
    rcases hminmax with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · rw [ha]; exact le_of_lt hac
    · rw [ha]
  have hi2_le_c : (i₂ : ℕ) ≤ c := by
    rcases hminmax with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · rw [hc]
    · rw [hc]; exact le_of_lt hac
  have hPac : ∀ i : Fin n, P i ↔ ((i : ℕ) ≠ a ∧ (i : ℕ) ≠ c) := by
    intro i
    rw [hPv i]
    rcases hminmax with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · rw [ha, hc]
    · rw [ha, hc]; tauto
  have hka : ¬ P ⟨a, ha_lt⟩ := by rw [hPac]; simp
  have hkc : ¬ P ⟨c, hc_lt⟩ := by rw [hPac]; simp [ne_of_gt hac]
  have ha0 : a = 0 ∨ c = n - 1 := by
    by_contra h
    obtain ⟨ha_ne, hc_ne⟩ := not_or.mp h
    have hcle : c ≤ n - 1 := by omega
    have hc_lt' : c < n - 1 := lt_of_le_of_ne hcle hc_ne
    have hu : P ⟨0, by omega⟩ := by
      rw [hPac]
      exact ⟨fun h => ha_ne h.symm,
        ne_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero ha_ne) (le_of_lt hac))⟩
    have hv : P ⟨n - 1, by omega⟩ := by
      rw [hPac]
      exact ⟨ne_of_gt (lt_of_lt_of_le hac (le_of_lt hc_lt')), ne_of_gt hc_lt'⟩
    exact l6si_sep hconnFin hka hu hv (Nat.pos_of_ne_zero ha_ne)
      (lt_of_lt_of_le hac (le_of_lt hc_lt'))
  have hcase : (a = 0 ∧ c = 1) ∨ (a = 0 ∧ c = n - 1) ∨ (a = n - 2 ∧ c = n - 1) := by
    by_cases ha0' : a = 0
    · by_cases hc1 : c = 1
      · exact Or.inl ⟨ha0', hc1⟩
      · have hcn : c = n - 1 := by
          by_contra hcn'
          exfalso
          have hc_pos : 0 < c := by have h := hac; rw [ha0'] at h; exact h
          have hc_ge2 : 2 ≤ c := by omega
          have hcn_lt : c < n - 1 := by omega
          have hu : P ⟨1, by omega⟩ := by
            rw [hPac]
            exact ⟨by rw [ha0']; norm_num, fun h => hc1 h.symm⟩
          have hv : P ⟨n - 1, by omega⟩ := by
            rw [hPac]
            exact ⟨by rw [ha0']; exact ne_of_gt (Nat.sub_pos_of_lt (by omega : 1 < n)),
              fun h => hcn' h.symm⟩
          exact l6si_sep hconnFin hkc hu hv
            (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hc_ge2) hcn_lt
        exact Or.inr (Or.inl ⟨ha0', hcn⟩)
    · have hcn : c = n - 1 := by
        rcases ha0 with h | h
        · exact absurd h ha0'
        · exact h
      have han2 : a = n - 2 := by
        by_contra ha'
        exfalso
        have hu : P ⟨0, by omega⟩ := by
          rw [hPac]
          exact ⟨fun h => ha0' h.symm, by rw [hcn]; exact ne_of_lt (by omega : 0 < n - 1)⟩
        have hv : P ⟨n - 2, by omega⟩ := by
          rw [hPac]
          exact ⟨fun h => ha' h.symm, by rw [hcn]; exact (by omega : n - 2 ≠ n - 1)⟩
        have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0'
        have hle : a ≤ n - 2 := by have h := hac; rw [hcn] at h; omega
        have hkvn : a < n - 2 := lt_of_le_of_ne hle ha'
        exact l6si_sep hconnFin hka hu hv ha_pos hkvn
      exact Or.inr (Or.inr ⟨han2, hcn⟩)
  rcases hcase with ⟨ha0', hc1⟩ | ⟨ha0', hcn⟩ | ⟨han2, hcn⟩
  · refine ⟨2, by omega, ?_⟩
    intro i
    have hi : (i : ℕ) < n := i.isLt
    change P i ↔ 2 ≤ (i : ℕ) ∧ (i : ℕ) < 2 + (n - 2)
    rw [hPac i, ha0', hc1]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h2, hlt⟩; exact ⟨by omega, by omega⟩
  · refine ⟨1, by omega, ?_⟩
    intro i
    have hi : (i : ℕ) < n := i.isLt
    change P i ↔ 1 ≤ (i : ℕ) ∧ (i : ℕ) < 1 + (n - 2)
    rw [hPac i, ha0', hcn]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, hlt⟩; exact ⟨by omega, by omega⟩
  · refine ⟨0, by omega, ?_⟩
    intro i
    have hi : (i : ℕ) < n := i.isLt
    change P i ↔ 0 ≤ (i : ℕ) ∧ (i : ℕ) < 0 + (n - 2)
    rw [hPac i, han2, hcn]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h0, hlt⟩; exact ⟨by omega, by omega⟩

theorem ggChainA_deletedS_interval {n k : ℕ} (hk : k < n) {Λ : Type} (e : Fin n ≃ Λ)
    (S : Finset Λ) (hS : S.card = k)
    (hconn : GGDeletedConnectedS ((CoxeterMatrix.A n).reindex e) S) :
    ∃ s ≤ k, ∀ i : Fin n, (e i ∉ S) ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (n - k) := by
  classical
  let P : Fin n → Prop := fun i => e i ∉ S
  let T := {i : Fin n // P i}
  have hconnFin : ∀ u v : T, Relation.ReflTransGen (l6si_chainS P) u v := by
    intro u v
    let E : {i : Λ // i ∉ S} ≃ T :=
      { toFun := fun x => ⟨e.symm x.1, by simpa [P] using x.2⟩
        invFun := fun y => ⟨e y.1, by simpa [P] using y.2⟩
        left_inv := fun x => by apply Subtype.ext; simp
        right_inv := fun y => by apply Subtype.ext; simp }
    have hpath := hconn (E.symm u) (E.symm v)
    have hstepE : ∀ x y : {i : Λ // i ∉ S},
        (x ≠ y ∧ ((CoxeterMatrix.A n).reindex e).M x.1 y.1 ≠ 2) →
        l6si_chainS P (E x) (E y) := by
      intro x y hxy
      refine ⟨fun h => hxy.1 (E.injective h), ?_⟩
      have h2 := hxy.2
      rw [CoxeterMatrix.reindex_apply] at h2
      simpa [E, l6si_chainS] using h2
    simpa using l6si_refltrans_map (fun x => E x) hstepE hpath
  let S' : Finset (Fin n) := S.image e.symm
  have hcardS' : S'.card = k := by
    rw [Finset.card_image_of_injective _ e.symm.injective, hS]
  have hcompl : Finset.univ.filter P = Finset.univ \ S' := by
    ext i
    simp [P, S', Finset.mem_image, Equiv.symm_apply_eq]
  have hcardT : Fintype.card T = n - k := by
    rw [Fintype.card_subtype, hcompl, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hcardS']
  have hpos : 0 < Fintype.card T := by rw [hcardT]; omega
  obtain ⟨x0⟩ := Fintype.card_pos_iff.mp hpos
  let vals : Finset ℕ := Finset.univ.image (fun x : T => (x.1 : ℕ))
  have hx0 : (x0.1 : ℕ) ∈ vals :=
    Finset.mem_image.mpr ⟨x0, Finset.mem_univ _, rfl⟩
  let s := vals.min' ⟨_, hx0⟩
  let t := vals.max' ⟨_, hx0⟩
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (Finset.min'_mem vals ⟨_, hx0⟩)
  obtain ⟨b, -, hb⟩ := Finset.mem_image.mp (Finset.max'_mem vals ⟨_, hx0⟩)
  have ha_min : ∀ y : T, (a.1 : ℕ) ≤ (y.1 : ℕ) := by
    intro y
    have hy : (y.1 : ℕ) ∈ vals := Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    calc (a.1 : ℕ) = s := ha
      _ ≤ (y.1 : ℕ) := Finset.min'_le vals _ hy
  have hb_max : ∀ y : T, (y.1 : ℕ) ≤ (b.1 : ℕ) := by
    intro y
    have hy : (y.1 : ℕ) ∈ vals := Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    calc (y.1 : ℕ) ≤ t := Finset.le_max' vals _ hy
      _ = (b.1 : ℕ) := hb.symm
  have hinter : ∀ i : Fin n, P i ↔ (a.1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (b.1 : ℕ) := by
    intro i
    constructor
    · intro hi
      exact ⟨ha_min ⟨i, hi⟩, hb_max ⟨i, hi⟩⟩
    · rintro ⟨h1, h2⟩
      by_contra hi
      have hPi : ¬ P i := by simpa [P] using hi
      have hai : (a.1 : ℕ) < (i : ℕ) := by
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · exact absurd (Fin.ext h ▸ a.2) hPi
      have hib : (i : ℕ) < (b.1 : ℕ) := by
        rcases lt_or_eq_of_le h2 with h | h
        · exact h
        · exact absurd (Fin.ext h.symm ▸ b.2) hPi
      exact l6si_sep hconnFin hPi a.2 b.2 hai hib
  have hfilter : Finset.univ.filter P = Finset.Icc a.1 b.1 := by
    ext i
    rw [Finset.mem_filter, Finset.mem_Icc, hinter i, Fin.le_def, Fin.le_def]
    simp
  have hcardIcc : (Finset.univ.filter P).card = (b.1 : ℕ) + 1 - (a.1 : ℕ) := by
    rw [hfilter, Fin.card_Icc]
  have hcard' : Fintype.card T = (b.1 : ℕ) + 1 - (a.1 : ℕ) := by
    rw [Fintype.card_subtype, hcardIcc]
  have hle_ab : (a.1 : ℕ) ≤ (b.1 : ℕ) := ha_min b
  have hb_eq : (b.1 : ℕ) + 1 = (a.1 : ℕ) + (n - k) := by omega
  have hsle : (a.1 : ℕ) ≤ k := by
    have hb_lt : (b.1 : ℕ) < n := b.1.isLt
    omega
  refine ⟨(a.1 : ℕ), hsle, fun i => ?_⟩
  change P i ↔ _
  rw [hinter i, ← hb_eq, Nat.lt_succ_iff]

theorem ggChainA_deletedS_coxeter {n k : ℕ} (hk : k < n) {Λ : Type} (e : Fin n ≃ Λ)
    (S : Finset Λ) (hS : S.card = k)
    (hconn : GGDeletedConnectedS ((CoxeterMatrix.A n).reindex e) S) :
    ∃ eS : {i : Λ // i ∉ S} ≃ Fin (n - k),
      ∀ i j : {i : Λ // i ∉ S},
        ((CoxeterMatrix.A n).reindex e).M i j =
          (CoxeterMatrix.A (n - k)).M (eS i) (eS j) := by
  classical
  obtain ⟨s, hsle, hsint⟩ := ggChainA_deletedS_interval hk e S hS hconn
  let toF : {i : Λ // i ∉ S} → Fin (n - k) := fun i =>
    ⟨(e.symm i.1).val - s, by
      have h := (hsint (e.symm i.1)).mp (by simpa using i.2)
      omega⟩
  let iOf : Fin (n - k) → Fin n := fun t =>
    ⟨s + t.val, by
      have ht := t.isLt
      omega⟩
  have hiOf_val : ∀ t : Fin (n - k), (iOf t : ℕ) = s + t.val := fun t => rfl
  let invF : Fin (n - k) → {i : Λ // i ∉ S} := fun t =>
    ⟨e (iOf t), by
      have h : s ≤ (iOf t : ℕ) ∧ (iOf t : ℕ) < s + (n - k) := by
        rw [hiOf_val t]
        exact ⟨by omega, by have ht := t.isLt; omega⟩
      exact (hsint (iOf t)).mpr h⟩
  let eS : {i : Λ // i ∉ S} ≃ Fin (n - k) :=
    { toFun := toF
      invFun := invF
      left_inv := fun i => by
        apply Subtype.ext
        have h := (hsint (e.symm i.1)).mp (by simpa using i.2)
        simp [toF, invF, iOf, Nat.add_sub_of_le h.1]
      right_inv := fun t => by
        apply Fin.ext
        simp [toF, invF, iOf] }
  have hval : ∀ i : {a : Λ // a ∉ S},
      (e.symm i.1).val = s + (eS i).val := by
    intro i
    have h := (hsint (e.symm i.1)).mp (by simpa using i.2)
    simp [eS, toF, Nat.add_sub_of_le h.1]
  refine ⟨eS, fun i j => ?_⟩
  rw [CoxeterMatrix.reindex_apply]
  by_cases hij : i = j
  · subst j
    rw [CoxeterMatrix.diagonal, CoxeterMatrix.diagonal]
  · have hne : (e.symm i.1).val ≠ (e.symm j.1).val := by
      intro h
      exact hij (Subtype.ext (e.symm.injective (Fin.ext h)))
    have hneS : (eS i).val ≠ (eS j).val := by
      intro h
      exact hij (eS.injective (Fin.ext h))
    by_cases hadj : (eS i).val + 1 = (eS j).val ∨ (eS j).val + 1 = (eS i).val
    · have hadj' : (e.symm i.1).val + 1 = (e.symm j.1).val ∨
          (e.symm j.1).val + 1 = (e.symm i.1).val := by
        rw [hval i, hval j]
        omega
      rw [TauCeti.coxeterMatrixA_eq_three hadj', TauCeti.coxeterMatrixA_eq_three hadj]
    · have hfarS : (eS i).val + 2 ≤ (eS j).val ∨ (eS j).val + 2 ≤ (eS i).val := by
        omega
      have hfar : (e.symm i.1).val + 2 ≤ (e.symm j.1).val ∨
          (e.symm j.1).val + 2 ≤ (e.symm i.1).val := by
        rw [hval i, hval j]
        omega
      rw [TauCeti.coxeterMatrixA_eq_two hfar, TauCeti.coxeterMatrixA_eq_two hfarS]

private lemma l6si_order_general {G : Type} [Group G] {ι : Type} {M : CoxeterMatrix ι}
    {L : Subgroup G} {Bs : Subgroup G} (f : M.Group ≃* ↥(ggAutomizer L Bs))
    (ψ : ι → MulAut ↥Bs)
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i) (i j : ι) :
    M.M i j = orderOf (ψ i * ψ j) := by
  have hcs := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
  simp only [CoxeterMatrix.toCoxeterSystem_simple] at hcs
  have hord : orderOf (f (M.simple i * M.simple j)) = orderOf (M.simple i * M.simple j) :=
    orderOf_injective f.toMonoidHom f.injective (M.simple i * M.simple j)
  rw [← hcs, ← hord]
  rw [← Subgroup.orderOf_coe (f (M.simple i * M.simple j))]
  congr 1
  rw [map_mul, Subgroup.coe_mul, hf i, hf j]

theorem ggJoint_coxeter_J_eq {G : Type} [Group G] {Bs L K : Subgroup G} {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b₁ b₂ : Λ} {Λa : Type} [Fintype Λa] [DecidableEq Λa] {ML : CoxeterMatrix Λ}
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    (hfL : ∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (hfK : ∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
      ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) :
    ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1 := by
  rcases hfL with ⟨fL, hfL⟩
  rcases hfK with ⟨fK, hfK⟩
  intro i j
  have hK := l6si_order_general fK (fun o => φ (o.map Subtype.val id)) hfK (Sum.inl i) (Sum.inl j)
  have hL := l6si_order_general fL (fun k => φ (Sum.inl k)) hfL i.1 j.1
  rw [hK, hL]
  simp

end CFSG.StandardType

end
