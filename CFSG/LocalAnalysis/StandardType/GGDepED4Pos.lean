module

public import CFSG.LocalAnalysis.StandardType.GGDepED4False
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat1
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nEP_reflTransGen_of_closed {α : Type*} {r : α → α → Prop} {P : α → Prop}
    {a : α} (hcl : ∀ x y, P x → r x y → P y) (ha : P a) :
    ∀ b, Relation.ReflTransGen r a b → P b := by
  intro b hb
  induction hb with
  | refl => exact ha
  | tail hprev hr ih => exact hcl _ _ ih hr

private def l05nEP_goodPair (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
  (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 5) ∨ (i = 5 ∧ j = 1) ∨
  (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4)

private def l05nEP_S (i j : Fin 6) : Finset (Fin 6) :=
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then {1}
  else if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) then {5}
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then {0}
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then {0, 2}
  else if (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) then {5}
  else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then {0}
  else if (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) then {0}
  else if (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2) then {0}
  else if (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then {1}
  else if (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3) then {1}
  else {0}

private def l05nEP_a (i j : Fin 6) : Fin 6 :=
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 1
  else if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) then 5
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 0
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 0
  else if (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) then 5
  else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 0
  else if (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) then 0
  else if (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2) then 0
  else if (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 1
  else if (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3) then 1
  else 0

private def l05nEP_v (i j : Fin 6) : Fin 6 :=
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 4
  else if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) then 1
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 3
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 4
  else if (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) then 0
  else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 4
  else if (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) then 1
  else if (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2) then 1
  else if (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 0
  else if (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3) then 0
  else 1

private lemma l05nEP_spec (i j : Fin 6) (hij : i ≠ j) (hbad : ¬ l05nEP_goodPair i j) :
    l05nEP_a i j ∈ l05nEP_S i j ∧ l05nEP_v i j ∉ l05nEP_S i j ∧
    l05nEP_a i j ≠ i ∧ l05nEP_a i j ≠ j ∧ l05nEP_v i j ≠ i ∧ l05nEP_v i j ≠ j ∧
    (∀ p q, p ∈ l05nEP_S i j → p ≠ q → CoxeterMatrix.E₆ p q ≠ 2 →
      q ≠ i → q ≠ j → q ∈ l05nEP_S i j) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact (hbad (by unfold l05nEP_goodPair; decide)).elim
    | (unfold l05nEP_S l05nEP_a l05nEP_v
       refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       · decide
       · decide
       · decide
       · decide
       · decide
       · decide
       · intro p q
         fin_cases p <;> fin_cases q <;> decide)

private lemma l05nEP_not_conn_ML {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) {b₁ b₂ : Λ}
    (S : Finset (Fin 6)) (a v : Fin 6) (haS : a ∈ S) (hvS : v ∉ S)
    (hcl : ∀ p q, p ∈ S → p ≠ q → CoxeterMatrix.E₆ p q ≠ 2 →
      q ≠ e.symm b₁ → q ≠ e.symm b₂ → q ∈ S)
    (hai : a ≠ e.symm b₁) (haj : a ≠ e.symm b₂)
    (hvi : v ≠ e.symm b₁) (hvj : v ≠ e.symm b₂) :
    ¬ GGDeletedConnected2 ML b₁ b₂ := by
  intro hconn
  let a' : {x : Λ // x ≠ b₁ ∧ x ≠ b₂} :=
    ⟨e a, fun h => hai ((Equiv.apply_eq_iff_eq_symm_apply e).mp h),
      fun h => haj ((Equiv.apply_eq_iff_eq_symm_apply e).mp h)⟩
  let v' : {x : Λ // x ≠ b₁ ∧ x ≠ b₂} :=
    ⟨e v, fun h => hvi ((Equiv.apply_eq_iff_eq_symm_apply e).mp h),
      fun h => hvj ((Equiv.apply_eq_iff_eq_symm_apply e).mp h)⟩
  have hcl' : ∀ x y : {x : Λ // x ≠ b₁ ∧ x ≠ b₂},
      (e.symm x.1 ∈ S) → (x ≠ y ∧ ML.M x y ≠ 2) → (e.symm y.1 ∈ S) := by
    intro x y hx hr
    obtain ⟨hne, hM2⟩ := hr
    have hxy : e.symm x.1 ≠ e.symm y.1 :=
      fun h => hne (Subtype.ext (e.symm.injective h))
    have hy1 : e.symm y.1 ≠ e.symm b₁ := fun h => y.2.1 (by
      have := congrArg e h; simpa using this)
    have hy2 : e.symm y.1 ≠ e.symm b₂ := fun h => y.2.2 (by
      have := congrArg e h; simpa using this)
    refine hcl _ _ hx hxy ?_ hy1 hy2
    intro h2
    exact hM2 (by rw [hML, CoxeterMatrix.reindex_apply]; exact h2)
  have hmain : e.symm v'.1 ∈ S :=
    l05nEP_reflTransGen_of_closed hcl' (by simpa [a'] using haS) v' (hconn a' v')
  exact hvS (by simpa [v'] using hmain)

private lemma l05nEP_classify_ML {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) {b₁ b₂ : Λ}
    (hb : b₁ ≠ b₂) (hconn : GGDeletedConnected2 ML b₁ b₂) :
    l05nEP_goodPair (e.symm b₁) (e.symm b₂) := by
  by_contra hbad
  have hij : e.symm b₁ ≠ e.symm b₂ := fun h => hb (by
    have := congrArg e h; simpa using this)
  obtain ⟨haS, hvS, hai, haj, hvi, hvj, hcl⟩ :=
    l05nEP_spec (e.symm b₁) (e.symm b₂) hij hbad
  exact l05nEP_not_conn_ML e hML (S := l05nEP_S (e.symm b₁) (e.symm b₂))
    (a := l05nEP_a (e.symm b₁) (e.symm b₂)) (v := l05nEP_v (e.symm b₁) (e.symm b₂))
    haS hvS hcl hai haj hvi hvj hconn

private lemma l05nEP_A4_card {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) {b₁ b₂ : Λ}
    {MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂}}
    (hJM : ∀ j j' : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, MJ.M j j' = ML.M j j')
    (c : Fin 4 → Fin 6) (hc_inj : Function.Injective c)
    (hi : ∀ a, c a ≠ e.symm b₁) (hj : ∀ a, c a ≠ e.symm b₂)
    (hc_surj : ∀ k : Fin 6, k ≠ e.symm b₁ → k ≠ e.symm b₂ → ∃ a, c a = k)
    (hchain : ∀ a b : Fin 4, CoxeterMatrix.E₆ (c a) (c b) = (CoxeterMatrix.A 4).M a b) :
    Nat.card MJ.Group = 120 := by
  let g : Fin 4 → {j : Λ // j ≠ b₁ ∧ j ≠ b₂} := fun a =>
    ⟨e (c a), by
      constructor
      · intro h; exact hi a ((Equiv.apply_eq_iff_eq_symm_apply e).mp h)
      · intro h; exact hj a ((Equiv.apply_eq_iff_eq_symm_apply e).mp h)⟩
  have hg_inj : Function.Injective g := by
    intro a b h
    exact hc_inj (e.injective (congrArg Subtype.val h))
  have hg_surj : Function.Surjective g := by
    intro y
    have hk1 : e.symm y.1 ≠ e.symm b₁ := fun h => y.2.1 (by
      have := congrArg e h; simpa using this)
    have hk2 : e.symm y.1 ≠ e.symm b₂ := fun h => y.2.2 (by
      have := congrArg e h; simpa using this)
    obtain ⟨a, ha⟩ := hc_surj (e.symm y.1) hk1 hk2
    exact ⟨a, by apply Subtype.ext; show e (c a) = y.1; rw [ha, Equiv.apply_symm_apply]⟩
  let f : Fin 4 ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hMJ : MJ = (CoxeterMatrix.A 4).reindex f := by
    apply CoxeterMatrix.ext
    funext x y
    have hfx : (f (f.symm x)).1 = e (c (f.symm x)) := rfl
    have hfy : (f (f.symm y)).1 = e (c (f.symm y)) := rfl
    rw [← f.apply_symm_apply x, ← f.apply_symm_apply y]
    rw [hJM, hML, CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
    simp only [hfx, hfy, Equiv.symm_apply_apply]
    exact hchain _ _
  calc Nat.card MJ.Group = Nat.card ((CoxeterMatrix.A 4).reindex f).Group := by rw [hMJ]
    _ = Nat.card (CoxeterMatrix.A 4).Group :=
        Nat.card_congr ((CoxeterMatrix.A 4).reindexGroupEquiv f).toEquiv
    _ = 120 := by rw [l05nK3a_card_coxeterA 4]; norm_num

private lemma l05nEP_A4_contra {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) {b₁ b₂ : Λ}
    {MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂}}
    (hJM : ∀ j j' : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, MJ.M j j' = ML.M j j')
    (c : Fin 4 → Fin 6) (hc_inj : Function.Injective c) (i j : Fin 6)
    (ei : e.symm b₁ = i) (ej : e.symm b₂ = j)
    (hcne : ∀ a, c a ≠ i ∧ c a ≠ j)
    (hcs : ∀ k, k ≠ i → k ≠ j → ∃ a, c a = k)
    (hchain : ∀ a b : Fin 4, CoxeterMatrix.E₆ (c a) (c b) = (CoxeterMatrix.A 4).M a b)
    (hcard : 192 ≤ Nat.card MJ.Group) : False := by
  have h120 := l05nEP_A4_card e hML hJM c hc_inj
    (fun a => by rw [ei]; exact (hcne a).1)
    (fun a => by rw [ej]; exact (hcne a).2)
    (fun k hk1 hk2 => hcs k (fun h => hk1 (h.trans ei.symm)) (fun h => hk2 (h.trans ej.symm)))
    hchain
  omega

private def l05nEP_tau : Fin 6 ≃ Fin 6 :=
  (Equiv.swap 0 5).trans (Equiv.swap 2 4)

private lemma l05nEP_tau_symm_apply (p : Fin 6) : l05nEP_tau.symm p = l05nEP_tau p := by
  fin_cases p <;> decide

private lemma l05nEP_tau_inv (p q : Fin 6) :
    CoxeterMatrix.E₆ (l05nEP_tau p) (l05nEP_tau q) = CoxeterMatrix.E₆ p q := by
  fin_cases p <;> fin_cases q <;> decide

private lemma l05nEP_reindex_tau {Λ : Type} (e : Fin 6 ≃ Λ) :
    CoxeterMatrix.E₆.reindex (l05nEP_tau.trans e) = CoxeterMatrix.E₆.reindex e := by
  apply CoxeterMatrix.ext
  funext x y
  rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
  simp only [Equiv.symm_trans_apply, l05nEP_tau_symm_apply]
  exact l05nEP_tau_inv _ _

theorem ggDepED4_positions {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {b₁ b₂ : Λ} (hb : b₁ ≠ b₂) (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e)
    (hconn : GGDeletedConnected2 ML b₁ b₂)
    (MJ : CoxeterMatrix {j : Λ // j ≠ b₁ ∧ j ≠ b₂})
    (hJM : ∀ j j' : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, MJ.M j j' = ML.M j j')
    (hcard : 192 ≤ Nat.card MJ.Group) :
    ∃ e' : Fin 6 ≃ Λ, ML = CoxeterMatrix.E₆.reindex e' ∧ b₁ = e' 0 ∧ b₂ = e' 5 := by
  have hg := l05nEP_classify_ML e hML hb hconn
  rcases hg with ⟨h0, h5⟩ | ⟨h5, h0⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h0, h2⟩ | ⟨h2, h0⟩ |
    ⟨h1, h5⟩ | ⟨h5, h1⟩ | ⟨h4, h5⟩ | ⟨h5, h4⟩
  · exact ⟨e, hML, by have := congrArg e h0; simpa using this,
      by have := congrArg e h5; simpa using this⟩
  · refine ⟨l05nEP_tau.trans e, ?_, ?_, ?_⟩
    · rw [hML, l05nEP_reindex_tau]
    · have hτ : l05nEP_tau 0 = 5 := by decide
      show b₁ = (l05nEP_tau.trans e) 0
      rw [Equiv.trans_apply, hτ]
      have := congrArg e h5; simpa using this
    · have hτ : l05nEP_tau 5 = 0 := by decide
      show b₂ = (l05nEP_tau.trans e) 5
      rw [Equiv.trans_apply, hτ]
      have := congrArg e h0; simpa using this
  · exact (l05nEP_A4_contra e hML hJM ![2, 3, 4, 5] (by decide) 0 1 h0 h1
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![2, 3, 4, 5] (by decide) 1 0 h1 h0
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![1, 3, 4, 5] (by decide) 0 2 h0 h2
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![1, 3, 4, 5] (by decide) 2 0 h2 h0
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![0, 2, 3, 4] (by decide) 1 5 h1 h5
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![0, 2, 3, 4] (by decide) 5 1 h5 h1
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![0, 2, 3, 1] (by decide) 4 5 h4 h5
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim
  · exact (l05nEP_A4_contra e hML hJM ![0, 2, 3, 1] (by decide) 5 4 h5 h4
      (by decide) (by decide)
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) hcard).elim

end CFSG.StandardType

end
