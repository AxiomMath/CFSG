module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux5
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux3

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] {p : ℕ}

@[expose] def Below.{v} (p n : ℕ) : Prop :=
  ∀ (Γ : Type v) [Group Γ] [Finite Γ] (A X D D₂ N L R : Subgroup Γ) [(D₂.subgroupOf D).Normal],
    Nat.card ↥X < n → Hyp p A X D D₂ N L R → Concl A D D₂ R

theorem hyp_of_le [Finite Γ] {A X X' D D₂ N L R X₁ X₂ : Subgroup Γ} [(D₂.subgroupOf D).Normal]
    (H : Hyp p A X D D₂ N L R) (hP : (X₁, X₂) ∈ iPairsY A X D₂) (hX'X : X' ≤ X) (hDX' : D ≤ X')
    (hAX' : Admits A X') (hX₁ : X₁ ≤ X') (hRX' : R ≤ X') : Hyp p A X' D D₂ N L R := by
  have hD' : cenIn X (A : Set Γ) ≤ X' := by
    rw [H.cen]
    exact hDX'
  have hcen : cenIn X' (A : Set Γ) = D := by
    rw [Thm211.cenIn_eq_of_le hX'X hD']
    exact H.cen
  exact
    { near := Thm211.nearAsolvAction_of_le H.near hX'X hAX'
      cen := hcen
      pair := ⟨(X₁, X₂), by
        rw [Thm33a.iPairsY_of_le hD' hX'X]
        exact ⟨hP, hX₁⟩⟩
      hN := H.N_le_L.trans (H.LR.trans hRX')
      hL := H.LR.trans hRX'
      hR := hRX'
      nN := H.nN
      nL := H.nL
      nR := H.nR
      chief := H.chief
      LR := H.LR
      cent := H.cent
      RD := H.RD
      ND := H.ND
      prod := H.prod }

theorem main_step
    [Finite Γ] {A X D D₂ N L R : Subgroup Γ} [(D₂.subgroupOf D).Normal]
    (ih : Below.{u} p (Nat.card ↥X)) (H : Hyp p A X D D₂ N L R) : Concl A D D₂ R := by
  obtain rfl : cenIn X (A : Set Γ) = D := H.cen
  by_contra hfail
  obtain ⟨⟨X₁', X₂'⟩, hP'⟩ := H.pair
  obtain ⟨X₁, X₂, -, -, hP, hX₂sol, -⟩ := iThm32 H.near hP'
  have hXeq : X = X₁ ⊔ R ⊔ cenIn X (A : Set Γ) := by
    by_contra hne
    have hle : X₁ ⊔ R ⊔ cenIn X (A : Set Γ) ≤ X :=
      sup_le (sup_le (Thm33a.pair_le hP) H.hR) H.D_le_X
    have hlt : X₁ ⊔ R ⊔ cenIn X (A : Set Γ) < X := lt_of_le_of_ne hle fun h => hne h.symm
    have hA' : Admits A (X₁ ⊔ R ⊔ cenIn X (A : Set Γ)) := by
      have hA₁ : Admits A X₁ := le_sup_right.trans (Thm33a.pair_admits_left hP)
      have hA₂ : Admits A R := (A_le_H R _ A).trans H.H_le_R
      have hA₃ : Admits A (cenIn X (A : Set Γ)) :=
        admits_of_le_cenIn (X := X) le_rfl
      exact (hA₁.sup hA₂).sup hA₃
    have hH := hyp_of_le H hP hle le_sup_right hA' (le_sup_left.trans le_sup_left)
      (le_sup_right.trans le_sup_left)
    have hcard : Nat.card ↥(X₁ ⊔ R ⊔ cenIn X (A : Set Γ)) < Nat.card ↥X :=
      Thm211.card_lt_of_ne hle (ne_of_lt hlt)
    exact hfail (ih Γ A _ _ D₂ N L R hcard hH)
  have key : ∀ M : Subgroup Γ, M ≤ X → Admits X M → Admits A M → M ⊓ X₁ ≤ X₂ → M = ⊥ := by
    intro M hMX hXM hAM hM1
    by_contra hM
    have hMD : cenIn X (A : Set Γ) ⊓ M ≤ D₂ := by
      have := Thm33a.inf_dsub_le hP hXM hM1
      rwa [inf_comm]
    have := normal_qimg_subgroupOf (M := M) (D := cenIn X (A : Set Γ)) (D₂ := D₂) H.D₂_le_D
    have hlt := Thm211.card_qimg_lt hMX hXM hM
    have hHq := hyp_qimg H hP hMX hXM hAM hM1
    exact hfail (concl_of_qimg H hMD hXM hAM
      (ih (AChief.QG M) (AChief.qimg M A) (AChief.qimg M X) _ _ _ _ _ hlt hHq))
  have hXne : X ≠ ⊥ := by
    intro hX0
    have h1 : X₁ = ⊥ := le_bot_iff.mp (hX0 ▸ Thm33a.pair_le hP)
    have h2 : X₂ = ⊥ := le_bot_iff.mp (h1 ▸ Thm33a.pair_le₂ hP)
    exact (Thm33a.pair_lt hP).ne (h2.trans h1.symm)
  have hsol : sol X = ⊥ := by
    have hHsol : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (sol X) :=
      sup_le (sup_le ((Thm33a.pair_le hP).trans (SolQuot.le_nrm_sol X))
        (inf_le_left.trans (SolQuot.le_nrm_sol X)))
        (H.near.admits.trans (SolQuot.normalizer_le_nrm_sol X))
    refine key (sol X) (sol_le X) (SolQuot.le_nrm_sol X)
      (H.near.admits.trans (SolQuot.normalizer_le_nrm_sol X)) ?_
    exact Thm33a.le_of_solvable hP inf_le_right (Admits.inf hHsol (Thm33a.pair_admits_H hP))
      (Thm211.isSolvable_of_le inf_le_left (isSolvable_sol X))
  have hXK : Admits X (kOf X) :=
    Subgroup.le_normalizer.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hAK : Admits A (kOf X) := H.near.admits.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hKX₁ : ¬ (kOf X ⊓ X₁ ≤ X₂) := fun hle =>
    Thm211.kOf_ne_bot hsol hXne (key (kOf X) (kOf_le X) hXK hAK hle)
  obtain ⟨W, hWB, hWperf, hWadm, hWX, hWinf⟩ :=
    Thm33a.exists_perfect_sup H.near hsol hXne hP hX₂sol hKX₁
  have S : Setup p A X (cenIn X (A : Set Γ)) D₂ N L R X₁ X₂ W :=
    ⟨H, hP, hsol, hXne, hWB.trans inf_le_left, hWB.trans inf_le_right, hWperf, hWadm, hWX, hWinf⟩
  exact hfail (S.concl_of_k1_eq_bot (S.k1_eq_bot hXeq key))

theorem thm35_below
    (p n : ℕ) : Below.{u} p n := by
  induction n with
  | zero =>
    intro Γ _ _ A X D D₂ N L R _ hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro Γ _ _ A X D D₂ N L R _ hn H
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact ih Γ A X D D₂ N L R hlt H
    · exact main_step (heq ▸ ih) H

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35
