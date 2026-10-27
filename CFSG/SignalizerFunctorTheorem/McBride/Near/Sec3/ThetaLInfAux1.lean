module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33b

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33h

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv Thm33a Thm33b

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y N X₁ X₂ : Subgroup Γ}

theorem iThetaL_eq_qpre
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hNX : N ≤ X) (hX : Admits X N) (hA : Admits A N) (hND : N ⊓ cenIn X (A : Set Γ) ≤ Y) :
    iThetaL A X Y =
      SolQuot.qpre N (iThetaL (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)) := by
  have hXn : X ≤ AChief.nrm N := hX
  have hAn : A ≤ AChief.nrm N := hA
  have hYD : Y ≤ cenIn X (A : Set Γ) := pair_Y_le hP
  have himg : ∀ P ∈ iPairsY A X Y, (AChief.qimg N P.1, AChief.qimg N P.2) ∈
      iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := fun P hP' =>
    qimg_mem_iPairsY h (X₁ := P.1) (X₂ := P.2) hP' hXn hAn
      (inf_le_of_inf_dsub_le h (X₁ := P.1) (X₂ := P.2) hP' hX hA hND)
  have hhat := iThetaM_iThetaL_mem (Thm211.nearAsolvAction_qimg h hXn hAn)
    ⟨_, himg (X₁, X₂) hP⟩
  have hlift := qpre_mem_iPairsY h hNX hXn hAn hYD hND hhat
  refine le_antisymm (iSup₂_le fun P hP' => ?_) ?_
  · have h1 := le_iSup₂ (f := fun (Q : Subgroup (AChief.QG N) × Subgroup (AChief.QG N))
      (_ : Q ∈ iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)) => Q.2)
      (AChief.qimg N P.1, AChief.qimg N P.2) (himg P hP')
    exact (SolQuot.qimg_le_iff (((pair_le₂ (X₁ := P.1) (X₂ := P.2) hP').trans
      (pair_le (X₁ := P.1) (X₂ := P.2) hP')).trans hXn)).mp h1
  · exact le_iSup₂ (f := fun (Q : Subgroup Γ × Subgroup Γ) (_ : Q ∈ iPairsY A X Y) => Q.2)
      (SolQuot.qpre N (iThetaM (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)),
        SolQuot.qpre N (iThetaL (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y))) hlift

omit [Finite Γ] in
theorem qimg_iThetaU_le (h : NearAsolvAction p A X) (hX : X ≤ AChief.nrm N)
    (hA : A ≤ AChief.nrm N) (hYA : Admits A Y) (hYD : Y ≤ cenIn X (A : Set Γ)) :
    AChief.qimg N (iThetaU A X Y) ≤
      iThetaU (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := by
  unfold iThetaU
  rw [SolQuot.qimg_biSup (S := fun Z => Z) (s := iUset A X Y) fun Z hZ => hZ.1.1.trans hX]
  exact iSup₂_le fun Z hZ => le_iThetaU (qimg_mem_iUset h hX hA hYA hYD hZ)

@[expose] def Below.{v} (p n : ℕ) : Prop :=
  ∀ (Γ : Type v) [Group Γ] [Finite Γ] (A X Y : Subgroup Γ), Nat.card ↥X < n →
    NearAsolvAction p A X → (iPairsY A X Y).Nonempty →
      Admits (iThetaU A X Y) (iThetaL A X Y)

theorem iThetaL_eq_bot_of_key
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hθ : iThetaU A X Y = X)
    (key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N →
      N ⊓ cenIn X (A : Set Γ) ≤ Y → N = ⊥) : iThetaL A X Y = ⊥ := by
  have hXe : X = kOf X ⊔ iThetaU A X Y :=
    le_antisymm (by rw [hθ]; exact le_sup_right) (sup_le (kOf_le X) iThetaU_le)
  have hXne : X ≠ ⊥ := by
    intro hX0
    have h1 : X₁ = ⊥ := le_bot_iff.mp (hX0 ▸ pair_le hP)
    have h2 : X₂ = ⊥ := le_bot_iff.mp (h1 ▸ pair_le₂ hP)
    exact (pair_lt hP).ne (h2.trans h1.symm)
  have hsol : sol X = ⊥ := sol_eq_bot_of_key h hP key
  obtain ⟨Z₁, Z₂, -, -, hZP, hZsol, -⟩ := iThm32 h hP
  obtain ⟨W₀, -, -, -, -, -, -, -, hY0⟩ := pair_rigid h hsol hXne hXe key hZP hZsol
  subst hY0
  exact le_bot_iff.mp (iSup₂_le fun P hP'' =>
    (pair_eq_of_Y_bot h hsol hXne hXe key hP'').1.le)

theorem step
    (ih : Below.{u} p (Nat.card ↥X)) (h : NearAsolvAction p A X)
    (hY : (iPairsY A X Y).Nonempty) : Admits (iThetaU A X Y) (iThetaL A X Y) := by
  obtain ⟨⟨X₁, X₂⟩, hP⟩ := hY
  by_cases hθ : iThetaU A X Y = X
  · by_cases hN : ∃ N : Subgroup Γ, N ≤ X ∧ Admits X N ∧ Admits A N ∧
        N ⊓ cenIn X (A : Set Γ) ≤ Y ∧ N ≠ ⊥
    · obtain ⟨N, hNX, hXN, hAN, hND, hN1⟩ := hN
      have hXn : X ≤ AChief.nrm N := hXN
      have hAn : A ≤ AChief.nrm N := hAN
      have hYA : Admits A Y := le_sup_right.trans (pair_admits_Y hP)
      have hYD : Y ≤ cenIn X (A : Set Γ) := pair_Y_le hP
      have hlt : Nat.card ↥(AChief.qimg N X) < Nat.card ↥X :=
        Thm211.card_qimg_lt hNX hXN hN1
      have hbarP := qimg_mem_iPairsY h hP hXn hAn (inf_le_of_inf_dsub_le h hP hXN hAN hND)
      have hih := ih (AChief.QG N) (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) hlt
        (Thm211.nearAsolvAction_qimg h hXn hAn) ⟨_, hbarP⟩
      rw [iThetaL_eq_qpre h hP hNX hXN hAN hND]
      have hUn : iThetaU A X Y ≤ AChief.nrm N := iThetaU_le.trans hXn
      refine (admits_iff_qimg hUn (SolQuot.qpre_le_nrm _) (SolQuot.le_qpre _)).mpr ?_
      rw [SolQuot.qimg_qpre]
      exact (qimg_iThetaU_le h hXn hAn hYA hYD).trans hih
    · have key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N →
          N ⊓ cenIn X (A : Set Γ) ≤ Y → N = ⊥ := fun N hNX hXN hAN hND =>
        by_contra fun hN1 => hN ⟨N, hNX, hXN, hAN, hND, hN1⟩
      rw [iThetaL_eq_bot_of_key h hP hθ key]
      exact admits_bot _
  · have hle : iThetaU A X Y ≤ X := iThetaU_le
    have hDX' : cenIn X (A : Set Γ) ≤ iThetaU A X Y := dsub_le_iThetaU hP
    have hcard : Nat.card ↥(iThetaU A X Y) < Nat.card ↥X := Thm211.card_lt_of_ne hle hθ
    have hnear : NearAsolvAction p A (iThetaU A X Y) :=
      Thm211.nearAsolvAction_of_le h hle (le_sup_right.trans admits_iThetaU)
    have hpairs : iPairsY A (iThetaU A X Y) Y = iPairsY A X Y := by
      rw [iPairsY_of_le hDX' hle]
      ext P
      exact ⟨fun hP' => hP'.1, fun hP' =>
        ⟨hP', pair_le_iThetaU (X₁ := P.1) (X₂ := P.2) hP'⟩⟩
    have hmem := ih Γ A (iThetaU A X Y) Y hcard hnear (by rw [hpairs]; exact ⟨_, hP⟩)
    have hL : iThetaL A (iThetaU A X Y) Y = iThetaL A X Y := by
      unfold iThetaL
      rw [hpairs]
    rwa [iThetaU_eq_of_iThetaU_le hDX' hle le_rfl, hL] at hmem

theorem below
    (p : ℕ) (n : ℕ) : Below.{u} p n := by
  induction n with
  | zero =>
    intro Γ _ _ A X Y hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro Γ _ _ A X Y hn h hY
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact ih Γ A X Y hlt h hY
    · exact step (heq ▸ ih) h hY

theorem admits_iThetaL
    (h : NearAsolvAction p A X) (hY : (iPairsY A X Y).Nonempty) :
    Admits (iThetaU A X Y) (iThetaL A X Y) :=
  below p (Nat.card ↥X + 1) _ A X Y (Nat.lt_succ_self _) h hY

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33h
