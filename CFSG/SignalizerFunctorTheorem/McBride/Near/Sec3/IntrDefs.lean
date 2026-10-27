module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ]

@[expose] def IsDAIn (A X Z : Subgroup Γ) : Prop :=
  Z ≤ X ∧ Admits (cenIn X (A : Set Γ) ⊔ A) Z

@[expose] def iPairs (A X : Subgroup Γ) : Set (Subgroup Γ × Subgroup Γ) :=
  {P | IsDAIn A X P.1 ∧ IsDAIn A X P.2 ∧
    IsChiefFactorOf (P.1 ⊔ cenIn X (A : Set Γ) ⊔ A) P.1 P.2 ∧
    secCenIn (P.1 ⊔ cenIn X (A : Set Γ)) P.1 P.2 = P.2}

@[expose] def iPairsY (A X Y : Subgroup Γ) : Set (Subgroup Γ × Subgroup Γ) :=
  {P | P ∈ iPairs A X ∧ P.2 ⊓ cenIn X (A : Set Γ) = Y}

@[expose] def iUset (A X Y : Subgroup Γ) : Set (Subgroup Γ) :=
  {Z | IsDAIn A X Z ∧ cenIn X (A : Set Γ) ≤ Z ∧ orbitClosure Y Z ⊓ cenIn X (A : Set Γ) = Y}

@[expose] def iEset (A X Y : Subgroup Γ) : Set (Subgroup Γ) :=
  {Z | IsDAIn A X Z ∧ Z ⊓ cenIn X (A : Set Γ) = Y}

@[expose] def iThetaY (A X Y : Subgroup Γ) : Subgroup Γ :=
  ⨆ Z ∈ iEset A X Y, Z

@[expose] def iThetaU (A X Y : Subgroup Γ) : Subgroup Γ :=
  ⨆ Z ∈ iUset A X Y, Z

@[expose] def iThetaL (A X Y : Subgroup Γ) : Subgroup Γ :=
  ⨆ P ∈ iPairsY A X Y, P.2

@[expose] def iThetaM (A X Y : Subgroup Γ) : Subgroup Γ :=
  ⨆ P ∈ iPairsY A X Y, P.1

theorem IsDAIn.le {A X Z : Subgroup Γ} (h : IsDAIn A X Z) : Z ≤ X :=
  h.1

theorem IsDAIn.admits_dsub {A X Z : Subgroup Γ} (h : IsDAIn A X Z) :
    Admits (cenIn X (A : Set Γ)) Z :=
  le_trans le_sup_left h.2

theorem IsDAIn.admits_left {A X Z : Subgroup Γ} (h : IsDAIn A X Z) : Admits A Z :=
  le_trans le_sup_right h.2

theorem isDAIn_iff {A X Z : Subgroup Γ} :
    IsDAIn A X Z ↔ Z ≤ X ∧ Admits (cenIn X (A : Set Γ)) Z ∧ Admits A Z :=
  ⟨fun h => ⟨h.1, h.admits_dsub, h.admits_left⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, sup_le h2 h3⟩⟩

section Compare

variable {p : ℕ} {A : Subgroup Γ} {θ : Γ → Subgroup Γ} {X Y : Subgroup Γ}

theorem cenIn_eq_dsub_of_mem_mtil (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    cenIn X (A : Set Γ) = dsub A θ :=
  cenIn_eq_dsub hθ hX

variable [Finite Γ]

theorem mem_mhat_iff_isDAIn (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) {Z : Subgroup Γ} :
    (Z ≤ X ∧ Z ∈ mhat p A θ) ↔ IsDAIn A X Z := by
  have hD := cenIn_eq_dsub_of_mem_mtil hθ hX
  constructor
  · rintro ⟨hZX, hZ⟩
    rw [isDAIn_iff, hD]
    exact ⟨hZX, hZ.2, hZ.1.1⟩
  · intro hZ
    rw [isDAIn_iff, hD] at hZ
    exact ⟨hZ.1, mem_mhat_of_le_mtil hθ.prime hX hZ.1 (sup_le hZ.2.1 hZ.2.2)⟩

theorem pairsYX_eq_iPairsY (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    pairsYX p A θ Y X = iPairsY A X Y := by
  have hD := cenIn_eq_dsub_of_mem_mtil hθ hX
  ext P
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, h6⟩
    have h2le : P.2 ≤ P.1 := h3.2.2.1.le
    have hP1 := (mem_mhat_iff_isDAIn hθ hX (Z := P.1)).mp ⟨h6, h1⟩
    have hP2 := (mem_mhat_iff_isDAIn hθ hX (Z := P.2)).mp ⟨h2le.trans h6, h2⟩
    refine ⟨⟨hP1, hP2, ?_, ?_⟩, ?_⟩
    · rwa [hD]
    · rwa [hD]
    · rwa [hD]
  · rintro ⟨⟨hP1, hP2, h3, h4⟩, h5⟩
    rw [hD] at h3 h4 h5
    have h1 := ((mem_mhat_iff_isDAIn hθ hX (Z := P.1)).mpr hP1).2
    have h2 := ((mem_mhat_iff_isDAIn hθ hX (Z := P.2)).mpr hP2).2
    exact ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, hP1.1⟩

theorem usetX_eq_iUset (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    usetX p A θ Y X = iUset A X Y := by
  have hD := cenIn_eq_dsub_of_mem_mtil hθ hX
  ext Z
  constructor
  · rintro ⟨⟨hZ, hZY⟩, hZX⟩
    refine ⟨⟨hZX, ?_⟩, ?_, ?_⟩
    · rw [hD]
      exact sup_le (admits_dsub_of_le hZ.2) hZ.1.1
    · rw [hD]
      exact hZ.2
    · rw [hD]
      exact hZY
  · rintro ⟨hZ, hZD, hZY⟩
    rw [hD] at hZD hZY
    exact ⟨⟨⟨mem_assoc_of_le hθ.prime hX.1 hZ.1 hZ.admits_left, hZD⟩, hZY⟩, hZ.1⟩

end Compare

end CFSG.SignalizerFunctorTheorem.McBride.Near
