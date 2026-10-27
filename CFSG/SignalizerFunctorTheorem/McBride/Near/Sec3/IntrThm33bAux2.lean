module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux1

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

open Thm33a

variable {Γ : Type u} [Group Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

theorem iEset_of_le {X' : Subgroup Γ} (hDX' : cenIn X (A : Set Γ) ≤ X') (hX'X : X' ≤ X) :
    iEset A X' Y = {Z | Z ∈ iEset A X Y ∧ Z ≤ X'} := by
  have hcen : cenIn X' (A : Set Γ) = cenIn X (A : Set Γ) := Thm211.cenIn_eq_of_le hX'X hDX'
  ext Z
  simp only [iEset, IsDAIn, Set.mem_ofPred_eq, hcen]
  constructor
  · rintro ⟨⟨hZ', hZadm⟩, hZY⟩
    exact ⟨⟨⟨hZ'.trans hX'X, hZadm⟩, hZY⟩, hZ'⟩
  · rintro ⟨⟨⟨_, hZadm⟩, hZY⟩, hZ'⟩
    exact ⟨⟨hZ', hZadm⟩, hZY⟩

theorem sup_dsub_mem_iUset {Z : Subgroup Γ} (hZ : Z ∈ iEset A X Y) :
    Z ⊔ cenIn X (A : Set Γ) ∈ iUset A X Y := by
  have hYZ : Y ≤ Z := hZ.2 ▸ inf_le_left
  have hYD : Y ≤ cenIn X (A : Set Γ) := hZ.2 ▸ inf_le_right
  refine ⟨⟨sup_le hZ.1.1 inf_le_left, hZ.1.2.sup (admits_cenIn_sup A X)⟩, le_sup_right,
    le_antisymm ?_ (le_inf (le_orbitClosure _ _) hYD)⟩
  have h1 : orbitClosure Y (Z ⊔ cenIn X (A : Set Γ)) ≤ Z :=
    orbitClosure_le_of_admits hYZ (sup_le Subgroup.le_normalizer hZ.1.admits_dsub)
  calc orbitClosure Y (Z ⊔ cenIn X (A : Set Γ)) ⊓ cenIn X (A : Set Γ)
      ≤ Z ⊓ cenIn X (A : Set Γ) := inf_le_inf_right _ h1
    _ = Y := hZ.2

theorem le_iThetaU_of_mem_iEset {Z : Subgroup Γ} (hZ : Z ∈ iEset A X Y) :
    Z ≤ iThetaU A X Y :=
  le_sup_left.trans (le_iThetaU (sup_dsub_mem_iUset hZ))

variable [Finite Γ]

theorem concl_iff_of_le {X' : Subgroup Γ} (hP : (X₁, X₂) ∈ iPairsY A X Y) (hX'X : X' ≤ X)
    (hU : iThetaU A X Y ≤ X') (hK : kOf X ≤ X') : Concl A X' Y ↔ Concl A X Y := by
  have hD : cenIn X (A : Set Γ) ≤ X' := (dsub_le_iThetaU hP).trans hU
  have hpairs : iPairsY A X' Y = iPairsY A X Y := by
    rw [iPairsY_of_le hD hX'X]
    ext P
    exact ⟨fun hP' => hP'.1, fun hP' =>
      ⟨hP', (pair_le_iThetaU (X₁ := P.1) (X₂ := P.2) hP').trans hU⟩⟩
  have hE : iEset A X' Y = iEset A X Y := by
    rw [iEset_of_le hD hX'X]
    ext Z
    exact ⟨fun hZ => hZ.1, fun hZ => ⟨hZ, (le_iThetaU_of_mem_iEset hZ).trans hU⟩⟩
  have hKe : kOf X' = kOf X := kOf_eq_of_kOf_le hX'X hK
  unfold Concl iThetaM iThetaL iThetaY
  rw [hpairs, hE, hKe]

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b
