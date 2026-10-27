module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a

variable {Γ : Type u} [Group Γ] {A X Y X₁ X₂ : Subgroup Γ}

theorem admits_orbitClosure {Q Y Z : Subgroup Γ} (hY : Admits Q Y) (hZ : Admits Q Z) :
    Admits Q (orbitClosure Y Z) := by
  rw [Thm211.admits_iff] at hY hZ ⊢
  intro q hq x hx
  have hle : orbitClosure Y Z ≤ (orbitClosure Y Z).comap (MulAut.conj q).toMonoidHom := by
    refine orbitClosure_le fun a ha y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have h1 : (MulAut.conj q).toMonoidHom ((MulAut.conj a).toMonoidHom y₀) =
        (MulAut.conj (q * a * q⁻¹)).toMonoidHom (q * y₀ * q⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h2 : (MulAut.conj (q * a * q⁻¹)).toMonoidHom (q * y₀ * q⁻¹) ∈
        orbitClosure Y Z :=
      map_conj_le_orbitClosure Y (hZ q hq a ha) ⟨q * y₀ * q⁻¹, hY q hq y₀ hy₀, rfl⟩
    rw [Subgroup.mem_comap, h1]
    exact h2
  simpa [MulAut.conj_apply] using hle hx

theorem orbitClosure_le_of_admits {Y Z L : Subgroup Γ} (hY : Y ≤ L) (hZ : Admits Z L) :
    orbitClosure Y Z ≤ L :=
  orbitClosure_le fun a ha => by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hZ ha) y).mp (hY hy)

theorem admits_left_cenIn (A X : Subgroup Γ) : Admits A (cenIn X (A : Set Γ)) :=
  Thm211.le_normalizer_inf_of_le_centralizer le_rfl

theorem admits_cenIn_sup (A X : Subgroup Γ) :
    Admits (cenIn X (A : Set Γ) ⊔ A) (cenIn X (A : Set Γ)) :=
  sup_le Subgroup.le_normalizer (admits_left_cenIn A X)

theorem le_iThetaU {Z : Subgroup Γ} (hZ : Z ∈ iUset A X Y) : Z ≤ iThetaU A X Y :=
  le_iSup₂ (f := fun Z (_ : Z ∈ iUset A X Y) => Z) Z hZ

theorem iThetaU_le : iThetaU A X Y ≤ X :=
  iSup₂_le fun _ hZ => hZ.1.1

theorem iThetaU_le_of {L : Subgroup Γ} (h : ∀ Z ∈ iUset A X Y, Z ≤ L) : iThetaU A X Y ≤ L :=
  iSup₂_le h

theorem admits_iThetaU : Admits (cenIn X (A : Set Γ) ⊔ A) (iThetaU A X Y) :=
  Admits.iSup fun _ => Admits.iSup fun hZ => hZ.1.2

theorem admits_iThetaU_of {Q : Subgroup Γ} (h : ∀ Z ∈ iUset A X Y, Admits Q Z) :
    Admits Q (iThetaU A X Y) :=
  Admits.iSup fun Z => Admits.iSup fun hZ => h Z hZ

theorem iUset_of_le {X' : Subgroup Γ} (hDX' : cenIn X (A : Set Γ) ≤ X') (hX'X : X' ≤ X) :
    iUset A X' Y = {Z | Z ∈ iUset A X Y ∧ Z ≤ X'} := by
  have hcen : cenIn X' (A : Set Γ) = cenIn X (A : Set Γ) := Thm211.cenIn_eq_of_le hX'X hDX'
  ext Z
  simp only [iUset, IsDAIn, Set.mem_ofPred_eq, hcen]
  constructor
  · rintro ⟨⟨hZ', hZadm⟩, hDZ, hY⟩
    exact ⟨⟨⟨hZ'.trans hX'X, hZadm⟩, hDZ, hY⟩, hZ'⟩
  · rintro ⟨⟨⟨_, hZadm⟩, hDZ, hY⟩, hZ'⟩
    exact ⟨⟨hZ', hZadm⟩, hDZ, hY⟩

theorem iUset_eq_of_iThetaU_le {X' : Subgroup Γ} (hDX' : cenIn X (A : Set Γ) ≤ X')
    (hX'X : X' ≤ X) (h : iThetaU A X Y ≤ X') : iUset A X' Y = iUset A X Y := by
  rw [iUset_of_le hDX' hX'X]
  ext Z
  exact ⟨fun hZ => hZ.1, fun hZ => ⟨hZ, (le_iThetaU hZ).trans h⟩⟩

theorem iThetaU_eq_of_iThetaU_le {X' : Subgroup Γ} (hDX' : cenIn X (A : Set Γ) ≤ X')
    (hX'X : X' ≤ X) (h : iThetaU A X Y ≤ X') : iThetaU A X' Y = iThetaU A X Y := by
  unfold iThetaU
  rw [iUset_eq_of_iThetaU_le hDX' hX'X h]

theorem iPairsY_of_le {X' : Subgroup Γ} (hDX' : cenIn X (A : Set Γ) ≤ X') (hX'X : X' ≤ X) :
    iPairsY A X' Y = {P | P ∈ iPairsY A X Y ∧ P.1 ≤ X'} := by
  have hcen : cenIn X' (A : Set Γ) = cenIn X (A : Set Γ) := Thm211.cenIn_eq_of_le hX'X hDX'
  ext ⟨P₁, P₂⟩
  simp only [iPairsY, iPairs, IsDAIn, Set.mem_ofPred_eq, hcen]
  constructor
  · rintro ⟨⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, h3, h4⟩, h5⟩
    exact ⟨⟨⟨⟨h1.trans hX'X, h1'⟩, ⟨h2.trans hX'X, h2'⟩, h3, h4⟩, h5⟩, h1⟩
  · rintro ⟨⟨⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, h3, h4⟩, h5⟩, h6⟩
    exact ⟨⟨⟨h6, h1'⟩, ⟨(h3.2.2.1.le).trans h6, h2'⟩, h3, h4⟩, h5⟩

theorem le_H : X₁ ≤ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A := le_sup_left.trans le_sup_left

theorem dsub_le_H : cenIn X (A : Set Γ) ≤ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A :=
  le_sup_right.trans le_sup_left

section Pair

variable (hP : (X₁, X₂) ∈ iPairsY A X Y)

include hP

theorem pair_le : X₁ ≤ X := hP.1.1.1

theorem pair_lt : X₂ < X₁ := hP.1.2.2.1.2.2.1


theorem pair_chief : IsChiefFactorOf (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) X₁ X₂ := hP.1.2.2.1

theorem pair_secCenIn : secCenIn (X₁ ⊔ cenIn X (A : Set Γ)) X₁ X₂ = X₂ := hP.1.2.2.2

theorem pair_inf : X₂ ⊓ cenIn X (A : Set Γ) = Y := hP.2

theorem pair_admits_left : Admits (cenIn X (A : Set Γ) ⊔ A) X₁ := hP.1.1.2

theorem pair_admits_H : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) X₁ := hP.1.2.2.1.2.1.2

theorem pair_admits_H₂ : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) X₂ := hP.1.2.2.1.1.2

theorem pair_le₂ : X₂ ≤ X₁ := (pair_lt hP).le

theorem pair_Y_le : Y ≤ cenIn X (A : Set Γ) := (pair_inf hP) ▸ inf_le_right

theorem pair_Y_le₂ : Y ≤ X₂ := (pair_inf hP) ▸ inf_le_left

theorem pair_admits_DA₂ : Admits (cenIn X (A : Set Γ) ⊔ A) X₂ :=
  le_trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right) (pair_admits_H₂ hP)

theorem pair_admits_X₁D₂ : Admits (X₁ ⊔ cenIn X (A : Set Γ)) X₂ :=
  le_trans le_sup_left (pair_admits_H₂ hP)

theorem pair_admits_Y : Admits (cenIn X (A : Set Γ) ⊔ A) Y := by
  rw [← pair_inf hP]
  exact (pair_admits_DA₂ hP).inf (admits_cenIn_sup A X)

theorem pair_admits_D_Y : Admits (cenIn X (A : Set Γ)) Y :=
  le_sup_left.trans (pair_admits_Y hP)

end Pair

theorem dsub_mem_iUset (hY : Admits (cenIn X (A : Set Γ)) Y) (hYD : Y ≤ cenIn X (A : Set Γ)) :
    cenIn X (A : Set Γ) ∈ iUset A X Y := by
  refine ⟨⟨inf_le_left, admits_cenIn_sup A X⟩, le_rfl,
    le_antisymm ?_ (le_inf (le_orbitClosure _ _) hYD)⟩
  exact (inf_le_inf_right _ (orbitClosure_le_of_admits le_rfl hY)).trans inf_le_left

theorem sup_mem_iUset (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    X₁ ⊔ cenIn X (A : Set Γ) ∈ iUset A X Y := by
  refine ⟨⟨sup_le (pair_le hP) inf_le_left,
    (pair_admits_left hP).sup (admits_cenIn_sup A X)⟩, le_sup_right, le_antisymm ?_
    (le_inf (le_orbitClosure _ _) (pair_Y_le hP))⟩
  have h1 : orbitClosure Y (X₁ ⊔ cenIn X (A : Set Γ)) ≤ X₂ :=
    orbitClosure_le_of_admits (pair_Y_le₂ hP) (pair_admits_X₁D₂ hP)
  calc orbitClosure Y (X₁ ⊔ cenIn X (A : Set Γ)) ⊓ cenIn X (A : Set Γ)
      ≤ X₂ ⊓ cenIn X (A : Set Γ) := inf_le_inf_right _ h1
    _ = Y := pair_inf hP

theorem pair_le_iThetaU (hP : (X₁, X₂) ∈ iPairsY A X Y) : X₁ ≤ iThetaU A X Y :=
  le_sup_left.trans (le_iThetaU (sup_mem_iUset hP))

theorem dsub_le_iThetaU (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    cenIn X (A : Set Γ) ≤ iThetaU A X Y :=
  le_sup_right.trans (le_iThetaU (sup_mem_iUset hP))

theorem iThetaU_mem_iUset_of (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (h : orbitClosure Y (iThetaU A X Y) ⊓ cenIn X (A : Set Γ) = Y) :
    iThetaU A X Y ∈ iUset A X Y :=
  ⟨⟨iThetaU_le, admits_iThetaU⟩, dsub_le_iThetaU hP, h⟩

theorem chief_dichotomy {H L N M : Subgroup Γ} (hc : IsChiefFactorOf H L N) (hM : Admits H M)
    (hML : M ≤ L) : M ≤ N ∨ M ⊔ N = L := by
  have hK : IsNormalIn (M ⊔ N) H :=
    ⟨sup_le (hML.trans hc.2.1.1) hc.1.1, (hM.sup hc.1.2)⟩
  rcases hc.2.2.2 (M ⊔ N) hK le_sup_right (sup_le hML hc.2.2.1.le) with h | h
  · exact Or.inl (sup_eq_right.mp h)
  · exact Or.inr h

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a
