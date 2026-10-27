module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux4
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

theorem exists_perfect_sup
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) (hX₂sol : Group.IsSolvable ↥X₂)
    (hKX₁ : ¬ (kOf X ⊓ X₁ ≤ X₂)) :
    ∃ W : Subgroup Γ, W ≤ kOf X ⊓ X₁ ∧ Group.IsPerfect ↥W ∧
      Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) W ∧ W ⊔ X₂ = X₁ ∧ W ⊓ X₂ = ⊥ := by
  have hss := semisimpleAction_kOf h hsol hXne
  have hXK : Admits X (kOf X) :=
    Subgroup.le_normalizer.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hHK : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (kOf X) :=
    sup_le (sup_le ((pair_le hP).trans hXK) (inf_le_left.trans hXK))
      (h.admits.trans (Thm211.normalizer_le_normalizer_kOf X))
  have hBadm : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (kOf X ⊓ X₁) :=
    Admits.inf hHK (pair_admits_H hP)
  have hB : (kOf X ⊓ X₁) ⊔ X₂ = X₁ :=
    (chief_dichotomy (pair_chief hP) hBadm inf_le_right).resolve_left hKX₁
  set W : Subgroup Γ := perfRes (kOf X ⊓ X₁) with hWdef
  have hWB : W ≤ kOf X ⊓ X₁ := Subgroup.map_subtype_le _
  have hWK : W ≤ kOf X := hWB.trans inf_le_left
  have hWX₁ : W ≤ X₁ := hWB.trans inf_le_right
  have hWperf : Group.IsPerfect ↥W := Nonsolvable.isPerfect_perfectResidual_map _
  have hWadm : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) W :=
    hBadm.trans (Nonsolvable.normalizer_le_normalizer_perfectResidual_map _)
  have hWX : W ⊔ X₂ = X₁ := by
    rcases chief_dichotomy (pair_chief hP) hWadm hWX₁ with hle | heq
    · exact (not_perfRes_le hP inf_le_right hB hle).elim
    · exact heq
  refine ⟨W, hWB, hWperf, hWadm, hWX, ?_⟩
  have hRsol : Group.IsSolvable ↥(X₂ ⊓ kOf X) := Thm211.isSolvable_of_le inf_le_left hX₂sol
  have hWX₂ : Admits W X₂ := (hWX₁.trans le_H).trans (pair_admits_H₂ hP)
  have hWR : Admits W (X₂ ⊓ kOf X) := Admits.inf hWX₂ (hWK.trans Subgroup.le_normalizer)
  have hWDA : Admits (cenIn (kOf X) (A : Set Γ) ⊔ A) W :=
    (sup_le_sup_right (inf_le_inf_right _ (kOf_le X)) A).trans
      ((sup_le (dsub_le_H.trans le_rfl) le_sup_right).trans hWadm)
  have hbot := inf_eq_bot_of_solvable hss hWK inf_le_right hWDA hWperf hRsol hWR
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx' : x ∈ W ⊓ (X₂ ⊓ kOf X) := Subgroup.mem_inf.mpr ⟨hx.1, hx.2, hWK hx.1⟩
  rw [hbot] at hx'
  exact hx'

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a
