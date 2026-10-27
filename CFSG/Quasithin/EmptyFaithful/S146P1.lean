module

public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Stage14613LabP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        (Case13One T M H p H₁ ∨ Case13Two T M H p H₁) ∨
          (Case13One T M H p H₂ ∨ Case13Two T M H p H₂)

section Ranks

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.mIdx_uK_sup (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hp : p = 3 ∨ p = 5) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 4 ∨
      mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8 := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hU₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hc : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hU₁ hx) (hU₂ hy)
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁)
    (uHi T M H H₂) hc
  rw [h.dir_inf] at hprod
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := by rw [S.card_Z]; norm_num
  have eS := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁ ⊔ uHi T M H H₂)
  rw [inf_eq_left.mpr (le_sup_right.trans le_sup_left)] at eS
  have e1 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₁)] at e1
  have e2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₂)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₂)] at e2
  have hmul : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) =
      (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
        (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) := by
    have hZ2 : 0 < Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T) :=
      Nat.mul_pos hZpos hZpos
    refine Nat.eq_of_mul_eq_mul_right hZ2 ?_
    rw [← eS, ← e1, ← e2] at hprod
    calc (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) *
          (Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T))
        = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) *
            Nat.card (quasithinOmegaOneCenter T)) * Nat.card (quasithinOmegaOneCenter T) := by ring
      _ = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
            Nat.card (quasithinOmegaOneCenter T)) *
          ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) *
            Nat.card (quasithinOmegaOneCenter T)) := hprod
      _ = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
            (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂)) *
          (Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T)) := by ring
  have hcard : Nat.card (uHi T M H H₁) = Nat.card (uHi T M H H₂) := by
    rw [← h.conjSub_uHi hred]
    exact (CosetGeom.card_conjSub t _).symm
  have hr : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) =
      (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) := by
    refine Nat.eq_of_mul_eq_mul_right hZpos ?_
    rw [e1, e2, hcard]
  have hne : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) ≠ 0 := Subgroup.index_ne_zero_of_finite
  unfold mIdx at *
  rw [← h.dir_sup, hmul, ← hr, padicValNat.mul hne hne]
  have h1 := h.rank₁
  rcases hp with rfl | rfl
  · rcases h1.2 rfl with h3 | h3
    · left
      unfold mIdx at h3
      omega
    · right
      unfold mIdx at h3
      omega
  · right
    have h3 := h1.1 rfl
    unfold mIdx at h3
    omega

end Ranks

@[expose] def Input14613AP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        ∀ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
          F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g →
          F8.Uγ (VZ T M) H (g : G) = F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) →
            Case13One T M H p H₁ ∨ Case13One T M H p H₂

@[expose] def Input14613B1P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        (∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
          F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
            F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) <
              F8.Uγ (VZ T M) H (g : G)) →
        mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 4 →
          Case13One T M H p H₁ ∨ Case13One T M H p H₂

@[expose] def Input14613B2P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        (∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
          F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
            F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) <
              F8.Uγ (VZ T M) H (g : G)) →
        mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8 →
          (∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
            F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
              F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) <
                F8.Uγ (VZ T M) H (g : G) ∧
              F8.Uγ (VZ T M) H (g : G) ≤ H₁ ∧
              F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₁ ∧
              quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H H₁)) ∨
          (∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
            F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
              F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) <
                F8.Uγ (VZ T M) H (g : G) ∧
              F8.Uγ (VZ T M) H (g : G) ≤ H₂ ∧
              F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₂ ∧
              quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H H₂))

theorem stage14613Lab_of_P (h : Stage14613LabP) : Stage14613Lab := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t hdec
  exact h G T M S H PQ p hred H₀ H₁ H₂ t (hdec.toIsDecP hred)

end CFSG.Quasithin
