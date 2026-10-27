module

public import CFSG.Quasithin.EmptyFaithful.S153GCount

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def CountStrongD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → ∀ A : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A →
        cm3 (conjBy153 t' (UL153 T I L)) A <
            rk ↥A - rk ↥(A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) →
          cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) A + 1 =
            cm3 (conjBy153 t' (UL153 T I L)) A

theorem countSideUt_of_strong (hI : CountIneq) (hU : CountSideU) (hD : CountStrongD) :
    CountSideUt := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA
  have h1 := hU G T Mc M V₁ V₂ Yp I L t c cc A hA
  have h2 := hI G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA.1
  have hPeq : P153 T M V₁ = (Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)) ⊔
      (Sgp153 T V₁ ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) :=
    (cc.P_split t' ht'T ht'S).1
  have hCP : Sgp153 T V₁ ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) ≤
      P153 T M V₁ := by
    rw [hPeq]
    exact le_sup_right
  have hAS : A ≤ Sgp153 T V₁ := hA.1.1
  have heq : A ⊓ P153 T M V₁ ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) =
      A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := by
    refine le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx => ⟨⟨hx.1, hCP ⟨hAS hx.1, hx.2⟩⟩, hx.2⟩
  have m1 : rk ↥(A ⊓ P153 T M V₁) ≤ rk ↥A := rk_mono inf_le_left
  have m2 : rk ↥(A ⊓ P153 T M V₁ ⊓ Subgroup.centralizer
      ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) ≤ rk ↥(A ⊓ P153 T M V₁) :=
    rk_mono inf_le_left
  have hrank : rk ↥A - rk ↥(A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) =
      cm0 (P153 T M V₁) A + cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) A := by
    simp only [cm0, cm1]
    rw [← heq]
    omega
  refine hD G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA.1 ?_
  rw [hrank]
  obtain ⟨-, h1b, -⟩ := h1
  omega

end CFSG.Quasithin
