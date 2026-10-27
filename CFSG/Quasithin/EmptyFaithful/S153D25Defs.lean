module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.EmptyFaithful.S153D0All

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

noncomputable abbrev Star153 {G : Type} [Group G] (T I X : Subgroup G) : Subgroup (MulAut ↥(UI153 T I)) :=
  autOn X (UI153 T I)

abbrev UL153 {G : Type} [Group G] (T I L : Subgroup G) : Subgroup G := ⁅UI153 T I, L⁆

structure Facts153 {G : Type} [Group G] [Finite G] (T M V₁ Yp I : Subgroup G) : Prop where
  sylow : IsSylowTwoOf (Sgp153 T V₁) I
  cent_le : I ⊓ Subgroup.centralizer (UI153 T I : Set G) ≤ M ⊓ I
  norm_eq : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I
  theta : Yp = thetaOf (M ⊓ I)
  star_norm : Subgroup.normalizer (Star153 T I Yp : Set (MulAut ↥(UI153 T I))) ⊓ Star153 T I I =
    Star153 T I (M ⊓ I)
  star_lt : Star153 T I (M ⊓ I) < Star153 T I I
  star_ne : Star153 T I Yp ≠ ⊥
  J_not_le : ¬ Star153 T I (thompsonJ I) ≤ Star153 T I (M ⊓ I)

structure Facts15325 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) : Prop
    extends Facts153 T M V₁ Yp I where
  case_two : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
    Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))
  s3 : ∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
    φ.ker = (R153 T V₁ Yp).subgroupOf (Yp ⊔ Sgp153 T V₁)
  yp_eq : Yp = oPrimeResidualOf 3 (M ⊓ I)
  R_eq : R153 T V₁ Yp = Sgp153 T V₁ ⊓ Subgroup.centralizer (V₂ : Set G)

@[expose] def Input15311FiveII : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 1 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
            Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) ∧
          (∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
            φ.ker = (R153 T V₁ Yp).subgroupOf (Yp ⊔ Sgp153 T V₁)) ∧
          Yp = oPrimeResidualOf 3 (M ⊓ I) ∧
          R153 T V₁ Yp = Sgp153 T V₁ ⊓ Subgroup.centralizer (V₂ : Set G)

structure Ctx15325 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G) :
    Prop where
  hyp : Hyp15310 G T Mc M V₁ V₂ Yp t
  inH : IsHPlus Yp (Sgp153 T V₁) M I
  rank : CFSG.Open.pRank 3 Yp = 1
  charTwo : CharTwo I

structure Ctx15325L {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop where
  ctx : Ctx15325 T Mc M V₁ V₂ Yp I t
  facts : Facts15325 T Mc M V₁ V₂ Yp I
  conc : Concl15315Two T M Yp I L

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem facts153_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    Facts153 T M V₁ Yp I where
  sylow := h.lemma_15_3_11_one h11 h113 hI
  cent_le := h.lemma_15_3_11_two h113 hI
  norm_eq := h.lemma_15_3_11_four h113 hI
  theta := h.theta_eq h113 hI
  star_norm := h.star_norm h113 hI
  star_lt := h.star_lt h113 hI
  star_ne := h.star_ne h113 hI
  J_not_le := J_not_le_of_hyp h11 h113 h hI

theorem facts15325_of_inputs (hin : Input15311FiveII) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hr : CFSG.Open.pRank 3 Yp = 1)
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) : Facts15325 T Mc M V₁ V₂ Yp I := by
  obtain ⟨h2, h3, h4, h5⟩ := hin G T Mc M V₁ V₂ Yp t h hr I hI
  exact { facts153_of_stages h11 h113 h hI with case_two := h2, s3 := h3, yp_eq := h4, R_eq := h5 }

end S153D

end CFSG.Quasithin
