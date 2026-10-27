module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofHalf
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

structure GGHalfCoords {G : Type} [Group G] (Bs L J K : Subgroup G) (m : ℕ)
    (φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : Prop where
  range₁ : φ₁.range = L
  range₂ : φ₂.range = K
  inj₁ : Function.Injective φ₁
  inj₂ : Function.Injective φ₂
  agree : φ₁.comp (slLower2Hom m) = φ₂.comp (slUpper2Hom m)
  rangeJ : (φ₁.comp (slLower2Hom m)).range = J
  actL : ∀ b ∈ Bs, ∃ t ∈ halfTorus (m + 1 + 1), ∀ l ∈ L, b * l * b⁻¹ = φ₁ t * l * (φ₁ t)⁻¹
  actK : ∀ b ∈ Bs, ∃ t ∈ halfTorusK (m + 1 + 1), ∀ k ∈ K, b * k * b⁻¹ = φ₂ t * k * (φ₂ t)⁻¹

@[expose] def GGTypeAHalfCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J →
    GGTypeAHalfNbr p B Bs x L D J (m + 1 + 1) y K →
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) (GaloisField 2 1) →* G,
      GGHalfCoords Bs L J K m φ₁ φ₂

@[expose] def GGHalfEndNodesOn (S : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n : ℕ) (y : G) (K : Subgroup G), S n → GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeAHalfNbr p B Bs x L D J n y K →
    GGHalfAutWithin Bs L K →
    ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1)) ∧
      ∃ T₁ T₂ : G, T₁ ∈ L ⊔ K ∧ T₂ ∈ L ⊔ K ∧ GGTypeATwoEndNodes φ₁ T₁ T₂ ∧
        K ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
          L.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
            L.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom

theorem GGHalfEndNodesOn.of_cases (h5 : GGHalfEndNodesOn (fun n => n = 5))
    (h6 : GGHalfEndNodesOn (fun n => 6 ≤ n)) : GGTypeAHalfJoinEndNodesInput := by
  intro G _ _ p B Bs x L D J n y K hcfg hOp hInn hNoTr hN hAut
  by_cases hn5 : n = 5
  · exact h5 G p B Bs x L D J n y K hn5 hcfg hOp hInn hNoTr hN hAut
  · exact h6 G p B Bs x L D J n y K (by have := hN.2.2.1; omega) hcfg hOp hInn hNoTr hN hAut

structure GGHalfCtx {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (m : ℕ) (y : G) (K : Subgroup G)
    (φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : Prop where
  cfg : GGConfig p B Bs x L D J
  inner : GGInnerDiagAll p B Bs x L D J
  noTr : GGNoTransvection p Bs
  nbr : GGTypeAHalfNbr p B Bs x L D J (m + 1 + 1) y K
  coords : GGHalfCoords Bs L J K m φ₁ φ₂

section Elts

variable {G : Type} [Group G] {m : ℕ}

@[expose] noncomputable def GGHalf.gElt
    (φ₁ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₁ (slPerm gf2_two (sigmaPerm m))

@[expose] noncomputable def GGHalf.hElt
    (φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₂ (slPerm gf2_two (tauPerm m))

@[expose] noncomputable def GGHalf.endT₁
    (φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₂ (weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)

@[expose] noncomputable def GGHalf.endT₂
    (φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₂ (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩)

@[expose] noncomputable def GGHalf.vElt
    (φ₁ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩)

@[expose] noncomputable def GGHalf.uElt
    (φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₂ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩)

@[expose] noncomputable def GGHalf.wElt
    (φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)

@[expose] noncomputable def GGHalf.sZero
    (φ₁ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : G :=
  φ₁ (weylRep (m + 1 + 1) F2 ⟨0, by omega⟩)

@[expose] def GGHalf.zSet
    (φ₁ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : Set G :=
  {z | ∃ k : Fin (m + 1 + 1), k.val % 2 = 0 ∧ 4 ≤ k.val ∧ z = φ₁ (omegaBlock (m + 1 + 1) k)}

@[expose] def GGHalf.GGHalfNormSL014
    (φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : Prop :=
  ((slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁).map (MulAut.conj (hElt φ₂)).toMonoidHom =
    (slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁

@[expose] def GGHalf.GGHalfAlphaInner
    (φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G) : Prop :=
  ∃ a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
    ∀ s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ = hElt φ₂ * φ₁ (a * s * a⁻¹) * (hElt φ₂)⁻¹

end Elts

end CFSG.StandardType

end
