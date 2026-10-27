module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups

@[expose] def ThreeCover (S : ∀ (Y : Type) [Group Y], Prop) (L : Type) [Group L] : Prop :=
  CFSG.Open.IsQuasisimple L ∧ Nat.card (Subgroup.center L) = 3 ∧ S (L ⧸ Subgroup.center L)

@[expose] def K32 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsKGroup L → IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 1 →
      (∃ p f : ℕ, LieModel L .PSL 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 3 p f) ∨ IsSpor L .J1

@[expose] def K33 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) → IsPGroup 3 (Subgroup.center L) →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 →
      (ThreeCover (fun Y _ => IsAlt Y 6) L ∨ ThreeCover (fun Y _ => IsAlt Y 7) L ∨
        ThreeCover (fun Y _ => IsSpor Y .M22) L ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ ThreeCover (fun Y _ => LieModel Y .PSL 3 p f) L) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ ThreeCover (fun Y _ => LieModel Y .PSU 3 p f) L)) ∨
      (IsAlt L 7 ∨ IsAlt L 6) ∨
      (LieModel L .PSL 3 3 1 ∨ LieModel L .PSU 3 3 1) ∨
      ((∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSL 3 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSU 3 p f) ∨
        (∃ p f : ℕ, LieModel L .PSp 2 p f) ∨ (∃ p f : ℕ, LieModel L .G2 0 p f) ∨
        (∃ p f : ℕ, LieModel L .trialityD4 0 p f) ∨ (∃ f : ℕ, LieModel L .twistedF4 0 2 f) ∨
        LieModel L .Tits 0 2 1 ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 5 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 5 p f)) ∨
      ∃ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
        s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) ∧ IsSpor L s

@[expose] def K34 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) → IsPGroup 3 (Subgroup.center L) →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 →
      ThreeCover (fun Y _ => IsSpor Y .ONan) L ∨
      (IsAlt L 9 ∨ IsAlt L 10 ∨ IsAlt L 11) ∨
      (LieModel L .PSL 2 3 3 ∨ LieModel L .PSp 2 3 1) ∨
      ((∃ p f : ℕ, LieModel L .PSp 3 p f) ∨ (∃ p f : ℕ, LieModel L .POmegaMinus 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSL 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSU 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 6 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 6 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 7 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 7 p f) ∨
        (∃ p f : ℕ, p ≠ 3 ∧ LieModel L .POmegaOdd 3 p f)) ∨
      IsSpor L .J3

@[expose] def IrredGL3 (p : ℕ) (G : Subgroup (GL (Fin 3) (ZMod p))) : Prop :=
  ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p),
    (∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def cartanOfDecomp (p : ℕ) (W : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p)) :
    Subgroup (GL (Fin 3) (ZMod p)) where
  carrier := {h | ∀ i (v : Fin 3 → ZMod p),
    (h : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec v ∈ W i ↔ v ∈ W i}
  mul_mem' {a b} ha hb i v := by
    have : ((a * b : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec v =
        (a : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
          ((b : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec v) := by
      simp [Matrix.mulVec_mulVec]
    rw [this, ha i, hb i]
  one_mem' i v := by simp
  inv_mem' {a} ha i v := by
    have h1 := ha i (((a⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec v)
    have h2 : (a : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
        (((a⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec v) = v := by
      simp [Matrix.mulVec_mulVec]
    rw [h2] at h1
    exact h1.symm

@[expose] def K322 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ G : Subgroup (GL (Fin 3) (ZMod p)), IrredGL3 p G → ¬ p ∣ Nat.card G →
    ∀ Z : Submodule (ZMod p) (Fin 3 → ZMod p), Module.finrank (ZMod p) Z = 1 →
    ∀ x ∈ G, orderOf x = 4 →
      {v : Fin 3 → ZMod p | (((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
        v = v)} = (Z : Set (Fin 3 → ZMod p)) →
      ((p ^ 3 % 7 = 1 ∧ LieModel ↥(genFittingLayer ↥G) .PSL 3 2 1) ∨
        (p % 30 = 1 ∨ p % 30 = 19) ∧ ThreeCover (fun Y _ => IsAlt Y 6) ↥(genFittingLayer ↥G) ∨
        (p % 3 = 1 ∧ ∃ H : Subgroup (GL (Fin 3) (ZMod p)), H ≤ G ∧ (H.subgroupOf G).Normal ∧
          ExtraspecialExpP 3 H) ∨
        (Set.ncard {W : Submodule (ZMod p) (Fin 3 → ZMod p) | ∃ g ∈ G,
            W = Z.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod p)))} = 3 ∧
          ∃ W : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p),
            (∀ i, Module.finrank (ZMod p) (W i) = 1) ∧ iSupIndep W ∧ (⨆ i, W i) = ⊤ ∧
              G ≤ normalizer ((cartanOfDecomp p W : Subgroup (GL (Fin 3) (ZMod p))) :
                Set (GL (Fin 3) (ZMod p))))) ∧
        3 ∣ Nat.card G ∧ 3 < p

@[expose] def K323 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ G : Subgroup (GL (Fin 3) (ZMod p)), IrredGL3 p G →
    ∀ Z : Submodule (ZMod p) (Fin 3 → ZMod p), Module.finrank (ZMod p) Z = 1 →
    ∀ X : Subgroup (GL (Fin 3) (ZMod p)), X ≤ G →
      (∀ x ∈ X, ∀ z ∈ Z, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec z = z) →
      IsCyclic X → Nat.card X = (p ^ 2 - 1) / 2 → p ∣ Nat.card G

@[expose] def K324 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2 →
    ∀ E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 5 E ⊤ → CFSG.Open.IsElemAbelian 5 E →
    Nat.card E = 25 → ∀ Z : Subgroup G, Z ≤ E → Nat.card Z = 5 →
    IsAlt ↥((genFittingLayer ↥(centralizer (Z : Set G))).map (centralizer (Z : Set G)).subtype) 6 →
      ¬ 3 ∣ Nat.card ↥(Subgroup.normalClosure (Z : Set G))

end CFSG.LocalAnalysis.UniquenessCase.UCK
