module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.E2Seventeen
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise MatrixGroups

section Vocabulary

variable {G : Type} [Group G]

@[expose] def IsSumOfNatSL2ModulesN153 (s : ℕ) (M Si S S₂ : Subgroup G) : Prop :=
  ∃ (β : ↥M →* SL(2, ZMod 2)) (φ : ↥Si →* Multiplicative (Fin s → Fin 2 → ZMod 2)),
    Function.Surjective β ∧ (∀ x : ↥M, β x = 1 ↔ (x : G) ∈ S) ∧
    Function.Surjective φ ∧ (∀ x : ↥Si, φ x = 1 ↔ (x : G) ∈ S₂) ∧
    ∀ (m : ↥M) (x y : ↥Si), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
      φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)

abbrev Igp153 (T M V₁ Mc : Subgroup G) (g : G) : Subgroup G :=
  UH153 T M V₁ Mc ⊔ conjSubgroup (UH153 T M V₁ Mc) g

abbrev Pgp153 (T M V₁ Mc : Subgroup G) (g : G) : Subgroup G := pCoreOf 2 (Igp153 T M V₁ Mc g)

abbrev Wgp153 (T M V₁ Mc : Subgroup G) (g : G) : Subgroup G :=
  UH153 T M V₁ Mc ⊓ Pgp153 T M V₁ Mc g

noncomputable abbrev Pi153 (T Mc M V₁ : Subgroup G) (N : Subgroup (MulAut ↥(VZ T M))) (g : G) :
    Subgroup G :=
  ⁅Pgp153 T M V₁ Mc g, Yi153 T Mc M V₁ N⁆ ⊔ VZ T M

open scoped Classical in
@[expose] noncomputable def pwr153 (u : G) : ZMod 2 := if u ^ 2 = 1 then 0 else 1

open scoped Classical in
@[expose] noncomputable def comm153 (u v : G) : ZMod 2 := if ⁅u, v⁆ = 1 then 0 else 1

abbrev Fgp153 (T M V₁ Mc : Subgroup G) (y : G) : Subgroup G :=
  UH153 T M V₁ Mc ⊓ conjSubgroup Mc y

abbrev Xgp153 (T M V₁ Mc : Subgroup G) (y : G) : Subgroup G :=
  conjSubgroup (Fgp153 T M V₁ Mc y) y

abbrev Egp153 (T M V₁ Mc : Subgroup G) (y : G) : Subgroup G :=
  Fgp153 T M V₁ Mc y ⊓ conjSubgroup (Fgp153 T M V₁ Mc y) y

noncomputable abbrev V0gp153 (T Mc M V₁ : Subgroup G) (N₁ : Subgroup (MulAut ↥(VZ T M))) :
    Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) (Yi153 T Mc M V₁ N₁)

variable {W : Type*} [Group W]

@[expose] def IsFullTransvGroup153 (A : Subgroup (MulAut W)) (C : Subgroup W) : Prop :=
  ∀ g : MulAut W, g ∈ A ↔ ∀ w : W, g w * w⁻¹ ∈ C

@[expose] def IsFullAxisGroup153 (A : Subgroup (MulAut W)) (Ax : Subgroup W) : Prop :=
  ∀ g : MulAut W, g ∈ A ↔ (∀ a ∈ Ax, g a = a) ∧ ∀ w : W, g w * w⁻¹ ∈ Ax

@[expose] def commIn153 (A : Subgroup (MulAut W)) (W₀ : Subgroup W) : Subgroup W :=
  Subgroup.closure {x | ∃ a ∈ A, ∃ w ∈ W₀, x = a w * w⁻¹}

@[expose] def IsIrrOn153 (K : Subgroup (MulAut W)) (W₀ : Subgroup W) : Prop :=
  W₀ ≠ ⊥ ∧ (∀ k ∈ K, ∀ a ∈ W₀, k a ∈ W₀) ∧
    ∀ B : Subgroup W, B ≤ W₀ → (∀ k ∈ K, ∀ b ∈ B, k b ∈ B) → B = ⊥ ∨ B = W₀

end Vocabulary

@[expose] def IsD8Power153 (s : ℕ) {X : Type*} [Group X] (D : Subgroup X) : Prop :=
  (s = 0 ∧ Nat.card D = 2) ∨ (0 < s ∧ E2.IsExtraspecialPlus s D)

section Concl54

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15354 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G)
    (s : ℕ) : Prop where
  one : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc
  two_prod : ((Pgp153 T M V₁ Mc g : Subgroup G) : Set G) =
    (Wgp153 T M V₁ Mc g : Set G) * (conjSubgroup (Wgp153 T M V₁ Mc g) g : Set G)
  two_center : VZ T M ≤ centerOf (Pgp153 T M V₁ Mc g)
  three_eq : UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g =
    Wgp153 T M V₁ Mc g ⊓ conjSubgroup (Wgp153 T M V₁ Mc g) g
  three_perp : ∃ B₁ B₂ : Subgroup G, IsPerp153 cx.c (quasithinOmegaOneCenter T) B₁ ∧
    IsPerp153 cx.c (conjSubgroup (quasithinOmegaOneCenter T) g) B₂ ∧
    UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g = B₁ ⊓ B₂
  three_klein : IsKleinFour153 (UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g)
  four_sup : Pi153 T Mc M V₁ N₁ g ⊔ Pi153 T Mc M V₁ N₂ g = Pgp153 T M V₁ Mc g
  four_inf : Pi153 T Mc M V₁ N₁ g ⊓ Pi153 T Mc M V₁ N₂ g = VZ T M
  four_cent₁ : Pi153 T Mc M V₁ N₁ g =
    centralizerMod (VZ T M) (Pgp153 T M V₁ Mc g) (Ni153 T Mc M V₁ N₂)
  four_cent₂ : Pi153 T Mc M V₁ N₂ g =
    centralizerMod (VZ T M) (Pgp153 T M V₁ Mc g) (Ni153 T Mc M V₁ N₁)
  four_nat₁ : IsSumOfNatSL2ModulesN153 s (Ni153 T Mc M V₁ N₁) (Pi153 T Mc M V₁ N₁ g)
    (Pgp153 T M V₁ Mc g) (VZ T M)
  four_nat₂ : IsSumOfNatSL2ModulesN153 s (Ni153 T Mc M V₁ N₂) (Pi153 T Mc M V₁ N₂ g)
    (Pgp153 T M V₁ Mc g) (VZ T M)
  five_comm : ⁅conjSubgroup (Wgp153 T M V₁ Mc g) g, UH153 T M V₁ Mc⁆ ≤ Wgp153 T M V₁ Mc g
  five_norm : conjSubgroup (Wgp153 T M V₁ Mc g) g ≤ Subgroup.normalizer (UH153 T M V₁ Mc : Set G)

end Concl54

@[expose] def Concl15355 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
    (_cx : Ctx15350 T Mc M V₁ V₂ t) (g : G) : Prop :=
  CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc) ∧ VZ T M = centerOf (Pgp153 T M V₁ Mc g)

section Concl56

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15356 (cx : Ctx15350 T Mc M V₁ V₂ t) (N₁ : Subgroup (MulAut ↥(VZ T M))) (s : ℕ)
    (y t₁ : G) : Prop where
  orth_inv : ∀ u ∈ UH153 T M V₁ Mc, ∀ z ∈ quasithinOmegaOneCenter T, pwr153 (u * z) = pwr153 u
  orth_polar : ∀ u ∈ UH153 T M V₁ Mc, ∀ v ∈ UH153 T M V₁ Mc,
    pwr153 (u * v) + pwr153 u + pwr153 v = comm153 u v
  orth_nondeg : ∀ u ∈ UH153 T M V₁ Mc, (∀ v ∈ UH153 T M V₁ Mc, ⁅u, v⁆ = 1) →
    u ∈ quasithinOmegaOneCenter T
  orth_inv_H : ∀ h ∈ Mc, ∀ u ∈ UH153 T M V₁ Mc, pwr153 (h * u * h⁻¹) = pwr153 u
  rank : mIdx (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) = 2 * (s + 2)
  X_inf_Q : Xgp153 T M V₁ Mc y ⊓ pCoreOf 2 Mc = Egp153 T M V₁ Mc y
  comm_XF : ⁅Xgp153 T M V₁ Mc y, Fgp153 T M V₁ Mc y⁆ ≤ Egp153 T M V₁ Mc y
  V0_eq : V0gp153 T Mc M V₁ N₁ = quasithinOmegaOneCenter T ⊔
    conjSubgroup (quasithinOmegaOneCenter T) y
  E_sing : quasithinOmegaOneCenter T ≤ Egp153 T M V₁ Mc y ∧
    (∀ e ∈ Egp153 T M V₁ Mc y, e ^ 2 = 1) ∧
    mIdx (Egp153 T M V₁ Mc y) (quasithinOmegaOneCenter T) = s + 2
  X_norm_E : Xgp153 T M V₁ Mc y ≤ Subgroup.normalizer (Egp153 T M V₁ Mc y : Set G)
  X_rank : IsElemAbelianOfRank 2 (s + 1) ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y))
  X_transv : IsFullTransvGroup153
    (autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)))
    ((tildeOf (quasithinOmegaOneCenter T) (V0gp153 T Mc M V₁ N₁)).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)))
  dsum : tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) =
      tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊔
        tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) ∧
    tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊓
        tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) = ⊥
  X_norm_Et : Xgp153 T M V₁ Mc y ≤ Subgroup.normalizer (conjSubgroup (Egp153 T M V₁ Mc y) t₁ : Set G)
  X_axis : IsFullAxisGroup153
    (autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)))
    ((tildeOf (quasithinOmegaOneCenter T)
        (conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
          Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G))).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)))
  inter : XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊓
      XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) =
    XStar153 T M V₁ Mc (VZ T M)
  card_Vstar : Nat.card (XStar153 T M V₁ Mc (VZ T M)) = 2
  D8s : IsD8Power153 s (XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊔
    XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁))
  fixed : ZS153 T M V₁ = centralizerMod (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
    (Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁)

end Concl56

section Concl57

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15357 (cx : Ctx15350 T Mc M V₁ V₂ t) (s : ℕ) : Prop where
  one_ne : quasithinOmegaOneCenter T < UH153 T M V₁ Mc
  one_irr : ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W → W ≤ UH153 T M V₁ Mc →
    Mc ≤ Subgroup.normalizer (W : Set G) → W = quasithinOmegaOneCenter T ∨ W = UH153 T M V₁ Mc
  two : ∀ Kst : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))),
    Kst ≤ HStar153 T M V₁ Mc → Kst ≠ ⊥ → oTwoUpper Kst = Kst →
    (∀ h ∈ HStar153 T M V₁ Mc, ∀ k ∈ Kst, h * k * h⁻¹ ∈ Kst) →
    (∀ W₀ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
      IsIrrOn153 Kst W₀ → 8 ≤ Nat.card W₀) →
    ⁅Kst, XStar153 T M V₁ Mc (VZ T M)⁆ ≠ ⊥ ∧
      (IsIrrOn153 Kst ⊤ ∨
        ∃ W₁ W₂ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
          IsIrrOn153 Kst W₁ ∧ IsIrrOn153 Kst W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = ⊥ ∧
          Nat.card W₁ = 2 ^ (s + 2) ∧ Nat.card W₂ = 2 ^ (s + 2) ∧
          (∀ v ∈ XStar153 T M V₁ Mc (VZ T M), ∀ w ∈ W₁, v w ∈ W₁) ∧
          (∀ v ∈ XStar153 T M V₁ Mc (VZ T M), ∀ w ∈ W₂, v w ∈ W₂) ∧
          Nat.card ↥(commIn153 (XStar153 T M V₁ Mc (VZ T M)) W₁) = 2 ∧
          Nat.card ↥(commIn153 (XStar153 T M V₁ Mc (VZ T M)) W₂) = 2)

end Concl57

section Concl58

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure Concl15358 (cx : Ctx15350 T Mc M V₁ V₂ t) (s : ℕ) : Prop where
  one : Nonempty (↥(HStar153 T M V₁ Mc) ≃* MulAut ↥(StatedSL 3 (ZMod 2)))
  two_s : s = 1
  two_U : E2.IsExtraspecialPlus 3 (UH153 T M V₁ Mc)
  three : ∀ t₁ ∈ T, t₁ ∉ UCT153 T M V₁ Mc →
    ∃ (π : ↥(StatedSL 3 (ZMod 2)) →* ↥(oTwoUpper (HStar153 T M V₁ Mc))) (U₁ : Subgroup G),
      quasithinOmegaOneCenter T ≤ U₁ ∧ U₁ ≤ UH153 T M V₁ Mc ∧
      letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
        commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
      IsIntDirect
        ((tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf
          (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
        ((tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ t₁)).subgroupOf
          (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ⊤ ∧
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia (oTwoUpper (HStar153 T M V₁ Mc))
        ((tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf
          (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ⊥ π ∧
      (FFModel.dualNat (StatedSL 3 (ZMod 2))).RealizesVia (oTwoUpper (HStar153 T M V₁ Mc))
        ((tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ t₁)).subgroupOf
          (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ⊥ π

end Concl58

end CFSG.Quasithin
