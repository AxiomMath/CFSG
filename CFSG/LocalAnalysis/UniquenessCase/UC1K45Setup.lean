module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open scoped commutatorElement

@[expose] def Z3E9A5Mod2 {H : Type} [Group H] (Y : Subgroup H) : Prop :=
  ∀ (N : Subgroup ↥Y) [N.Normal], N = (CFSG.Open.pCoreOf 2 Y).subgroupOf Y →
    (IsCyclic (↥Y ⧸ N) ∧ Nat.card (↥Y ⧸ N) = 3) ∨
    (Nat.card (↥Y ⧸ N) = 9 ∧ IsMulCommutative (↥Y ⧸ N)) ∨ CFSG.Quasithin.IsAlt 5 (↥Y ⧸ N)

@[expose] def PairSp : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (B : LinearMap.BilinForm (ZMod 2) W), B.Nondegenerate → B.IsAlt →
    ∀ a b : W ≃ₗ[ZMod 2] W,
      (∀ x y, B (a x) (a y) = B x y) → (∀ x y, B (b x) (b y) = B x y) →
      orderOf a = 3 → orderOf b = 3 →
      Module.finrank (ZMod 2) (LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 →
      Module.finrank (ZMod 2) (LinearMap.range ((b : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 →
      Z3E9A5Mod2 (Subgroup.closure {a, b})

@[expose] def InspPairShape : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Open.IsKGroup S → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1 →
    ¬ CFSG.Quasithin.IsAlt 5 S → ∀ D : Subgroup S, Nat.card D = 3 →
      ∃ g : S, ¬ Z3E9A5Mod2 (D ⊔ D.map (MulAut.conj g).toMonoidHom)

@[expose] def SimpleThreePrimeIsSz : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ¬ (∀ a b : S, a * b = b * a) →
    CFSG.Open.IsKGroup S → ¬ 3 ∣ Nat.card S → ∃ f : ℕ, CFSG.Blueprint.SuzukiModel S 2 f

@[expose] def SzOrder3Aut : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (f : ℕ), CFSG.Blueprint.SuzukiModel S 2 f →
    ∀ σ : MulAut S, orderOf σ = 3 →
      ∃ ℓ₁ ℓ₂ : ℕ, ℓ₁.Prime ∧ ℓ₂.Prime ∧ ℓ₁ ≠ ℓ₂ ∧ ℓ₁ ≠ 2 ∧ ℓ₂ ≠ 2 ∧
        ∀ P : Subgroup S,
          (CFSG.ABGLocalTools.IsSylowOf ℓ₁ P ⊤ ∨ CFSG.ABGLocalTools.IsSylowOf ℓ₂ P ⊤) →
            ∃ x ∈ P, σ x ≠ x

@[expose] def SympForm : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPGroup 2 X → commutator X ≤ Subgroup.center X →
    (∀ x : X, x ^ 2 ∈ Subgroup.center X) → IsCyclic ↥(Subgroup.center X) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (B : LinearMap.BilinForm (ZMod 2) W) (π : X →* Multiplicative W),
      B.Nondegenerate ∧ B.IsAlt ∧ Function.Surjective π ∧ π.ker = Subgroup.center X ∧
      ∀ x y : X, B (Multiplicative.toAdd (π x)) (Multiplicative.toAdd (π y)) = 0 ↔ ⁅x, y⁆ = 1

@[expose] def SympData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X N : Subgroup G) [X.Normal] [N.Normal],
    IsPGroup 2 X → commutator ↥X ≤ Subgroup.center ↥X →
    (∀ x : ↥X, x ^ 2 ∈ Subgroup.center ↥X) → IsCyclic ↥(Subgroup.center ↥X) →
    (∀ g : G, g ∈ N ↔ ∀ x ∈ X, ⁅g, x⁆ ∈ (Subgroup.center ↥X).map X.subtype) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (B : LinearMap.BilinForm (ZMod 2) W) (φ : (G ⧸ N) →* (W ≃ₗ[ZMod 2] W))
      (π : ↥X →* Multiplicative W),
      B.Nondegenerate ∧ B.IsAlt ∧ Function.Injective φ ∧
      (∀ γ x y, B (φ γ x) (φ γ y) = B x y) ∧
      Function.Surjective π ∧ π.ker = Subgroup.center ↥X ∧
      (∀ (g : G) (x : ↥X), π (MulAut.conjNormal g x) =
        Multiplicative.ofAdd (φ (QuotientGroup.mk g) (Multiplicative.toAdd (π x)))) ∧
      (∀ x y : ↥X, B (Multiplicative.toAdd (π x)) (Multiplicative.toAdd (π y)) = 0 ↔
        ⁅x, y⁆ = 1) ∧
      (∀ (g : G) (x : ↥X),
        (x : G) ∈ ⁅X, Subgroup.zpowers g⁆ ⊔ (Subgroup.center ↥X).map X.subtype ↔
          Multiplicative.toAdd (π x) ∈ LinearMap.range
            ((φ (QuotientGroup.mk g) : W →ₗ[ZMod 2] W) - LinearMap.id)) ∧
      ∀ g : G, Nat.card ↥(⁅X, Subgroup.zpowers g⁆ ⊔ (Subgroup.center ↥X).map X.subtype) =
        Nat.card ↥((Subgroup.center ↥X).map X.subtype) *
          2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
            ((φ (QuotientGroup.mk g) : W →ₗ[ZMod 2] W) - LinearMap.id))

@[expose] def PairX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X N : Subgroup G) [X.Normal] [N.Normal],
    IsPGroup 2 X → commutator ↥X ≤ Subgroup.center ↥X →
    (∀ x : ↥X, x ^ 2 ∈ Subgroup.center ↥X) → IsCyclic ↥(Subgroup.center ↥X) →
    (∀ g : G, g ∈ N ↔ ∀ x ∈ X, ⁅g, x⁆ ∈ (Subgroup.center ↥X).map X.subtype) →
    ∀ a b : G, orderOf (QuotientGroup.mk a : G ⧸ N) = 3 →
      orderOf (QuotientGroup.mk b : G ⧸ N) = 3 →
      Nat.card ↥(⁅X, Subgroup.zpowers a⁆ ⊔ (Subgroup.center ↥X).map X.subtype) =
        4 * Nat.card ↥((Subgroup.center ↥X).map X.subtype) →
      Nat.card ↥(⁅X, Subgroup.zpowers b⁆ ⊔ (Subgroup.center ↥X).map X.subtype) =
        4 * Nat.card ↥((Subgroup.center ↥X).map X.subtype) →
      Z3E9A5Mod2 ((Subgroup.closure ({a, b} : Set G)).map (QuotientGroup.mk' N))

@[expose] def SplitDelta5 : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (H Z : Subgroup E) [H.Normal] [Z.Normal], Z ≤ H →
    ∀ η : E →* Equiv.Perm (Fin 5), η.ker = H → η.range = alternatingGroup (Fin 5) →
    ∀ θ : (↥H ⧸ Z.subgroupOf H) ≃* ↥(CFSG.Quasithin.G6.coreMod 5),
      (∀ (g : E) (h : ↥H), θ (QuotientGroup.mk (MulAut.conjNormal g h)) =
        CFSG.Quasithin.G6.coreAct 5 (η g) (θ (QuotientGroup.mk h))) →
      ∃ S : Subgroup E, Z ≤ S ∧ S ⊓ H = Z ∧ S ⊔ H = ⊤

@[expose] def Core2 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Dbar Kbar : Subgroup Γ) [Kbar.Normal],
    Nat.card Dbar = 3 → Subgroup.normalClosure (Dbar : Set Γ) = ⊤ → IsSolvable ↥Kbar →
    Nat.Coprime 3 (Nat.card Kbar) → ⁅Kbar, (⊤ : Subgroup Γ)⁆ = Kbar →
    (∀ k ∈ Kbar, Z3E9A5Mod2 (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom)) → IsPGroup 2 Kbar

namespace UC46

open Subgroup

noncomputable abbrev Kof (G : Type) [Group G] : Subgroup G :=
  ⁅CFSG.pPrimeCore 3 G, (⊤ : Subgroup G)⁆

noncomputable abbrev Xof (G : Type) [Group G] : Subgroup G :=
  CFSG.Open.pCoreOf 2 (Kof G)

noncomputable abbrev ZXof (G : Type) [Group G] : Subgroup G :=
  (Subgroup.center ↥(Xof G)).map (Xof G).subtype

noncomputable abbrev Tof (G : Type) [Group G] (D : Subgroup G) : Subgroup G :=
  ⁅Xof G, D⁆

variable {G : Type} [Group G]

instance kof_normal : (Kof G).Normal := by
  haveI : (CFSG.pPrimeCore 3 G).Normal := CFSG.pPrimeCore_normal
  exact Subgroup.commutator_normal _ _

theorem xof_isPGroup : IsPGroup 2 (Xof G) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(Kof G))).map (Kof G).subtype

instance xof_normal : (Xof G).Normal := by
  haveI : (Kof G).Normal := kof_normal
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨MulAut.conjNormal g y, ?_, ?_⟩
  · have hch : (CFSG.pCore 2 ↥(Kof G)).Characteristic := inferInstance
    have := (Subgroup.characteristic_iff_map_le.1 hch) (MulAut.conjNormal g)
    exact this ⟨y, hy, rfl⟩
  · simp [MulAut.conjNormal_apply]

instance zxof_normal : (ZXof G).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨MulAut.conjNormal g y, ?_, ?_⟩
  · have hch : (Subgroup.center ↥(Xof G)).Characteristic := inferInstance
    have := (Subgroup.characteristic_iff_map_le.1 hch) (MulAut.conjNormal g)
    exact this ⟨y, hy, rfl⟩
  · simp [MulAut.conjNormal_apply]

def Wker (G : Type) [Group G] : Subgroup G where
  carrier := {g | ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G}
  one_mem' := fun x _ => by simp
  mul_mem' := by
    intro g g' hg hg' x hx
    have h3 : g * ⁅g', x⁆ * g⁻¹ ∈ ZXof G := (zxof_normal (G := G)).conj_mem _ (hg' x hx) g
    have e : ⁅g * g', x⁆ = (g * ⁅g', x⁆ * g⁻¹) * ⁅g, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem h3 (hg x hx)
  inv_mem' := by
    intro g hg x hx
    have h3 : g⁻¹ * ⁅g, x⁆⁻¹ * g⁻¹⁻¹ ∈ ZXof G :=
      (zxof_normal (G := G)).conj_mem _ (inv_mem (hg x hx)) g⁻¹
    have e : ⁅g⁻¹, x⁆ = g⁻¹ * ⁅g, x⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h3

theorem mem_wker {g : G} : g ∈ Wker G ↔ ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G := Iff.rfl

instance wker_normal : (Wker G).Normal := by
  refine ⟨fun g hg h x hx => ?_⟩
  have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ Xof G := (xof_normal (G := G)).conj_mem x hx h⁻¹
  have h1 : h * ⁅g, h⁻¹ * x * h⁻¹⁻¹⁆ * h⁻¹ ∈ ZXof G :=
    (zxof_normal (G := G)).conj_mem _ (hg _ hx') h
  have e : ⁅h * g * h⁻¹, x⁆ = h * ⁅g, h⁻¹ * x * h⁻¹⁻¹⁆ * h⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

@[expose] def XDelta5 (G : Type) [Group G] : Prop :=
  ∃ (η : G →* Equiv.Perm (Fin 5)) (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5)),
    η.ker = CFSG.pPrimeCore 3 G ∧ η.range = alternatingGroup (Fin 5) ∧
    Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥(Xof G) ∧
    ∀ (g : G) (x : ↥(Xof G)),
      ψ (MulAut.conjNormal g x) = CFSG.Quasithin.G6.coreAct 5 (η g) (ψ x)

structure Base45 (p : ℕ) (G : Type) [Group G] [Finite G] (D : Subgroup G) : Prop where
  prime : p.Prime
  odd : 2 < p
  ne_three : p ≠ 3
  kgroup : CFSG.Open.IsKGroup G
  card_three : Nat.card D = 3
  gen : Subgroup.normalClosure (D : Set G) = ⊤
  Op : CFSG.pCore p G = ⊥
  center_cyclic : IsCyclic ↥(Subgroup.center G)
  noAbel2 : ∀ A : Subgroup G, IsPGroup 2 A → A ≠ ⊥ → IsMulCommutative ↥A →
    D ≤ Subgroup.normalizer (A : Set G) → ⁅D, A⁆ = A → False
  noOdd : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → q ≠ p → ∀ Q : Subgroup G, IsPGroup q Q →
    D ≤ Subgroup.normalizer (Q : Set G) → ⁅D, Q⁆ = Q → Q = ⊥
  quat : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → D ≤ Subgroup.normalizer (T : Set G) →
    ⁅D, T⁆ = T → IsCyclic ↥(Subgroup.center ↥T) → Nonempty (↥T ≃* QuaternionGroup 2)

structure Pre45 (p : ℕ) (G : Type) [Group G] [Finite G] (D : Subgroup G) : Prop
    extends Base45 p G D where
  K22p : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Kof G) → q = 2 ∨ q = p
  ZX_le : ZXof G ≤ Subgroup.center G
  class_two : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G) ∧
    ∀ x : ↥(Xof G), x ^ 2 ∈ Subgroup.center ↥(Xof G)
  Q8 : Nonempty (↥(Tof G D) ≃* QuaternionGroup 2)

structure Front45 (p : ℕ) (G : Type) [Group G] [Finite G] (D : Subgroup G) : Prop
    extends Pre45 p G D where
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1
  perfect : commutator G = ⊤
  K_eq : Kof G = Xof G
  X_gen : Subgroup.normalClosure (Tof G D : Set G) = Xof G

structure Ctx45 (p : ℕ) (G : Type) [Group G] [Finite G] (D : Subgroup G) : Prop
    extends Front45 p G D where
  alt5 : CFSG.Quasithin.IsAlt 5 (G ⧸ CFSG.pPrimeCore 3 G)

end UC46

end CFSG.LocalAnalysis.UniquenessCase.UCK
