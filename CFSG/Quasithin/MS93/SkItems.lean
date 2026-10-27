module

public import CFSG.Quasithin.MS93.SkConcl
public import CFSG.Quasithin.MS93.Sec2Geo

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

section IntModSub

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def intModVal : IntMod V hV →* G where
  toFun v := v.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def intSub (W : Subgroup G) : Subgroup (IntMod V hV) := W.comap (intModVal hV)

theorem intSub_bot : intSub hV ⊥ = ⊥ := by
  ext v
  rw [intSub, Subgroup.mem_comap, Subgroup.mem_bot, Subgroup.mem_bot]
  constructor
  · intro h
    exact IntMod.val_injective (h.trans IntMod.val_one.symm)
  · rintro rfl
    rfl

end IntModSub

section Modules

@[expose] def IsSp4DerSec (A V Z : Subgroup G) (k : ℕ) : Prop :=
  (k = 1 ∧ ∃ N : Subgroup ↥A, IsAltNaturalSection A V Z N 6) ∨
    (2 ≤ k ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥A →* ↥(StatedSp 2 F)),
      Fintype.card F = 2 ^ k ∧ Function.Surjective α ∧ IsSumOfNaturalModulesVia A V Z α false 1)

end Modules

section Cases32

@[expose] def IsSL3U (M T L : Subgroup G) : Prop :=
  Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
        IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 1

@[expose] def IsHatA6U (M T L : Subgroup G) : Prop :=
  Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    ∃ hU : IsElemAbelian 2 (Uq M T L), TripleA6Six (autI hU L) ⊤ ⊥

@[expose] def IsDoubleSL3U (M T L : Subgroup G) : Prop :=
  Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
        IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 2

@[expose] def IsSL3TwoU (M T L : Subgroup G) : Prop :=
  Xq M = Zq M L ⊔ Uq M T L ∧ Nat.card ↥(Zq M L ⊓ Uq M T L) = 2 ∧
    (∃ α : ↥M →* ↥(StatedSL 3 (ZMod 2)), Function.Surjective α ∧
      IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1) ∧
    (∀ S : Subgroup G, IsSylowTwoOf S M →
      Uq M T L ⊓ Subgroup.centralizer (S : Set G) = Uq M T L ⊓ Subgroup.centralizer (M : Set G)) ∧
    ∀ S : Subgroup G, IsSylowTwoOf S M → ∀ t ∈ S, (∃ u ∈ Uq M T L, t * u * t⁻¹ ≠ u) →
      Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, Subgroup.zpowers t⁆

@[expose] def IsSL3TwoZ (M T L : Subgroup G) : Prop :=
  Z0q M T = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧ (Z0q M T).relIndex (Xq M) = 2 ∧
    ∃ α : ↥L →* ↥(StatedSL 3 (ZMod 2)), Function.Surjective α ∧
      IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 1

@[expose] def IsG2U {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G) : Prop :=
  Xq M = Z0q M T ∧ Z0q M T = Zq M L ⊔ Uq M T L ∧
    (∃ hU : IsElemAbelian 2 (Uq M T L),
      G2NaturalDerived (autI hU L) ⊤ (intSub hU (Uq M T L ⊓ Zq M L)) 1) ∧
    ∀ α' : Vtx (puAmalgam hTM), IsCritical (puAmalgam hTM) (baseA _) α' →
      imM hTM (Uq M T L ⊓ Zq M L) = puTrans hTM (Uq M T L) α' ⊓
          Subgroup.centralizer (puTrans hTM L α' : Set (puAmalgam hTM).Universal) ∧
        imM hTM (Uq M T L ⊓ Zq M L) ≤
          ⁅ZM (puAmalgam hTM) (baseA _), ZM (puAmalgam hTM) α'⁆

end Cases32

section Cases368

@[expose] def IsDoubleSL3Ext (M T L : Subgroup G) : Prop :=
  frattiniIn (Vq M L) = ⊥ ∧ Xq M = Zq M L ⊔ Uq M T L ∧
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
      IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 1 ∧
      IsSumOfNaturalModulesVia L (Vq M L) (Uq M T L) α false 1

@[expose] def IsSL3TwoNonsplit (M T L : Subgroup G) : Prop :=
  (∃ α : ↥M →* ↥(StatedSL 3 (ZMod 2)), Function.Surjective α ∧
      IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Dq M L) α false 1) ∧
    Nat.card ↥(Uq M T L ⊓ Dq M L) = 2 ∧ (pCoreOf 2 M).relIndex T = 4 ∧
    (Uq M T L ⊓ Dq M L).relIndex (⁅Uq M T L, T⁆ ⊔ Uq M T L ⊓ Dq M L) = 2 ∧
    Xq M = Zq M L ⊔ Uq M T L ∧
    ∀ S : Subgroup G, IsSylowTwoOf S M →
      Uq M T L ⊓ Subgroup.centralizer (S : Set G) = Uq M T L ⊓ Subgroup.centralizer (M : Set G)

@[expose] def IsSp4U (M T L : Subgroup G) : Prop :=
  (∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSp 2 F)),
      2 ≤ k ∧ Fintype.card F = 2 ^ k ∧ Function.Surjective α ∧
      IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α
        false 1) ∨
    ∃ α : ↥M →* ↥(StatedSp 2 (ZMod 2)), Function.Surjective α ∧
      IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α false 1

@[expose] def IsSL3Full (M T L : Subgroup G) : Prop :=
  Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥M →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
        IsSumOfNaturalModulesVia M (Uq M T L) ⊥ α false 1

@[expose] def IsSp4Full (M T L : Subgroup G) : Prop :=
  ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥M →* ↥(StatedSp 2 F)),
    1 ≤ k ∧ Fintype.card F = 2 ^ k ∧ Function.Surjective α ∧
    IsSumOfNaturalModulesVia M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α false 1

end Cases368

section Objects33

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def critR (α α' : Vtx X) : Subgroup X.Universal := ⁅ZM X α, ZM X α'⁆

@[expose] def critA (α α' : Vtx X) : Subgroup X.Universal := XM X α' ⊓ Qv X α

@[expose] def stabCenter (δ : Vtx X) : Subgroup X.Universal :=
  (Subgroup.center ↥(stab X δ)).map (stab X δ).subtype

end Objects33

section Cases33

variable [Finite G] {M T L : Subgroup G}

@[expose] def S33i (h : PUHyp M T L) (α' : Vtx (puAmalgam h.le))
    (Y : Subgroup (puAmalgam h.le).Universal) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ Function.Surjective a ∧
    IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1 ∧
    Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
    Nat.card ↥(critR _ (baseA _) α') = 2 ^ n ∧
    (critR _ (baseA _) α').relIndex ⁅Y ⊔ ZM _ (baseA _), ZM _ α'⁆ = 2 ^ n

@[expose] def S33iiW (h : PUHyp M T L) (α' : Vtx (puAmalgam h.le)) : Prop :=
  ∃ k : ℕ, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k ∧
    ((k = 1 ∧ ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
        (∀ t ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal),
          (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
        t₁ * t₂⁻¹ ∉ Qv _ α' ∧
        ZM _ (baseA _) ⊔ Qv _ α' =
          Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α') ∨
      (Qv _ α').relIndex (ZM _ (baseA _)) = 2 ^ k)

end Cases33

section Items

@[expose] def S32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M ∧ ⁅Xq M, L⁆ ≤ Uq M T L ∧
      (IsSL3U M T L ∨ IsHatA6U M T L ∨ IsDoubleSL3U M T L ∨ IsSL3TwoU M T L ∨ IsSL3TwoZ M T L ∨
        (∃ k, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) ∨ IsG2U h.le L)

@[expose] def S33w : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (α' : Vtx (puAmalgam h.le)), IsCritical (puAmalgam h.le) (baseA _) α' →
    ∀ Y : Subgroup (puAmalgam h.le).Universal, Y ≤ Qv _ (geo _ α' (baseA _) 1) →
      Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) →
      ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
          ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
            ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ →
      (critDist (puAmalgam h.le) = 2 → ¬ IsSL3U M T L →
        (∀ k, ¬ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) →
        Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal)) →
        S33i h α' Y ∨ S33iiW h α'

@[expose] def S36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 2 →
    (Vq M L = Uq M T L ∨ IsDoubleSL3Ext M T L) ∧
      (Uq M T L ⊓ Dq M L = ⊥ ∨ (∃ k, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Dq M L) k) ∨
        IsSL3TwoNonsplit M T L)

@[expose] def S37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 2 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSp 2 F)),
      2 ≤ k → Fintype.card F = 2 ^ k → Function.Surjective α →
      IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1 → IsOddRadical M T →
      k = 2

@[expose] def S18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 2 → Vq M L ≠ Uq M T L → IsDoubleSL3Ext M T L →
      MS93Case5 (Vq M L) L

@[expose] def S38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    2 < critDist (puAmalgam h.le) → IsSL3U M T L ∨ IsSp4U M T L

@[expose] def S46 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 → IsSL3Full M T L → MS93Case11 (Vq M L) T L

@[expose] def S512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) → IsSp4Full M T L → False

@[expose] def S7Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L M₁ T₁ : Subgroup G) (h : PUHyp M T L)
    (h₁ : PUHyp M₁ T₁ L), T₁ ≤ T → PUMin M₁ T₁ L → Vq M₁ L = Vq M L →
      2 < critDist (puAmalgam h.le) → critDist (puAmalgam h₁.le) = 2 → MS93Case5 (Vq M L) L

@[expose] def PUReduce : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L T₁ : Subgroup G), PUHyp M T L →
    T₁ ≤ T → (T₁.subgroupOf T).Characteristic → (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁ → T₁ ≠ ⊥ →
      PUHyp (L ⊔ T₁) T₁ L ∧ Vq (L ⊔ T₁) L = Vq M L

end Items

end CFSG.Quasithin.MS93
