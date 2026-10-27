
module

public import CFSG.Quasithin.Background.C3Statement
public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section C41

variable {G : Type} [Group G]

@[expose] def IsStabilizedLineOfNatural (F : Type) [Field F] (R M K V₁ : Subgroup G) : Prop :=
  ∃ W : Subgroup G, W ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆ ∧
    ∃ (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥W →* Multiplicative (Fin 3 → F)),
      IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β ∧ IsFLineVia W V₁ β ∧
        M ⊓ K = K ⊓ Subgroup.normalizer (V₁ : Set G)

@[expose] def C41Case1 (_H R M L V K : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 5 ∨ n = 6) ∧ IsAltBlockType (conjClosure L M) n ∧
    V = blockU (conjClosure L M) ∧ IsAltBlockType K (n + 2) ∧ InducesTransposition R K (n + 2) ∧
    M ⊓ K = K ⊓ Subgroup.normalizer (R : Set G)

@[expose] def C41Case2 (_H _R M L V K : Subgroup G) : Prop :=
  IsSp4Block K ∧
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSp 2 F))
      (β : ↥(blockU K) →* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
      Fintype.card F = 4 ∧ IsMatrixBlockTypeWith K (StatedSp 2 F) α β ∧
        IsFLineVia (blockU K) (V ⊔ blockZ K) β ∧ IsMaxParabolic2 K (M ⊓ K) ∧
        M ⊓ K = K ⊓ Subgroup.normalizer (V : Set G) ∧
        IsPSL 2 2 2 (ModO2 (conjClosure L M))

@[expose] def C41Case4 (_H _R M L _V K : Subgroup G) : Prop :=
  (IsPSL 4 2 1 (ModO2 K) ∨ IsPSL 5 2 1 (ModO2 K)) ∧ IsParabolic2 K (M ⊓ K) ∧
    (IsPSL 3 2 1 (ModO2 (conjClosure L M)) ∨ IsPSL 4 2 1 (ModO2 (conjClosure L M)))

end C41

section C41MS

variable {G : Type} [Group G] [Finite G]

@[expose] def C41Case3 (_H R M L V K : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 < n ∧ Fintype.card F = 2 ^ n ∧
    Nonempty (ModO2 K ≃* ↥(StatedSL 3 F)) ∧ IsMSPair (K ⊔ R) R ∧
    (IsC134Case 1 (K ⊔ R) R K ∨ IsC134Case 2 (K ⊔ R) R K ∨ IsC134Case 3 (K ⊔ R) R K ∨
      C134CorrLocal.IsC134Case4Corr (K ⊔ R) R K) ∧
    IsMaxParabolic2 K (M ⊓ K) ∧ IsPSL 2 2 n (ModO2 (conjClosure L M)) ∧
    (IsStabilizedLineOfNatural F R M K V ∨
      (IsC134Case 2 (K ⊔ R) R K ∧ ∃ V₁ V₂ : Subgroup G,
        IsStabilizedLineOfNatural F R M K V₁ ∧ IsStabilizedLineOfNatural F R M K V₂ ∧
        V = V₁ ⊔ V₂))

@[expose] def C41Conclusion (H R M L V K : Subgroup G) : Prop :=
  L = conjClosure L M ∧ conjClosure L M ≤ conjClosure K H ∧ conjClosure K H = K ∧
    (C41Case1 H R M L V K ∨ C41Case2 H R M L V K ∨ C41Case3 H R M L V K ∨
      C41Case4 H R M L V K)

end C41MS

@[expose] def ASC41Statement (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → K ∈ cComp H → CharTwo K →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → ¬ K ≤ M → C41Conclusion H R M L V K

section C48

variable {G : Type} [Group G]

@[expose] def C48Case1 (_H R M L V K : Subgroup G) : Prop :=
  ∃ n : ℕ, IsPSL 2 2 n (ModO2 L) ∧
    ((∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
          (R.subgroupOf (L ⊔ R)) (StatedSL 2 F)) ∨
      (n = 2 ∧ IsAltNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
        (R.subgroupOf (L ⊔ R)) 5) ∨
      (1 < n ∧ IsC134Case 2 (K ⊔ R) R K ∧
        (∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (V₁ : Subgroup G), 1 < m ∧
          Fintype.card F = 2 ^ m ∧ IsStabilizedLineOfNatural F R M K V₁) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F) (V₁ V₂ : Subgroup G),
          Fintype.card F = 2 ^ n ∧ V = V₁ ⊔ V₂ ∧
          IsNaturalSection (L ⊔ R) V₁ (V₁ ⊓ Subgroup.centralizer (L : Set G))
            (R.subgroupOf (L ⊔ R)) (StatedSL 2 F) ∧
          IsNaturalSection (L ⊔ R) V₂ (V₂ ⊓ Subgroup.centralizer (L : Set G))
            (R.subgroupOf (L ⊔ R)) (StatedSL 2 F)))

@[expose] def C48Case2 (_H R _M L V _K : Subgroup G) : Prop :=
  ∃ m : ℕ, (m = 3 ∨ m = 4) ∧ IsPSL m 2 1 (ModO2 L) ∧
    ((∃ k : ℕ, 1 ≤ k ∧ IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R))
        (StatedSL m (ZMod 2)) false k) ∨
      (m = 4 ∧ IsAltNaturalSection (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) 8))

@[expose] def C48Case3 (_H _R _M L _V K : Subgroup G) : Prop :=
  (IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K) ∨ IsSporadic .HS (↥K ⧸ Subgroup.center ↥K)) ∧
    IsAltBlockType L 6

@[expose] def C48Case4 (_H _R _M L _V K : Subgroup G) : Prop :=
  IsSporadic .M23 ↥K ∧ IsExcA7Block L

@[expose] def C48Case5 (_H _R _M L _V K : Subgroup G) : Prop :=
  (IsSporadic .M24 ↥K ∨ IsSporadic .He ↥K) ∧ IsHatA6Block L

@[expose] def C48Case6 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .J4 ↥K ∧ IsShort2 L ∧
    ((IsSporadic .M24 (ModO2 L) ∧ C31Case6M24 M L) ∨ (IsPSL 5 2 1 (ModO2 L) ∧ C31Case6L5 M L))

@[expose] def C48Case7 (_H _R _M L _V K : Subgroup G) : Prop :=
  IsSporadic .Ru (↥K ⧸ Subgroup.center ↥K) ∧ IsG2Block L

@[expose] def C48Case8 (_H _R _M L _V K : Subgroup G) : Prop :=
  IsAltBlockType K 8 ∧ IsAltBlockType L 6

@[expose] def C48Case9 (_H _R _M L V K : Subgroup G) : Prop :=
  IsDoubleCover ↥K ↥(alternatingGroup (Fin 8)) ∧ IsLnBlock L 3 ∧ IsE2 4 ↥V

@[expose] def C48Case10 (H _R M L _V _K : Subgroup G) : Prop :=
  oTwoFstarIn H ≤ M ∧
    ((∃ n : ℕ, IsPSL 2 2 n (ModO2 L)) ∨ (∃ n : ℕ, IsSz n (ModO2 L)) ∨
      IsSporadic .J1 (ModO2 L) ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPSL 2 p 1 (ModO2 L)) ∧
    M = H ⊓ Subgroup.normalizer (conjClosure L M : Set G) ∧ M.relIndex H = 2

end C48

section C48Last

variable {G : Type} [Group G] [Finite G]

@[expose] def C48KDescribed (H R M L V K : Subgroup G) : Prop :=
  (CFSG.Open.IsComponentOf K H ∧ C31Conclusion H R M L V K) ∨
    (K ∈ cComp H ∧ CharTwo K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ K ≤ M ∧
      C41Conclusion H R M L V K)

@[expose] def C48Conclusion (H R M L V : Subgroup G) : Prop :=
  L = conjClosure L M ∧
    ∃ K : Subgroup G, K ∈ cComp H ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ L ≤ K ∧
      (C48Case10 H R M L V K ∨
        ((C48Case1 H R M L V K ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
            C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
            C48Case7 H R M L V K ∨ C48Case8 H R M L V K ∨ C48Case9 H R M L V K) ∧
          ¬ K ≤ M ∧ M ≤ Subgroup.normalizer (K : Set G) ∧ C48KDescribed H R M L V K))

end C48Last

@[expose] def ASC48Statement (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V : Subgroup G, HypC28 H R M L V → M < H → C48Conclusion H R M L V

end CFSG.Quasithin
