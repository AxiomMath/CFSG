module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Hyp139LowAll
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

structure Std139 {W : Type} [CommGroup W] [Finite W]
    (G X D : Subgroup (MulAut W)) (s : MulAut W) (Y : Subgroup W) (n : ℕ) : Prop where
  isK : CFSG.Open.IsKGroup ↥G
  o2 : pCoreOf 2 G = ⊥
  irr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤
  cost : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3
  XG : X ≤ G
  Xnorm : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X
  Xcard : Nat.card X = 3
  sG : s ∈ G
  s2 : orderOf s = 2
  s_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W))
  Yinv : ∀ x ∈ X, ∀ y ∈ Y, x y ∈ Y
  Yrk : rkIdx Y = 2
  card : Nat.card W = 4 ^ n
  DG : D ≤ G
  DX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d
  Dcs : ∀ d ∈ D, d * s = s * d
  elem : CFSG.Quasithin.IsElemAbelian2 D
  Dcard : Nat.card D = 2 ^ (n - 1)
  YD : Y ≤ fixV D

@[expose] def Hyp139Ge3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
  ∀ (G X D : Subgroup (MulAut W)) (s : MulAut W) (Y : Subgroup W) (n : ℕ),
    Std139 G X D s Y n → 3 ≤ n → Concl139 W G X n

theorem hyp139_of_ge3 (h : Hyp139Ge3) : Hyp139 := by
  intro W _ _ hw2 G X D s Y n hK hpCore hirr ht hXG hXnorm hXcard hsG hs_ord2 hs_not_cent
    hYinv hYrk hW hD hDCX hDs hElem hDcard hYD
  by_cases hn : 3 ≤ n
  · exact h W hw2 G X D s Y n
      ⟨hK, hpCore, hirr, ht, hXG, hXnorm, hXcard, hsG, hs_ord2, hs_not_cent, hYinv, hYrk, hW,
        hD, hDCX, hDs, hElem, hDcard, hYD⟩ hn
  · exact concl139_of_concl139Printed
      (concl139_of_hyp139_le_two hw2 hK hpCore hirr ht hXG hXnorm hXcard hsG hs_ord2
        hs_not_cent hYinv hYrk hW hD hDCX hDs hElem hDcard hYD (by omega))

variable {W : Type} [CommGroup W] [Finite W]

abbrev swapPair (K : Subgroup (MulAut W)) (d : MulAut W) : Subgroup (MulAut W) :=
  K ⊔ K.map (MulAut.conj d).toMonoidHom

@[expose] def DNormComp (G D : Subgroup (MulAut W)) : Prop :=
  ∀ K : Subgroup (MulAut W), IsComponentOf K G → ∀ d ∈ D,
    K.map (MulAut.conj d).toMonoidHom = K

@[expose] def KXIrr (K X : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  U ≠ ⊥ ∧ StableUnder K U ∧ StableUnder X U ∧
    ∀ C : Subgroup W, StableUnder K C → StableUnder X C → C ≤ U → C = ⊥ ∨ C = U

structure Comp139 (G X D K : Subgroup (MulAut W)) : Prop where
  comp : IsComponentOf K G
  notCent : ¬ K ≤ Subgroup.centralizer (D : Set (MulAut W))
  normal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K
  top : commSub ⊤ K = ⊤
  fix : fixV K = ⊥
  irr : KXIrr K X ⊤

@[expose] def ShapeNat4 (K X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  ∃ (φ : ↥K ≃* Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2))
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)),
    (∀ (a : ↥K) (w : W), ψ ((a : MulAut W) w) =
      Multiplicative.ofAdd ((φ a : Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec
        (Multiplicative.toAdd (ψ w)))) ∧
    ∀ x ∈ X, ∃ c : GaloisField 2 2, ∀ w : W,
      ψ (x w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (ψ w))

@[expose] def ShapeTensor (K X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  ∃ (M : Subgroup W) (x : MulAut W), x ∈ X ∧ x ≠ 1 ∧ StableUnder K M ∧ rk ↥M = n ∧
    M ⊓ M.map x.toMonoidHom = ⊥ ∧ M ⊔ M.map x.toMonoidHom = ⊤ ∧
    (∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1) ∧
    ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W)

@[expose] def ShapeCover (K X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  n = 3 ∧ IsHat ↥K ↥(alternatingGroup (Fin 6)) ∧
    (Subgroup.center ↥K).map K.subtype = X ∧ Nat.card W = 2 ^ 6

@[expose] def HasSympForm (K : Subgroup (MulAut W)) : Prop :=
  ∃ B : W →* W →* Multiplicative (ZMod 2),
    (∀ x, (∀ y, B x y = 1) → x = 1) ∧ (∀ x, B x x = 1) ∧
      ∀ k ∈ K, ∀ x y, B (k x) (k y) = B x y

@[expose] def McLaughlin1969 : Prop :=
  ∀ (M : Type) [CommGroup M] [Finite M], (∀ m : M, m ^ 2 = 1) →
    ∀ (J L : Subgroup (MulAut M)), L ≤ J → (L.subgroupOf J).Normal →
      (L.subgroupOf J).index ≤ 2 → IsQuasisimple ↥L → IsIrrOn J ⊤ ⊥ →
      J = Subgroup.closure {t | t ∈ J ∧ InducesTransvection t ⊤} →
        (∃ m : ℕ, IsSLn ↥L m 1 ∧ BinaryNaturalSL L ⊤ ⊥ m 1) ∨
        (∃ m : ℕ, IsSpn ↥L m 1 ∧ NatSpn L ⊤ ⊥ m 1) ∨
        (∃ m : ℕ, IsOmegaPlus ↥L m 1 ∧ NatOmegaPlus L ⊤ ⊥ m 1) ∨
        (∃ m : ℕ, IsOmegaMinus ↥L m 1 ∧ NatOmegaMinus L ⊤ ⊥ m 1) ∨
        (∃ m : ℕ, IsAlt ↥L m ∧ AlternatingNatural L ⊤ ⊥ m)

@[expose] def GapEndU33 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), LieModel ↥L .PSU 3 3 1 → IsIrrOn L ⊤ ⊥ → Nat.card W = 2 ^ 6 →
      Subgroup.centralizer (L : Set (MulAut W)) = ⊥

@[expose] def GapEndSp62 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsSpn ↥L 6 1 → IsIrrOn L ⊤ ⊥ → Nat.card W = 2 ^ 8 →
      Subgroup.centralizer (L : Set (MulAut W)) = ⊥

@[expose] def GapEndL52 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsSLn ↥L 5 1 → IsIrrOn L ⊤ ⊥ → Nat.card W = 2 ^ 10 →
      Subgroup.centralizer (L : Set (MulAut W)) = ⊥

@[expose] def GapEndM22 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsSpor ↥L .M22 → IsIrrOn L ⊤ ⊥ → Nat.card W = 2 ^ 10 →
      Subgroup.centralizer (L : Set (MulAut W)) = ⊥

@[expose] def GapEndL32 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsL3 ↥L 1 → IsIrrOn L ⊤ ⊥ → Nat.card W = 2 ^ 8 →
      Subgroup.centralizer (L : Set (MulAut W)) = ⊥

@[expose] def GapThreeA6Normalizer : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ K : Subgroup (MulAut W), IsHat ↥K ↥(alternatingGroup (Fin 6)) → IsIrrOn K ⊤ ⊥ →
      Nat.card W = 2 ^ 6 →
      ∃ φ : ↥(Subgroup.normalizer (K : Set (MulAut W))) →* Equiv.Perm (Fin 6),
        Function.Surjective φ ∧
          φ.ker = ((Subgroup.center ↥K).map K.subtype).subgroupOf
            (Subgroup.normalizer (K : Set (MulAut W)))

@[expose] def GapOutU43 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 →
    ∀ E : Subgroup (MulAut S), (∀ a ∈ E, a ^ 2 = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ∈ (MulAut.conj : S →* MulAut S).range → a = 1) → Nat.card E ≤ 8

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
