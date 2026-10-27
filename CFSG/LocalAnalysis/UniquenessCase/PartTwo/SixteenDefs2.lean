module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Shapes2

@[expose] def IsSym (X : Type) [Group X] (n : ℕ) : Prop :=
  Nonempty (X ≃* Equiv.Perm (Fin n))

@[expose] def IsOMinus (X : Type) [Group X] (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ^ a ∧
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
    Nonempty (X ≃* ↥(CFSG.MatrixModel.isometryCore (StatedQuadMinus (n / 2) K b c)))

@[expose] def IsInternalDirect {A : Type*} [Group A] (K L X : Subgroup A) : Prop :=
  ⁅K, L⁆ = ⊥ ∧ K ⊓ L = ⊥ ∧ K ⊔ L = X

variable {W : Type} [CommGroup W]

@[expose] def SumOfTwoInequiv
    (N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop)
    (H : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  ∃ I₁ I₂ : Subgroup W, Z ≤ I₁ ∧ Z ≤ I₂ ∧ I₁ ⊓ (Z ⊔ I₂) ≤ Z ∧ I₂ ⊓ (Z ⊔ I₁) ≤ Z ∧
    Z ⊔ I₁ ⊔ I₂ = U ∧ N H I₁ Z ∧ N H I₂ Z ∧
    ∀ ψ ∈ Subgroup.centralizer (H : Set (MulAut W)), I₁.map ψ.toMonoidHom ≠ I₂

@[expose] def SymSumOfConj (A : Subgroup (MulAut W)) (U : Subgroup W) (r m : ℕ) : Prop :=
  ∃ Z : Subgroup W, rk ↥Z = m ∧ sSupIndep (conjSubs A Z) ∧ sSup (conjSubs A Z) = U ∧
    (conjSubs A Z).ncard = r + 1 ∧
    ∀ π : Equiv.Perm ↥(conjSubs A Z), ∃ g ∈ A, ∀ Y : ↥(conjSubs A Z),
      (Y : Subgroup W).map g.toMonoidHom = (π Y : Subgroup W)

@[expose] def PairsOfConj (A : Subgroup (MulAut W)) (m : ℕ) (Δ : Set (Subgroup W)) : Prop :=
  ∃ Z : Subgroup W, rk ↥Z = m ∧ sSupIndep (conjSubs A Z) ∧ sSup (conjSubs A Z) = ⊤ ∧
    (conjSubs A Z).ncard = 4 ∧
    (∀ π : Equiv.Perm ↥(conjSubs A Z), ∃ g ∈ A, ∀ Y : ↥(conjSubs A Z),
      (Y : Subgroup W).map g.toMonoidHom = (π Y : Subgroup W)) ∧
    ∀ I ∈ Δ, ∃ Y₁ ∈ conjSubs A Z, ∃ Y₂ ∈ conjSubs A Z, Y₁ ≠ Y₂ ∧ I = Y₁ ⊔ Y₂

end Shapes2

section NotationBar

variable {G : Type} [Group G]

@[expose] noncomputable def kBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  Mbar M V₀ V hV ⊓ centralizer ((lBar V₀ V hV L : Subgroup _) : Set _)

@[expose] noncomputable def oddBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  relPPrimeCore 2 (Mbar M V₀ V hV)

end NotationBar

section Cases

variable {G : Type} [Group G] [Finite G]
variable (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)

@[expose] noncomputable def Case168_1 : Prop :=
  Nonempty (↥(Mbar D.M V₀ V hV) ≃* MulAut ↥(alternatingGroup (Fin 6))) ∧
    UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∧
    SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ ∧
    D.sig = {3}

@[expose] noncomputable def Case168_2 : Prop :=
  IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
    (∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
        ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 11 ∧ IsSym ↥L₀ n ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
            SumOfNat (fun H U Z => AlternatingNatural H U Z n)
              (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2) ∨
          (∃ m : ℕ, 3 ≤ m ∧ m ≤ 5 ∧ IsLn ↥L₀ m 1 ∧ IsLn ↥(lBar V₀ V hV L) m 1 ∧
            SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
              (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2) ∨
          (IsSpn ↥L₀ 6 1 ∧ IsSpn ↥(lBar V₀ V hV L) 6 1 ∧
            SumOfNat (fun H U Z => NatSpn H U Z 6 1)
              (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2) ∨
          (IsOMinus ↥L₀ 6 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
            SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
              (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2) ∨
          (IsOMinus ↥L₀ 8 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) 8 1 ∧
            SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
              (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 2))) ∧
    D.sig = {3}

@[expose] noncomputable def Case168_2Star : Prop :=
  IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
    (∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
        ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 11 ∧ IsSym ↥L₀ n ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
            SumOfNat (fun H U Z => AlternatingNatural H U Z n)
              (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) ∨
          (∃ m : ℕ, 3 ≤ m ∧ m ≤ 5 ∧ IsLn ↥L₀ m 1 ∧ IsLn ↥(lBar V₀ V hV L) m 1 ∧
            SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
              (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) ∨
          (IsSpn ↥L₀ 6 1 ∧ IsSpn ↥(lBar V₀ V hV L) 6 1 ∧
            SumOfNat (fun H U Z => NatSpn H U Z 6 1)
              (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) ∨
          (IsOMinus ↥L₀ 6 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
            SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
              (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) ∨
          (IsOMinus ↥L₀ 8 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) 8 1 ∧
            SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
              (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2))) ∧
    D.sig = {3}

@[expose] noncomputable def Case168_3 : Prop :=
  IsPOnePlusTwo 3 ↥(lBar V₀ V hV L) ∧ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 ∧ D.sig = {3}

@[expose] noncomputable def Case168_4At (p r : ℕ) : Prop :=
  IsElemAbelianOfRank p r ↥(lBar V₀ V hV L) ∧
    SymSumOfConj (Mbar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) r (dParam p) ∧ p ∈ D.sig

@[expose] noncomputable def Case168_4 : Prop :=
  ∃ p r : ℕ, (p = 3 ∨ p = 7) ∧ 1 < r ∧ Case168_4At D V₀ V hV L p r

@[expose] noncomputable def Case168_5 : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L))) ∧
    IsOmegaPlus ↥(lBar V₀ V hV L) 4 2 ∧
    NatOmegaPlus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 4 2 ∧ D.sig = {3}

@[expose] noncomputable def Case168_5Star : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L))) ∧
    IsOmegaPlus ↥(lBar V₀ V hV L) 4 2 ∧
    NatOmegaPlus (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 4 2 ∧ D.sig = {3}

@[expose] noncomputable def Case168_6 : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L))) ∧
    ((UC22.IsAlt ↥(lBar V₀ V hV L) 5 ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
          (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 2) ∨
      (IsL3 ↥(lBar V₀ V hV L) 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
          (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 2)) ∧
    s15 D.M V₀ V hV L = 2 ∧ D.sig = {3}

@[expose] noncomputable def Case168_7 : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L))) ∧
    IsL3 ↥(lBar V₀ V hV L) 1 ∧
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 3 ∧ D.sig = {7}

@[expose] noncomputable def Case168_8 : Prop :=
  IsElemAbelianOfRank 3 2 ↥(fstarBar D.M V₀ V hV) ∧
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 8 ∧ D.sig = {3}

@[expose] noncomputable def Case168_9 : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L))) ∧
    IsL3 ↥(lBar V₀ V hV L) 1 ∧ s15 D.M V₀ V hV L = 2 ∧
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 ∧ D.sig = {7}

@[expose] noncomputable def Case168_10At (p : ℕ) : Prop :=
  IsCyclicOrd ↥(lBar V₀ V hV L) p ∧ rk ↥(wTil V₀ V hV L) = 2 * dParam p ∧
    s15 D.M V₀ V hV L = 2 ∧ D.sig = {p} ∧ IsElemAbelianOfRank p 3 ↥(fstarBar D.M V₀ V hV)

@[expose] noncomputable def Case168_10 : Prop :=
  ∃ p : ℕ, (p = 3 ∨ p = 7) ∧ Case168_10At D V₀ V hV L p

@[expose] noncomputable def Case168_11 : Prop :=
  IsCyclicOrd ↥(lBar V₀ V hV L) 7 ∧ rk ↥(wTil V₀ V hV L) = 3 ∧ s15 D.M V₀ V hV L = 2 ∧
    D.sig = {7}

@[expose] noncomputable def Concl168 : Prop :=
  Case168_1 D V₀ V hV L ∨ Case168_2Star D V₀ V hV L ∨ Case168_3 D V₀ V hV L ∨
    Case168_4 D V₀ V hV L ∨ Case168_5Star D V₀ V hV L ∨ Case168_6 D V₀ V hV L ∨
    Case168_7 D V₀ V hV L ∨ Case168_8 D V₀ V hV ∨ Case168_9 D V₀ V hV L ∨
    Case168_10 D V₀ V hV L ∨ Case168_11 D V₀ V hV L

@[expose] def ChoiceNorm1613 : Prop :=
  Case168_4At D V₀ V hV L 3 2 → D.sig = {3} → ¬ IsPOnePlusTwo 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV))

structure Counterex16 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  setting : Setting16 D V₀ V L
  ne_bot : barSub V₀ V hV L ≠ ⊥
  conc : Conc4_136 D V₀ V hV L
  not_concl : ¬ Concl167 D V₀ V hV L
  not_concl_all : ∀ L' : Subgroup G, Setting16 D V₀ V L' → barSub V₀ V hV L' ≠ ⊥ →
    Conc4_136 D V₀ V hV L' → ¬ Concl167 D V₀ V hV L'
  concl168 : Concl168 D V₀ V hV L
  norm : ChoiceNorm1613 D V₀ V hV L

end Cases

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
