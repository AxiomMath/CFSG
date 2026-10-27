module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Choice2011ZRepair (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, c.n = CFSG.Open.pRank 2 D.Z →
    c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥

@[expose] def KTab23a : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        letI : MulAction ↥S W :=
          MulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        Nat.card ℓ = 2 ^ n ∧ IsParabolicTwo ↥H Pℓ ∧ (S : Subgroup ↥H) ≤ Pℓ

@[expose] def KTab23b : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        ∀ Tstar : Subgroup (MulAut W),
          Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
          IsPGroup 2 ↥Tstar →
          (S : Subgroup ↥H).map H.subtype ≤ Tstar →
          let Good : Subgroup ↥H → Prop := fun Pstar =>
            IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
            (∀ t ∈ Tstar,
              (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
            ¬ Pstar ≤ Pℓ
          ((IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) n) ∧
          ((IsOmegaMinus ↥H 4 n ∧ NatOmegaMinus H ⊤ ⊥ 4 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) (2 * n)) ∧
          ((IsOmegaPlus ↥H 4 n ∧ NatOmegaPlus H ⊤ ⊥ 4 n ∧
              (∀ N : Subgroup ↥H, N.Normal →
                (∀ t ∈ Tstar,
                  (N.map H.subtype).map (MulAut.conj t).toMonoidHom = N.map H.subtype) →
                N ≠ ⊤ → N ≤ Subgroup.center ↥H)) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar = ⊤ ∧ IsL2Square (Bar2 (Hinf Pstar)) n) ∧
          ((IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))) ∧
          ((IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n) →
            ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
              Pstar ≠ ⊤ ∧
                (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥)))

@[expose] def KTab23c : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let CH : Subgroup ↥H := fixingSubgroupOf ↥H W (ℓ : Set W)
        ∀ B : Subgroup ↥H, IsMulCommutative ↥B → Odd (Nat.card ↥B) →
          Nat.card ↥((S : Subgroup ↥H) ⊔ B) = Nat.card (S : Subgroup ↥H) * Nat.card ↥B →
          ((IsOmegaMinus ↥H 4 n ∧ NatOmegaMinus H ⊤ ⊥ 4 n) →
            piSet (B ⊓ CH) = piSet B ∩ {p : ℕ | p.Prime ∧ p ∣ 2 ^ n + 1}) ∧
          ((IsOmegaPlus ↥H 4 n ∧ NatOmegaPlus H ⊤ ⊥ 4 n) →
            IsCyclic ↥(B ⊓ CH) ∧
              ∀ E : Subgroup ↥H, E ≤ B → E ⊓ CH = ⊥ → IsCyclic ↥E)

@[expose] def NineLines {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  (IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) ∨
  (IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) ∨
  (IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n) ∨
  (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) ∨
  (IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) ∨
  (IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n) ∨
  (IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) ∨ (IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) ∨
  (IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n)

@[expose] def KTab23cNine : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    NineLines H n → ⁅H, H⁆ = H →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        ∀ Tstar : Subgroup (MulAut W),
          Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
          IsPGroup 2 ↥Tstar →
          (S : Subgroup ↥H).map H.subtype ≤ Tstar →
          let Good : Subgroup ↥H → Prop := fun Pstar =>
            IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
            (∀ t ∈ Tstar,
              (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
            ¬ Pstar ≤ Pℓ
          ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
            ∀ B : Subgroup ↥H, B ≤ Hinf Pstar → Odd (Nat.card ↥B) →
              B ⊓ fixingSubgroupOf ↥H W (ℓ : Set W) = ⊥

@[expose] def KSchurL2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (j : ℕ), ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ →
    ∀ (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X → Odd (Nat.card ↥Z) →
      (IsL2 (X ⧸ Z) j ∨ IsL2Square (X ⧸ Z) j) → Z = ⊥

@[expose] def KNshape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k j : ℕ), NParam L k →
    (IsL2 (Bar2 L) j ∨ IsL2Square (Bar2 L) j) → k = j

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
