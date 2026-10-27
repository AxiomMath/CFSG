module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def KTab23d : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H → 3 ≤ n →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        let Kstar : Subgroup ↥H := Hinf Pℓ
        ((IsL2 ↥H n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) → Kstar = ⊥) ∧
        ((IsOmegaMinus ↥H 4 n ∧ NatOmegaMinus H ⊤ ⊥ 4 n) → Kstar = ⊥) ∧
        ((IsOmegaPlus ↥H 4 n ∧ NatOmegaPlus H ⊤ ⊥ 4 n) → Kstar = ⊥) ∧
        ((IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) → IsL2 (Bar2 Kstar) n) ∧
        ((IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n) → IsL2 (Bar2 Kstar) n) ∧
        ((∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) →
          ∃ a : ℕ, n = 2 * a ∧ IsL2 (Bar2 Kstar) a) ∧
        ((IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) → IsL2 (Bar2 Kstar) (2 * n)) ∧
        ((IsSLn ↥H 4 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 n) →
          IsSLn (Bar2 Kstar) 3 n) ∧
        ((IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) → IsL2Square (Bar2 Kstar) n) ∧
        ((IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) → IsSp4 (Bar2 Kstar) n) ∧
        ((IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n) → IsU4 (Bar2 Kstar) n)

@[expose] def KAdj : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H → 3 ≤ n →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        let Kstar : Subgroup ↥H := Hinf Pℓ
        Kstar ≠ ⊥ →
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
          ∀ r : ℕ, r.Prime → r ≠ 2 →
            ((∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
              (∃ k : ℕ, n = 2 ^ k ∧ r = 3)) →
          ∀ t ∈ Hinf Pstar ⊓ Pℓ, orderOf t = r →
            t ∉ fixingSubgroupOf ↥H W (ℓ : Set W) →
            ∃ m : ℕ, (m = n ∨ m = 2 * n ∨
              (n = 2 * m ∧ IsSUn ↥H 4 m ∧ NatSUn H ⊤ ⊥ 4 m)) ∧
            ∃ X₁ X₂ : Subgroup ↥H, X₁ ≤ Kstar ∧ X₂ ≤ Kstar ∧
              (∀ N : Subgroup ↥H, N ≤ Kstar →
                Kstar ≤ Subgroup.normalizer (N : Set ↥H) → X₁ ≤ N → X₂ ≤ N → N = Kstar) ∧
              ∀ X : Subgroup ↥H, (X = X₁ ∨ X = X₂) →
                IsSLn ↥X 2 m ∧ t ∈ Subgroup.normalizer (X : Set ↥H) ∧
                  ∃ d ∈ X, orderOf d = r ∧ ∀ x ∈ X, t * x * t⁻¹ = d * x * d⁻¹

@[expose] def KSU44 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    IsSUn ↥H 4 2 → NatSUn H ⊤ ⊥ 4 2 →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        let Kstar : Subgroup ↥H := Hinf Pℓ
        ∃ E : Subgroup ↥H, IsElemAbelian 3 E ∧ Nat.card ↥E = 9 ∧
          E ≤ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H) ∧
          E ⊓ fixingSubgroupOf ↥H W (ℓ : Set W) = E ⊓ Kstar ∧
          Nat.card ↥(E ⊓ Kstar) = 3 ∧
          (∃ k ∈ Kstar, ∃ e ∈ E ⊓ Kstar, e * k ≠ k * e) ∧
          ∃ w : ↥H, w ∉ Pℓ ∧ ∀ e ∈ E, w * e * w⁻¹ = e⁻¹

@[expose] def KGen : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H → 3 ≤ n →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        let Kstar : Subgroup ↥H := Hinf Pℓ
        ((IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) →
          ∃ A : Subgroup ↥H, A ≤ Kstar ∧ Nat.card ↥A = 3 ∧
            ∃ w : ↥H, w ∉ Pℓ ∧ ∀ a ∈ A, w * a * w⁻¹ ∈ A) ∧
        ((∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) →
          ∃ A : Subgroup ↥H, A ≤ Kstar ∧ Nat.card ↥A = 3 ∧
            ∃ w : ↥H, w ∉ Pℓ ∧ ∀ a ∈ A, w * a * w⁻¹ ∈ A) ∧
        ((IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) →
          ∃ A : Subgroup ↥H, A ≤ Kstar ∧ Nat.card ↥A = 3 ∧
            ∃ w : ↥H, w ∉ Pℓ ∧ ∀ a ∈ A, w * a * w⁻¹ ∈ A)

@[expose] def KSchurSL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ →
    ∀ (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X →
      IsSLn (X ⧸ Z) 3 n → 3 ≤ n → Z = ⊥

@[expose] def S23_9_PointStab (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    D.M ⊓ c.L = c.L ⊓ Subgroup.normalizer (D.Z : Set G) ∧
    (∀ a : ℕ, IsL2 (Bar2 c.L) a → Hinf (D.M ⊓ c.L) = ⊥) ∧
    (∀ a : ℕ, IsOmegaMinus (Bar2 c.L) 4 a → Hinf (D.M ⊓ c.L) = ⊥)

@[expose] def S23_9_O2L (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, CFSG.Open.pCoreOf 2 c.L ≤ D.M

@[expose] def S23_9_Semireg (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 →
    ∀ Q : Subgroup G, Q ≤ D.M → IsPGroup q ↥Q → ¬ IsCyclic ↥Q →
      (∀ x ∈ Q, x ^ q = 1) → ⁅⁅Q, Q⁆, Q⁆ = ⊥ →
      D.M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 D.M ⊔ Q : Subgroup G) : Set G) →
      ∀ e ∈ D.M,
        (∀ X : Subgroup G, X ≠ ⊥ → IsPGroup q ↥X →
          X ≤ D.M ⊓ Subgroup.centralizer ({e} : Set G) →
            X ∉ uniqueSet D.M ∧ q ∉ D.sig) →
        Q ⊓ Subgroup.centralizer ({e} : Set G) = ⊥

@[expose] def S23_9_A1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    Hinf (D.M ⊓ c.L) ≠ ⊥ → c.n = CFSG.Open.pRank 2 D.Z →
    ∃ b ∈ c.B0, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ orderOf b = r ∧
      b ∉ Subgroup.centralizer (D.Z : Set G) ∧
      ((∃ s : ℕ, s ∣ c.n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
        (∃ k : ℕ, c.n = 2 ^ k ∧ r = 3))

@[expose] def S23_9_StepA (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    let K : Subgroup G := Hinf (D.M ⊓ c.L)
    ⁅barImage D.M K, CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥

@[expose] def S23_9_B1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    let K : Subgroup G := Hinf (D.M ⊓ c.L)
    barImage D.M K ≤ CFSG.layer (Bar2 D.M)

@[expose] def S23_9_B23 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    let K : Subgroup G := Hinf (D.M ⊓ c.L)
    let n : ℕ := CFSG.Open.pRank 2 D.Z
    K = ⊥ ∨ K ∈ calC D.M ∨
      ((∃ hV : IsElemAbelian 2 c.V, IsOmegaPlus ↥(barSub ⊥ c.V hV c.L) 6 n ∧
          NatOmegaPlus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 6 n) ∧
        ∃ X₁ X₂ : Subgroup G, X₁ ∈ calC D.M ∧ X₂ ∈ calC D.M ∧ X₁ ≠ X₂ ∧
          barImage D.M K = barImage D.M X₁ ⊔ barImage D.M X₂) ∨
      ((∃ hV : IsElemAbelian 2 c.V, ∃ a : ℕ, n = 2 * a ∧
          IsSUn ↥(barSub ⊥ c.V hV c.L) 4 a ∧ NatSUn (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 a) ∧
        ∃ X : Subgroup G, X ∈ calC D.M ∧ K ≤ X)

@[expose] def S23_9_NotSp4SU4O6m (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ hV : IsElemAbelian 2 c.V,
      let Lstar : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
      let n : ℕ := CFSG.Open.pRank 2 D.Z
      ¬ ((IsSp4 ↥Lstar n ∧ NatSpn Lstar ⊤ ⊥ 4 n) ∨
          (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥Lstar 4 a ∧ NatSUn Lstar ⊤ ⊥ 4 a) ∨
          (IsOmegaMinus ↥Lstar 6 n ∧ NatOmegaMinus Lstar ⊤ ⊥ 6 n))

@[expose] def S23_9_NotO6p (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ hV : IsElemAbelian 2 c.V,
      let Lstar : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
      let n : ℕ := CFSG.Open.pRank 2 D.Z
      ¬ (IsOmegaPlus ↥Lstar 6 n ∧ NatOmegaPlus Lstar ⊤ ⊥ 6 n)

@[expose] def S23_9_NotLarge (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ hV : IsElemAbelian 2 c.V,
      let Lstar : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
      let n : ℕ := CFSG.Open.pRank 2 D.Z
      ¬ ((IsSLn ↥Lstar 4 n ∧ CFSG.Quasithin.BinaryNaturalSL Lstar ⊤ ⊥ 4 n) ∨
          (IsSpn ↥Lstar 6 n ∧ NatSpn Lstar ⊤ ⊥ 6 n) ∨
          (IsOmega8m ↥Lstar n ∧ NatOmegaMinus Lstar ⊤ ⊥ 8 n))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
