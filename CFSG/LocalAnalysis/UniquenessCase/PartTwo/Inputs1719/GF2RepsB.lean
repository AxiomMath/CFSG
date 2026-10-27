module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.F6
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

@[expose] def HasPGL2Subgroup (Y L : Subgroup (MulAut W)) (q : ℕ) : Prop :=
  ∃ A : Subgroup (MulAut W), A ≤ Y ∧ L ≤ A ∧ CFSG.Quasithin.F6.IsPGL2 q ↥A

@[expose] noncomputable def epsL2 (Y L : Subgroup (MulAut W)) (q : ℕ) : ℕ := by
  classical
  exact if IsSquare q ∧ ¬ HasPGL2Subgroup Y L q then 2 else 1

@[expose] noncomputable def deltaP (p : ℕ) : ℕ := by
  classical
  exact if Even (dParam p) then 1 else 2

@[expose] def HasInvertedSylowP (p : ℕ) (L Y : Subgroup (MulAut W)) : Prop :=
  ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsSylowIn p E L ∧
    ∃ g ∈ Y, ∀ e ∈ E, g * e * g⁻¹ = e⁻¹

@[expose] def InducesPGL2Involution (q : ℕ) (Y L : Subgroup (MulAut W)) (t : MulAut W) : Prop :=
  t ∈ L ∨ ∃ A : Subgroup (MulAut W), A ≤ Y ∧ L ≤ A ∧ t ∈ A ∧ CFSG.Quasithin.F6.IsPGL2 q ↥A

@[expose] def InGq (X : Type) [Group X] (q : ℕ) : Prop :=
  (∃ (t : CFSG.Open.StatedLieTag) (n p e : ℕ),
      p.Prime ∧ p ≠ 2 ∧ 0 < e ∧ q = p ^ e ∧ LieModel X t n p e) ∨
    (q = 3 ∧ LieModel X .PSL 2 2 3)

@[expose] def tableM : TauCeti.SporadicName → ℕ
  | .M11 => 4 | .M12 => 4 | .M22 => 3 | .M23 => 4 | .M24 => 4
  | .J1 => 8 | .J2 => 4 | .J3 => 6 | .J4 => 50
  | .Co1 => 8 | .Co2 => 6 | .Co3 => 8
  | .Fi22 => 18 | .Fi23 => 18 | .Fi24Prime => 18
  | .HS => 6 | .McL => 8 | .He => 10 | .Ru => 12 | .Suz => 8 | .ONan => 21
  | .HN => 40 | .Ly => 33 | .Th => 9 | .B => 54 | .M => 54

@[expose] def tableA : TauCeti.SporadicName → ℕ
  | .M11 => 1 | .M12 => 2 | .M22 => 5 | .M23 => 4 | .M24 => 6
  | .J1 => 3 | .J2 => 3 | .J3 => 4 | .J4 => 11
  | .Co1 => 11 | .Co2 => 10 | .Co3 => 4
  | .Fi22 => 10 | .Fi23 => 11 | .Fi24Prime => 12
  | .HS => 4 | .McL => 4 | .He => 6 | .Ru => 6 | .Suz => 6 | .ONan => 4
  | .HN => 6 | .Ly => 4 | .Th => 5 | .B => 22 | .M => 24

@[expose] def W4Lem7_4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (p e q : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      p.Prime → p ≠ 2 → 0 < e → q = p ^ e → 9 < q → LieModel ↥L .PSL 2 p e →
        ((q - 1) * dParam p / (epsL2 Y L q * (p - 1)) ≤ rk W) ∧
        (HasInvertedSylowP p L Y →
          (q - 1) * deltaP p * dParam p / (epsL2 Y L q * (p - 1)) ≤ rk W) ∧
        (∀ t : MulAut W, t ∈ Y → orderOf t = 2 →
          (InducesPGL2Involution q Y L t →
            ∃ x y z : MulAut W, x ∈ Y ∧ y ∈ Y ∧ z ∈ Y ∧
              Subgroup.closure ({x * t * x⁻¹, y * t * y⁻¹, z * t * z⁻¹} : Set (MulAut W)) =
                L ⊔ Subgroup.zpowers t)) ∧
        (1 < e → 8 ≤ E3.mParam Y ∨ (q = 25 ∧ 6 ≤ E3.mParam L)) ∧
        4 ≤ E3.mParam Y

@[expose] def W4Lem7_7 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y K A : Subgroup (MulAut W)) (k : ℕ),
      letI : Finite ↥K := Finite.of_injective (fun x : ↥K => ((x : MulAut W) : W → W))
        (fun x y h => Subtype.ext (DFunLike.ext _ _ (congrFun h)))
      IsComponentOf K Y → A ∈ E3.aSet k Y →
      (∀ n, Nonempty (ACandidate ↥K n) → n < k) → ⁅A, K⁆ = ⊥

@[expose] def W4Lem10_5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (p e q : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → q = p ^ e →
      InGq (↥L ⧸ Subgroup.center ↥L) q →
        8 ≤ E3.mParam Y ∨
        (LieModel ↥L .PSL 3 3 1 ∧ 4 ≤ E3.mParam Y) ∨
        ((LieModel ↥L .PSL 4 3 1 ∨ LieModel ↥L .PSU 4 3 1 ∨
            LieModel ↥L .G2 0 3 1 ∨
            (∃ (Z : Subgroup ↥L) (hZ : Z.Normal), Z ≤ Subgroup.center ↥L ∧
              Nat.card Z = 3 ∧ LieModel (quotBy Z hZ) .G2 0 3 1) ∨
            LieModel ↥L .PSp 3 3 1) ∧
          6 ≤ E3.mParam Y) ∨
        (LieModel ↥L .PSU 3 3 1 ∨ LieModel ↥L .PSp 2 3 1 ∨
          LieModel ↥L .PSL 2 2 3 ∨
          (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 ∧
            Subgroup.center ↥L ≠ ⊥)) ∨
        ((LieModel ↥L .PSL 2 5 2 ∨ LieModel ↥L .PSL 2 p 1) ∧ 4 ≤ E3.mParam Y) ∨
        (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 5 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 7 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2)

@[expose] def W4Lem10_6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (p e q : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → q = p ^ e →
      InGq (↥L ⧸ Subgroup.center ↥L) q →
        (9 < q → E3.aParam Y = 1) ∧
        (3 < q → E3.aParam Y ≤ 2) ∧
        (q = 3 → E3.aParam Y ≤ 3)

@[expose] def W4Lem11_9 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L T : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor ↥L .HS →
      T ≤ Y → IsSylowIn 2 T Y →
      fixV T ≠ fixV Y →
        E3.aParam Y ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
