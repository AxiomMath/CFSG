module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S20_7Shape (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 < n ∧ (IsSz X n ∨ IsL2 X n ∨ IsL3 X n ∨ IsU3 X n ∨ LieModel X .PSL 4 2 n ∨
    IsU4 X n ∨ IsG2 X n ∨ Is3D4 X n ∨ LieModel X .twistedF4 0 2 n ∨ IsSp4 X n ∨ IsSL3 X n ∨
    IsSU3 X n ∨ LieModel X .PSp 3 2 n ∨ IsOmega8m X n)) ∨
  IsU4 X 2 ∨ IsU5 X 2 ∨ IsOmega8m X 2 ∨ Is3D4 X 2 ∨ Is3D4 X 1 ∨
  (∃ n : ℕ, 2 < n ∧ IsSzL2Product X n) ∨ IsSU3CentralSquare X

@[expose] def S20_10Shape (T L : Subgroup G) : Prop :=
  (∃ n : ℕ, IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) ∨
  (∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ ∧
    (∃ t ∈ T, L₂ = L₁.map (MulAut.conj t).toMonoidHom) ∧
    ∃ n : ℕ, ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
      IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3)) ∨
  (∃ n : ℕ, (IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) ∧ ∃ t ∈ T, ActsNontrivOnDiagram L t)

@[expose] def S23_1A (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ (V : Subgroup G) (hV : IsElemAbelian 2 V),
    V ≤ c.V → V = conjClosure c.N (V ⊓ D.Z) → V ≠ ⊥ →
      ∃ hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z)),
        mBar c.N ⊥ V hV ≤ aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + 1 ∧
        aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW ≤ c.n

@[expose] def KRankOneBorel : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (T L J : Subgroup G),
    IsPGroup 2 T → T ≤ normalizer (L : Set G) → IsSylowIn 2 (T ⊓ L) L → ⁅L, L⁆ = L →
    S20_10Shape T L → T ⊓ L ≤ J → J ≤ L → T ≤ normalizer (J : Set G) →
      J ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∨ J = L

@[expose] def KBorelSolv20_7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], S20_7Shape X → ∀ S : Sylow 2 X,
    IsSolvable ↥(normalizer ((S : Subgroup X) : Set X))

@[expose] def KNatBorelIrr : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H S P : Subgroup (MulAut W)) (k : ℕ),
    IsNaturalClassicalModule H k → ⁅H, H⁆ = H → IsSylowIn 2 S H →
    H ⊓ normalizer (S : Set (MulAut W)) ≤ P → P ≤ H → ¬ P ≤ stabSub (fixV S) →
    ∀ J : Subgroup W, J ≤ fixV S → StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J →
      J = ⊥ ∨ J = fixV S

@[expose] def KNatParMax : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H R K S X : Subgroup (MulAut W)) (k : ℕ),
    IsNaturalClassicalModule H k → ⁅H, H⁆ = H → R ≤ normalizer (H : Set (MulAut W)) →
    IsComponentOf K H → H = (⨆ r ∈ R, K.map (MulAut.conj r).toMonoidHom) →
    IsSylowIn 2 S H → R ≤ normalizer (S : Set (MulAut W)) →
    R ≤ normalizer (X : Set (MulAut W)) → H ⊓ stabSub (fixV S) ≤ X → X < H →
      X = H ⊓ stabSub (fixV S)

@[expose] def KMinDegLow : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L K P : Subgroup G) (n : ℕ),
    S20_7Shape (Bar2 L) → K ∈ calC L → ParabolicOf L P → NParam (Hinf P) n → 2 < n →
      n + 1 < dMinDeg (Bar2 K)

@[expose] def KNatInvol : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (k : ℕ) (s : MulAut W),
    IsNaturalClassicalModule H k → s ∈ normalizer (H : Set (MulAut W)) → orderOf s = 2 →
    (∃ h ∈ H, s * h * s⁻¹ ≠ h) → k ≤ rkIdx (fixV (Subgroup.zpowers s))

@[expose] def KNoTransv : Prop :=
  ∀ (B : Type) [CommGroup B] [Finite B], (∀ b : B, b ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut B)) (X : Type) [Group X] [Finite X] (k : ℕ) (s : MulAut B),
      IsClassicalGroup23 X k → (3 ≤ k ∨ (2 ≤ k ∧ IsOmegaMinus X 4 k)) → ⁅H, H⁆ = H →
      (∃ f : ↥H →* X ⧸ Subgroup.center X, Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥H) →
      s ∈ normalizer (H : Set (MulAut B)) → orderOf s = 2 → (∃ h ∈ H, s * h * s⁻¹ ≠ h) →
        2 ≤ rkIdx (fixV (Subgroup.zpowers s))

@[expose] def KNatOm4mA : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H X : Subgroup (MulAut W)) (k : ℕ),
    IsOmegaMinus ↥H 4 k → NatOmegaMinus H ⊤ ⊥ 4 k → H ≤ X →
      X ≤ normalizer (H : Set (MulAut W)) → E3.aParam X ≤ k

@[expose] def KO4PlusSwap : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (R K S : Subgroup (MulAut W)) (e : ℕ),
    PartTwo.IsNaturalO4Plus R e → CFSG.Open.IsQuasisimple K → CFSG.Open.IsSubnormal K R →
    IsSylowIn 2 S R → ¬ S ≤ normalizer (K : Set (MulAut W))

theorem s20_7Shape_of {D : Data G} (h207 : S20_7 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) : S20_7Shape (Bar2 L) :=
  h207 h1930 L hL

theorem s20_10Shape_of {D : Data G} (h2010 : S20_10 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calLLow D.T D.M) : S20_10Shape D.T L :=
  h2010 h1930 L hL

end CFSG.LocalAnalysis.UniquenessCase.UC22

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def W4Thm14_5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L T P : Subgroup (MulAut W)) (e n : ℕ),
      IsKGroup ↥Y → O2Trivial Y → IsIrrOn Y ⊤ ⊥ → IsComponentOf L Y → T ≤ Y → IsSylowIn 2 T Y →
      fixV (⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) = ⊥ →
      (conjSet L T).ncard ≤ 2 →
      ((IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e) ∨
        ((L.subgroupOf Y).Normal ∧ (IsL3 ↥L e ∨ IsSL3 ↥L e ∨ IsSp4 ↥L e ∨ IsU4 ↥L e ∨ IsG2 ↥L e ∨
          Is3D4 ↥L e ∨ LieModel ↥L .twistedF4 0 2 e ∨ (e = 2 ∧ IsU5 ↥L 2) ∨
          LieModel ↥L .PSL 4 2 e ∨ LieModel ↥L .PSp 3 2 e ∨ IsOmega8m ↥L e))) →
      P ≤ L → IsParabolicTwo ↥L (P.subgroupOf L) → Hinf P ≠ ⊥ →
      normIn T L ≤ normalizer (P : Set (MulAut W)) → commSub (fixV T) (Hinf P) ≠ ⊥ →
      NParam (Hinf P) n → 2 < n →
      (∀ Q : Subgroup (MulAut W), Q < P → IsParabolicTwo ↥L (Q.subgroupOf L) →
        normIn T L ≤ normalizer (Q : Set (MulAut W)) → Hinf Q = ⊥) →
      ∀ K : Subgroup (MulAut W), K = (⨆ t ∈ T, (Hinf P).map (MulAut.conj t).toMonoidHom) →
      ∀ W₀ : Subgroup W, W₀ = (⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom) →
      E3.mParam Y ≤ E3.aParam (autSub (K ⊔ T) W₀) + 1 → E3.aParam (autSub (K ⊔ T) W₀) ≤ n →
      ∀ H : Subgroup (MulAut W), H = (⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) →
        (H ≠ L ∧ IsDirSumOver (conjSet L Y) (fun X => commV X) ∧
            ((IsL2 ↥L n ∧ BinaryNaturalSL L (commV L) ⊥ 2 n) ∨
              (Even n ∧ IsOmegaMinus ↥L 4 (n / 2) ∧ NatOmegaMinus L (commV L) ⊥ 4 (n / 2)))) ∨
          IsNaturalClassicalModule H n ∨
          (Even n ∧ IsOmegaMinus ↥H 4 (n / 2) ∧ NatOmegaMinus H ⊤ ⊥ 4 (n / 2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
