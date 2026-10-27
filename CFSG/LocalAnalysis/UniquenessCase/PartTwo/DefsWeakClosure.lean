module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem conjSubgroup_conjSubgroup_inv (A : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup A g) g⁻¹ = A := by
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem conjSubgroup_eq_bot_iff {A : Subgroup G} {g : G} : conjSubgroup A g = ⊥ ↔ A = ⊥ := by
  constructor
  · intro h
    rw [← conjSubgroup_conjSubgroup_inv A g, h]
    exact Subgroup.map_bot _
  · rintro rfl
    exact Subgroup.map_bot _

@[expose] noncomputable def rMV (M V : Subgroup G) : ℕ∞ :=
  ⨅ U ∈ {U : Subgroup G | U ≤ V ∧ ¬ centralizer (U : Set G) ≤ M}, (E3.mQuot V U : ℕ∞)

theorem rMV_eq_rParam {M V : Subgroup G} (h : normalizer (V : Set G) = M) :
    rMV M V = E3.rParam V := by
  unfold rMV E3.rParam
  rw [h]

theorem rMV_eq_rParam_of_inCalV [Finite G] (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) :
    rMV D.M V = E3.rParam V :=
  rMV_eq_rParam (normalizer_eq_of_inCalV D hV)

@[expose] def InCalVStar (M V : Subgroup G) : Prop :=
  InCalV M V ∧ ∀ W : Subgroup G, InCalV M W → V ≤ W → W = V

@[expose] def OFirst (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop :=
  ¬ conjSubgroup V g ≤ M ∧ E3.mQuot V (conjSubgroup M g) ≤ n ∧
    (V₀ ≠ ⊥ → V₀ ⊓ conjSubgroup M g ≠ ⊥)

@[expose] def ODual (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop :=
  ¬ V ≤ conjSubgroup M g ∧ E3.mQuot (conjSubgroup V g) M ≤ n ∧
    (V₀ ≠ ⊥ → conjSubgroup V₀ g ⊓ M ≠ ⊥)

theorem oFirst_swap (n : ℕ) (M V₀ V : Subgroup G) (g : G) :
    OFirst n (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ ↔ ODual n M V₀ V g := by
  simp only [OFirst, ODual, conjSubgroup_conjSubgroup_inv, ne_eq, conjSubgroup_eq_bot_iff]

@[expose] def InCalO (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop :=
  OFirst n M V₀ V g ∧ ODual n M V₀ V g

@[expose] def calO (n : ℕ) (M V₀ V : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = conjSubgroup V g ∧ InCalO n M V₀ V g}

section O1

variable [Finite G]

@[expose] def OneFirst (M V₀ V : Subgroup G) (g : G) : Prop :=
  conjSubgroup V g ⊓ M ⊓ centralizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) ≤
    F11.CTilde M V₀ V

@[expose] def OneDual (M V₀ V : Subgroup G) (g : G) : Prop :=
  V ⊓ conjSubgroup M g ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) ≤
    F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g)

theorem oneFirst_swap (M V₀ V : Subgroup G) (g : G) :
    OneFirst (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ ↔ OneDual M V₀ V g := by
  simp only [OneFirst, OneDual, conjSubgroup_conjSubgroup_inv]

@[expose] def InCalO1 (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop :=
  InCalO n M V₀ V g ∧ OneFirst M V₀ V g ∧ OneDual M V₀ V g

@[expose] def calO1 (n : ℕ) (M V₀ V : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = conjSubgroup V g ∧ InCalO1 n M V₀ V g}

end O1

@[expose] def TwoFirst (n : ℕ) (M V : Subgroup G) (g : G) : Prop :=
  ∃ I ∈ E3.gammaSet V n (V ⊓ conjSubgroup M g),
    ¬ conjSubgroup V g ⊓ M ⊓ centralizer (I : Set G) ≤ centralizer (V : Set G)

@[expose] def TwoDual (n : ℕ) (M V : Subgroup G) (g : G) : Prop :=
  ∃ I ∈ E3.gammaSet (conjSubgroup V g) n (conjSubgroup V g ⊓ M),
    ¬ V ⊓ conjSubgroup M g ⊓ centralizer (I : Set G) ≤ centralizer (conjSubgroup V g : Set G)

theorem twoFirst_swap (n : ℕ) (M V : Subgroup G) (g : G) :
    TwoFirst n (conjSubgroup M g) (conjSubgroup V g) g⁻¹ ↔ TwoDual n M V g := by
  simp only [TwoFirst, TwoDual, conjSubgroup_conjSubgroup_inv]

@[expose] def InCalO2 (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop :=
  InCalO n M V₀ V g ∧ TwoFirst n M V g ∧ TwoDual n M V g ∧
    ¬ IsPGroup 2 (V ⊔ conjSubgroup V g : Subgroup G)

@[expose] def calO2 (n : ℕ) (M V₀ V : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = conjSubgroup V g ∧ InCalO2 n M V₀ V g}

section OStar

variable [Finite G]

@[expose] def QuotShape (L K : Subgroup G) [(K.subgroupOf L).Normal] (d : ℕ) : Prop :=
  ((∃ r : ℕ, IsL2 (↥L ⧸ K.subgroupOf L) r) ∨ (∃ r : ℕ, IsSz (↥L ⧸ K.subgroupOf L) r) ∨
    (∃ m : ℕ, Odd m ∧ Nonempty ((↥L ⧸ K.subgroupOf L) ≃* DihedralGroup m))) ∧
  twoRank (↥L ⧸ K.subgroupOf L) = d

@[expose] def InCalOStar (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop :=
  InCalO n M V₀ V g ∧
    ∃ K : Subgroup G, ∃ _ : (K.subgroupOf (V ⊔ conjSubgroup V g)).Normal,
      (K : Set G) = ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) *
          ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) ∧
        QuotShape (V ⊔ conjSubgroup V g) K (E3.mQuot V (conjSubgroup M g)) ∧
        (∃ l ∈ V ⊔ conjSubgroup V g, conjSubgroup V g = conjSubgroup V l) ∧
        ⁅conjSubgroup V₀ g, V⁆ ≤ V₀ ∧
        V ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) =
          (V ⊓ conjSubgroup V g) ⊔ V₀ ∧
        (V ⊓ conjSubgroup V g) ⊔ V₀ ≠ V ⊓ conjSubgroup M g

@[expose] def calOStar (n : ℕ) (M V₀ V : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g : G, X = conjSubgroup V g ∧ InCalOStar n M V₀ V g}

end OStar

@[expose] def commElt (W : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.closure {x | ∃ w ∈ W, x = w⁻¹ * t⁻¹ * w * t}

theorem commElt_le_commutator (W : Subgroup G) (t : G) :
    commElt W t ≤ ⁅W, Subgroup.zpowers t⁆ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, hw, rfl⟩
  have h := Subgroup.commutator_mem_commutator (H₁ := W) (H₂ := Subgroup.zpowers t)
    (W.inv_mem hw) (Subgroup.inv_mem _ (Subgroup.mem_zpowers t))
  simpa [commutatorElement_def, mul_assoc] using h

@[expose] def propN (P : Subgroup G → Prop) (n : ℕ) (M V : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ V ∧ ∃ t ∈ M ⊓ centralizer (U : Set G), (∃ k : ℕ, orderOf t = 2 ^ k) ∧
    ∃ W : Subgroup G, W ≤ V ∧ E3.mQuot V W ≤ n ∧ U ≤ W ∧
      ¬ W ≤ centralizer ({t} : Set G) ∧ P (commElt W t)}

@[expose] def PropB (M Z : Subgroup G) : Prop :=
  ¬ centralizer (Z : Set G) ≤ M

@[expose] def PropC [Finite G] (M Z : Subgroup G) : Prop :=
  ∃ g : G, g ∉ M ∧ rankThreeGamma 1 2 Z ≤ conjSubgroup M g

@[expose] def PropD (M Z : Subgroup G) : Prop :=
  ∀ z ∈ Z, ¬ centralizer ({z} : Set G) ≤ M

@[expose] def calBn (n : ℕ) (M V : Subgroup G) : Set (Subgroup G) :=
  propN (PropB M) n M V

@[expose] def calCn [Finite G] (n : ℕ) (M V : Subgroup G) : Set (Subgroup G) :=
  propN (PropC M) n M V

@[expose] def calDn (n : ℕ) (M V : Subgroup G) : Set (Subgroup G) :=
  propN (PropD M) n M V

@[expose] noncomputable def betaN (n : ℕ) (M V : Subgroup G) : ℕ∞ :=
  ⨅ U ∈ calBn n M V, (E3.mQuot V U : ℕ∞)

@[expose] noncomputable def gammaN [Finite G] (n : ℕ) (M V : Subgroup G) : ℕ∞ :=
  ⨅ U ∈ calCn n M V, (E3.mQuot V U : ℕ∞)

@[expose] noncomputable def deltaN (n : ℕ) (M V : Subgroup G) : ℕ∞ :=
  ⨅ U ∈ calDn n M V, (E3.mQuot V U : ℕ∞)

@[expose] noncomputable def deltaInf (M V : Subgroup G) : ℕ∞ := deltaN (mSub V) M V

@[expose] def kerM (M H : Subgroup G) : Subgroup G :=
  ((M.subgroupOf H).normalCore).map H.subtype

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
