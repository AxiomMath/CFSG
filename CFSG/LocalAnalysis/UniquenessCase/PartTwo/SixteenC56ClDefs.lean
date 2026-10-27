module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveDefs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

structure SingLineShape {W : Type} [CommGroup W] (E : Subgroup (MulAut W)) : Prop where
  fix_ne_bot : fixV E ≠ ⊥
  index_le : (E3.gammaCheck 2 E).index ≤ 4
  fix_le_comm : ∀ f ∈ fixV E, ∃ e ∈ E, ∃ u ∈ E3.gammaCheck 2 E, e u * u⁻¹ = f
  mem_of_comm : ∀ e ∈ E, e ≠ 1 → ∀ w : W, e w * w⁻¹ ∈ fixV E → w ∈ E3.gammaCheck 2 E

@[expose] def GeoDichotomy : Prop :=
  ∀ {W : Type} [CommGroup W] (S : OmegaModel W), Nat.card S.K = 4 →
    ∀ {X E : Subgroup (MulAut W)}, X ≤ Subgroup.normalizer (S.omega : Set (MulAut W)) →
      E ∈ E3.aSet 2 X → E3.gammaCheck 2 E = ⊤ ∨ SingLineShape E

variable {G : Type} [Group G]

@[expose] def C33Orth (V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∃ S : OmegaModel (IntMod V hV), Nat.card S.K = 4 ∧
    autI hV ⊤ ≤ Subgroup.normalizer (S.omega : Set (MulAut (IntMod V hV)))

structure C33Setting (M V : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  normalizer_eq : Subgroup.normalizer (V : Set G) = M
  orth : C33Orth V elemAbelian
  gamma_le : ∀ i : ℕ, i ≤ 1 → ∀ A ∈ E3.gammaSet V i M, A ≤ Subgroup.centralizer (V : Set G)
  aSet_two : ∀ A ∈ E3.gammaSet V 2 M, ¬ A ≤ Subgroup.centralizer (V : Set G) →
    autI elemAbelian A ∈ E3.aSet 2 (autI elemAbelian ⊤)
  lt_rMV : (4 : ℕ∞) < rMV M V

structure C33Prim (M V : Subgroup G) (g : G) : Prop where
  not_conjV_le_M : ¬ conjSubgroup V g ≤ M
  not_V_le_conjM : ¬ V ≤ conjSubgroup M g
  mQuot_U : E3.mQuot V (conjSubgroup M g) ≤ 2
  centralizer_le : V ⊓ Subgroup.centralizer ((BOf M V g : Subgroup G) : Set G) ≤ conjSubgroup V g
  comm_ne : ¬ UOf M V g ≤ Subgroup.centralizer (conjSubgroup V g : Set G)
  mem_of_commutator_mem : ∀ b ∈ BOf M V g, b ∉ Subgroup.centralizer (V : Set G) → ∀ v ∈ V,
    ⁅v, b⁆ ∈ V ⊓ conjSubgroup V g → v ∈ conjSubgroup M g

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
