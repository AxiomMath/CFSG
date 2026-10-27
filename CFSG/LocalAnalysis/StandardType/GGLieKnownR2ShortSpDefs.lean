module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType.ClassicalPosition CFSG.LieType.BorelTits

@[expose] def spAltSiegel (n : ℕ) (F : Type) [Field F] (a₁ a₂ : Fin n ⊕ Fin n → F) :
    Subgroup ↥(StatedSp n F) :=
  (altSiegelGroup (spJ n F) a₁ a₂).comap (StatedSp n F).subtype

@[expose] def SpPlanePair (n : ℕ) (F : Type) [Field F] (a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F) : Prop :=
  a₁ ⬝ᵥ Matrix.mulVec (spJ n F) b₁ = 1 ∧ a₂ ⬝ᵥ Matrix.mulVec (spJ n F) b₂ = 1 ∧
    (a₁ ⬝ᵥ Matrix.mulVec (spJ n F) a₂ = 0 ∧ b₁ ⬝ᵥ Matrix.mulVec (spJ n F) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (spJ n F) b₂ = 0 ∧ a₂ ⬝ᵥ Matrix.mulVec (spJ n F) b₁ = 0)

open scoped Matrix in
theorem spJ_transpose_char_two {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (spJ n F)ᵀ = spJ n F := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [spJ, Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

open scoped Matrix in
theorem mem_spAltSiegel_of_mulVec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F} {g : ↥(StatedSp n F)} (c : F)
    (h : ∀ v : Fin n ⊕ Fin n → F,
      Matrix.mulVec ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v =
        v + (c * (a₂ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₁ +
          (c * (a₁ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₂) :
    g ∈ spAltSiegel n F a₁ a₂ := by
  have hsym : ∀ (w : Fin n ⊕ Fin n → F) (j : Fin n ⊕ Fin n),
      w ⬝ᵥ Matrix.mulVec (spJ n F) (Pi.single j 1) = Matrix.mulVec (spJ n F) w j := by
    intro w j
    rw [Matrix.dotProduct_mulVec, ← spJ_transpose_char_two (n := n) (F := F),
      Matrix.vecMul_transpose, spJ_transpose_char_two, dotProduct_single_one]
  refine Subgroup.subset_closure ⟨c, ?_⟩
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hj
  simp only [Matrix.col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsym] at hj
  change ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j = _
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  simp only [Pi.single_apply] at hj
  rw [hj]
  ring

open scoped Matrix in
theorem exists_mem_spAltSiegel_mulVec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F} (h : a₁ ⬝ᵥ Matrix.mulVec (spJ n F) a₂ = 0) (c : F) :
    ∃ g ∈ spAltSiegel n F a₁ a₂, ∀ v : Fin n ⊕ Fin n → F,
      Matrix.mulVec ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v =
        v + (c * (a₂ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₁ +
          (c * (a₁ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₂ := by
  have hxy : (spForm n F).β a₁ (c • a₂) = 0 := by
    rw [spForm_β, Matrix.mulVec_smul, dotProduct_smul, h, smul_zero]
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.B113Lie.Sp.exists_siegel a₁ (c • a₂) hxy
  have hg' : ∀ v : Fin n ⊕ Fin n → F,
      Matrix.mulVec ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v =
        v + (c * (a₂ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₁ +
          (c * (a₁ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₂ := by
    intro v
    have := hg v
    rw [natRep_apply] at this
    rw [this]
    simp only [spForm_β, smul_dotProduct, smul_eq_mul, smul_smul]
    rw [mul_comm (a₁ ⬝ᵥ _) c, add_right_comm]
  exact ⟨g, mem_spAltSiegel_of_mulVec c hg', hg'⟩

end CFSG.StandardType.LieKnownR2.Short
