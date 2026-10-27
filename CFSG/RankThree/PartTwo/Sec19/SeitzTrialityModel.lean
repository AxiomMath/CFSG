module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

theorem eq_top_of_maximal_pair {G : Type*} [Group G] {A B H : Subgroup G}
    (hmax : ∀ N : Subgroup G, A ⊔ B ≤ N → N = A ⊔ B ∨ N = ⊤)
    (hA : A ≤ H) (hB : B ≤ H) (hH : ¬ H ≤ A ⊔ B) : H = ⊤ :=
  (hmax H (sup_le hA hB)).resolve_left fun h => hH (h ▸ le_refl _)

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

abbrev C0 : Type := graphFixedRootGroup TwistTag.D4 X σ.toRingHom

noncomputable abbrev Asub : Subgroup (C0 σ) := KS11Lie4Proof.d4ShortSL2 X σ.toRingHom

@[expose] noncomputable def Bsub : Subgroup (C0 σ) := Subgroup.centralizer ((Asub σ : Subgroup (C0 σ)) : Set (C0 σ))

noncomputable abbrev tauAut : MulAut (C0 σ) := fieldActor (t := TwistTag.D4) σ σ

@[expose] noncomputable def Gsub : Subgroup (C0 σ) := MonoidHom.eqLocus (tauAut σ).toMonoidHom (MonoidHom.id _)

@[expose] noncomputable def A0sub : Subgroup (C0 σ) := Asub σ ⊓ Gsub σ

@[expose] def IsClassX (x : C0 σ) : Prop := x ^ 3 = 1 ∧ x ≠ 1 ∧ ∃ g : C0 σ, g * x * g⁻¹ ∈ Asub σ

end Model

end CFSG.RankThree.PartTwo.Sec19
