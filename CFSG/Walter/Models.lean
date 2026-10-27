module

public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Models

public section

namespace CFSG.Walter

open CFSG.Assembly.LowTwoRank

theorem walterJ1_eq_properTwoGenCoreJ1 :
    CFSG.Open.walterJ1 = CFSG.Open.properTwoGenCoreJ1 := by
  unfold CFSG.Open.walterJ1 CFSG.Open.properTwoGenCoreJ1
  congr 1

@[expose] noncomputable def walterJ1EquivNative :
    CFSG.Open.walterJ1 ≃* CFSG.Blueprint.NativeSporadic.J1 :=
  (MulEquiv.subgroupCongr walterJ1_eq_properTwoGenCoreJ1).trans
    CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv

theorem isSporadic_J1_of_mulEquiv {G : Type} [Group G] (e : G ≃* CFSG.Open.walterJ1) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 :=
  ⟨e.trans walterJ1EquivNative⟩

theorem lieModel_psl_two_of_mulEquiv {G : Type} [Group G] (p f : ℕ) [hp : Fact p.Prime]
    (h4 : 4 ≤ p ^ f)
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) :
    CFSG.Models.LieModel G .PSL 2 p f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h4
  have hadm : StatedLieAdmissible .PSL 2 p f := by
    refine ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hf, le_rfl, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  refine ⟨hadm, Or.inl ⟨hadm, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f hf, ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 _)⟩⟩⟩

end CFSG.Walter
