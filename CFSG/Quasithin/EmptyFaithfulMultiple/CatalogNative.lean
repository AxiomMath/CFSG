module

public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithful.Vocabulary
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Recognition.ModelBridgesJ3
import CFSG.Timmesfeld.Final.PSU33
public import Certificates.Certificate8085
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G]

theorem catalog_of_mulEquiv_alternating_six (e : G ≃* alternatingGroup (Fin 6)) :
    Blueprint.Catalog G :=
  Or.inr (Or.inl ⟨6, by norm_num, ⟨e⟩⟩)

theorem lieModel_psl_three_two_of_mulEquiv
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    Blueprint.LieModel G .PSL 3 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

theorem catalog_of_mulEquiv_psl_three_zmod_two
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : Blueprint.Catalog G :=
  Blueprint.lieModel_catalog G .PSL 3 2 1 (lieModel_psl_three_two_of_mulEquiv e)

theorem catalog_of_isLThreeTwoOrASix (h : IsLThreeTwoOrASix G) : Blueprint.Catalog G := by
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · exact catalog_of_mulEquiv_psl_three_zmod_two e
  · exact catalog_of_mulEquiv_alternating_six e

theorem catalog_of_mulEquiv_quasithinJ2 (e : G ≃* quasithinJ2) : Blueprint.Catalog G :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨.J2, ⟨e.trans CFSG.Quasithin.quasithinJ2MulEquivNative⟩⟩)))

theorem catalog_of_mulEquiv_quasithinJ3
    (e : G ≃* quasithinJ3) : Blueprint.Catalog G :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨.J3, ⟨e.trans CFSG.Quasithin.quasithinJ3MulEquivNative⟩⟩)))

theorem catalog_of_mulEquiv_quasithinM12 (e : G ≃* quasithinM12) : Blueprint.Catalog G :=
  Or.inr (Or.inr (Or.inr (Or.inr
    ⟨.M12, ⟨e.trans (MulEquiv.subgroupCongr CFSG.Quasithin.quasithinM12_eq_native)⟩⟩)))

theorem lieModel_psu_three_three_of_mulEquiv (e : G ≃* PSU3 3 1) :
    Blueprint.LieModel G .PSU 3 3 1 := by
  obtain ⟨e'⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1),
    inferInstance, inferInstance,
    by rw [GaloisField.card 3 (2 * 1) (by norm_num)]; norm_num, ⟨e.trans e'.symm⟩⟩

theorem catalog_of_mulEquiv_psu3_three_one (e : G ≃* PSU3 3 1) : Blueprint.Catalog G :=
  Blueprint.lieModel_catalog G .PSU 3 3 1 (lieModel_psu_three_three_of_mulEquiv e)

theorem catalog_of_sixModels
    (hD4 : Blueprint.Catalog quasithinTrialityD4Two)
    (hTits : Blueprint.Catalog quasithinTits) (h : CFSG.Quasithin.SixModels G) :
    Blueprint.Catalog G := by
  rcases h with h | h | h | h | h | h <;> obtain ⟨e⟩ := h
  · exact catalog_of_mulEquiv_quasithinJ2 e
  · exact catalog_of_mulEquiv_quasithinJ3 e
  · exact CFSG.SectionRank.catalog_of_mulEquiv e hD4
  · exact CFSG.SectionRank.catalog_of_mulEquiv e hTits
  · exact catalog_of_mulEquiv_psu3_three_one e
  · exact catalog_of_mulEquiv_quasithinM12 e

theorem catalog_of_theoremE_alternatives
    (hD4 : Blueprint.Catalog quasithinTrialityD4Two)
    (hTits : Blueprint.Catalog quasithinTits)
    (h : CFSG.Quasithin.SixModels G ∨ IsLThreeTwoOrASix G) : Blueprint.Catalog G := by
  rcases h with h | h
  · exact catalog_of_sixModels hD4 hTits h
  · exact catalog_of_isLThreeTwoOrASix h

@[expose] def G2TwoDerivedUnitaryTransport : Prop :=
  ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
    Blueprint.LieModel ↥⁅Blueprint.Chevalley.adjointGroup .G2 k,
      Blueprint.Chevalley.adjointGroup .G2 k⁆ .PSU 3 3 1

theorem catalog_of_sixModelsNative (hG2 : G2TwoDerivedUnitaryTransport)
    (h : SixModelsNative G) : Blueprint.Catalog G := by
  rcases h with e | e | h | h | ⟨k, _, _, hk, e⟩ | e
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.J2, e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.J3, e⟩)))
  · exact Blueprint.lieModel_catalog G _ _ _ _ h
  · exact Blueprint.lieModel_catalog G _ _ _ _ h
  · obtain ⟨e⟩ := e
    exact CFSG.SectionRank.catalog_of_mulEquiv e
      (Blueprint.lieModel_catalog _ _ _ _ _ (hG2 k hk))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M12, e⟩)))

theorem catalog_of_theoremE_alternatives_native (hG2 : G2TwoDerivedUnitaryTransport)
    (h : SixModelsNative G ∨ IsLThreeTwoOrASix G) : Blueprint.Catalog G := by
  rcases h with h | h
  · exact catalog_of_sixModelsNative hG2 h
  · exact catalog_of_isLThreeTwoOrASix h

end CFSG.Quasithin.EmptyFaithfulMultiple
