module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharNative
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharBridge

public section

namespace CFSG.StandardType

open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial


theorem ggLieParabolicCharInputOn_notOpen :
    GGLieParabolicCharInputOn fun d => ¬ GGLieParabolicOpenIndex d := by
  intro K _ _ d hd ⟨e⟩ h2 S X hS hSi hNX hX
  obtain ⟨F, _, _, _, D, ⟨b⟩⟩ := exists_rootWeightDatum_of_not_open d hd h2
  haveI : Fact d.1.characteristic.Prime := ⟨TauCeti.LieTypeIndex.characteristic_prime d.1⟩
  set φ : K ≃* ↥D.group := e.trans b
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hS' : IsPGroup d.1.characteristic (S.map φ.toMonoidHom) := hS.map _
  have hSi' : ¬ d.1.characteristic ∣ (S.map φ.toMonoidHom).index := by
    rwa [Subgroup.index_map_of_bijective φ.bijective]
  have hNX' : Subgroup.normalizer ((S.map φ.toMonoidHom : Subgroup ↥D.group) : Set ↥D.group) ≤
      X.map φ.toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNX
  have hX' : X.map φ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hX
    have h' := Subgroup.comap_map_eq_self_of_injective hinj X
    rw [h, Subgroup.comap_top] at h'
    exact h'.symm
  exact isCharacteristicP_of_mulEquiv (X.equivMapOfInjective _ hinj).symm
    (RootWeightDatum.isCharacteristicP_of_normalizer_sylow_le d.1.characteristic D hS' hSi' hNX'
      hX')

end CFSG.StandardType
