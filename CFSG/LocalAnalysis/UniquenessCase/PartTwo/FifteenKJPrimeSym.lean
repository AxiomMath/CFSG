module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.Quasithin.Background.G64Realize
import CFSG.Quasithin.Background.B5Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s15k_jp_sym_five {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    {m : ℕ} (hm : 5 ≤ m) (h : SymmetricNatural J R ⊥ m) :
    (⁅J, J⁆.subgroupOf J).index ≤ 2 ∧ s15KNat ↥⁅J, J⁆ ⁅J, J⁆ R := by
  obtain ⟨π₁, hπ⟩ := h
  let π : Equiv.Perm (Fin m) →* ↥J := π₁
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (G64.symDn_faithful hm) hπ
  have hsurj : Function.Surjective π := hπ.1
  have hbij : Function.Bijective π := ⟨hinj, hsurj⟩
  let ψ : Equiv.Perm (Fin m) →* MulAut W := J.subtype.comp π
  have hψinj : Function.Injective ψ := J.subtype_injective.comp hinj
  have hA : commutator (Equiv.Perm (Fin m)) = alternatingGroup (Fin m) :=
    alternatingGroup.commutator_perm_eq (by simpa using hm)
  have hmapψ : (alternatingGroup (Fin m)).map ψ = ⁅J, J⁆ := by
    rw [← hA]
    exact s15k_jp_derived_map_eq π hsurj
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  refine ⟨?_, ?_⟩
  · rw [s15k_jp_index_eq π hbij, hA, alternatingGroup.index_eq_two]
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm,
      ⟨((Subgroup.equivMapOfInjective _ ψ hψinj).trans (MulEquiv.subgroupCongr hmapψ)).symm⟩,
      B5.alternatingNatural_derived hm ⟨π₁, hπ⟩⟩))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
