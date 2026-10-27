module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelShapeE
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_inner_conj_mem_diag_e6
    {F : Type} [Field F] [Finite F] [CharP F 2] (h3 : 3 ∣ Nat.card F - 1)
    {E : Subgroup (MulAut ↥(adjointGroup .E6 F))} (hE𝒟 : E ≤ LayerSixE.inndiagAut .E6 F)
    (hE : IsElemAbelian 3 E) (h5 : 3 ^ 5 ≤ Nat.card E) :
    ∃ g : ↥(adjointGroup .E6 F), ∀ x ∈ E,
      MulAut.conj g * x * (MulAut.conj g)⁻¹ ∈ (rootDiagAutHom .E6 F).range := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hEH : E ≤ (E6ThreeModel.eFrame F ζ hζ).H :=
    hE𝒟.trans (le_of_eq NoOffE6Three.hatAut_range_eq_sup.symm)
  obtain ⟨γ, hγ, hγE⟩ := E6ThreeModel.eFrame_shape hζo hζ E hEH hE h5
  obtain ⟨g, hg⟩ := OutdiagE6.exists_inner_conj_map_le le_rfl hγ (by
    rintro _ ⟨x, hx, rfl⟩
    exact OutdiagE6.vAd_le_diag ζ hζ (hγE x hx))
  exact ⟨g, fun x hx => hg ⟨x, hx, rfl⟩⟩

end CFSG.StandardType

end
