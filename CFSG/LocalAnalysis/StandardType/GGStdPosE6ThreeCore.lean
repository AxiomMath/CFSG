module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LieType.Steinberg.Minuscule.Datum
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
import CFSG.LocalAnalysis.StandardType.GGStdPosInnDiagCore
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelShapeE
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE6
import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
import CFSG.LieType.Steinberg.Isogeny.E6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.ClassicalInvolution

namespace StdPosExc

private theorem exists_inner_conj_le_diag_e6
    {F : Type} [Field F] [Finite F] [CharP F 2] (h3 : 3 ∣ Nat.card F - 1)
    {E : Subgroup (MulAut ↥(adjointGroup .E6 F))} (hE𝒟 : E ≤ LayerSixE.inndiagAut .E6 F)
    (hE : IsElemAbelian 3 E) (h5 : 3 ^ 5 ≤ Nat.card E) :
    ∃ g : ↥(adjointGroup .E6 F),
      E.map (MulAut.conj (MulAut.conj g)).toMonoidHom ≤ (rootDiagAutHom .E6 F).range := by
  have := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hEH : E ≤ (E6ThreeModel.eFrame F ζ hζ).H :=
    hE𝒟.trans (le_of_eq NoOffE6Three.hatAut_range_eq_sup.symm)
  obtain ⟨γ, hγ, hγE⟩ := E6ThreeModel.eFrame_shape hζo hζ E hEH hE h5
  refine OutdiagE6.exists_inner_conj_map_le le_rfl hγ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact OutdiagE6.vAd_le_diag ζ hζ (hγE x hx)

theorem exists_stdPos_e6_three
    {F : Type} [Field F] [Finite F] [CharP F 2] (h3 : 3 ∣ Nat.card F - 1)
    {G : Type} [Group G] [Finite G] {ψ : ↥(e6Data_valid.minGroup F) →* G} {Bs : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F)) (hBs : IsElemAbelian 3 Bs)
    (hBN : Bs ≤ Subgroup.normalizer (ψ.range : Set G))
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (e6Datum F) ψ b)
    (hc : 3 ^ 5 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : ↥(e6Data_valid.minGroup F),
      GGKGPosStdPos (e6Datum F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  have : Group.IsPerfect ↥(e6Data_valid.minGroup F) := LieType.CurtisTits.isPerfect_e6 F
  have hperf : commutator ↥ψ.range = ⊤ := Group.isPerfect_def.1 (Group.IsPerfect.range ψ)
  refine exists_stdPos_of_inducedToral (𝒟 := LayerSixE.inndiagAut .E6 F)
    (V := (rootDiagAutHom .E6 F).range) (p := 3) (r := 5) (e6Isogeny_surjective F)
    (ModelFacts.ChevAut.e6Isogeny_ker_le_center F)
    (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker F)))
    ?_ ?_ (fun E hE𝒟 hE h5 => exists_inner_conj_le_diag_e6 h3 hE𝒟 hE h5) hBs hBN
    (fun b hb => LayerSixE.exists_induces_E6 ψ hker (hBN hb) (hinn b hb))
    (fun b hb h1 => ExcNonsplit.mem_centralizer_of_induces_one
      (ModelFacts.ChevAut.e6Isogeny_ker_le_center F) hperf (hBN hb) h1) hc
  ·
    intro γ _ z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup F).1 hz
    rw [← MinData.Valid.xm_add, CharTwo.add_self_eq_zero, MinData.Valid.xm_zero]
  ·
    rintro _ ⟨a, rfl⟩ γ hγ
    obtain ⟨h, hh, hhz⟩ := RootDetectExc.hdiag_E6 F γ hγ a
    exact ⟨h, hh, fun z hz => Subtype.ext (hhz z hz)⟩

end StdPosExc

end CFSG.StandardType

end
