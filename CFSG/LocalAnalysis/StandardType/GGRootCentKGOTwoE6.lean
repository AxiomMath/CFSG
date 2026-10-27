module

public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Chevalley.RootOps.Family
public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExc
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoE6Step
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExc

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.SeitzReduction RootCentExc

namespace KGE6

section Base

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem oTwoFaithful_pinnedElt_E6 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    KGExc.OTwoFaithful (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) := by
  intro G _ ψ hψ hC
  exact pCoreOf_le_range_of_highRoot_E6 hf hK hψ hC

theorem oTwoFaithful_xPar_highRoot_E6 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E6) {i₀ : Fin (Tag.rank .E6)}
    (hd : HighRootData .E6 (highRoot .E6) i₀) :
    KGExc.OTwoFaithful (xPar F (highRoot .E6) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F (highRoot .E6) (1 : K) = EPilot.pinnedElt .E6 (highRoot .E6) 1 :=
    Subtype.ext (coe_xPar_eq_pinnedX h2 F hd.maxHeight.1 1)
  rw [he]
  exact oTwoFaithful_pinnedElt_E6 hf hK

theorem oTwoFaithful_e6Isogeny {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ (e6Datum K).roots)
    {z : e6Data_valid.minGroup K} (hz : z ∈ (e6Datum K).rootGroup γ)
    (hz1 : e6Isogeny K z ≠ 1) : KGExc.OTwoFaithful (e6Isogeny K z) := by
  have hγ' : IsRoot .E6 γ :=
    e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
  rw [e6Isogeny_xm K hγ'] at hz1 ⊢
  exact RootCentQLTyped.of_mem_rootGroup (P := KGExc.OTwoFaithful)
    (fun α z h => h.map α) (rootOperatorFamily .E6)
    (fun j => RootCentQLTyped.single_E6 (P := KGExc.OTwoFaithful) (fun α z h => h.map α)
      (rootOperatorFamily .E6)
      (oTwoFaithful_xPar_highRoot_E6 hf hK _ highRootData_E6) j)
    hγ' (xPar_mem hγ' _) hz1

theorem exists_factor_e6Isogeny {f : ℕ} {G : Type} [Group G]
    {ψ : e6Data_valid.minGroup (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ ψbar : adjointGroup .E6 (GaloisField 2 f) →* G,
      Function.Injective ψbar ∧ ψbar.range = ψ.range ∧
        ∀ x, ψbar (e6Isogeny (GaloisField 2 f) x) = ψ x := by
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  have hψker : ψ.ker = Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)) :=
    AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψker.symm
  let eC : adjointGroup .E6 (GaloisField 2 f) ≃*
      e6Data_valid.minGroup (GaloisField 2 f) ⧸ ψ.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective (e6Isogeny (GaloisField 2 f))
      (e6Isogeny_surjective _)).symm.trans (QuotientGroup.quotientMulEquivOfEq hπker)
  let ψbar : adjointGroup .E6 (GaloisField 2 f) →* G :=
    (QuotientGroup.kerLift ψ).comp eC.toMonoidHom
  have hcomp : ∀ x, ψbar (e6Isogeny (GaloisField 2 f) x) = ψ x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective (e6Isogeny (GaloisField 2 f))
        (e6Isogeny_surjective _)).symm (e6Isogeny (GaloisField 2 f) x) =
        (QuotientGroup.mk x :
          e6Data_valid.minGroup (GaloisField 2 f) ⧸ (e6Isogeny (GaloisField 2 f)).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψbar, eC, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
      Function.comp_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]
  refine ⟨ψbar, ?_, ?_, hcomp⟩
  · exact (QuotientGroup.kerLift_injective ψ).comp eC.injective
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) x
      rw [hcomp]
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e6Isogeny (GaloisField 2 f) a, hcomp a⟩

end Base

end KGE6

section Tag


theorem ggRootCentOTwoTag_E6 : GGRootCentOTwoTag .E6 := by
  intro G _ _ n f ψ hadm _ hker _ _ hC _ r hr _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψker : ψ.ker = Subgroup.center (ggU .E6 n f).K := AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψker.symm
  obtain ⟨ψbar, hψbar_inj, hψbar_range, hcomp⟩ := KGE6.exists_factor_e6Isogeny (f := f) hker hC
  have hCbar : Subgroup.centralizer (ψbar.range : Set G) = ⊥ := by
    rw [hψbar_range]
    exact hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz : KGExc.OTwoFaithful (e6Isogeny (GaloisField 2 f) z) :=
    KGE6.oTwoFaithful_e6Isogeny hf hK hγ hz hz1
  have hcz' : KGExc.OTwoFaithful (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹)) := by
    let u' : e6Data_valid.minGroup (GaloisField 2 f) := u
    let z' : e6Data_valid.minGroup (GaloisField 2 f) := z
    change KGExc.OTwoFaithful (e6Isogeny (GaloisField 2 f) (u' * z' * u'⁻¹))
    have e : e6Isogeny (GaloisField 2 f) (u' * z' * u'⁻¹) =
        e6Isogeny (GaloisField 2 f) u' * e6Isogeny (GaloisField 2 f) z' *
          (e6Isogeny (GaloisField 2 f) u')⁻¹ := by
      simp only [map_mul, map_inv]
    have h := hcz.map (MulAut.conj (e6Isogeny (GaloisField 2 f) u'))
    change KGExc.OTwoFaithful (e6Isogeny (GaloisField 2 f) u' *
      e6Isogeny (GaloisField 2 f) z' * (e6Isogeny (GaloisField 2 f) u')⁻¹) at h
    rwa [← e] at h
  have hr_eq : ψ (u * z * u⁻¹) = ψbar (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹)) := by
    let u' : e6Data_valid.minGroup (GaloisField 2 f) := u
    let z' : e6Data_valid.minGroup (GaloisField 2 f) := z
    exact (hcomp (u' * z' * u'⁻¹)).symm
  rw [hr_eq]
  have hconcl := hcz' G ψbar hψbar_inj hCbar
  rwa [hψbar_range] at hconcl

end Tag

end CFSG.StandardType
