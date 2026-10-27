module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
public import Certificates.Certificate709540
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcCoord
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcWit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveCR3OfPump
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylReflTriple
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggRealized_conj_of_mem_ggAInf {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hp : p.Prime) {r g : MulAut ↥Bs}
    (hr : GGRealized p Bs r) (hg : g ∈ ggAInf p B Bs x L D J) :
    GGRealized p Bs (g * r * g⁻¹) := by
  obtain ⟨n, -, hnN, hn⟩ := ggRM_ainf_le_induced hg
  have hgn : ggConjAut Bs hnN = g :=
    MulEquiv.ext fun y => Subtype.ext (by rw [ggConjAut_apply, hn y])
  have h := GGRealized.conj hp hr hnN
  rwa [hgn] at h

private theorem weyl_not_G₂_of_orderOf_le_four {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs))
    (hD : ∀ s ∈ ggAInf p B Bs x L D J, ∀ t ∈ ggAInf p B Bs x L D J, GGIsReflection p s →
      GGIsReflection p t → orderOf (s * t) ≤ 4) :
    (GGWeylReflectionGroup p (ggAutomizer L Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer L Bs)) ∧
    ∀ (d : G) (K : Subgroup G), GGNbr p B x D J d K →
      GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
        ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) := by
  have hLA : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J := le_sup_left
  refine ⟨⟨GGWeylOfType.weylReflectionGroup
    (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 3 (by norm_num)) hA3,
    not_ggWeylOfType_G₂_of_le hLA hD⟩, fun d K hn => ⟨?_,
    not_ggWeylOfType_G₂_of_le (ggAutomizer_le_ggAInf_of_nbr hn) hD⟩⟩
  exact GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.1
    (ggSecFiveRouteCfg'_of_routeCfg hR).2.1 hn


theorem ggSecFiveBFourPermExcInput_of_inputs
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hX : GGResXDichotomyInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGSecFiveBFourPermExcInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hPres hM hx hnot eta hLA k hk h4 hmod hone hD
  exfalso
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hp : p.Prime := (GGConfig.tableB_facts hcfg).1
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have := Nat.le_of_dvd (by have := hp.two_le; omega) h4
    omega
  have hp2 : p ≠ 2 := by omega
  have hA3 := ggWeylOfType_A_of_map_eq_aPermutationFull (m := 3) hp2 eta hLA
  obtain ⟨f, hf1, hlab⟩ :=
    exists_label_A3_of_weylOfType hcfg hR.1.2.2.2.1 (natCard_eq_pow_of_mulEquiv eta) hA3
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    rcases hlab with ⟨hd, -⟩ | ⟨hd, -⟩ <;>
    · have := Nat.le_of_dvd (by norm_num) hd
      norm_num at this
      omega
  obtain ⟨r₁, hr₁J, r₂, hr₂J, hr₁, hr₂, hord⟩ := exists_A2_pair_of_label_A3 hLB hR hf2 hlab
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hLA' : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J := le_sup_left
  have hr₁L := ggAutomizer_mono Bs hJL hr₁J
  have hkM : k.needsModel := by rcases hk with rfl | rfl <;> trivial
  obtain ⟨g, hgA, hnc, hndvd⟩ := exists_conj_not_dvd_48_of_modelIso hp2 eta hkM hone hmod
    (hLA' hr₁L) (hLA' (ggAutomizer_mono Bs hJL hr₂J)) hr₁ hr₂ hord
  have hreal : GGRealized p Bs r₁ := by
    rcases hlab with ⟨-, h⟩ | ⟨-, h⟩
    exacts [ggRealized_of_label_A3 hP hraw hiso hcfg hR.1.2.2.1 hR.1.2.2.2.1 hp5 (Or.inl rfl) hf2
        h hr₁L hr₁,
      ggRealized_of_label_A3 hP hraw hiso hcfg hR.1.2.2.1 hR.1.2.2.2.1 hp5 (Or.inr rfl) hf2 h
        hr₁L hr₁]
  obtain ⟨hWL, hWK⟩ := weyl_not_G₂_of_orderOf_le_four hX TCJ.ggTCJKnown_holds
    ggLabelRigidInput_holds hTPn hA8 hraw hiso hR hA3 hD
  have h48 := card_closure_conj_dvd_48_of_weyl hLB hP ggWeylReflTripleInput_holds hcfg
    hR.1.2.2.1 hR.1.2.2.2.1 hWL hWK hr₁J hr₂J hr₁ hr₂ hord (one_mem_ggInduced ⊤ Bs)
    (hr₁.conj' g) (ggRealized_conj_of_mem_ggAInf hp hreal hgA)
    (by simpa using fun h₁ h₂ => hnc ⟨h₁, h₂⟩)
  simp only [one_mul, inv_one, mul_one] at h48
  exact hndvd h48

end CFSG.StandardType

end
