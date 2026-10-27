module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrLabelOfJDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrLabel
import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrFieldK0
import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrFieldRA
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Label

theorem GGSecFiveRouteCfg.permNbr_mark_of_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (hAutK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {t : LargeEvenLieTag} {e : ℕ} (ht : t = .A ∨ t = .twA)
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨t, n - 1, e⟩) p Bs K := by
  have hM := GGSecFiveRouteCfg.permNbr_permLabel hR hn eta hK𝒦 hAutK
  unfold GGInnerDiagOnLabel at hM ⊢
  obtain ⟨hKperf, labK, hΛK, hraw⟩ := hM
  have hhasK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hpermK : GGSecFiveBPermLabel n p labK := by
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    exact hP.1
  have hrank : labK.rank = n - 1 := by
    rcases hpermK with ⟨-, hr, -⟩ | ⟨-, hr, -⟩ <;> exact hr
  have hfield : labK.tag = t ∧ labK.n = e := by
    by_cases hpn : p ∣ n
    · exact GGSecFiveRouteCfg.permNbr_field_of_RA hR hn hK𝒦 hΛK hhasK hpermK hpn ht hΛJ hJ
    · exact GGSecFiveRouteCfg.permNbr_field_of_generic hR hn hK𝒦 hΛK hhasK hpermK hpn ht hΛJ hJ
  have hlab : labK = ⟨t, n - 1, e⟩ := by
    obtain ⟨tag, rank, fld⟩ := labK
    simp only at hrank hfield
    rw [hfield.1, hrank, hfield.2]
  refine ⟨hKperf, labK, hΛK, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hP⟩
  exact ⟨hs, hna, θ, hlab, hP.2⟩

theorem GGSecFiveRouteCfg.permNbr_label_of_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (hAutK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {t : LargeEvenLieTag} {e : ℕ} (ht : t = .A ∨ t = .twA)
    (hΛJ : LargeEvenInLambda2 ⟨t, n - 2, e⟩)
    (hJ : GGHasLabel ⟨t, n - 2, e⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGHasLabel ⟨t, n - 1, e⟩ (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨lab, -, hhas, -, -, -, -, -, hlab, -⟩ :=
    largeEvenMarking_exists_hasLabel
      (GGSecFiveRouteCfg.permNbr_mark_of_J hR hn eta hK𝒦 hAutK ht hΛJ hJ)
  rwa [hlab] at hhas

theorem ggSecFivePermNbrLabelOfJInput_holds : GGSecFivePermNbrLabelOfJInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR n hn eta K hK𝒦 hAutK t e ht hΛJ hJ
  exact GGSecFiveRouteCfg.permNbr_label_of_J hR hn eta hK𝒦 hAutK ht hΛJ hJ

end Label

end CFSG.StandardType

end
