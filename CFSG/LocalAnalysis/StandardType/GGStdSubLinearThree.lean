module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
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
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggStdSubLinearThreeAux_label_arith {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {m : ℕ}
    (h1 : markTag lab = .PSL) (h2 : markRank lab = 3) (h3 : markDeg lab = m) :
    lab.tag = .A ∧ lab.rank = 2 ∧ lab.n = m := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t <;> simp_all [markTag, markRank, markDeg]
  case twD =>
    by_cases hl2 : l = 2
    · simp [hl2] at h2
    · by_cases hl3 : l = 3
      · simp [hl2, hl3] at h2
      · simp [hl2, hl3] at h2

private theorem ggStdSubLinearThreeAux_label
    {R_J : Type} [Group R_J] {lab_J : LargeEvenLabel} (hlab_J : LargeEvenInLambda2 lab_J)
    {m : ℕ} (hm : 2 ≤ m)
    (hMarked : MarkedModel lab_J R_J) (hPSL : CFSG.Blueprint.LieModel R_J .PSL 3 2 m) :
    lab_J.tag = .A ∧ lab_J.rank = 2 ∧ lab_J.n = m := by
  by_cases hc : markChar lab_J = 2
  · have hLie := NbrInnerMore.lieModel_of_markedModel_two hc hMarked
    obtain ⟨hT, hR, hD⟩ :=
      CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num : 3 ≤ 3) hPSL hLie
    exact ggStdSubLinearThreeAux_label_arith hlab_J hT hR hD
  · exact absurd hMarked
      (NbrInnerMore.not_markedModel_of_char_ne_two hPSL (by simp)
        (by rintro ⟨-, -, h⟩; omega) (by simp) hc)

theorem ggConfig_exists_abelianPreimage_psl_three {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hID : GGInnerDiagOn Bs L) (hQ2 : GGBstarAbelianPreimageJLinInput)
    (hIDJ : GGInnerDiagOn Bs J) {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 2 ≤ m)
    (hE : Nat.card E = 2 ^ m)
    (σ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E')
      (θJ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E'))
      (At : Subgroup (GL (Fin 3) E')), IsMulCommutative At ∧
        ∀ b ∈ Bs, ∃ g ∈ At, ∀ j : ↥J, ∃ j' : ↥J, (j' : G) = b * (j : G) * b⁻¹ ∧
          θJ (QuotientGroup.mk j') =
            TableB.linConjAut (Fin 3) E' g (θJ (QuotientGroup.mk j)) := by
  obtain ⟨hJperf, lab_J, hlab_J, hraw_J⟩ := hIDJ
  have hraw_marked := largeEvenRawDatum_markedModel hlab_J
    (Q := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : (↥J ⧸ Subgroup.center ↥J) ≃* R,
        Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (fun R _ I F hQ => hQ.2.1) hraw_J
  obtain ⟨R', _, I', F', hQ', hMM'⟩ := largeEvenRawDatum_exists hraw_marked
  obtain ⟨hs', hna', θ', hNJ', hhall'⟩ := hQ'
  have hMarkedCenter : MarkedModel lab_J (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ'.symm hMM'
  have hEadm : CFSG.Open.StatedLieAdmissible .PSL 3 2 m :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩
  have hSCM : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) .PSL 3 2 m :=
    statedClassicalModel_linear 3 m hE hEadm
  have hPSL0 : CFSG.Blueprint.LieModel
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) E)) .PSL 3 2 m :=
    Or.inl ⟨by decide, hSCM⟩
  have hPSLJ : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 m :=
    lieModel_of_mulEquiv' σ.symm hPSL0
  obtain ⟨hAtag, hArank, hAn⟩ :=
    ggStdSubLinearThreeAux_label hlab_J hm hMarkedCenter hPSLJ
  have hlab_eq : lab_J = ⟨.A, 2, m⟩ := by
    obtain ⟨t, l, n⟩ := lab_J
    dsimp only at hAtag hArank hAn
    subst hAtag; subst hArank; subst hAn; rfl
  subst hlab_eq
  dsimp only [LargeEvenRawDatum] at hraw_J
  obtain ⟨K0, hK0field, hK0fin, hK0card, hQK⟩ := hraw_J
  obtain ⟨hs_J, hna_J, θ_J, hNJ, hhall_J⟩ := hQK
  let At : Subgroup (GL (Fin 3) K0) :=
    (((ggBsAut hNJ).range).map (kgInducedAut θ_J)).comap (TableB.linConjAut (Fin 3) K0)
  have hAt_comm : IsMulCommutative At :=
    hQ2 G p B Bs x L D J hcfg hID hNJ 3 K0 θ_J
  refine ⟨K0, hK0field, hK0fin, θ_J, At, hAt_comm, ?_⟩
  intro b hb
  have hmem : ggLAut J θ_J ⟨b, hNJ hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K0)) Set.univ :=
    ggLAut_mem_of_induces J θ_J hNJ hhall_J hb
  obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut (ι := Fin 3) (K := K0) hmem
  refine ⟨A, ?_, ?_⟩
  · rw [Subgroup.mem_comap]
    rw [← hA]
    exact Subgroup.mem_map.mpr
      ⟨ggBsAut hNJ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  · intro j
    refine ⟨ggBsAut hNJ ⟨b, hb⟩ j, normalizerMonoidHom_coe J ⟨b, hNJ hb⟩ j, ?_⟩
    rw [← hA]
    exact (ggLAut_apply J θ_J ⟨b, hNJ hb⟩ j).symm

end CFSG.StandardType
