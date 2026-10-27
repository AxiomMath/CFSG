module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrU6
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabelAuxFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qtwoDNbr_lieModel_of_su {H : Type} [Group H] [Finite H] {m f : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (e : H ⧸ Subgroup.center H ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ f))) :
    LieModel (H ⧸ Subgroup.center H) .PSU m 2 f := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hf, by omega, ?_⟩, K, inferInstance, inferInstance,
    hK, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (by omega)
  · exact ⟨show H ⧸ Subgroup.center H ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSU m (2 ^ f) K) from e⟩

section


theorem qtwoDNbr_esu (hC : GGSecFiveNSCornerInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) (hJX : J ≤ X) {m : ℕ} (hm : 7 ≤ m)
    (hcard : Nat.card ↥Bs = 3 ^ m)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 ^ 2)
    (hFix : QTwoDFixBound Bs X m)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1) 3 Bs X) :
    QTwoDL1Chart 3 B Bs X := by
  classical
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have h2 : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) ∨
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
        (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank ≠ 3 ∧ lab.rank ≠ 5))) 3 Bs X :=
    hmark.mono' fun lab ⟨hl, hn⟩ => by
      by_cases h3 : lab.rank = 3
      · exact Or.inl ⟨hl, hn, h3⟩
      · by_cases h5 : lab.rank = 5
        · exact Or.inr (Or.inl ⟨hl, hn, h5⟩)
        · exact Or.inr (Or.inr ⟨hl, hn, h3, h5⟩)
  rcases GGInnerDiagOnLabel.elim_or h2 with h3 | h56
  ·
    exfalso
    obtain ⟨K, hKf, hKfin, lab, m', θ, hK, -, hmrank, hSide, -, hperf, -, hBsN, -⟩ :=
      ggNSLieN3A_esuCore h3 (fun p lab hl => hl.1)
    obtain ⟨tag, rank, n⟩ := lab
    obtain ⟨-, hn, hr3⟩ := hSide
    change n = 1 at hn
    change rank = 3 at hr3
    change m' = rank + 1 at hmrank
    subst hn
    subst hr3
    have hm4 : m' = 4 := by omega
    subst hm4
    have hKd : LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 1 :=
      qtwoDNbr_lieModel_of_su hK (le_refl 4) le_rfl θ
    have hxB : x ∈ B := hconf.1.2.2.2.2.2.2.1.2.1
    have hxBs : x ∈ Bs := hconf.2.1.1 hxB
    have hx3 : x ^ 3 = 1 := hconf.2.1.2.1.2 x hxBs
    exact qTwoNbrLabel_four_false hnbr hxBs hx3 hperf hBsN
      (ggIsComponentOf_inf_centralizer_nbr hconf hnbr hJX) hKd
  · rcases GGInnerDiagOnLabel.elim_or h56 with h5 | h6
    · exact qtwoDNbr_u6 hC hcfg hnbr hm hcard hcent hFix h5
    · exact qtwoDNbr_unit hC hcfg hnbr hcard hFix h6

end

end CFSG.StandardType.QTwo

end
