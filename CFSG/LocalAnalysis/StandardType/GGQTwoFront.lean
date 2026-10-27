module

public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQ
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontM
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qTwoFront_p_eq_three
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hG : QTwoJoinGuard p B Bs x L D J 𝒦) : p = 3 := by
  obtain ⟨hcfg, -, -, ι, M, e, hpres, -, r, hr, hrc, h6⟩ := hG
  exact ggQTwo_p_eq_three hcfg M e hpres hr hrc h6

theorem qTwoFront_esuLabel
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hG : QTwoJoinGuard p B Bs x L D J 𝒦) (hEn : GGSecFiveNSEnnolaInput) :
    GGInnerDiagOnLabel ggRowP_ESU p Bs L := by
  obtain ⟨hcfg, -, hL, ι, M, e, hpres, hA, -⟩ := hG
  exact ggX_esu_of_nonSplit hEn hcfg hL hpres hA (Or.inl rfl) hL

theorem qTwoFront_lieModel {H : Type} [Group H] [Finite H] {m f : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (e : H ⧸ Subgroup.center H ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ f))) :
    LieModel (H ⧸ Subgroup.center H) .PSU m 2 f := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hf, by omega, ?_⟩, K, inferInstance, inferInstance,
    hK, ?_⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (by omega)
  · exact ⟨show H ⧸ Subgroup.center H ≃* StatedProj (StatedSU m (2 ^ f) K) from e⟩

theorem qTwoFront_esuTied {p : ℕ} {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel ggRowP_ESU p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f m : ℕ), Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ m ∧
      p ∣ 2 ^ f + 1 ∧ commutator X = ⊤ ∧
      Nonempty (↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ f))) ∧
      GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.rank + 1 = m ∧ lab.n = f) p Bs X := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hrow, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨K, hf, hfin, m, hK, h4m, hmrank, hQ'⟩ := ggNSLieN3A_esuRecipe hrow hraw
  obtain ⟨-, -, θ', -, -, -⟩ := hQ'
  have htie : GGInnerDiagOnLabel
      (fun p lab' => ggRowP_ESU p lab' ∧ lab'.rank + 1 = m ∧ lab'.n = lab.n) p Bs X := by
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro _ _ _ _ ⟨hs0, hna0, θ0, hP0, hBsN0, hbs0⟩
    exact ⟨hs0, hna0, θ0, ⟨hP0, hmrank.symm, rfl⟩, hBsN0, hbs0⟩
  exact ⟨K, hf, hfin, lab.n, m, hK, h4m, hrow.2, hperf, ⟨θ'⟩, htie⟩

theorem qTwo_front
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hG : QTwoJoinGuard p B Bs x L D J 𝒦)
    (hEn : GGSecFiveNSEnnolaInput) :
    p = 3 ∧ ∃ m : ℕ, 5 ≤ m ∧ LieModel (L ⧸ Subgroup.center L) .PSU m 2 1 := by
  have hp : p = 3 := qTwoFront_p_eq_three hG
  have hlabel : GGInnerDiagOnLabel ggRowP_ESU p Bs L := qTwoFront_esuLabel hG hEn
  obtain ⟨K, hfld, hfin, f, m, hK, hm4, hdvd, hperf, he, hlabelT⟩ := qTwoFront_esuTied hlabel
  obtain ⟨e⟩ := he
  letI := hfld
  letI := hfin
  have hf1 : f = 1 := qTwoFront_q_eq_one hG hlabelT hK hm4 hperf hdvd e
  have hm5 : 5 ≤ m := qTwoFront_m_ge_five hG hK hm4 hf1 hperf e
  subst hf1
  exact ⟨hp, m, hm5, qTwoFront_lieModel hK hm4 (le_refl 1) e⟩

end CFSG.StandardType.QTwo

end
