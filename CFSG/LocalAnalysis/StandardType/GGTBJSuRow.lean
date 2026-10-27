module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowUFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggSuRow_recipe_adjoint
    {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hd : 4 ≤ d)
    (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ (r d' n' : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
        (_ : R ≃* LargeEvenProj (LargeEvenSUGroup (Fin d') K (2 ^ n'))),
        GGTorusLift p r R ∧ 4 ≤ d' ∧ 2 ≤ n' ∧ ¬ p ∣ d' ∧ p ∣ 2 ^ n' + 1 ∧
          Nat.card K = (2 ^ n') ^ 2 ∧
          ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    rintro h
    have h1 : d = 3 := congrArg Prod.fst h
    omega
  exact ⟨ggUnitaryTorusRank p d, d, n, K, inferInstance, inferInstance, MulEquiv.refl _,
    ggTorusLift_unitary hK (by omega) (by omega) hdq hp hpq, hd, hn, hpd, hpq, hK,
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK (by omega) (by omega) hdq hp hpq hpd φ
      hφ hφp⟩

theorem ggSuRow_labelAll_adjoint
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hq : GGLabQFour p lab) (h : GGTBRowR5U p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (r d n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
        (_ : R ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))),
        GGTorusLift p r R ∧ 4 ≤ d ∧ 2 ≤ n ∧ ¬ p ∣ d ∧ p ∣ 2 ^ n + 1 ∧
          Nat.card K = (2 ^ n) ^ 2 ∧
          ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  obtain ⟨htag, hpq⟩ := h
  unfold GGLabQFour at hq
  dsimp only at hq hpq htag
  rcases htag with ⟨ht, hl, hpd⟩ | ⟨ht, hl⟩
  · subst ht
    exact ggSuRow_recipe_adjoint hp hpq hq (by omega) hpd hQ
  · subst ht
    subst hl
    exact ggSuRow_recipe_adjoint hp hpq hq (by norm_num)
      (nbrC_not_dvd_four hp (TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 hpq)) hQ

theorem ggTBJTorusNoncomm_rowR5U :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR5U p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' hJl hcount
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour p lab ∧ GGTBRowR5U p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggSuRow_labelAll_adjoint hp hlab hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, d, n, K, _, _, e, hlift, hd, hn, hpd, hpq, hK,
    hIp⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv (I' := MulAut.congr e '' I) e
    (fun φ hφ => ⟨φ, hφ, rfl⟩) hTB
  have hIp' : ∀ φ ∈ MulAut.congr e '' I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
    rintro _ ⟨φ, hφ, rfl⟩ hφp
    obtain ⟨g, hg⟩ := hIp φ hφ ((MulAut.congr e).injective (by rw [map_pow, hφp, map_one]))
    exact ⟨e g, by
      rw [← hg]
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩
  exact ggTBJ_su_torusJNoncomm hK hn hd hp hp2 hpq hpd hIp' (e.toMonoidHom.comp (ggQuotHom θ)) _
    hTB' y hy hJ' hcount

theorem ggTBJNaWeylQFourOn_rowR5U :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5U p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm ggTBJTorusNoncomm_rowR5U

end CFSG.StandardType

end
