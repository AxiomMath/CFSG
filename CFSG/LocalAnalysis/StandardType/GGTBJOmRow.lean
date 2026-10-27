module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmTorusJ
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowOFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTBRowOFrame
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB OrthExc

theorem ggO1Row_recipe_adjoint
    {m n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1 ∨ (Odd m ∧ p ∣ 2 ^ n + 1)) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ (r m' n' : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K)
        (_ : R ≃* OrthRest.RMinus K m' b c),
        GGTorusLift p r R ∧ 3 ≤ m' ∧ 1 ≤ n' ∧ Nat.card K = 2 ^ n' ∧
          (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ (p ∣ 2 ^ n' - 1 ∨ (Odd m' ∧ p ∣ 2 ^ n' + 1)) ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have hCP : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0, m, n, K, inferInstance,
    inferInstance, hCP, b, c, MulEquiv.refl _,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc), hm, hn, hK, hbc, hpn,
    subset_rfl⟩

theorem largeEvenRawDatum_twD_exact
    {n f : ℕ} (hn : 4 ≤ n) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRawDatum (⟨.twD, n, f⟩ : LargeEvenLabel) Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K),
      Nat.card K = 2 ^ f ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Q (OrthRest.RMinus K (n - 1) b c)
        (LargeEvenInnSet (OrthRest.RMinus K (n - 1) b c))
        (LargeEvenPhiQ (n - 1) b c (LargeEvenProjMk _)) := by
  dsimp only [LargeEvenRawDatum] at hQ
  split_ifs at hQ
  · exfalso
    omega
  · exfalso
    omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, b, c, hK, hbc, hQ⟩

theorem ggO1Row_labelAll_adjoint
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hq : 1 ≤ lab.n) (h : GGTBRowR5O1 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (r m n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K)
        (_ : R ≃* OrthRest.RMinus K m b c),
        GGTorusLift p r R ∧ 3 ≤ m ∧ 1 ≤ n ∧ Nat.card K = 2 ^ n ∧
          (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ (p ∣ 2 ^ n - 1 ∨ (Odd m ∧ p ∣ 2 ^ n + 1)) ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, hpn⟩ := h
  subst htag
  dsimp only at h4 hpn hlab hq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · refine ggO1Row_recipe_adjoint hp hq ?_ (by omega) hQ
    rcases hpn with h | ⟨he, h⟩
    · exact Or.inl h
    · obtain ⟨j, hj⟩ := he
      exact Or.inr ⟨⟨j - 1, by omega⟩, h⟩

theorem ggTBJTorusNoncomm_rowR5O1 :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR5O1 p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' hJl hcount
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour p lab ∧ GGTBRowR5O1 p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggO1Row_labelAll_adjoint hp hlab hlab.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, K, _, _, _, b, c, e, hlift, hm, hn, hK,
    hbc, hpq, hIc⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hIc' : ∀ φ ∈ I, MulAut.congr e φ ∈ Set.range (MulAut.conj :
      OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)) := by
    intro φ hφ
    obtain ⟨g, hg⟩ := hIc hφ
    exact ⟨e g, by
      rw [← hg]
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c))) e hIc' hTB
  exact ggTBJ_om_torusJNoncomm hp hp2 hbc hm (by rw [hK]; exact hpq)
    (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB' y hy hJ' hcount

theorem ggTBJNaWeylQFourOn_rowR5O1 :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5O1 p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm ggTBJTorusNoncomm_rowR5O1

end CFSG.StandardType

end
