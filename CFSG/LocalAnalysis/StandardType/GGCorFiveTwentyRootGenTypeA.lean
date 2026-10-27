module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLabels

public section

namespace CFSG.StandardType

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly

section Assembly

variable {d p : ℕ} {K : Type} [Field K] [Finite K]

theorem ggTorusRootGen_psl_coprime [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K)
    (h4 : 4 ≤ Nat.card K) :
    GGTorusRootGen p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ _ _ ρ
  obtain ⟨φ, hφs, hφker, hM⟩ :=
    exists_isDiagTorusModel hp hpK hd hpd hsec hψ hker hperf hA hAI hr
  obtain ⟨i₀, j₀, hρ⟩ : ∃ i₀ j₀ : Fin d, ∀ i j, i ≠ j →
      ggConjAut A (conj_permSL_mem_normalizer hM i j) = ρ →
        ({i, j} : Finset (Fin d)) = {i₀, j₀} := by
    by_cases h : ∃ i j, i ≠ j ∧ ggConjAut A (conj_permSL_mem_normalizer hM i j) = ρ
    · obtain ⟨i₀, j₀, hij₀, h₀⟩ := h
      exact ⟨i₀, j₀, fun i j hij hρ' => pair_eq_of_ggConjAut_eq hp hp2 hpK hpd hφker hM
        hij hij₀ (hρ'.trans h₀.symm)⟩
    · push Not at h
      exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, fun i j hij hρ' => absurd hρ' (h i j hij)⟩
  apply le_antisymm le_top
  rw [← Subgroup.map_top_of_surjective φ hφs, ← iSup_coordBlockSL_pairs (K := K) (by omega) i₀ j₀]
  simp only [Subgroup.map_iSup]
  refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
  have hcomp := isComponentOf_coordBlockSL_pair (φ := φ) hp hp2 hpK h4 hd hφker hij.1
  rw [← ggHypCent_permSL_eq hpd hφs hφker hM i j] at hcomp
  exact le_iSup_of_le (φ (permSL (Equiv.swap i j))) (le_iSup_of_le
    (conj_permSL_mem_normalizer hM i j) (le_iSup_of_le ((coordBlockSL K {i, j}).map φ)
      (le_iSup_of_le ⟨ggTorusWeylElt_permSL hM i j,
        isReflection_conj_permSL hp hp2 hpK hpd hφker hM hij.1,
        fun h => hij.2 (hρ i j hij.1 h), Subgroup.mem_map_of_mem φ permSL_mem_coordBlockSL,
        hcomp, dvd_card_coordBlockSL_pair hp hpK (by omega) hφker hij.1⟩ le_rfl)))

theorem ggTorusRootGen_small (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusRootGen p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

end Assembly

section Recipe

theorem recipeLinear_rootGen {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGen p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggTorusRootGen_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusRootGen_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggTorusRootGen_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusRootGen_psl_coprime hp hp2 hpK hd4 hpd' hsec h4)⟩

theorem largeEvenLabelAll_rootGen_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootGen p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_rootGen hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_rootGen hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_rootGen hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end Recipe

end TypeA

theorem ggRootGenKGTypeA_holds : GGRootGenKGOn GGTypeALabel :=
  fun _ _ hp _ hlab h => TypeA.largeEvenLabelAll_rootGen_typeA hp hlab h

section Config

open CFSG.Assembly TableB

theorem GGInnerDiagOnLabel.typeA_or {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel GGLabPhiOneTwo p Bs X) :
    GGInnerDiagOnLabel (fun p lab => GGLabPhiOneTwo p lab ∧ GGTypeALabel p lab) p Bs X ∨
      GGInnerDiagOnLabel GGRootGenOpenLabel p Bs X := by
  have h' : GGInnerDiagOnLabel (fun p lab => (GGLabPhiOneTwo p lab ∧ GGTypeALabel p lab) ∨
      GGRootGenOpenLabel p lab) p Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hs, hP⟩ =>
      ⟨(em (GGTypeALabel p _)).elim (fun h => Or.inl ⟨hs, h⟩) (fun h => Or.inr ⟨hs, h⟩), hP⟩) h
  exact h'.elim_or

theorem ggRootGenLInput_of_typeA (hKG : GGRootGenKGOn GGTypeALabel)
    (hopen : GGRootGenLInputOn GGRootGenOpenLabel) : GGRootGenLInput := by
  intro G _ _ p B Bs x L D J hHyp hq hNb hW
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1.2.1
  rcases GGInnerDiagOnLabel.typeA_or hW.2.2.1 with hA | hO
  swap
  · exact hopen G p B Bs x L D J hHyp hq hNb hW hO
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGLabPhiOneTwo p lab ∧ GGTypeALabel p lab)
    (fun lab hlab hs => hKG p lab hp (ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1) hlab hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hA
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  have hp2 : p ≠ 2 := ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  exact ggRootCompGenAvoiding_of_marking hp hp2 hBs hSC hxBs hLx hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr h3' hW.2.1 hT

theorem ggRootGenNbrInput_of_typeA (hKG : GGRootGenKGOn GGTypeALabel)
    (hopen : GGRootGenNbrInputOn GGRootGenOpenLabel) : GGRootGenNbrInput := by
  intro G _ _ p B Bs x L D J hHyp hq hNb hW y K hnb
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  rcases GGInnerDiagOnLabel.typeA_or (hW.2.2.2 y K hnb).2 with hA | hO
  swap
  · exact hopen G p B Bs x L D J hHyp hq hNb hW y K hnb hO
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGLabPhiOneTwo p lab ∧ GGTypeALabel p lab)
    (fun lab hlab hs => hKG p lab hp (ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1) hlab hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hA
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  have hp2 : p ≠ 2 := ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1
  exact ggRootCompGenAvoiding_of_marking hp hp2 hBs hSC hyBs hKy.2.1 hK θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN h3 hb)
    (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK θ hBsN hlift)
    (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) (hW.2.2.2 y K hnb).1 hT

theorem ggRootGenLInput_of_openOn (hopen : GGRootGenLInputOn GGRootGenOpenLabel) :
    GGRootGenLInput :=
  ggRootGenLInput_of_typeA ggRootGenKGTypeA_holds hopen

theorem ggRootGenNbrInput_of_openOn (hopen : GGRootGenNbrInputOn GGRootGenOpenLabel) :
    GGRootGenNbrInput :=
  ggRootGenNbrInput_of_typeA ggRootGenKGTypeA_holds hopen

theorem ggRootGenLInputOn_open_of_full (h : GGRootGenLInput) :
    GGRootGenLInputOn GGRootGenOpenLabel :=
  fun G _ _ p B Bs x L D J hHyp hq hNb hW _ => h G p B Bs x L D J hHyp hq hNb hW

theorem ggRootGenNbrInputOn_open_of_full (h : GGRootGenNbrInput) :
    GGRootGenNbrInputOn GGRootGenOpenLabel :=
  fun G _ _ p B Bs x L D J hHyp hq hNb hW y K hnb _ => h G p B Bs x L D J hHyp hq hNb hW y K hnb

end Config

end CFSG.StandardType

end
