module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTorusRootGenAvoidKG (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      GGTorusRootGenAvoid p A

theorem ggTorusRootGenAvoidKG_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusRootGenAvoidKG p r R' I') :
    GGTorusRootGenAvoidKG p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa]⟩

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly

section Assembly

variable {d p : ℕ} {K : Type} [Field K] [Finite K]

private theorem avoidKG_psl_coprime [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K)
    (h4 : 4 ≤ Nat.card K) :
    GGTorusRootGenAvoidKG p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ _ ρ
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

private theorem avoidKG_small (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusRootGenAvoidKG p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
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

private theorem avoidKG_recipeLinear_rootGen {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
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
      ggTorusRootGenAvoidKG_of_mulEquiv (recipeEquiv d K) hI
        (avoidKG_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggTorusRootGenAvoidKG_of_mulEquiv (recipeEquiv d K) hI
        (avoidKG_psl_coprime hp hp2 hpK hd4 hpd' hsec h4)⟩

private theorem avoidKG_largeEvenLabelAll_rootGen_typeA {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact avoidKG_recipeLinear_rootGen hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine avoidKG_recipeLinear_rootGen hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine avoidKG_recipeLinear_rootGen hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end Recipe

end TypeA

@[expose] def GGRootGenKGAvoidOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I

theorem ggRootGenKGAvoidTypeA_holds : GGRootGenKGAvoidOn GGTypeALabel := by
  exact fun _ _ hp _ hlab h => TypeA.avoidKG_largeEvenLabelAll_rootGen_typeA hp hlab h

theorem ggRootCompGenAvoiding_of_marking_avoidKG {G : Type} [Group G] [Finite G] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {z : G}
    (hzBs : z ∈ Bs) (hXz : IsSubnormal X (Subgroup.centralizer ({z} : Set G)))
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range)
    (hT : GGTorusRootGenAvoidKG p r R I) : GGRootCompGenAvoiding p Bs X := by
  set γ := ggGamma X hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, hBsI b b.2, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  exact ggRootCompGenAvoiding_of_rootGenAvoid hp hp2 hBs hSC hBsN hzBs hXz
    (hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX γ.range hA hAI hr
      h3 (ggTorusSelfCent_ggGamma hBsN hSC))

theorem ggRootCompGenAvoiding_L_of_avoidOn {S : ℕ → LargeEvenLabel → Prop}
    (hKG : GGRootGenKGAvoidOn S) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel S p Bs L) : GGRootCompGenAvoiding p Bs L := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hLc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := S p)
    (fun lab hlab hs => hKG p lab hp hp2 hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hLc θ hBsN hlift
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hxBs hLx hLc θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr h3' hT

theorem ggRootCompGenAvoiding_nbr_of_avoidOn {S : ℕ → LargeEvenLabel → Prop}
    (hKG : GGRootGenKGAvoidOn S) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : GGInnerDiagOnLabel S p Bs K) :
    GGRootCompGenAvoiding p Bs K := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hKc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := S p)
    (fun lab hlab hs => hKG p lab hp hp2 hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hyBs hKy.2.1 hKc θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN h3 hb)
    (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hKc θ hBsN hlift)
    (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

end CFSG.StandardType

end
