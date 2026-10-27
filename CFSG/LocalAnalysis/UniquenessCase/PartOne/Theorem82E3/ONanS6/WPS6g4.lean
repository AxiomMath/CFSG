module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.SolvableTransport
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGen
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXMovingPlaneKernel
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXPlaneComponentOrbitRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits
public import CFSG.RankThree.GroupTheory.CentralLineComponentAction
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL11
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL8b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6f
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6g1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6g2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6g3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem false_of_A_normalizes_orbit'
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J))
    (hAnorm : ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      A ≤ Subgroup.normalizer (K : Set G)) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup G := perfectCoreL c a
  letI : MulAction ↥I (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp I.subtype)
  have hsmul : ∀ (b : ↥I) (M : Subgroup G), b • M = M.map (MulAut.conj (b : G)).toMonoidHom :=
    fun b M => by
      change (MulAut.conj (b : G)) • M = _
      rw [Subgroup.pointwise_smul_def]
      rfl
  let Ω : Set (Subgroup G) := MulAction.orbit ↥I J
  have hΩeq : Ω = orbitConjugates I J := by
    ext M
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(b : G)⁻¹, inv_mem b.2, by rw [hsmul, CFSG.conjugate, inv_inv]⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b⁻¹, inv_mem hb⟩, by rw [hsmul, CFSG.conjugate]⟩
  have hfin' : (orbitConjugates I J).Finite := by
    have hrange : orbitConjugates I J =
        Set.range (fun b : ↥I => CFSG.conjugate J (b : G)) := by
      ext M
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, b.2, rfl⟩
    rw [hrange]
    exact Set.finite_range _
  have hfin : Ω.Finite := by rw [hΩeq]; exact hfin'
  haveI : Fintype Ω := hfin.fintype
  have hΩn : Fintype.card Ω = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hΩeq]
    exact h6
  let e : Ω ≃ Fin 6 := Fintype.equivFinOfCardEq hΩn
  let ρ : ↥I →* Equiv.Perm Ω := MulAction.toPermHom ↥I Ω
  let ρ' : ↥I →* Equiv.Perm (Fin 6) := (Equiv.permCongrHom e).toMonoidHom.comp ρ
  let H : Subgroup (Equiv.Perm (Fin 6)) := ρ'.range
  haveI : Group.IsPerfect ↥I := perfectCoreL_isPerfect c a
  have hHperf : Group.IsPerfect H := Group.IsPerfect.range ρ'
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hρ' : ρ' = 1 := MonoidHom.range_eq_bot_iff.mp hbot
    have hfix : ∀ (g : ↥I) (x : Ω), g • x = x := by
      intro g x
      have hg : (Equiv.permCongrHom e) (ρ g) = 1 := by
        simpa [ρ'] using DFunLike.congr_fun hρ' g
      have h2 : (Equiv.permCongrHom e) (ρ g) (e x) = e x := by
        rw [hg]
        rfl
      have h1 : e (ρ g x) = e x := by
        simpa [Equiv.permCongr_apply] using h2
      have hx : ρ g x = x := e.injective h1
      simpa [ρ, MulAction.toPermHom_apply, Equiv.Perm.smul_def, MulAction.toPerm_apply] using hx
    have hsingle : Ω = {J} := by
      ext K
      constructor
      · intro hK
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hK
        have hJfix : g • J = J := by
          have h := congrArg Subtype.val (hfix g ⟨J, MulAction.mem_orbit_self J⟩)
          rwa [MulAction.orbit.coe_smul] at h
        rw [← hg, hJfix]
        rfl
      · intro hK
        rw [Set.mem_singleton_iff] at hK
        rw [hK]
        exact MulAction.mem_orbit_self J
    have hcard1 : Fintype.card Ω = 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsingle]
      simp
    omega
  have hHcard := card_perm_six_perfect hHperf hHne
  have hM'2 : IsPGroup 2 ((CFSG.pCore 2 ↥I).map ρ') :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).map ρ'
  have hM'le : (CFSG.pCore 2 ↥I).map ρ' ≤ H := Subgroup.map_le_range ρ' _
  have hM'norm : ∀ h ∈ H, ∀ m ∈ (CFSG.pCore 2 ↥I).map ρ',
      h * m * h⁻¹ ∈ (CFSG.pCore 2 ↥I).map ρ' := by
    intro h hh m hm
    obtain ⟨g, rfl⟩ := hh
    obtain ⟨n, hn, rfl⟩ := hm
    have hconj : g * n * g⁻¹ ∈ CFSG.pCore 2 ↥I :=
      (CFSG.pCore_normal (p := 2) (G := ↥I)).conj_mem n hn g
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem ρ' hconj
  have hM'bot : (CFSG.pCore 2 ↥I).map ρ' = ⊥ :=
    perm_six_eq_bot_of_normal_isPGroup_two hM'le hHperf hM'norm hM'2
  have hO2ker : CFSG.pCore 2 ↥I ≤ ρ'.ker :=
    (Subgroup.map_eq_bot_iff (CFSG.pCore 2 ↥I)).1 hM'bot
  let X := ↥I ⧸ CFSG.pCore 2 ↥I
  obtain ⟨hZcard, ⟨eQ⟩⟩ := hP2.1
  have hQcard : Nat.card (X ⧸ Subgroup.center X) = 360 := by
    rw [Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hQsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact (MulEquiv.isSimpleGroup_congr eQ).2 inferInstance
  have hXcard : Nat.card X = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [hQcard, hZcard] at h
    norm_num at h ⊢
    exact h
  have hIcard : Nat.card ↥I = 1080 * Nat.card (CFSG.pCore 2 ↥I) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I)
    rw [hXcard] at h
    exact h
  let K : Subgroup ↥I := ρ'.ker
  have hKnormal : K.Normal := by infer_instance
  have hcardI' : Nat.card ↥I = Nat.card ↥K * Nat.card ↥H := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have hq : Nat.card (↥I ⧸ K) = Nat.card ↥H := by
      change Nat.card (↥I ⧸ ρ'.ker) = Nat.card ↥ρ'.range
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv
    rw [hq, Nat.mul_comm] at h
    exact h
  let π : ↥I →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  let Kbar : Subgroup X := K.map π
  have hKbar_normal : Kbar.Normal :=
    hKnormal.map π (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I))
  haveI : Kbar.Normal := hKbar_normal
  let φK : ↥K →* X := π.comp K.subtype
  have hφK_range : φK.range = Kbar := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_map_of_mem π k.2
    · intro hy
      obtain ⟨x, hxK, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hxK⟩, rfl⟩
  have hφK_ker : φK.ker = (CFSG.pCore 2 ↥I).subgroupOf K := by
    ext k
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change (QuotientGroup.mk (k : ↥I) : X) = 1 ↔
      (k : ↥I) ∈ CFSG.pCore 2 ↥I
    exact QuotientGroup.eq_one_iff (k : ↥I)
  have hpc_card :
      Nat.card ↥((CFSG.pCore 2 ↥I).subgroupOf K) = Nat.card (CFSG.pCore 2 ↥I) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO2ker).toEquiv
  have hKcard : Nat.card ↥K = Nat.card ↥Kbar * Nat.card (CFSG.pCore 2 ↥I) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φK.ker
    have hq : Nat.card (↥K ⧸ φK.ker) = Nat.card ↥Kbar := by
      rw [← hφK_range]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φK).toEquiv
    rw [hq, hφK_ker, hpc_card] at h
    exact h
  have hKbarH : Nat.card ↥Kbar * Nat.card ↥H = 1080 := by
    have h1 : Nat.card ↥Kbar * Nat.card ↥H * Nat.card (CFSG.pCore 2 ↥I)
        = 1080 * Nat.card (CFSG.pCore 2 ↥I) := by
      calc
        Nat.card ↥Kbar * Nat.card ↥H * Nat.card (CFSG.pCore 2 ↥I)
            = (Nat.card ↥Kbar * Nat.card (CFSG.pCore 2 ↥I)) * Nat.card ↥H := by ring
        _ = Nat.card ↥K * Nat.card ↥H := by rw [← hKcard]
        _ = Nat.card ↥I := hcardI'.symm
        _ = 1080 * Nat.card (CFSG.pCore 2 ↥I) := hIcard
    exact Nat.mul_right_cancel Nat.card_pos h1
  have hcard9 : 9 ≤ Nat.card ↥(A ⊓ I) :=
    card_inf_perfectCoreL_ge_nine' c hA hA27 ha haZ hP2.2.2.1 hP2.2.2.2
  have hAI3 : IsPGroup 3 ↥(A ⊓ I) := by
    refine IsPGroup.of_card_dvd_pow (n := 3) ?_
    have hdvd : Nat.card ↥(A ⊓ I) ∣ Nat.card ↥A := Subgroup.card_dvd_of_le inf_le_left
    rw [hA27] at hdvd
    exact hdvd.trans (by norm_num : (27 : ℕ) ∣ 3 ^ 3)
  obtain ⟨m, hm⟩ := hAI3.exists_card_eq
  have h9dvdAI : 9 ∣ Nat.card ↥(A ⊓ I) := by
    rw [hm]
    have h2 : 2 ≤ m := by
      by_contra h
      have hm1 : m ≤ 1 := by omega
      have hle : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      rw [hm] at hcard9
      norm_num at hle
      omega
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 h2
  have hAK : A ⊓ I ≤ K.map I.subtype := by
    rintro x ⟨hxA, hxI⟩
    have hg : (⟨x, hxI⟩ : ↥I) ∈ K := by
      show ρ' ⟨x, hxI⟩ = 1
      have hρg : ρ ⟨x, hxI⟩ = 1 := by
        refine Equiv.ext fun M => ?_
        have hMmem : M.1 ∈ orbitConjugates I J := by
          rw [← hΩeq]
          exact M.2
        have hxnorm : x ∈ Subgroup.normalizer (M.1 : Set G) :=
          hAnorm M.1 hMmem hxA
        have hmap : M.1.map (MulAut.conj x).toMonoidHom = M.1 :=
          CFSG.LocalAnalysis.GorensteinLyons.map_conj_eq_self_iff.mpr hxnorm
        have hfix : (⟨x, hxI⟩ : ↥I) • M = M := by
          apply Subtype.ext
          rw [MulAction.orbit.coe_smul, hsmul]
          simpa using hmap
        have h1 : ρ ⟨x, hxI⟩ • M = M := by
          simpa [ρ, MulAction.toPermHom_apply, Equiv.Perm.smul_def, MulAction.toPerm_apply]
            using hfix
        simpa [Equiv.Perm.smul_def] using h1
      change (Equiv.permCongrHom e) (ρ ⟨x, hxI⟩) = 1
      rw [hρg, map_one]
    exact Subgroup.mem_map_of_mem I.subtype hg
  have h9K : 9 ∣ Nat.card ↥K := by
    rw [← Subgroup.card_map_of_injective I.subtype_injective]
    exact h9dvdAI.trans (Subgroup.card_dvd_of_le hAK)
  rcases hHcard with hH360 | hH60
  · have hKbar3 : Nat.card ↥Kbar = 3 := by
      rw [hH360] at hKbarH
      omega
    have hKcard3 : Nat.card ↥K = 3 * Nat.card (CFSG.pCore 2 ↥I) := by
      rw [hKcard, hKbar3]
    rw [hKcard3] at h9K
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    rw [hn] at h9K
    obtain ⟨t, ht⟩ := h9K
    have h2 : 2 ^ n = 3 * t := by omega
    have h3dvd : 3 ∣ 2 ^ n := ⟨t, h2⟩
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    norm_num at h32
  · have hKbar18 : Nat.card ↥Kbar = 18 := by
      rw [hH60] at hKbarH
      omega
    exact not_normal_card_eighteen Kbar hQsimple hZcard hXcard hKbar18

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem threePrimeComponent_orbit_ne_six_coprime'
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J)) :
    False := by
  have hcardZ : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hZne : zSub P c.L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardZ
    exact absurd hcardZ (by norm_num)
  haveI hntriv : Nontrivial ↥(zSub P c.L) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(zSub P c.L))
  let z : G := (x : G)
  have hz : z ∈ zSub P c.L := x.2
  have hz1 : z ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext h)
  have hzord : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := by
      rw [← hcardZ]
      have h := orderOf_dvd_natCard (⟨z, hz⟩ : zSub P c.L)
      rw [← Subgroup.orderOf_coe] at h
      exact h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzgen : zSub P c.L = Subgroup.zpowers z := by
    have hcardzp : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, hzord]
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [hcardzp, hcardZ])).symm
  have hS1 := z_normalizes_orbit c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
    hP2 hP3 hP5 hJ h3 h6 h7J
  have hS2 := z_centralizes_orbit_images c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL
    ha haZ hP2 hP3 hP5 hJ h3 h6 h7J hS1
  obtain ⟨W, hWH, hWz, hWperf, hW3, hWmap⟩ :=
    exists_perfect_lift' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
      hP2 hP3 hP5 hJ h3 h6 h7J hS1 hS2 hz hz1
  exact false_of_A_normalizes_orbit' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
    hP2 hP3 hP5 hJ h3 h6 h7J
    (A_normalizes_orbit' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
      hP2 hP3 hP5 hJ h3 h6 h7J hS1 hS2 hz hz1 hzgen hWH hWz hWperf hW3 hWmap)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem threePrimeComponent_orbit_ne_six''
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6) :
    False := by
  by_cases h7J : 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J)
  · exact threePrimeComponent_orbit_ne_six_seven'' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA
      hAPL ha haZ hP2 hP3 hP5 hJ h3 h6 h7J
  · exact threePrimeComponent_orbit_ne_six_coprime' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA
      hAPL ha haZ hP2 hP3 hP5 hJ h3 h6 h7J

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem threePrimeComponent_normalized'
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J) :
    perfectCoreL c a ≤ Subgroup.normalizer (J : Set G) := by
  rw [perfectCoreL_le_normalizer_iff_orbit_ncard_eq_one]
  rcases perfectCoreL_orbit_card c hP2.1 J with h1 | h6
  · exact h1
  · rcases eq_or_lt_of_le h6 with h6eq | h6lt
    · exact (threePrimeComponent_orbit_ne_six'' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
        hP2 hP3 hP5 hJ h3 h6eq.symm).elim
    · exact (threePrimeComponent_orbit_lt_seven' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
        hP2 hP3 hP5 hJ h3 (by omega)).elim

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
