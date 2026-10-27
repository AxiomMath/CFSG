module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7b
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
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem exists_elementaryAbelian_seven_rank_two'
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
    (h7J : 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J)) :
    ∃ Y : Subgroup (↥(Subgroup.centralizer ({a} : Set G)) ⧸
        CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))),
      IsPGroup 7 Y ∧ 2 ≤ Group.rank Y := by
  classical
  haveI : IsSimpleGroup G := D.standing.simple
  let H := Subgroup.centralizer ({a} : Set G)
  let N := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H
  let X := H ⧸ N
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact haZ (Subgroup.one_mem (zSub P c.L))
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := D.standing.nonab
      exact hxy (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h) x y)
  have ha_center : a ∉ Subgroup.center G := by
    rw [hcenter]
    intro ha'
    exact ha1 (Subgroup.mem_bot.mp ha')
  have hHproper : H ≠ ⊤ := by
    intro htop
    apply ha_center
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg a (Set.mem_singleton a)).symm
  have hKH : CFSG.Open.IsKGroup ↥H := c.kProper.isKGroup H hHproper
  have hKX : CFSG.Open.IsKGroup X := hKH.quotient N
  have hJH : J ≤ H := (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ).1
  have hJ' : J.subgroupOf H ∈ thetaComponents 3 H :=
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ).2
  have h1 : 1 < (orbitConjugates (perfectCoreL c a) J).ncard := by omega
  obtain ⟨J₂, hJ₂mem, hJ₂ne⟩ := Set.exists_ne_of_one_lt_ncard h1 J
  obtain ⟨b, hb, hbJ⟩ := hJ₂mem
  have hb' : b⁻¹ ∈ perfectCoreL c a := Subgroup.inv_mem _ hb
  have hbH : b⁻¹ ∈ H := (perfectCoreL_le c a hb').2
  have hJ₂theta : J₂ ∈ thetaComponentsAt 3 a := by
    rw [hbJ]
    exact CFSG.RankThree.PartOne.F106.conj_mem_thetaComponentsAt_cent Nat.prime_three hbH hJ
  have hJ₂H : J₂ ≤ H := (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ₂theta).1
  have hJ₂' : J₂.subgroupOf H ∈ thetaComponents 3 H :=
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ₂theta).2
  let K₁ : Subgroup X := (J.subgroupOf H).map (QuotientGroup.mk' N)
  let K₂ : Subgroup X := (J₂.subgroupOf H).map (QuotientGroup.mk' N)
  have hK₁comp : IsComponent K₁ :=
    isComponent_map_of_mem_thetaComponents Nat.prime_three hJ'
  have hK₂comp : IsComponent K₂ :=
    isComponent_map_of_mem_thetaComponents Nat.prime_three hJ₂'
  have hKne : K₁ ≠ K₂ := by
    intro hEq
    have hsubeq : J.subgroupOf H = J₂.subgroupOf H :=
      (theta_component_quotient_correspondence (H := H) Nat.prime_three).1.injOn hJ' hJ₂' hEq
    have hJeq : J = J₂ := by
      have hmap := congrArg (Subgroup.map H.subtype) hsubeq
      rwa [Subgroup.map_subgroupOf_eq_of_le hJH,
        Subgroup.map_subgroupOf_eq_of_le hJ₂H] at hmap
    exact hJ₂ne hJeq.symm
  have hKcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := by
    have hcomm : ⁅K₁, K₂⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hK₁comp hK₂comp with h | h
      · exact absurd h hKne
      · exact h
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  have hcardImage : ∀ {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a),
      Nat.card ↥((K.subgroupOf H).map (QuotientGroup.mk' N)) =
        Nat.card (K ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K) := by
    intro K hK
    have hK' : K.subgroupOf H ∈ thetaComponents 3 H :=
      (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK).2
    obtain ⟨η, -⟩ := CFSG.RankThree.exists_thetaQuotient_mulEquiv_map (H := H) (p := 3)
      Nat.prime_three (L := K.subgroupOf H) hK'.2.1
    let eK : K.subgroupOf H ≃* K :=
      Subgroup.subgroupOfEquivOfLe (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK).1
    let eθ : (K.subgroupOf H ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        (K.subgroupOf H)) ≃*
        (K ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K) :=
      QuotientGroup.congr _ _ eK
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv (p := 3) Nat.prime_three eK)
    calc
      Nat.card ↥((K.subgroupOf H).map (QuotientGroup.mk' N)) =
          Nat.card (K.subgroupOf H ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
            (K.subgroupOf H)) := (Nat.card_congr η.toEquiv).symm
      _ = Nat.card (K ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 K) :=
          Nat.card_congr eθ.toEquiv
  have h7K₁ : 7 ∣ Nat.card K₁ := by
    change 7 ∣ Nat.card ↥((J.subgroupOf H).map (QuotientGroup.mk' N))
    rw [hcardImage hJ]
    exact h7J
  have hJ₂def : J₂ = J.map (MulAut.conj b⁻¹).toMonoidHom := by
    rw [hbJ]
    rfl
  have h7J₂ : 7 ∣ Nat.card (J₂ ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J₂) := by
    rw [hJ₂def]
    let ec : J ≃* J.map (MulAut.conj b⁻¹).toMonoidHom :=
      Subgroup.equivMapOfInjective J (MulAut.conj b⁻¹).toMonoidHom
        (MulAut.conj b⁻¹).injective
    let eθc : (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J) ≃*
        (J.map (MulAut.conj b⁻¹).toMonoidHom ⧸
          CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
            (J.map (MulAut.conj b⁻¹).toMonoidHom)) :=
      QuotientGroup.congr _ _ ec
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv (p := 3) Nat.prime_three ec)
    rw [← Nat.card_congr eθc.toEquiv]
    exact h7J
  have h7K₂ : 7 ∣ Nat.card K₂ := by
    change 7 ∣ Nat.card ↥((J₂.subgroupOf H).map (QuotientGroup.mk' N))
    rw [hcardImage hJ₂theta]
    exact h7J₂
  have h3K₁ : ¬ 3 ∣ Nat.card K₁ := by
    have hdvd : Nat.card K₁ ∣ Nat.card J := by
      change Nat.card ↥((J.subgroupOf H).map (QuotientGroup.mk' N)) ∣ Nat.card J
      rw [hcardImage hJ]
      exact Subgroup.card_quotient_dvd_card _
    exact fun h => h3 (h.trans hdvd)
  have hq₁ : CFSG.Open.IsQuasisimple ↥K₁ :=
    ⟨hK₁comp.1.1.commutator_eq_top, hK₁comp.1.2.1⟩
  have hK₁K : CFSG.Open.IsKGroup ↥K₁ := hKX.subgroup K₁
  have hZ₁two : IsPGroup 2 (Subgroup.center K₁) :=
    center_isPGroup_two_of_quasisimple_isKGroup hq₁ hK₁K h3K₁
  obtain ⟨y₁, hy1ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₁) 7 h7K₁
  obtain ⟨y₂, hy2ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₂) 7 h7K₂
  have hy1ordX : orderOf (y₁ : X) = 7 := by
    rw [Subgroup.orderOf_coe, hy1ord]
  have hy2ordX : orderOf (y₂ : X) = 7 := by
    rw [Subgroup.orderOf_coe, hy2ord]
  have hcommute : (y₁ : X) * (y₂ : X) = (y₂ : X) * (y₁ : X) :=
    hKcomm (y₁ : X) y₁.2 (y₂ : X) y₂.2
  let A : Subgroup X := Subgroup.zpowers (y₁ : X)
  let B : Subgroup X := Subgroup.zpowers (y₂ : X)
  have htrivialintersect : A ⊓ B = ⊥ := by
    let I : Subgroup X := A ⊓ B
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hZ2 : IsPGroup 2 ((Subgroup.center ↥K₁).map K₁.subtype) :=
      hZ₁two.map K₁.subtype
    have hIle : I ≤ (Subgroup.center ↥K₁).map K₁.subtype := by
      intro z hz
      have hzK₁ : z ∈ K₁ := (Subgroup.zpowers_le.mpr y₁.2) hz.1
      have hzK₂ : z ∈ K₂ := (Subgroup.zpowers_le.mpr y₂.2) hz.2
      have hzc : (⟨z, hzK₁⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact hKcomm (g : X) g.2 z hzK₂
      exact Subgroup.mem_map.mpr ⟨⟨z, hzK₁⟩, hzc, rfl⟩
    have hI2 : IsPGroup 2 I := hZ2.to_le hIle
    have hA7 : IsPGroup 7 A := by
      have hcardA : Nat.card ↥A = 7 ^ 1 := by
        rw [Nat.card_zpowers, hy1ordX]
        norm_num
      exact IsPGroup.of_card hcardA
    have hI7 : IsPGroup 7 I := hA7.to_le (show I ≤ A from inf_le_left)
    have hdisj : Disjoint I I := IsPGroup.disjoint_of_ne 2 7 (by norm_num) I I hI2 hI7
    exact hdisj.eq_bot_of_self
  let Y : Subgroup X := Subgroup.closure ({(y₁ : X), (y₂ : X)} : Set X)
  have hYeq : Y = A ⊔ B := by
    show Subgroup.closure ({(y₁ : X), (y₂ : X)} : Set X) = A ⊔ B
    rw [show ({(y₁ : X), (y₂ : X)} : Set X) =
        ({(y₁ : X)} : Set X) ∪ ({(y₂ : X)} : Set X) by
      ext z
      simp [or_comm]]
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcent : B ≤ Subgroup.centralizer (A : Set X) := by
    rw [show B = Subgroup.zpowers (y₂ : X) from rfl,
      show A = Subgroup.zpowers (y₁ : X) from rfl]
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    change z ∈ Subgroup.zpowers (y₁ : X) at hz
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨m, rfl⟩ := hz
    have hc : Commute (y₁ : X) (y₂ : X) := hcommute
    simpa using (hc.zpow_zpow m 1).eq
  have hnorm : B ≤ Subgroup.normalizer (A : Set X) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (A : Set X))
  have hdisjAB : Disjoint A B := disjoint_iff.mpr htrivialintersect
  have hcardAB : Nat.card ↥(A ⊔ B) = 7 * 7 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A B hnorm hdisjAB]
    rw [show A = Subgroup.zpowers (y₁ : X) from rfl,
      show B = Subgroup.zpowers (y₂ : X) from rfl,
      Nat.card_zpowers, Nat.card_zpowers, hy1ordX, hy2ordX]
  have hYcard : Nat.card ↥Y = 7 ^ 2 := by
    rw [hYeq, hcardAB]
    norm_num
  have hy1pow : (y₁ : X) ^ 7 = 1 := by
    rw [← hy1ordX, pow_orderOf_eq_one]
  have hy2pow : (y₂ : X) ^ 7 = 1 := by
    rw [← hy2ordX, pow_orderOf_eq_one]
  have hEA : IsElementaryAbelian 7 ↥Y := by
    rw [hYeq]
    haveI hEA1 : IsElementaryAbelian 7 ↥(Subgroup.zpowers (y₁ : X)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hy1pow
    haveI hEA2 : IsElementaryAbelian 7 ↥(Subgroup.zpowers (y₂ : X)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hy2pow
    exact IsElementaryAbelian.sup_of_le_centralizer hcent
  have hYp : IsPGroup 7 Y := by
    haveI : IsElementaryAbelian 7 ↥Y := hEA
    exact IsElementaryAbelian.isPGroup 7 ↥Y
  have hnotcyc : ¬ IsCyclic ↥Y := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI : IsElementaryAbelian 7 ↥Y := hEA
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hYcard
  have hYrank : 2 ≤ Group.rank ↥Y := by
    by_contra h
    push Not at h
    have hgen : CFSG.generatorRank ↥Y ≤ 1 := by
      rw [CFSG.generatorRank_eq_group_rank]
      omega
    exact hnotcyc (CFSG.isCyclic_of_generatorRank_le_one hgen)
  exact ⟨Y, hYp, hYrank⟩

theorem threePrimeComponent_orbit_ne_six_seven''
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
    (h7J : 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J)) :
    False := by
  classical
  let H := Subgroup.centralizer ({a} : Set G)
  let N := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H
  obtain ⟨Y, hYp, hYrank⟩ := exists_elementaryAbelian_seven_rank_two' c hPSz hK8 hON h7 hP hNZ
    hA hA27 hZA hAPL ha haZ hP2 hP3 hP5 hJ h3 h6 h7J
  have hYlift : (Y.comap (QuotientGroup.mk' N)).map H.subtype ≤ H :=
    Subgroup.map_subtype_le _
  have hlt : 1 < CFSG.Open.pRank 7 H := by
    have h := CFSG.AGLEmbedding.lt_pRank_of_quotient CFSG.AGLEmbedding.thompsonNormalAbelianGen
      (p := 7) (by norm_num) (H := H) (L := H) (N := N) hYp hYlift (r := 1) ?_
    · simpa using h
    · exact lt_of_lt_of_le (by norm_num) hYrank
  have hP3H : CFSG.Open.pRank 7 H = 1 := hP3
  omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
