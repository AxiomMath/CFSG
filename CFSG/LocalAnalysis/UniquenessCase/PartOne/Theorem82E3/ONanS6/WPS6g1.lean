module

public import CFSG.GroupTheory.PGroup.PrimePartTransport
public import CFSG.GroupTheory.PRankCommutingSup
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
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
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6f
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

theorem exists_perfect_lift'
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
    (hS1 : ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G))
    (hS2 : ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      autThetaQuot (zSub P c.L) K = ⊥)
    {z : G} (hz : z ∈ zSub P c.L) (hz1 : z ≠ 1) :
    ∃ W : Subgroup G,
      W ≤ centralizerAt a ∧
      W ≤ Subgroup.centralizer ({z} : Set G) ∧
      Group.IsPerfect ↥W ∧ ¬ 3 ∣ Nat.card W ∧
      ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
        thetaImgAt a K ≤
          (W.subgroupOf (centralizerAt a)).map (QuotientGroup.mk' (thetaAt a)) := by
  classical
  let H : Subgroup G := centralizerAt a
  let θ : Subgroup H := thetaAt a
  let q : H →* H ⧸ θ := QuotientGroup.mk' θ
  let zH : H := ⟨z, (Subgroup.mem_centralizer_singleton_iff).mpr (by
    have hAc : A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).mpr hA.1
    have hza : a * z = z * a := (Subgroup.mem_centralizer_iff.mp (hAc (hZA hz))) a ha
    exact hza.symm)⟩
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore (G := H)
  let S : Set (Subgroup G) := orbitConjugates (perfectCoreL c a) J
  let s : Finset (Subgroup G) := (Set.toFinite S).toFinset
  have hs_mem : ∀ K, K ∈ s ↔ K ∈ S := by
    intro K
    simp [s, S]
  have hthetaAt : ∀ K ∈ S, K ∈ thetaComponentsAt 3 a := by
    intro K hK
    obtain ⟨b, hb, rfl⟩ := hK
    exact CFSG.RankThree.PartOne.F106.conj_mem_thetaComponentsAt_cent Nat.prime_three
      (Subgroup.inv_mem _ ((perfectCoreL_le c a) hb).2) hJ
  have hKH : ∀ K ∈ S, K ≤ H := fun K hK =>
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp (hthetaAt K hK)).1
  have hKtheta : ∀ K ∈ S, K.subgroupOf H ∈ thetaComponents 3 H := fun K hK =>
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp (hthetaAt K hK)).2
  have hKcard : ∀ K ∈ S, Nat.card ↥K = Nat.card ↥J := by
    intro K hK
    obtain ⟨b, hb, rfl⟩ := hK
    exact Subgroup.card_map_of_injective (f := (MulAut.conj b⁻¹).toMonoidHom)
      (K := J) (MulAut.conj b⁻¹).injective
  have hK3 : ∀ K ∈ S, ¬ 3 ∣ Nat.card (K.subgroupOf H) := by
    intro K hK
    have hcard : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKH K hK)).toEquiv
    rw [hcard, hKcard K hK]
    exact h3
  let U : Subgroup G → Subgroup (H ⧸ θ) := fun K => (K.subgroupOf H).map q
  have hUinj : Set.InjOn (fun L : Subgroup H => L.map q) (thetaComponents 3 H) :=
    (theta_component_quotient_correspondence (H := H) (p := 3) Nat.prime_three).1.injOn
  have hLne : ∀ K₁ ∈ S, ∀ K₂ ∈ S, K₁ ≠ K₂ → K₁.subgroupOf H ≠ K₂.subgroupOf H := by
    intro K₁ h₁ K₂ h₂ hne heq
    apply hne
    have h := congrArg (Subgroup.map H.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le (hKH K₁ h₁),
      Subgroup.map_subgroupOf_eq_of_le (hKH K₂ h₂)] at h
  have hUne : ∀ K₁ ∈ S, ∀ K₂ ∈ S, K₁ ≠ K₂ → U K₁ ≠ U K₂ := by
    intro K₁ h₁ K₂ h₂ hne heq
    exact hLne K₁ h₁ K₂ h₂ hne (hUinj (hKtheta K₁ h₁) (hKtheta K₂ h₂) heq)
  have hcomp : ∀ K ∈ S, IsComponent (U K) := fun K hK =>
    isComponent_map_of_mem_thetaComponents Nat.prime_three (hKtheta K hK)
  have hcomm : ∀ K₁ ∈ s, ∀ K₂ ∈ s, K₁ ≠ K₂ →
      U K₁ ≤ Subgroup.centralizer (U K₂ : Set (H ⧸ θ)) := by
    intro K₁ h₁ K₂ h₂ hne
    have hneU : U K₁ ≠ U K₂ :=
      hUne K₁ ((hs_mem K₁).mp h₁) K₂ ((hs_mem K₂).mp h₂) hne
    have hbot : ⁅U K₁, U K₂⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute (hcomp K₁ ((hs_mem K₁).mp h₁))
        (hcomp K₂ ((hs_mem K₂).mp h₂))).resolve_left hneU
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hU3 : ∀ K ∈ S, ¬ 3 ∣ Nat.card ↥(U K) := by
    intro K hK
    exact fun h => hK3 K hK (h.trans (Subgroup.card_map_dvd _ _))
  have hZ : ∀ K ∈ s, ¬ 3 ∣ Nat.card
      ↥(U K ⊓ Subgroup.centralizer (U K : Set (H ⧸ θ))) := by
    intro K hK
    exact fun h => hU3 K ((hs_mem K).mp hK)
      (h.trans (Subgroup.card_dvd_of_le (inf_le_left : _ ≤ U K)))
  have hpRank := CFSG.GroupTheory.pRank_iSup_eq_sum_of_commute_of_not_dvd
    (Y := H ⧸ θ) (p := 3) Nat.prime_three s U hcomm hZ
  have hpzero : ∀ K ∈ s, CFSG.Open.pRank 3 (U K) = 0 := by
    intro K hK
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := U K)]
    exact CFSG.pRank_eq_zero_of_not_dvd_card (G := ↥(U K)) (p := 3) Nat.prime_three
      (hU3 K ((hs_mem K).mp hK))
  have hsum : CFSG.Open.pRank 3 (⨆ K ∈ s, U K) = 0 := by
    rw [hpRank]
    exact Finset.sum_eq_zero fun K hK => hpzero K hK
  have hT3 : ¬ 3 ∣ Nat.card ↥(⨆ K ∈ s, U K) :=
    CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero (p := 3) Nat.prime_three hsum
  let X : Subgroup H := (⨆ K ∈ s, K.subgroupOf H) ⊔ θ
  have hθmap : θ.map q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    change (QuotientGroup.mk x : H ⧸ θ) = 1
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hXmap : X.map q = ⨆ K ∈ s, U K := by
    dsimp [X, U]
    rw [Subgroup.map_sup]
    simp only [Subgroup.map_iSup, hθmap, sup_bot_eq]
  have hcardX := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker q X
  have hker : q.ker = θ := QuotientGroup.ker_mk' θ
  have hXθ : X ⊓ q.ker = θ := by
    rw [hker, inf_eq_right.mpr le_sup_right]
  rw [hXmap, hXθ] at hcardX
  have hX3 : ¬ 3 ∣ Nat.card ↥X := by
    intro hdvd
    rw [hcardX] at hdvd
    rcases Nat.prime_three.dvd_mul.mp hdvd with h | h
    · exact hT3 h
    · exact hθ3 h
  have hcardZ : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hzord : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := by
      rw [← hcardZ]
      have h := orderOf_dvd_natCard (⟨z, hz⟩ : zSub P c.L)
      rw [← Subgroup.orderOf_coe] at h
      exact h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzordH : orderOf zH = 3 := by
    rw [← Subgroup.orderOf_coe zH]
    exact hzord
  have hzN : ∀ K ∈ S, zH ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) := by
    intro K hK
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hzK : z ∈ Subgroup.normalizer (K : Set G) := hS1 z hz K hK
    have hlK : (l : G) ∈ K := Subgroup.mem_subgroupOf.mp hl
    have hmem : z * (l : G) * z⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hzK (l : G)).mp hlK
    simpa [zH, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  have haction : ∀ (K : Subgroup G) (hK : K ∈ S), ∀ k : ↥K,
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)
        (K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩ k) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) k := by
    intro K hK k
    have hmemAut : thetaQuotMulAut K (K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩) ∈
        autThetaQuot (zSub P c.L) K :=
      mem_autThetaQuot_iff.mpr ⟨z, hS1 z hz K hK, hz, rfl⟩
    have hσ1 : thetaQuotMulAut K (K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩) = 1 := by
      have hbot := hS2 K hK
      rw [hbot] at hmemAut
      simpa using hmemAut
    have h := congrArg (fun τ : MulAut (K ⧸ aschbacherSolvableCore 3 ↥K) =>
      τ (k : K ⧸ aschbacherSolvableCore 3 ↥K)) hσ1
    simpa [thetaQuotMulAut_mk] using h
  have hmemθH : ∀ (K : Subgroup G) (hK : K ∈ S), ∀ k : ↥K,
      ((K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩ k : ↥K) : G) * (k : G)⁻¹ ∈
        (thetaAt a).map (centralizerAt a).subtype := by
    intro K hK k
    have hd : (K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩ k) / k ∈
        aschbacherSolvableCore 3 ↥K :=
      (QuotientGroup.eq_iff_div_mem).mp (haction K hK k)
    have hmemG : ((K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩ k : ↥K) : G) * (k : G)⁻¹ ∈
        CFSG.inSubgroup (aschbacherSolvableCore 3) K := by
      refine Subgroup.mem_map.mpr ⟨(K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩ k) / k,
        hd, ?_⟩
      simp [Subgroup.coe_div, div_eq_mul_inv]
    have h := hmemG
    rw [CFSG.RankThree.PartOne.theta_eq_inf_of_mem_thetaComponentsAt
      (p := 3) Nat.prime_three (a := a) (hthetaAt K hK)] at h
    exact h.2
  have hfix : ∀ (K : Subgroup G) (hK : K ∈ S), ∀ l : ↥(K.subgroupOf H),
      q ((K.subgroupOf H).normalizerMonoidHom ⟨zH, hzN K hK⟩ l) = q l := by
    intro K hK l
    let σH : ↥(K.subgroupOf H) := (K.subgroupOf H).normalizerMonoidHom ⟨zH, hzN K hK⟩ l
    let k : ↥K := ⟨(l : G), l.2⟩
    have hval : (((σH * l⁻¹ : ↥(K.subgroupOf H)) : H) : G) =
        ((K.normalizerMonoidHom ⟨z, hS1 z hz K hK⟩ k : ↥K) : G) * (k : G)⁻¹ := by
      simp [σH, k, zH, Subgroup.coe_mul, Subgroup.coe_inv,
        normalizerMonoidHom_apply_coe]
    have hmem : ((σH * l⁻¹ : ↥(K.subgroupOf H)) : H) ∈ θ := by
      have h := hmemθH K hK k
      rw [← hval] at h
      exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp h
    have hq1 : q (((σH * l⁻¹ : ↥(K.subgroupOf H)) : H)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have hq2 : q (σH : H) = q (l : H) := by
      have hq1' : q (σH : H) * (q (l : H))⁻¹ = 1 := by
        simpa [map_mul, map_inv] using hq1
      exact mul_inv_eq_one.mp hq1' 
    simpa [σH] using hq2
  let D : Subgroup H := Subgroup.centralizer ({zH} : Set H) ⊓ X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 ↥(Subgroup.zpowers zH)) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzordH]; norm_num)⟩
  have hcopθ : Nat.Coprime 3 (Nat.card θ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hθ3
  have hcent_q : Subgroup.centralizer ({(q zH)} : Set (H ⧸ θ)) =
      (Subgroup.centralizer ({zH} : Set H)).map q := by
    have h := CFSG.centralizer_map_quotient_eq_map_centralizer
      (G := H) (p := 3) (T := Subgroup.zpowers zH) (M := θ) (by infer_instance) hcopθ
    calc Subgroup.centralizer ({q zH} : Set (H ⧸ θ))
        = Subgroup.centralizer
            ((Subgroup.zpowers (q zH) : Subgroup (H ⧸ θ)) : Set (H ⧸ θ)) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      _ = Subgroup.centralizer
            (((Subgroup.zpowers zH).map q : Subgroup (H ⧸ θ)) : Set (H ⧸ θ)) := by
          rw [MonoidHom.map_zpowers]
      _ = (Subgroup.centralizer ((Subgroup.zpowers zH : Subgroup H) : Set H)).map q := h
      _ = (Subgroup.centralizer ({zH} : Set H)).map q := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hDmap : D.map q =
      Subgroup.centralizer ({(q zH)} : Set (H ⧸ θ)) ⊓ X.map q := by
    apply le_antisymm
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
      refine ⟨?_, Subgroup.mem_map_of_mem q hd.2⟩
      show q d ∈ Subgroup.centralizer ({q zH} : Set (H ⧸ θ))
      rw [hcent_q]
      exact Subgroup.mem_map_of_mem q hd.1
    · intro y hy
      rw [hcent_q] at hy
      obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hy.1
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hy.2
      have hcx : c * x⁻¹ ∈ θ := by
        have h1 : q (c * x⁻¹) = 1 := by
          rw [map_mul, map_inv, hcq, hxq, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hcX : c ∈ X := by
        have hc_eq : c = (c * x⁻¹) * x := by group
        rw [hc_eq]
        refine X.mul_mem ?_ hx
        exact Subgroup.mem_sup_right hcx
      exact Subgroup.mem_map.mpr ⟨c, ⟨hc, hcX⟩, hcq⟩
  have hUK_le_D : ∀ K ∈ S, U K ≤ D.map q := by
    intro K hK
    rw [hDmap]
    refine le_inf ?_ ?_
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
      have hzq : Commute (q (l : H)) (q zH) := by
        have h := hfix K hK ⟨l, hl⟩
        have h3 : q zH * q (l : H) * (q zH)⁻¹ = q (l : H) := by
          simpa [normalizerMonoidHom_apply_coe, map_mul, map_inv] using h
        have h4 : q zH * q (l : H) = q (l : H) * q zH := by
          have := congrArg (fun t => t * q zH) h3
          simpa [mul_assoc] using this
        exact h4.symm
      exact Subgroup.mem_centralizer_singleton_iff.mpr hzq
    · refine Subgroup.map_mono ?_
      have h1 : K.subgroupOf H ≤ ⨆ K ∈ s, K.subgroupOf H :=
        le_iSup₂ (f := fun K (_ : K ∈ s) => K.subgroupOf H) K ((hs_mem K).mpr hK)
      exact h1.trans le_sup_left
  have hperfU : ∀ K ∈ S, Group.IsPerfect ↥(U K) := by
    intro K hK
    have hperfL : Group.IsPerfect ↥(K.subgroupOf H) := (hKtheta K hK).1
    rw [Subgroup.isPerfect_iff] at hperfL ⊢
    dsimp [U]
    rw [← Subgroup.map_commutator, hperfL]
  let W_H : Subgroup H := CFSG.inSubgroup CFSG.perfectResidual D
  let W : Subgroup G := W_H.map H.subtype
  have hperfD : Group.IsPerfect ↥(CFSG.perfectResidual ↥D) :=
    (CFSG.perfect_residual_characterization (G := ↥D)).2.2.1
  have hperfWH : Group.IsPerfect ↥W_H := by
    haveI : Group.IsPerfect ↥(CFSG.perfectResidual ↥D) := hperfD
    dsimp [W_H, CFSG.inSubgroup]
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective (CFSG.perfectResidual ↥D) D.subtype
        D.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (CFSG.perfectResidual ↥D) D.subtype
        D.subtype_injective).surjective
  have hperfW : Group.IsPerfect ↥W := by
    haveI : Group.IsPerfect ↥W_H := hperfWH
    dsimp [W]
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective W_H H.subtype H.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective W_H H.subtype H.subtype_injective).surjective
  let f : ↥D →* (H ⧸ θ) := q.comp D.subtype
  have htrans := CFSG.perfect_residual_transport (f := f)
  have hWq : W_H.map q = (CFSG.perfectResidual f.range).map f.range.subtype := by
    have h1 : W_H.map q = (CFSG.perfectResidual ↥D).map f := by
      dsimp [W_H, CFSG.inSubgroup, f]
      rw [Subgroup.map_map]
    rw [h1, htrans.1]
  have hrange_perf : ∀ P : Subgroup ↥(f.range), Group.IsPerfect P →
      P ≤ CFSG.perfectResidual ↥(f.range) :=
    (CFSG.perfect_residual_transport (f := MonoidHom.id ↥(f.range))).2.2
  have hUK_le_W : ∀ K ∈ S, U K ≤ W_H.map q := by
    intro K hK
    have hfrange : f.range = D.map q := by
      dsimp [f]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hUK_le_fr : U K ≤ f.range := by
      rw [hfrange]
      exact hUK_le_D K hK
    let P : Subgroup f.range := (U K).subgroupOf f.range
    have hPmap : P.map f.range.subtype = U K :=
      Subgroup.map_subgroupOf_eq_of_le hUK_le_fr
    have hPperf : Group.IsPerfect ↥P := by
      haveI : Group.IsPerfect ↥(U K) := hperfU K hK
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hUK_le_fr).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hUK_le_fr).symm.surjective
    have hPle : P ≤ CFSG.perfectResidual ↥(f.range) := hrange_perf P hPperf
    have hres : U K ≤ (CFSG.perfectResidual f.range).map f.range.subtype := by
      rw [← hPmap]
      exact Subgroup.map_mono hPle
    rw [hWq]
    exact hres
  have hWX : W_H ≤ X := by
    dsimp [W_H, CFSG.inSubgroup]
    exact (Subgroup.map_subtype_le (CFSG.perfectResidual D)).trans inf_le_right
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le W_H
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨h, hhW, rfl⟩ := Subgroup.mem_map.mp hw
    have hhC : h ∈ Subgroup.centralizer ({zH} : Set H) := by
      dsimp [W_H, CFSG.inSubgroup] at hhW
      exact (Subgroup.map_subtype_le (CFSG.perfectResidual D)).trans inf_le_left hhW
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hhC
    exact congrArg Subtype.val hcomm
  · exact hperfW
  · have hcardW : Nat.card ↥W = Nat.card ↥W_H :=
      Nat.card_congr (Subgroup.equivMapOfInjective W_H H.subtype H.subtype_injective).symm.toEquiv
    rw [hcardW]
    exact fun h => hX3 (h.trans (Subgroup.card_dvd_of_le hWX))
  · intro K hK
    have hKm : K ∈ s := (hs_mem K).mpr hK
    rw [show thetaImgAt a K = U K from rfl]
    have hWsub : W.subgroupOf H = W_H := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp hx
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map_of_mem H.subtype hx
    rw [hWsub]
    exact hUK_le_W K hK

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
