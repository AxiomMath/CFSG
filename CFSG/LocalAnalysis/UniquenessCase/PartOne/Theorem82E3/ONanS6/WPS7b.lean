module

public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Kf1
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEvenHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Sz
public import CFSG.Quasithin.Background.C2PushQuot
public import CFSG.Quasithin.Background.FFC12E
public import CFSG.Quasithin.EmptyFaithful.SBc2SzCore
public import CFSG.RankThree.GroupTheory.SteinbergBKComponentOrbitLocalRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDQuot
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJGe
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDOddHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup
public import CFSG.Quasithin.Background.B69E22Pre
public import CFSG.Quasithin.Background.B69Final
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.Quasithin.Background.B69Lift
public import CFSG.Quasithin.Background.B69Simple
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import Certificates.Certificate129001
public import Certificates.Certificate129003
public import Certificates.Certificate129004
public import Certificates.Certificate129005
public import Certificates.Certificate129006
public import Certificates.Certificate129007
public import Certificates.Certificate129008
public import Certificates.Certificate129009
public import Certificates.Certificate129020
public import Certificates.Certificate129021
public import Certificates.Certificate129030
public import Certificates.Certificate129040
public import Certificates.Certificate129041
public import Certificates.Certificate129060
public import Certificates.Certificate129061
public import Certificates.Certificate129062
public import Certificates.Certificate129070
public import Certificates.Certificate129071
public import Certificates.Certificate129072
public import Certificates.Certificate129073
public import Certificates.Certificate129080
public import Certificates.Certificate129081
public import Certificates.Certificate129082
public import Certificates.Certificate13005
public import Certificates.Certificate21140
public import Certificates.Certificate3961
public import Certificates.Certificate3962

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

noncomputable abbrev C82_wPS7b (a : G) : Subgroup G :=
  Subgroup.centralizer ({a} : Set G)

noncomputable abbrev T82_wPS7b (a : G) : Subgroup ↥(C82_wPS7b a) :=
  aschbacherSolvableCore 3 ↥(C82_wPS7b a)

@[expose] noncomputable def theta82_wPS7b (a : G) (K : Subgroup G) :
    Subgroup (↥(C82_wPS7b a) ⧸ T82_wPS7b a) :=
  (K.subgroupOf (C82_wPS7b a)).map (QuotientGroup.mk' (T82_wPS7b a))

theorem theta82_isComponent {a : G} {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 a) : IsComponent (theta82_wPS7b a K) :=
  isComponent_map_of_mem_thetaComponents Nat.prime_three
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK).2

theorem theta82_injective {a : G} {K K' : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 a) (hK' : K' ∈ thetaComponentsAt 3 a)
    (h : theta82_wPS7b a K = theta82_wPS7b a K') : K = K' := by
  have h1 : K.subgroupOf (C82_wPS7b a) = K'.subgroupOf (C82_wPS7b a) :=
    (theta_component_quotient_correspondence (H := C82_wPS7b a) Nat.prime_three).1.injOn
      (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK).2
      (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK').2 h
  have h2 : K ≤ C82_wPS7b a := (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK).1
  have h3 : K' ≤ C82_wPS7b a := (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hK').1
  rw [← Subgroup.map_subgroupOf_eq_of_le h2, ← Subgroup.map_subgroupOf_eq_of_le h3, h1]

theorem theta82_conj {a : G} {K : Subgroup G} {b : G} (hb : b ∈ C82_wPS7b a)
    (hK : K ≤ C82_wPS7b a) :
    theta82_wPS7b a (K.map (MulAut.conj b).toMonoidHom) =
      (theta82_wPS7b a K).map
        (MulAut.conj (QuotientGroup.mk' (T82_wPS7b a) ⟨b, hb⟩)).toMonoidHom := by
  let bH : ↥(C82_wPS7b a) := ⟨b, hb⟩
  have hbH : (bH : G) = b := rfl
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxK : (x : G) ∈ K.map (MulAut.conj b).toMonoidHom :=
      Subgroup.mem_subgroupOf.mp hx
    obtain ⟨k, hk, hkx⟩ := hxK
    let kH : ↥(C82_wPS7b a) := ⟨k, hK hk⟩
    refine ⟨QuotientGroup.mk' (T82_wPS7b a) kH, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    · have hxeqG : ((bH * kH * bH⁻¹ : ↥(C82_wPS7b a)) : G) = (x : G) := by
        simpa [kH] using hkx
      have hxeqπ : QuotientGroup.mk' (T82_wPS7b a) (bH * kH * bH⁻¹) =
          QuotientGroup.mk' (T82_wPS7b a) x :=
        congrArg (QuotientGroup.mk' (T82_wPS7b a)) (Subtype.ext hxeqG)
      rw [← hxeqπ]
      change MulAut.conj (QuotientGroup.mk' (T82_wPS7b a) ⟨b, hb⟩)
          (QuotientGroup.mk' (T82_wPS7b a) kH) =
        QuotientGroup.mk' (T82_wPS7b a) (bH * kH * bH⁻¹)
      rw [map_mul, map_mul, map_inv]
      rfl
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, hky⟩ := hy
    subst hky
    refine ⟨(bH * k * bH⁻¹ : ↥(C82_wPS7b a)), ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    · change QuotientGroup.mk' (T82_wPS7b a) (bH * k * bH⁻¹) =
        MulAut.conj (QuotientGroup.mk' (T82_wPS7b a) ⟨b, hb⟩) (QuotientGroup.mk' (T82_wPS7b a) k)
      rw [map_mul, map_mul, map_inv]
      rfl

theorem theta82_card_dvd {a : G} {K : Subgroup G} :
    Nat.card (theta82_wPS7b a K) ∣ Nat.card K := by
  have h1 : Nat.card (theta82_wPS7b a K) ∣ Nat.card (K.subgroupOf (C82_wPS7b a)) :=
    Subgroup.card_map_dvd _ (QuotientGroup.mk' (T82_wPS7b a))
  let K' : Subgroup G := (K.subgroupOf (C82_wPS7b a)).map (C82_wPS7b a).subtype
  have h2 : Nat.card (K.subgroupOf (C82_wPS7b a)) = Nat.card K' :=
    (Subgroup.card_map_of_injective (C82_wPS7b a).subtype_injective).symm
  have h3 : Nat.card K' ∣ Nat.card K :=
    Subgroup.card_dvd_of_le (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  rw [h2] at h1
  exact h1.trans h3

theorem card_conjugate (H : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H := by
  unfold CFSG.conjugate
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).toEquiv).symm

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

theorem twoLocal_rank_four_of_orbit (c : Ctx82E3 D) {a : G} {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (hge : 7 ≤ (orbitConjugates (perfectCoreL c a) J).ncard) :
    ∃ (r : ℕ) (L : Subgroup G),
      r.Prime ∧ r ≠ 2 ∧ CFSG.Open.IsTwoLocal L ∧ 4 ≤ CFSG.Open.pRank r L := by
  classical
  obtain ⟨t, A, ht7, hAmem, hAconj, hAinj⟩ := orbit_components_data c hJ hge
  let idx : Fin 7 → Fin t := Fin.castLE ht7
  let Jc : Fin 7 → Subgroup G := fun i => A (idx i)
  have hJmem : ∀ i, Jc i ∈ thetaComponentsAt 3 a := fun i => hAmem (idx i)
  have hJinj : Function.Injective Jc := by
    intro i j hij
    exact Fin.castLE_injective ht7 (hAinj hij)
  have hJconj : ∀ i, ∃ g ∈ perfectCoreL c a, Jc i = CFSG.conjugate (Jc 0) g := by
    intro i
    obtain ⟨bi, hbi, hbi_eq⟩ := hAconj (idx i)
    obtain ⟨b0, hb0, hb0_eq⟩ := hAconj (idx 0)
    refine ⟨b0⁻¹ * bi, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb0) hbi, ?_⟩
    have h0 : Jc 0 = CFSG.conjugate J b0 := hb0_eq
    have hi : Jc i = CFSG.conjugate J bi := hbi_eq
    calc
      Jc i = CFSG.conjugate J bi := hi
      _ = CFSG.conjugate (CFSG.conjugate J b0) (b0⁻¹ * bi) := by
            rw [CFSG.conjugate_conjugate]
            congr 1
            group
      _ = CFSG.conjugate (Jc 0) (b0⁻¹ * bi) := by rw [h0]
  choose g hg hJg using hJconj
  let K : Fin 7 → Subgroup (↥(C82_wPS7b a) ⧸ T82_wPS7b a) := fun i => theta82_wPS7b a (Jc i)
  have hKcomp : ∀ i, IsComponent (K i) := fun i => theta82_isComponent (hJmem i)
  have hKinj : Function.Injective K := by
    intro i j hij
    exact hJinj (theta82_injective (hJmem i) (hJmem j) hij)
  have h3K : ∀ i, ¬ 3 ∣ Nat.card (K i) := by
    obtain ⟨b0, -, hb0eq⟩ := hAconj (idx 0)
    have hcardJ0 : Nat.card (Jc 0) = Nat.card J := by
      change Nat.card (A (idx 0)) = Nat.card J
      rw [hb0eq, card_conjugate]
    have hcardJi : ∀ i, Nat.card (Jc i) = Nat.card J := by
      intro i
      calc
        Nat.card (Jc i) = Nat.card (CFSG.conjugate (Jc 0) (g i)) := by rw [hJg i]
        _ = Nat.card (Jc 0) := card_conjugate _ _
        _ = Nat.card J := hcardJ0
    intro i h3i
    have hdiv : Nat.card (K i) ∣ Nat.card (Jc i) := by
      change Nat.card (theta82_wPS7b a (Jc i)) ∣ Nat.card (Jc i)
      exact theta82_card_dvd
    exact h3 (by rw [← hcardJi i]; exact h3i.trans hdiv)
  have hKq : ∀ i, CFSG.Open.IsQuasisimple (K i) := fun i =>
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥(K i))).mp (hKcomp i).1
  have hJle : ∀ i, Jc i ≤ C82_wPS7b a := fun i =>
    (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp (hJmem i)).1
  have hJ0proper : Jc 0 ≠ ⊤ := by
    intro htop
    have h1top : Jc 1 = ⊤ := by
      rw [hJg 1, htop]
      simp [CFSG.conjugate]
    have hKeq : K 1 = K 0 := by
      change theta82_wPS7b a (Jc 1) = theta82_wPS7b a (Jc 0)
      rw [h1top, htop]
    have hJeq : Jc 1 = Jc 0 := theta82_injective (hJmem 1) (hJmem 0) hKeq
    have hfin : (1 : Fin 7) = 0 := hJinj hJeq
    exact Fin.zero_ne_one hfin.symm
  have hKJ0 : IsKGroup ↥(Jc 0) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isKGroup_of_ne_top_of_isKProper c.kProper hJ0proper
  have hK0 : IsKGroup ↥(K 0) := by
    let θ0 : ↥(Jc 0) →* (↥(C82_wPS7b a) ⧸ T82_wPS7b a) :=
      (QuotientGroup.mk' (T82_wPS7b a)).comp (Subgroup.inclusion (hJle 0))
    have hθ0range : θ0.range = K 0 := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr y.2)
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    have hquot : IsKGroup (↥(Jc 0) ⧸ θ0.ker) := hKJ0.quotient θ0.ker
    have e : (↥(Jc 0) ⧸ θ0.ker) ≃* ↥(K 0) := by
      rw [← hθ0range]
      exact QuotientGroup.quotientKerEquivRange θ0
    exact IsKGroup.of_mulEquiv hquot e.symm
  have hZ0 : IsPGroup 2 (Subgroup.center (K 0)) :=
    center_isPGroup_two_of_quasisimple_isKGroup (hKq 0)
      (CFSG.KCore.KGroupAllSimple.kGroupNonab hK0) (h3K 0)
  obtain ⟨f, hf⟩ := suzukiModel_centerQuotient_of_quasisimple_isKGroup (hKq 0)
    (CFSG.KCore.KGroupAllSimple.kGroupNonab hK0) (h3K 0)
  obtain ⟨T0, y0, r, hr, hr2, hy0ord, hy0norm, hy0nc⟩ :=
    exists_borel_lift_of_suzuki_quotient (hKq 0) hZ0 hf
  let q : Fin 7 → (↥(C82_wPS7b a) ⧸ T82_wPS7b a) := fun i =>
    QuotientGroup.mk' (T82_wPS7b a) ⟨(g i)⁻¹, Subgroup.inv_mem _ ((perfectCoreL_le c a (hg i)).2)⟩
  have hKmap : ∀ i, K i = (K 0).map (MulAut.conj (q i)).toMonoidHom := by
    intro i
    change theta82_wPS7b a (Jc i) = _
    rw [hJg i]
    unfold CFSG.conjugate
    exact theta82_conj (a := a) (K := Jc 0) (b := (g i)⁻¹)
      (Subgroup.inv_mem _ ((perfectCoreL_le c a (hg i)).2)) (hJle 0)
  let eK : (i : Fin 7) → (↥(K 0) ≃* ↥(K i)) := fun i =>
    (Subgroup.equivMapOfInjective (K 0) (MulAut.conj (q i)).toMonoidHom
      (MulAut.conj (q i)).injective).trans (MulEquiv.subgroupCongr (hKmap i).symm)
  let T : (i : Fin 7) → Sylow 2 (K i) := fun i =>
    Sylow.mapSurjective (f := (eK i).toMonoidHom) (eK i).surjective T0
  let y : (i : Fin 7) → K i := fun i => eK i y0
  have hyord : ∀ i, orderOf (y i) = r := by
    intro i
    exact (MulEquiv.orderOf_eq (eK i) y0).trans hy0ord
  have hync : ∀ i, y i ∉ Subgroup.center (K i) := by
    intro i hy
    have hmap : (Subgroup.center (K 0)).map (eK i).toMonoidHom = Subgroup.center (K i) :=
      Subgroup.map_center_eq (eK i)
    have hiff := Subgroup.mem_map_iff_mem (f := (eK i).toMonoidHom) (eK i).injective
      (K := Subgroup.center (K 0)) (x := y0)
    rw [hmap] at hiff
    exact hy0nc (hiff.mp hy)
  have hTcoe : ∀ i, (T i : Subgroup (K i)) = (T0 : Subgroup (K 0)).map (eK i).toMonoidHom := by
    intro i
    exact Sylow.coe_mapSurjective (f := (eK i).toMonoidHom) (eK i).surjective T0
  have hynormK : ∀ i, y i ∈ Subgroup.normalizer (T i : Subgroup (K i)) := by
    intro i
    have hnorm : y i ∈ Subgroup.normalizer
        ((T0 : Subgroup (K 0)).map (eK i).toMonoidHom : Set (K i)) := by
      rw [← Subgroup.map_normalizer_eq_of_bijective (T0 : Subgroup (K 0)) (eK i).bijective]
      exact Subgroup.mem_map_of_mem _ hy0norm
    rw [← hTcoe i] at hnorm
    exact hnorm
  have hyq : ∀ i, orderOf (((y i : K i) : K i ⧸ Subgroup.center (K i))) = r := by
    haveI : Fact r.Prime := ⟨hr⟩
    intro i
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← hyord i, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hync i
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨V, hVle, hVab, hVcard⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.exists_elemAbelian_of_component_family
      hr K hKcomp hKinj (fun i => (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a)) (fun i => (y i).2) hyq
  have hVrank : Group.rank ↥V = 7 :=
    CFSG.AGLEmbedding.rank_eq_of_elementary hr hVab.1.is_comm.comm
      (fun x => Subtype.ext (hVab.2 x x.2)) hVcard
  let Tsub : Fin 7 → Subgroup (↥(C82_wPS7b a) ⧸ T82_wPS7b a) := fun i =>
    (T i : Subgroup (K i)).map (K i).subtype
  have hTsubP : ∀ i, IsPGroup 2 (Tsub i) := fun i => (T i).isPGroup'.map _
  have hTsubK : ∀ i, Tsub i ≤ K i := fun i => Subgroup.map_subtype_le _
  have hTsubNe : ∀ i, Tsub i ≠ ⊥ := by
    intro i hbot
    have hEven : Even (Nat.card (K i)) := by
      have hnotodd : ¬ Odd (Nat.card (K i)) :=
        CFSG.Quasithin.B69.not_odd_card_quasisimple (hKq i)
      exact Nat.not_odd_iff_even.mp hnotodd
    have hTiNe : (T i : Subgroup (K i)) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (T i) (even_iff_two_dvd.mp hEven)
    exact hTiNe ((Subgroup.map_eq_bot_iff_of_injective _ (K i).subtype_injective).mp hbot)
  have hKcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥ := by
    intro i j hij
    exact (CFSG.LocalCores.distinct_components_commute (hKcomp i) (hKcomp j)).resolve_left
      (fun h => hij (hKinj h))
  have hTcomm : ∀ i j, i ≠ j → ⁅Tsub i, Tsub j⁆ = ⊥ := by
    intro i j hij
    exact le_bot_iff.mp
      ((Subgroup.commutator_mono (hTsubK i) (hTsubK j)).trans (le_of_eq (hKcomm i j hij)))
  let Tstar : Subgroup (↥(C82_wPS7b a) ⧸ T82_wPS7b a) := ⨆ i, Tsub i
  have hTstarP : IsPGroup 2 Tstar :=
    CFSG.Quasithin.C2Push.isPGroup_iSup_of_pairwise_commute Tsub hTsubP hTcomm
  have hTstarNe : Tstar ≠ ⊥ := by
    intro hbot
    exact hTsubNe 0 (le_bot_iff.mp (hbot ▸ le_iSup Tsub 0))
  have hy_norm_Tstar : ∀ i, (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a) ∈
      Subgroup.normalizer (Tstar : Set (↥(C82_wPS7b a) ⧸ T82_wPS7b a)) := by
    intro i
    have hmap :
        Tstar.map (MulAut.conj (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a)).toMonoidHom = Tstar := by
      change (⨆ j, Tsub j).map (MulAut.conj (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a)).toMonoidHom =
        ⨆ j, Tsub j
      rw [Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      by_cases h : j = i
      · subst j
        have hyTsub : (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a) ∈
            Subgroup.normalizer (Tsub i : Set (↥(C82_wPS7b a) ⧸ T82_wPS7b a)) :=
          Subgroup.le_normalizer_map (K i).subtype
            (Subgroup.mem_map_of_mem _ (hynormK i))
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyTsub
      · have hcent : K i ≤ Subgroup.centralizer (K j : Set (↥(C82_wPS7b a) ⧸ T82_wPS7b a)) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hKcomm i j (fun hij => h hij.symm))
        have hcomm : ∀ t ∈ Tsub j,
            Commute (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a) t := by
          intro t ht
          exact (Subgroup.mem_centralizer_iff.mp (hcent (y i).2) t (hTsubK j ht)).symm
        exact CFSG.Timmesfeld.ARS.conjSub_of_forall_commute hcomm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  let Kpre : Subgroup ↥(C82_wPS7b a) := Tstar.comap (QuotientGroup.mk' (T82_wPS7b a))
  let T2 : Sylow 2 Kpre := default
  let T2sub : Subgroup ↥(C82_wPS7b a) := (T2 : Subgroup Kpre).map Kpre.subtype
  have hT2subP : IsPGroup 2 T2sub := by
    change IsPGroup 2 ((T2 : Subgroup Kpre).map Kpre.subtype)
    exact (T2).isPGroup'.map _
  have hKpreMap : Kpre.map (QuotientGroup.mk' (T82_wPS7b a)) = Tstar :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Tstar
  let ψ : Kpre →* Tstar :=
    ((QuotientGroup.mk' (T82_wPS7b a)).comp Kpre.subtype).codRestrict Tstar (fun x => x.2)
  have hψsurj : Function.Surjective ψ := by
    intro x
    have hx : (x : ↥(C82_wPS7b a) ⧸ T82_wPS7b a) ∈ Kpre.map (QuotientGroup.mk' (T82_wPS7b a)) := by
      rw [hKpreMap]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hT2top : (T2 : Subgroup Kpre).map ψ = ⊤ := by
    have h := (T2.mapSurjective hψsurj).is_maximal' (Q := ⊤)
      (hTstarP.to_subgroup ⊤) le_top
    simpa [Sylow.coe_mapSurjective] using h.symm
  have hT2map : T2sub.map (QuotientGroup.mk' (T82_wPS7b a)) = Tstar := by
    have h2 : T2sub.map (QuotientGroup.mk' (T82_wPS7b a)) =
        ((T2 : Subgroup Kpre).map ψ).map Tstar.subtype := by
      change (((T2 : Subgroup Kpre).map Kpre.subtype).map (QuotientGroup.mk' (T82_wPS7b a))) =
        ((T2 : Subgroup Kpre).map ψ).map Tstar.subtype
      rw [Subgroup.map_map]
      conv_rhs => rw [Subgroup.map_map]
      rfl
    rw [h2, hT2top, Subgroup.map_top, Subgroup.range_subtype]
  have hT2Ne : T2sub ≠ ⊥ := by
    intro hbot
    have hmapbot : T2sub.map (QuotientGroup.mk' (T82_wPS7b a)) = ⊥ := by
      rw [hbot, Subgroup.map_bot]
    rw [hT2map] at hmapbot
    exact hTstarNe hmapbot
  let H' : Subgroup ↥(C82_wPS7b a) := Subgroup.normalizer (T2sub : Set ↥(C82_wPS7b a))
  let N' : Subgroup H' := (T82_wPS7b a).subgroupOf H'
  let φ : H' →* (↥(C82_wPS7b a) ⧸ T82_wPS7b a) :=
    (QuotientGroup.mk' (T82_wPS7b a)).comp H'.subtype
  have hφker : φ.ker = N' := by
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr
        ((QuotientGroup.eq_one_iff (x : ↥(C82_wPS7b a))).mp hx)
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : ↥(C82_wPS7b a))).mpr
        (Subgroup.mem_subgroupOf.mp hx)
  haveI : N'.Normal := inferInstance
  have hφrange : φ.range = H'.map (QuotientGroup.mk' (T82_wPS7b a)) := by
    rw [show φ = (QuotientGroup.mk' (T82_wPS7b a)).comp H'.subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hTstar_le_H'map : Tstar ≤ H'.map (QuotientGroup.mk' (T82_wPS7b a)) := by
    rw [← hT2map]
    exact Subgroup.map_mono (Subgroup.le_normalizer : T2sub ≤ H')
  have hy_mem_H' : ∀ i, (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a) ∈
      H'.map (QuotientGroup.mk' (T82_wPS7b a)) := by
    intro i
    obtain ⟨gi, hgi⟩ :=
      QuotientGroup.mk'_surjective (T82_wPS7b a) (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a)
    have hgi_norm : (QuotientGroup.mk' (T82_wPS7b a)) gi ∈
        Subgroup.normalizer (Tstar : Set (↥(C82_wPS7b a) ⧸ T82_wPS7b a)) := by
      rw [hgi]
      exact hy_norm_Tstar i
    have hAsyl : CFSG.ABGLocalTools.IsSylowOf 2 T2sub Kpre := ⟨T2, rfl⟩
    have hAle : T2sub ≤ Kpre := Subgroup.map_subtype_le _
    obtain ⟨n, hn, m, hm, hgm⟩ :=
      CFSG.GroupTheory.exists_mul_mem_comap_and_normalizer
        (p := 2) (f := QuotientGroup.mk' (T82_wPS7b a)) (Astar := Tstar) (A := T2sub)
        hAle hAsyl hgi_norm
    have hfn : (QuotientGroup.mk' (T82_wPS7b a)) n ∈ Tstar := hn
    have hfnH : (QuotientGroup.mk' (T82_wPS7b a)) n ∈ H'.map (QuotientGroup.mk' (T82_wPS7b a)) :=
      hTstar_le_H'map hfn
    have hfm : (QuotientGroup.mk' (T82_wPS7b a)) m ∈ H'.map (QuotientGroup.mk' (T82_wPS7b a)) :=
      Subgroup.mem_map_of_mem _ hm
    rw [← hgi, hgm, map_mul]
    exact Subgroup.mul_mem _ hfnH hfm
  have hclosure_le : Subgroup.closure (Set.range (fun i => (y i : ↥(C82_wPS7b a) ⧸ T82_wPS7b a))) ≤
      H'.map (QuotientGroup.mk' (T82_wPS7b a)) :=
    Subgroup.closure_le _ |>.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hy_mem_H' i)
  have hVrange : V ≤ φ.range := by
    rw [hφrange]
    exact hVle.trans hclosure_le
  let eH : (H' ⧸ N') ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hφker).symm.trans
      (QuotientGroup.quotientKerEquivRange φ)
  let ι : (H' ⧸ N') →* (↥(C82_wPS7b a) ⧸ T82_wPS7b a) :=
    φ.range.subtype.comp eH.toMonoidHom
  have hιinj : Function.Injective ι :=
    φ.range.subtype_injective.comp eH.injective
  have hιrange : ι.range = φ.range := by
    rw [show ι = φ.range.subtype.comp eH.toMonoidHom from rfl, MonoidHom.range_comp]
    have h : eH.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr eH.surjective
    rw [h, Subgroup.map_top, Subgroup.range_subtype]
  have hVrangeι : V ≤ ι.range := by rw [hιrange]; exact hVrange
  let Y' : Subgroup (H' ⧸ N') := V.comap ι
  have hY'map : Y'.map ι = V := Subgroup.map_comap_eq_self hVrangeι
  have hY'rank : Group.rank ↥Y' = 7 := by
    let eY : ↥Y' ≃* ↥V := (Subgroup.equivMapOfInjective Y' ι hιinj).trans
      (MulEquiv.subgroupCongr hY'map)
    rw [Group.rank_congr eY, hVrank]
  have hY'p : IsPGroup r Y' := by
    let eY : ↥Y' ≃* ↥V := (Subgroup.equivMapOfInjective Y' ι hιinj).trans
      (MulEquiv.subgroupCongr hY'map)
    have hcardY : Nat.card ↥Y' = r ^ 7 := by
      rw [Nat.card_congr eY.toEquiv]
      simpa using hVcard
    exact IsPGroup.of_card (n := 7) hcardY
  have hH'rank : 3 < CFSG.Open.pRank r H' :=
    CFSG.AGLEmbedding.lt_pRank_of_quotient
      CFSG.AGLEmbedding.thompsonNormalAbelianGen (p := r) hr2
      (G := ↥(C82_wPS7b a)) (H := H') (L := H') (N := N') hY'p
      (Subgroup.map_subtype_le _) (r := 3) (by rw [hY'rank]; norm_num)
  let HG : Subgroup G := H'.map (C82_wPS7b a).subtype
  have hH'pRank_eq : CFSG.Open.pRank r H' = CFSG.Open.pRank r HG :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective r hr
      (C82_wPS7b a).subtype (C82_wPS7b a).subtype_injective H').symm
  have hH'rankHG : 3 < CFSG.Open.pRank r HG := by
    rwa [← hH'pRank_eq]
  let TG : Subgroup G := T2sub.map (C82_wPS7b a).subtype
  have hTGp : IsPGroup 2 TG := hT2subP.map _
  have hTGne : TG ≠ ⊥ := by
    intro hbot
    apply hT2Ne
    exact (Subgroup.map_eq_bot_iff_of_injective _ (C82_wPS7b a).subtype_injective).mp hbot
  let L : Subgroup G := Subgroup.normalizer (TG : Set G)
  have hLtwo : CFSG.Open.IsTwoLocal L := ⟨TG, hTGne, hTGp, rfl⟩
  have hHGL : HG ≤ L := by
    rintro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.le_normalizer_map (C82_wPS7b a).subtype (Subgroup.mem_map_of_mem _ hh)
  have hHGrankL : CFSG.Open.pRank r HG ≤ CFSG.Open.pRank r L :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hHGL
  refine ⟨r, L, hr, hr2, hLtwo, ?_⟩
  omega

theorem suzuki_orbit_rank_assembly''
    (c : Ctx82E3 D)
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
    (hge : 7 ≤ (orbitConjugates (perfectCoreL c a) J).ncard) :
    False := by
  obtain ⟨r, L, hr, hr2, hL, hrank⟩ := twoLocal_rank_four_of_orbit c hJ h3 hge
  have hle : CFSG.Open.pRank r L ≤ 3 := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank r hr hr2 L hL
    rwa [c.rank] at h
  omega

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

theorem threePrimeComponent_orbit_lt_seven'
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
    (hge : 7 ≤ (orbitConjugates (perfectCoreL c a) J).ncard) :
    False  :=
  suzuki_orbit_rank_assembly'' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ hP2 hP3 hP5
    hJ h3 hge

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
