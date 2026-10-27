module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmGaps
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinZ
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.CentralQuotientCoprime
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Dickson.Bal207.CoreFreeInner
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.Quasithin.Background.F2Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import Certificates.Data.U62Rank.Check

public section
namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact
open CFSG.LocalAnalysis.GLTheoremA.HSubT
open CFSG.LocalAnalysis.GLTheoremA.CatB

open scoped commutatorElement

private theorem omegaPlusCompRes_holds : OmegaPlusCompRes :=
  omegaPlusCompRes_of_residuals
    (omegaCentDecomp_of_gaps center_aglOm8_eq_bot omegaUnitaryInOm8_holds
      omegaOrthRank2Solvable_holds omegaOrthRank1U4_holds) guBlockFacts_holds

private theorem catalogIs_rplus_of_card {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs (OrthRest.RPlus K 4)
      CFSG.LocalAnalysis.GLTheoremA.S9.isD4two := by
  have hscm : StatedClassicalModel (OrthRest.RPlus K 4) .POmegaPlus 4 2 1 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, K, inferInstance, inferInstance, ?_, ?_⟩
    · simpa using hK
    · exact ⟨MulEquiv.refl _⟩
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ :=
    exists_D_of_statedClassicalModel_POmegaPlus hscm
  refine ⟨.lie ⟨.D 4 q, hv⟩, ?_, ⟨e⟩⟩
  show q.card = 2
  rw [TauCeti.PrimePower.card_def, hqp, hqf]
  norm_num

private theorem x_not_mem_L {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hBs : IsElemAbelian 3 Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    x ∉ L := by
  intro hxLin
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxZ : (⟨x, hxLin⟩ : ↥L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxcent l l.2
  obtain ⟨k, hk⟩ := hZ2 ⟨⟨x, hxLin⟩, hxZ⟩
  have hxpow : x ^ 3 = 1 := by
    have hxBs : x ∈ Bs := by
      have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [hBL]
        exact Subgroup.mem_zpowers x
      exact this.1
    exact hBs.2 x hxBs
  have hx3 : orderOf x = 3 := orderOf_eq_prime hxpow hx1
  have hk' : (⟨x, hxLin⟩ : ↥L) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf (⟨x, hxLin⟩ : ↥L) ∣ 2 ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr hk'
  have h3x : orderOf (⟨x, hxLin⟩ : ↥L) = 3 := by
    rw [Subgroup.orderOf_mk x hxLin]
    exact hx3
  rw [h3x] at hdvd
  have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
  norm_num at h32

private theorem exists_element_of_inf {G : Type} [Group G] {Bs L D : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) :
    ∃ e : G, e ∈ Bs ∧ e ∈ L ∧ e ∈ D ∧ e ≠ 1 ∧ e ^ 3 = 1 := by
  classical
  let E : Subgroup G := Bs ⊓ L
  have hErelBs : E.relIndex Bs = 3 := by
    have h := Subgroup.relIndex_mul_card (H := E) (K := Bs)
    rw [inf_eq_left.mpr (show E ≤ Bs from inf_le_left), hcardE, hcard] at h
    have hmul : E.relIndex Bs * 3 ^ 4 = 3 * 3 ^ 4 := by
      rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3 ^ 4) hmul
  have hErelD_le : E.relIndex D ≤ 3 := by
    have h := Subgroup.relIndex_le_of_le_right (H := E) (K := D) (L := Bs) hDB (by
      rw [hErelBs]; norm_num)
    rwa [hErelBs] at h
  have hDEne : E ⊓ D ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(E ⊓ D) = 1 := by rw [hbot, Subgroup.card_bot]
    have hmul := Subgroup.relIndex_mul_card (H := E) (K := D)
    rw [hcard, mul_one, hDcard] at hmul
    have hle : E.relIndex D ≤ 3 := hErelD_le
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E ⊓ D, e ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton ↥(E ⊓ D) := ⟨fun a b => Subtype.ext (by
      rw [h a a.2, h b b.2])⟩
    apply hDEne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, hy⟩ : ↥(E ⊓ D)) = 1 := Subsingleton.elim _ _
    have : y = 1 := congrArg Subtype.val h1
    simpa using this
  exact ⟨e, he.1.1, he.1.2, he.2, he1, hBs.2 e he.1.1⟩

private theorem not_mem_zpowers_of_not_mem {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x e : G}
    (hxL : x ∉ L) (heL : e ∈ L)
    (hxorder : orderOf x = 3) (heorder : orderOf e = 3) :
    e ∉ Subgroup.zpowers x := by
  intro hmem
  have heq : Subgroup.zpowers e = Subgroup.zpowers x := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
    rw [Nat.card_zpowers, Nat.card_zpowers, heorder, hxorder]
  have hxL' : x ∈ L := Subgroup.zpowers_le.mpr heL (heq ▸ Subgroup.mem_zpowers x)
  exact hxL hxL'

private theorem eq_sup_zpowers_of_card_nine {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {x e : G}
    (hDcard : Nat.card D = 3 ^ 2)
    (hxD : x ∈ D) (heD : e ∈ D) (hxorder : orderOf x = 3)
    (hnotmem : e ∉ Subgroup.zpowers x) :
    D = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
  · have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
      rw [lt_iff_le_and_ne]
      refine ⟨le_sup_left, ?_⟩
      intro h
      have hesup : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers e :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
      rw [← h] at hesup
      exact hnotmem hesup
    have hcard_gt : 3 < Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) := by
      have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, hxorder]
      have hlecard : Nat.card ↥(Subgroup.zpowers x) ≤
          Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion le_sup_left)
          (Subgroup.inclusion_injective le_sup_left)
      have hne : Nat.card ↥(Subgroup.zpowers x) ≠
          Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) := by
        intro hc
        have hEq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
          apply Subgroup.eq_of_le_of_card_ge le_sup_left
          rw [← hc]
        exact hlt.ne hEq
      omega
    have hcard_dvd : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) ∣ 9 := by
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers e ≤ D :=
        sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr heD)
      have h := Subgroup.card_dvd_of_le hle
      rwa [hDcard] at h
    have hcard9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) = 9 := by
      have hle9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) ≤ 9 :=
        Nat.le_of_dvd (by norm_num) hcard_dvd
      set c := Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers e) with hc
      have hcgt : 3 < c := hcard_gt
      have hcle : c ≤ 9 := hle9
      have hcdvd : c ∣ 9 := hcard_dvd
      interval_cases c <;> norm_num at hcdvd
      norm_num
    rw [hcard9, hDcard]
    norm_num

private theorem not_mem_center_of_isPGroup_two {G : Type} [Group G] {L : Subgroup G}
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    {e : G} (heL : e ∈ L) (he1 : e ≠ 1) (he3 : e ^ 3 = 1) :
    (⟨e, heL⟩ : ↥L) ∉ Subgroup.center L := by
  intro hz
  obtain ⟨k, hk⟩ := hZ2 ⟨⟨e, heL⟩, hz⟩
  have hk' : (⟨e, heL⟩ : ↥L) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf (⟨e, heL⟩ : ↥L) ∣ 2 ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr hk'
  have h3 : orderOf (⟨e, heL⟩ : ↥L) = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa using he3
    · intro h
      apply he1
      simpa using congrArg Subtype.val h
  rw [h3] at h2
  have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h2
  norm_num at h32

private theorem centralizer_singleton_subgroupOf_eq_of_eq_sup_zpowers {G : Type} [Group G]
    {L D : Subgroup G} {x e : G} (hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers e)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (heD : e ∈ D) :
    (Subgroup.centralizer ({e} : Set G)).subgroupOf L =
      (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L := by
  ext m
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hm
    refine ⟨m.2, ?_⟩
    change (m : G) ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hmx : (m : G) * x = x * (m : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx m.2)
    have hme : (m : G) * e = e * (m : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hm
    have hAle : Subgroup.zpowers x ⊔ Subgroup.zpowers e ≤
        Subgroup.centralizer ({(m : G)} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hmx.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hme.symm
    rw [hDgen] at hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAle hd)
  · intro hm
    exact Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact heD) hm.2


private theorem exists_ambient_data {G : Type} [Group G] [Finite G] {Bs L D : Subgroup G}
    {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D) :
    ∃ (e : G) (heL : e ∈ L),
      e ∈ Bs ∧ e ∈ D ∧ e ≠ 1 ∧ e ^ 3 = 1 ∧ orderOf e = 3 ∧ x ∉ L ∧
      D = Subgroup.zpowers x ⊔ Subgroup.zpowers e ∧
      (⟨e, heL⟩ : ↥L) ∉ Subgroup.center L ∧
      (Subgroup.centralizer ({e} : Set G)).subgroupOf L =
        (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L := by
  have hxL := x_not_mem_L hZ2 hx1 hLx hBs hBL
  have hx3 : x ^ 3 = 1 := by
    have hxBs : x ∈ Bs := by
      have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [hBL]
        exact Subgroup.mem_zpowers x
      exact this.1
    exact hBs.2 x hxBs
  have hxorder : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨e, heBs, heL, heD, he1, he3⟩ := exists_element_of_inf hBs hcard hcardE hDB hDcard
  have heorder : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hnotmem := not_mem_zpowers_of_not_mem hxL heL hxorder heorder
  have hDgen := eq_sup_zpowers_of_card_nine hDcard hxD heD hxorder hnotmem
  have heZ := not_mem_center_of_isPGroup_two hZ2 heL he1 he3
  have hMK := centralizer_singleton_subgroupOf_eq_of_eq_sup_zpowers hDgen hLx heD
  exact ⟨e, heL, heBs, heD, he1, he3, heorder, hxL, hDgen, heZ, hMK⟩

private theorem aut_data {G : Type} [Group G] {K : Type} [Field K]
    {L : Subgroup G} (hperf : commutator ↥L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) {e : G} (heL : e ∈ L)
    (heZ : (⟨e, heL⟩ : ↥L) ∉ Subgroup.center L) (he3 : e ^ 3 = 1) :
    ∃ t : OrthRest.RPlus K 4,
      t = (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) ⟨e, heL⟩ ∧
      t ≠ 1 ∧ t ^ 3 = 1 ∧ orderOf t = 3 ∧ (MulAut.conj t) ^ 3 = 1 ∧
        MulAut.conj t ≠ 1 := by
  let π : ↥L →* OrthRest.RPlus K 4 :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  let t : OrthRest.RPlus K 4 := π ⟨e, heL⟩
  have ht1 : t ≠ 1 := by
    intro ht
    apply heZ
    have hπ : π ⟨e, heL⟩ = 1 := ht
    have : (QuotientGroup.mk' (Subgroup.center L)) ⟨e, heL⟩ = 1 := θ.injective (by
      simpa [π] using hπ)
    exact (QuotientGroup.eq_one_iff _).mp this
  have ht3 : t ^ 3 = 1 := by
    rw [show t = π ⟨e, heL⟩ from rfl, ← map_pow, show (⟨e, heL⟩ : ↥L) ^ 3 = 1 from by
      apply Subtype.ext
      simpa using he3, map_one]
  have htorder : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hα3 : (MulAut.conj t) ^ 3 = 1 := by
    rw [← map_pow (MulAut.conj : OrthRest.RPlus K 4 →* MulAut (OrthRest.RPlus K 4)) t 3,
      ht3, map_one]
  have hα1 : MulAut.conj t ≠ 1 := by
    intro h
    have htcent : t ∈ Subgroup.center (OrthRest.RPlus K 4) :=
      (CFSG.Quasithin.Amalgam.Completion.conj_eq_one_iff (G := OrthRest.RPlus K 4)).1 h
    have hcenterbot : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
      @Group.IsPerfect.center_quotient_center_eq_bot ↥L _ ⟨hperf⟩
    have hsym : θ.symm t ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [← Subgroup.map_center_eq θ.symm]
      exact Subgroup.mem_map_of_mem θ.symm.toMonoidHom htcent
    rw [hcenterbot] at hsym
    have htone : t = 1 := θ.symm.injective (by simpa using hsym)
    rw [htone] at htorder
    norm_num at htorder
  exact ⟨t, rfl, ht1, ht3, htorder, hα3, hα1⟩

private theorem map_centralizer_subgroupOf_le_fixSub {G : Type} [Group G]
    {K : Type} [Field K] {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) {e : G} (heL : e ∈ L) :
    Subgroup.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      ((Subgroup.centralizer ({e} : Set G)).subgroupOf L) ≤
      fixSub (MulAut.conj ((θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
        ⟨e, heL⟩)) := by
  let π : ↥L →* OrthRest.RPlus K 4 :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  change Subgroup.map π ((Subgroup.centralizer ({e} : Set G)).subgroupOf L) ≤
    fixSub (MulAut.conj (π ⟨e, heL⟩))
  rw [fixSub_conj]
  rintro r ⟨m, hm, rfl⟩
  have hmc : (m : ↥L) * ⟨e, heL⟩ = ⟨e, heL⟩ * m := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff (g := e) (k := (m : G))).mp
      (Subgroup.mem_subgroupOf.mp hm)
  rw [Subgroup.mem_centralizer_singleton_iff]
  show π m * π ⟨e, heL⟩ = π ⟨e, heL⟩ * π m
  rw [← map_mul, ← map_mul, hmc]

private theorem fixSub_le_map_centralizer_subgroupOf {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hZ2 : IsPGroup 2 (Subgroup.center L)) {e : G} (heL : e ∈ L) (he3 : e ^ 3 = 1) :
    fixSub (MulAut.conj ((θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      ⟨e, heL⟩)) ≤
    Subgroup.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      ((Subgroup.centralizer ({e} : Set G)).subgroupOf L) := by
  let π : ↥L →* OrthRest.RPlus K 4 :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπsurj : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hZc : Subgroup.center L ≤ Subgroup.center ↥L := le_rfl
  have hcopZ : ¬ 3 ∣ Nat.card (Subgroup.center L) := by
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hZ2
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (h3.trans hn)
    norm_num at h32
  have hx3' : (⟨e, heL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using he3)
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcopZ
  change fixSub (MulAut.conj (π ⟨e, heL⟩)) ≤
    Subgroup.map π ((Subgroup.centralizer ({e} : Set G)).subgroupOf L)
  rw [fixSub_conj]
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff] at hr
  obtain ⟨c, rfl⟩ := hπsurj r
  have hq : (QuotientGroup.mk' (Subgroup.center L)) c *
      (QuotientGroup.mk' (Subgroup.center L)) ⟨e, heL⟩ =
      (QuotientGroup.mk' (Subgroup.center L)) ⟨e, heL⟩ *
      (QuotientGroup.mk' (Subgroup.center L)) c := by
    apply θ.injective
    rw [map_mul, map_mul]
    exact hr
  have hqeq : ((c * ⟨e, heL⟩ * c⁻¹ : ↥L) : ↥L ⧸ Subgroup.center L) =
      ((⟨e, heL⟩ : ↥L) : ↥L ⧸ Subgroup.center L) := by
    calc ((c * ⟨e, heL⟩ * c⁻¹ : ↥L) : ↥L ⧸ Subgroup.center L)
        = (QuotientGroup.mk' (Subgroup.center L)) c *
            (QuotientGroup.mk' (Subgroup.center L)) ⟨e, heL⟩ *
            ((QuotientGroup.mk' (Subgroup.center L)) c)⁻¹ := by
          show (QuotientGroup.mk' (Subgroup.center L)) (c * ⟨e, heL⟩ * c⁻¹) = _
          rw [map_mul, map_mul, map_inv]
      _ = (QuotientGroup.mk' (Subgroup.center L)) ⟨e, heL⟩ := by rw [hq]; group
      _ = ((⟨e, heL⟩ : ↥L) : ↥L ⧸ Subgroup.center L) := rfl
  have hce : c * ⟨e, heL⟩ * c⁻¹ = ⟨e, heL⟩ := by
    refine CFSG.GroupTheory.eq_of_mk_eq_of_pow_eq_one_of_coprime hZc hcop ?_ hx3' hqeq
    rw [conj_pow, hx3']
    group
  have hceG : (c : G) * e = e * (c : G) := congrArg Subtype.val (by
    calc c * ⟨e, heL⟩ = (c * ⟨e, heL⟩ * c⁻¹) * c := by group
      _ = ⟨e, heL⟩ * c := by rw [hce])
  exact ⟨c, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hceG), rfl⟩

private theorem component_le_centralizer {G : Type} [Group G] {L D J : Subgroup G}
    {e : G}
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (heD : e ∈ D) :
    J ≤ Subgroup.centralizer ({e} : Set G) := by
  refine hJ.1.trans ?_
  exact inf_le_right.trans (Subgroup.centralizer_le (by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact heD))

private theorem component_facts {G : Type} [Group G] {L D J : Subgroup G}
    {e : G}
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hJCe : J ≤ Subgroup.centralizer ({e} : Set G))
    (hMK : (Subgroup.centralizer ({e} : Set G)).subgroupOf L =
      (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L) :
    J.subgroupOf L ≤ (Subgroup.centralizer ({e} : Set G)).subgroupOf L ∧
    CFSG.Open.IsQuasisimple
      ((J.subgroupOf L).subgroupOf ((Subgroup.centralizer ({e} : Set G)).subgroupOf L)) ∧
    CFSG.Open.IsComponentOf
      ((J.subgroupOf L).subgroupOf ((Subgroup.centralizer ({e} : Set G)).subgroupOf L)) ⊤ := by
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJLM : J.subgroupOf L ≤ (Subgroup.centralizer ({e} : Set G)).subgroupOf L := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hJCe hy
  have hsubK : CFSG.Open.IsSubnormal (J.subgroupOf L)
      ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L) := by
    simpa using CFSG.Open.IsSubnormal.comap L.subtype
      (CFSG.Assembly.isSubnormal_iff_open.mp hJ.2.1)
  have hsubM : CFSG.Open.IsSubnormal (J.subgroupOf L)
      ((Subgroup.centralizer ({e} : Set G)).subgroupOf L) := hMK.symm ▸ hsubK
  have hJLq : CFSG.Open.IsQuasisimple (J.subgroupOf L) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) hJ.2.2
  have hJqM : CFSG.Open.IsQuasisimple
      ((J.subgroupOf L).subgroupOf ((Subgroup.centralizer ({e} : Set G)).subgroupOf L)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJLM) hJLq
  have hJtop : CFSG.Open.IsComponentOf
      ((J.subgroupOf L).subgroupOf ((Subgroup.centralizer ({e} : Set G)).subgroupOf L)) ⊤ := by
    refine ⟨le_top, ?_, hJqM⟩
    rw [← CFSG.Assembly.isSubnormal_iff_open, CFSG.Assembly.IsSubnormal.top_iff]
    exact (CFSG.Assembly.isSubnormal_iff_open.mpr hsubM).subgroupOf
  exact ⟨hJLM, hJqM, hJtop⟩

private theorem ker_comp_subtype_mem_center_and_not_le {G : Type} [Group G]
    {L : Subgroup G} {M JL : Subgroup ↥L}
    {R : Type} [Group R] {π : ↥L →* R}
    (hkerπ : π.ker = Subgroup.center L)
    (hJqM : CFSG.Open.IsQuasisimple (JL.subgroupOf M)) :
    (π.comp M.subtype).ker ≤ Subgroup.center ↥M ∧
      ¬ JL.subgroupOf M ≤ (π.comp M.subtype).ker := by
  have hkerf : (π.comp M.subtype).ker ≤ Subgroup.center ↥M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hzπ : π z.1 = 1 := hz
    have hzL : z.1 ∈ Subgroup.center ↥L := by
      rw [← hkerπ]
      exact hzπ
    exact Subgroup.mem_center_iff.mp hzL w.1
  refine ⟨hkerf, ?_⟩
  intro hle
  have hleZ : JL.subgroupOf M ≤ Subgroup.center ↥M := hle.trans hkerf
  have hcomm : IsMulCommutative ↥(JL.subgroupOf M) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hleZ a.2) (b : ↥M)).symm
  exact not_isMulCommutative_of_quasisimple hJqM hcomm

private theorem map_top_comp_subtype {G : Type} [Group G] {L : Subgroup G}
    {M : Subgroup ↥L}
    {R : Type} [Group R] (π : ↥L →* R) :
    ((⊤ : Subgroup ↥M).map (π.comp M.subtype)) = Subgroup.map π M := by
  ext r
  constructor
  · intro hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨m, -, rfl⟩ := hr
    exact Subgroup.mem_map.mpr ⟨m.1, m.2, rfl⟩
  · intro hr
    rw [Subgroup.mem_map] at hr
    obtain ⟨l, hlM, rfl⟩ := hr
    exact Subgroup.mem_map.mpr ⟨⟨l, hlM⟩, Subgroup.mem_top _, rfl⟩

private theorem isComponentOf_map_top {Y R : Type} [Group Y] [Group R] {A : Subgroup Y}
    {f : Y →* R} (hA : CFSG.Open.IsComponentOf A ⊤)
    (hnotle : ¬ A ≤ f.ker) :
    CFSG.Open.IsComponentOf (A.map f) ((⊤ : Subgroup Y).map f) := by
  refine ⟨Subgroup.map_mono le_top, CFSG.Open.IsSubnormal.map f hA.2.1, ?_⟩
  have hJnative : CFSG.IsQuasisimple ↥A :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥A)).2 hA.2.2
  have himg : CFSG.IsQuasisimple ↥(A.map f) :=
    CFSG.LocalCores.isQuasisimple_map hJnative f hnotle
  exact (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥(A.map f))).1 himg

private theorem catalogIs_u4two_of_component {K : Type} [Field K]
    {A : Subgroup (OrthRest.RPlus K 4)}
    {t : OrthRest.RPlus K 4} (hres : OmegaPlusCompRes)
    (hcatR : CFSG.Yardstones.Md0ec50421ce4.catalogIs (OrthRest.RPlus K 4)
      CFSG.LocalAnalysis.GLTheoremA.S9.isD4two)
    (hα3 : (MulAut.conj t) ^ 3 = 1) (hα1 : MulAut.conj t ≠ 1)
    (hA : CFSG.Open.IsComponentOf A (fixSub (MulAut.conj t))) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs (↥A ⧸ Subgroup.center ↥A)
      CFSG.LocalAnalysis.GLTheoremA.S9.isU4two :=
  hres (OrthRest.RPlus K 4) hcatR (MulAut.conj t) hα3 hα1 ⟨t, rfl⟩ A hA

private theorem ggHasLabel_of_catalogIs_u4two {A : Type} [Group A]
    (h : CFSG.Yardstones.Md0ec50421ce4.catalogIs (A ⧸ Subgroup.center A)
      CFSG.LocalAnalysis.GLTheoremA.S9.isU4two) :
    GGHasLabel ⟨.twA, 3, 1⟩ (A ⧸ Subgroup.center A) := by
  obtain ⟨q, hv, hq2, ⟨eU⟩⟩ := lieIndex_isU4two h
  have hqpow : q.p ^ q.exponent = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq2
  obtain ⟨hqp, hqf⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hqpow
  have hscm : StatedClassicalModel (A ⧸ Subgroup.center A) .PSU 4 2 1 := by
    have h' := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv eU
    rwa [hqp, hqf] at h'
  exact CFSG.StandardType.recipeUnitary_of_statedClassicalModel hscm

private theorem ggHasLabel_of_mulEquiv_centralQuotient {G : Type} [Group G]
    {L : Subgroup G} {J : Subgroup G}
    {M : Subgroup ↥L} {R : Type} [Group R] {f : ↥M →* R}
    (hJL : J ≤ L) (hJLM : J.subgroupOf L ≤ M)
    (hJqM : CFSG.Open.IsQuasisimple ((J.subgroupOf L).subgroupOf M))
    (hkerf : f.ker ≤ Subgroup.center ↥M)
    (hlabel : GGHasLabel ⟨.twA, 3, 1⟩
      ((((J.subgroupOf L).subgroupOf M).map f) ⧸
        Subgroup.center (((J.subgroupOf L).subgroupOf M).map f))) :
    GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J) := by
  obtain ⟨eψ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      (H := ↥((J.subgroupOf L).subgroupOf M))
      (H' := ↥(((J.subgroupOf L).subgroupOf M).map f))
      hJqM.1 (f.subgroupMap ((J.subgroupOf L).subgroupOf M))
      (f.subgroupMap_surjective _) (by
        intro z hz
        have hzR : f (z : ↥M) = 1 := congrArg Subtype.val hz
        have hzker : (z : ↥M) ∈ f.ker := hzR
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp (hkerf hzker) (w : ↥M))
  let eJLq : J ⧸ Subgroup.center J ≃*
      (J.subgroupOf L) ⧸ Subgroup.center (J.subgroupOf L) :=
    QuotientGroup.congr (Subgroup.center J) (Subgroup.center (J.subgroupOf L))
      (Subgroup.subgroupOfEquivOfLe hJL).symm
      (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hJL).symm)
  let eMq : (J.subgroupOf L) ⧸ Subgroup.center (J.subgroupOf L) ≃*
      ((J.subgroupOf L).subgroupOf M) ⧸
        Subgroup.center ((J.subgroupOf L).subgroupOf M) :=
    QuotientGroup.congr (Subgroup.center (J.subgroupOf L))
      (Subgroup.center ((J.subgroupOf L).subgroupOf M))
      (Subgroup.subgroupOfEquivOfLe hJLM).symm
      (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hJLM).symm)
  exact ggHasLabel_of_mulEquiv (eJLq.trans (eMq.trans eψ)).symm hlabel

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem exists_label_of_component_omegaPlus (hK : Nat.card K = 2) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (hperf : commutator ↥L = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J) := by
  classical
  let R := OrthRest.RPlus K 4
  let π : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπsurj : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center L := by
    ext l
    simp [π]
  have hcatR := catalogIs_rplus_of_card hK
  have hres := omegaPlusCompRes_holds
  obtain ⟨e, heL, _, heD, _, he3, _, _, _, heZ, hMK⟩ :=
    exists_ambient_data hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD
  have hJCe := component_le_centralizer hJ heD
  obtain ⟨hJLM, hJqM, hJtop⟩ := component_facts hJ hJCe hMK
  obtain ⟨t, ht, ht1, ht3, htorder, hα3, hα1⟩ := aut_data hperf θ heL heZ he3
  subst t
  let M : Subgroup ↥L := (Subgroup.centralizer ({e} : Set G)).subgroupOf L
  let f : ↥M →* R := π.comp M.subtype
  have hMeq : Subgroup.map π M = fixSub (MulAut.conj (π ⟨e, heL⟩)) :=
    le_antisymm (map_centralizer_subgroupOf_le_fixSub θ heL)
      (fixSub_le_map_centralizer_subgroupOf θ hZ2 heL he3)
  obtain ⟨hkerf, hnotle⟩ :=
    ker_comp_subtype_mem_center_and_not_le (π := π) hkerπ hJqM
  have hcomp : CFSG.Open.IsComponentOf
      (((J.subgroupOf L).subgroupOf M).map f) (fixSub (MulAut.conj (π ⟨e, heL⟩))) := by
    have h := isComponentOf_map_top (A := (J.subgroupOf L).subgroupOf M) hJtop hnotle
    rwa [map_top_comp_subtype (π := π), hMeq] at h
  have hJJ := catalogIs_u4two_of_component hres hcatR hα3 hα1 hcomp
  have hlabel := ggHasLabel_of_catalogIs_u4two hJJ
  exact ggHasLabel_of_mulEquiv_centralQuotient (hJ.1.trans inf_le_left) hJLM hJqM hkerf hlabel
end CFSG.StandardType.E6QTwo
end
