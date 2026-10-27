module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Bar
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.RankThree.PartTwo.Sec5.Bender.Norm
public import CFSG.HardMathSupport.Dickson.I271.ChevPBal
public import CFSG.HardMathSupport.Dickson.I271.I202Full
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterStep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open CFSG.HardMathSupport.Solomon.Coordinator

attribute [local instance] gLAPPrimeCoreOf_normal

theorem twD5BarMap_ker {G : Type} [Group G] (b₂ : G) :
    (twD5BarMap b₂).ker =
      (primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂) :=
  QuotientGroup.ker_mk' _

theorem glaPComponent_twD5BarSub_top {G : Type} [Group G] [Finite G] {b₂ : G}
    {L : Subgroup G} (hL : GLAPComponent 3 ⊤ (L.subgroupOf (centralizerBTwo b₂))) :
    GLAPComponent 3 ⊤ (twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂))) := by
  have hcopO : Nat.Coprime 3 (Nat.card (primeCoreCentralizerBTwo b₂)) := by
    change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥(centralizerBTwo b₂)).map
      (centralizerBTwo b₂).subtype))
    rw [Subgroup.card_map_of_injective (centralizerBTwo b₂).subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥(centralizerBTwo b₂)
  have hcard : Nat.card ↥((primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂)) =
      Nat.card (primeCoreCentralizerBTwo b₂) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  have hker : Nat.Coprime 3 (Nat.card ↥(⊤ ⊓ (twD5BarMap b₂).ker)) := by
    rw [twD5BarMap_ker, top_inf_eq, hcard]
    exact hcopO
  have hmain := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map Nat.prime_three
    (twD5BarMap b₂) hker hL
  have htop : (⊤ : Subgroup ↥(centralizerBTwo b₂)).map (twD5BarMap b₂) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  simpa [twD5BarSub, htop] using hmain

theorem glaPComponent_twD5BarSub_of_glaPComponent {G : Type} [Group G] [Finite G] {b₂ : G}
    {L : Subgroup G} (hL : GLAPComponent 3 (centralizerBTwo b₂) L) :
    GLAPComponent 3 ⊤ (twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂))) :=
  glaPComponent_twD5BarSub_top (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_top hL)

theorem twD5BarBZero_mem_normalizer_twD5BarSub {G : Type} [Group G] {b₀ b₂ : G}
    {L : Subgroup G} (hLH : L ≤ centralizerBTwo b₂) (hb0 : b₀ ∈ centralizerBTwo b₂)
    (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G)) :
    twD5BarBZero b₂ b₀ hb0 ∈ Subgroup.normalizer
      (twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂)) :
        Set (barCentralizerBTwo b₂)) := by
  have hb0N' : (⟨b₀, hb0⟩ : ↥(centralizerBTwo b₂)) ∈ Subgroup.normalizer
      (L.subgroupOf (centralizerBTwo b₂) : Set ↥(centralizerBTwo b₂)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hLH]
    exact Subgroup.mem_subgroupOf.mpr hb0N
  have h := Subgroup.le_normalizer_map (twD5BarMap b₂)
    (Subgroup.mem_map_of_mem (twD5BarMap b₂) hb0N')
  simpa [twD5BarBZero, twD5BarSub] using h

theorem inf_sup_zpowers_eq_sup_inf {G : Type} [Group G] {b₂ : G} {E J : Subgroup G}
    (hb2E : b₂ ∈ E) (hJ : J ≤ centralizerBTwo b₂) :
    E ⊓ (Subgroup.zpowers b₂ ⊔ J) = Subgroup.zpowers b₂ ⊔ (E ⊓ J) := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b₂, ∀ b ∈ J, Commute a b := by
    intro a ha b hb
    have hbC : b ∈ centralizerBTwo b₂ := hJ hb
    have hbc : Commute b b₂ := Subgroup.mem_centralizer_singleton_iff.mp hbC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact hbc.symm.zpow_left k
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxE, hxsup⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨u, hu, j, hj, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hxsup
    have huE : u ∈ E := Subgroup.zpowers_le.mpr hb2E hu
    have hjE : j ∈ E := by
      have h : u⁻¹ * (u * j) ∈ E := E.mul_mem (E.inv_mem huE) hxE
      have huj : u⁻¹ * (u * j) = j := by group
      rwa [huj] at h
    exact (Subgroup.zpowers b₂ ⊔ (E ⊓ J)).mul_mem (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_right (x := j) (Subgroup.mem_inf.mpr ⟨hjE, hj⟩))
  · refine sup_le ?_ ?_
    · exact le_inf (Subgroup.zpowers_le.mpr hb2E) le_sup_left
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)

theorem b_two_not_mem_nineJ {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E) (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    B.b 2 ∉ nineJ K (B.b 2) := by
  intro hmem
  have hb2ne : B.b 2 ≠ 1 := by
    intro h
    have hord := B.ord 2
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hcenter : (⟨B.b 2, hmem⟩ : ↥(nineJ K (B.b 2))) ∈
      Subgroup.center ↥(nineJ K (B.b 2)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hyC : (y : G) ∈ centralizerBTwo (B.b 2) :=
      (Subgroup.commutator_le_self _).trans inf_le_right y.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hyC
  rw [center_nineJ_eq_bot hstd hB hrec] at hcenter
  exact hb2ne (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hcenter))

theorem disjoint_zpowers_b_two_nineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    Disjoint (Subgroup.zpowers (B.b 2)) (nineJ K (B.b 2)) := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hxJ⟩ := Subgroup.mem_inf.mp hx
  by_cases hx1' : x = 1
  · rw [hx1']
    exact Subgroup.mem_bot.mpr rfl
  · exfalso
    have hxord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ orderOf (B.b 2) := orderOf_dvd_of_mem_zpowers hx1
      rw [B.ord 2] at hdvd
      rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf x) hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1'
      · exact h3
    have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
    have hcardb : Nat.card ↥(Subgroup.zpowers (B.b 2)) = 3 := by
      rw [Nat.card_zpowers, B.ord 2]
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers (B.b 2) :=
      Subgroup.zpowers_le.mpr hx1
    have heq : Subgroup.zpowers x = Subgroup.zpowers (B.b 2) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardb])
    have hb2mem : B.b 2 ∈ Subgroup.zpowers x := by
      rw [heq]
      exact Subgroup.mem_zpowers (B.b 2)
    exact b_two_not_mem_nineJ hstd hB hrec ((Subgroup.zpowers_le.mpr hxJ) hb2mem)

theorem card_inf_nineJ_eq {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E) (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    Nat.card ↥(E ⊓ nineJ K (B.b 2)) = 3 ^ 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, hb0E, hEcard, -⟩ := hstd.2.1
  obtain ⟨-, hsupEK, -, hEKcard, -⟩ := hstd.2.2
  have hE : IsElemAbelian 3 E := hEmax.2.1
  obtain ⟨hb2E, hEH⟩ := b_two_mem_and_span_le_centralizer hB hE
  have hdec := inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec
  have hEKleH : E ⊓ K ≤ centralizerBTwo (B.b 2) := inf_le_left.trans hEH
  have hEK : E ⊓ K = Subgroup.zpowers (B.b 2) ⊔ (E ⊓ nineJ K (B.b 2)) := by
    have h1 : E ⊓ K = E ⊓ (K ⊓ centralizerBTwo (B.b 2)) := by
      rw [← inf_assoc, inf_eq_left.mpr hEKleH]
    rw [h1, hdec]
    exact inf_sup_zpowers_eq_sup_inf hb2E
      ((Subgroup.commutator_le_self _).trans inf_le_right)
  have hdisj : Disjoint (Subgroup.zpowers (B.b 2)) (E ⊓ nineJ K (B.b 2)) :=
    (disjoint_zpowers_b_two_nineJ hstd hB hrec).mono_right inf_le_right
  have hnorm : (E ⊓ nineJ K (B.b 2)) ≤
      Subgroup.normalizer (Subgroup.zpowers (B.b 2) : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer (Subgroup.zpowers (B.b 2) : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxE : x ∈ E := (Subgroup.mem_inf.mp hx).1
    have hyE : y ∈ E := Subgroup.zpowers_le.mpr hb2E hy
    have hc := hE.1.is_comm.comm (⟨x, hxE⟩ : ↥E) (⟨y, hyE⟩ : ↥E)
    exact (Subtype.ext_iff.mp hc).symm
  have hcardsup : Nat.card ↥(Subgroup.zpowers (B.b 2) ⊔ (E ⊓ nineJ K (B.b 2))) =
      3 * Nat.card ↥(E ⊓ nineJ K (B.b 2)) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers (B.b 2)) (E ⊓ nineJ K (B.b 2)) hnorm hdisj,
      Nat.card_zpowers, B.ord 2]
  have h := hEKcard
  rw [hEK, hcardsup] at h
  have h' : 3 * Nat.card ↥(E ⊓ nineJ K (B.b 2)) = 3 * 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 5 = 3 * 3 ^ 4 by norm_num] at h
    exact h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem card_twD5BarSub_eq_of_inf_primeCore_eq_bot {G : Type} [Group G] [Finite G]
    {b₂ : G} {A : Subgroup G} (hAH : A ≤ centralizerBTwo b₂)
    (hAO : A ⊓ primeCoreCentralizerBTwo b₂ = ⊥) :
    Nat.card (twD5BarSub b₂ (A.subgroupOf (centralizerBTwo b₂))) = Nat.card ↥A := by
  let L : Subgroup ↥(centralizerBTwo b₂) := A.subgroupOf (centralizerBTwo b₂)
  have hker : ((twD5BarMap b₂).subgroupMap L).ker = ⊥ := by
    rw [Subgroup.ker_subgroupMap, twD5BarMap_ker, Subgroup.subgroupOf_eq_bot, disjoint_iff,
      eq_bot_iff]
    intro x hx
    obtain ⟨hxO, hxA⟩ := Subgroup.mem_inf.mp hx
    apply Subtype.ext
    have hx' : (x : G) ∈ A ⊓ primeCoreCentralizerBTwo b₂ :=
      ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxO⟩
    rwa [hAO, Subgroup.mem_bot] at hx'
  have hinj : Function.Injective ((twD5BarMap b₂).subgroupMap L) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have himg : Nat.card (twD5BarSub b₂ L) = Nat.card ↥L :=
    (Nat.card_congr (Equiv.ofBijective ((twD5BarMap b₂).subgroupMap L)
      ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩)).symm
  have hLcard : Nat.card ↥L = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  exact himg.trans hLcard

theorem card_twD5BarSub_inf_nineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    Nat.card (twD5BarSub (B.b 2)
      ((E ⊓ nineJ K (B.b 2)).subgroupOf (centralizerBTwo (B.b 2)))) = 3 ^ 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, hb0E, hEcard, -⟩ := hstd.2.1
  have hE : IsElemAbelian 3 E := hEmax.2.1
  obtain ⟨hb2E, hEH⟩ := b_two_mem_and_span_le_centralizer hB hE
  have hcopO : Nat.Coprime 3 (Nat.card (primeCoreCentralizerBTwo (B.b 2))) := by
    change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥(centralizerBTwo (B.b 2))).map
      (centralizerBTwo (B.b 2)).subtype))
    rw [Subgroup.card_map_of_injective (centralizerBTwo (B.b 2)).subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥(centralizerBTwo (B.b 2))
  have hEO : E ⊓ primeCoreCentralizerBTwo (B.b 2) = ⊥ := by
    have hc : Nat.Coprime (Nat.card E) (Nat.card (primeCoreCentralizerBTwo (B.b 2))) := by
      rw [hEcard]
      exact hcopO.pow_left 6
    exact (Subgroup.disjoint_of_coprime_natCard hc).eq_bot
  have hAO : (E ⊓ nineJ K (B.b 2)) ⊓ primeCoreCentralizerBTwo (B.b 2) = ⊥ := by
    have hle : (E ⊓ nineJ K (B.b 2)) ⊓ primeCoreCentralizerBTwo (B.b 2) ≤
        E ⊓ primeCoreCentralizerBTwo (B.b 2) :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    rw [hEO] at hle
    exact le_bot_iff.mp hle
  rw [card_twD5BarSub_eq_of_inf_primeCore_eq_bot (inf_le_left.trans hEH) hAO,
    card_inf_nineJ_eq hstd hB hrec]

abbrev twD5BarLbar {G : Type} [Group G] {b₂ : G} (L : Subgroup G) :
    Subgroup (barCentralizerBTwo b₂) :=
  twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂))

abbrev twD5BarMapL {G : Type} [Group G] {b₂ : G} (L : Subgroup G)
    (hLH : L ≤ centralizerBTwo b₂) : ↥L →* barCentralizerBTwo b₂ :=
  (twD5BarMap b₂).comp (Subgroup.inclusion hLH)

abbrev twD5BarPi {G : Type} [Group G] {b₂ : G} (L : Subgroup G)
    (hLH : L ≤ centralizerBTwo b₂) : ↥L →* ↥(twD5BarLbar (b₂ := b₂) L) :=
  (twD5BarMapL L hLH).codRestrict _ fun x =>
    Subgroup.mem_map.mpr ⟨⟨x.1, hLH x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩

theorem twD5BarPi_ker_eq {G : Type} [Group G] {b₂ : G} {L : Subgroup G}
    (hLH : L ≤ centralizerBTwo b₂) :
    (twD5BarPi L hLH).ker = (L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx1 : (twD5BarMap b₂) (Subgroup.inclusion hLH x) = 1 := by
      have := congrArg Subtype.val hx
      simpa [twD5BarPi, twD5BarMapL, MonoidHom.codRestrict_apply] using this
    have hxO : Subgroup.inclusion hLH x ∈
        (primeCoreCentralizerBTwo b₂).subgroupOf (centralizerBTwo b₂) :=
      (QuotientGroup.eq_one_iff _).mp hx1
    exact ⟨x.2, Subgroup.mem_subgroupOf.mp hxO⟩
  · intro ⟨hxL, hxO⟩
    apply Subtype.ext
    change (twD5BarMap b₂) (Subgroup.inclusion hLH x) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxO)

theorem primeCoreCentralizerBTwo_le {G : Type} [Group G] (b₂ : G) :
    primeCoreCentralizerBTwo b₂ ≤ centralizerBTwo b₂ :=
  Subgroup.map_subtype_le _

theorem le_normalizer_primeCoreCentralizerBTwo {G : Type} [Group G] (b₂ : G) :
    centralizerBTwo b₂ ≤ Subgroup.normalizer (primeCoreCentralizerBTwo b₂ : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (primeCoreCentralizerBTwo_le b₂)).mp
    (gLAPPrimeCoreOf_normal 3 (centralizerBTwo b₂))

theorem mem_normalizer_inf_primeCore {G : Type} [Group G] {b₀ b₂ : G}
    {L : Subgroup G} (hb0 : b₀ ∈ centralizerBTwo b₂)
    (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G)) :
    b₀ ∈ Subgroup.normalizer ((L ⊓ primeCoreCentralizerBTwo b₂) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.mpr ⟨hb0N, le_normalizer_primeCoreCentralizerBTwo b₂ hb0⟩)

theorem coprime_card_inf_primeCore {G : Type} [Group G] [Finite G] {b₂ : G}
    {L : Subgroup G} :
    Nat.Coprime 3 (Nat.card ↥(L ⊓ primeCoreCentralizerBTwo b₂)) := by
  have hcopO : Nat.Coprime 3 (Nat.card (primeCoreCentralizerBTwo b₂)) := by
    change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥(centralizerBTwo b₂)).map
      (centralizerBTwo b₂).subtype))
    rw [Subgroup.card_map_of_injective (centralizerBTwo b₂).subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥(centralizerBTwo b₂)
  exact hcopO.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)

theorem twD5BarSub_inf_centralizer_le {G : Type} [Group G] {b₀ b₂ : G}
    {L : Subgroup G} (hb0 : b₀ ∈ centralizerBTwo b₂) :
    twD5BarSub b₂ ((L ⊓ Subgroup.centralizer ({b₀} : Set G)).subgroupOf
        (centralizerBTwo b₂)) ≤
      twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂)) ⊓
        Subgroup.centralizer ({twD5BarBZero b₂ b₀ hb0} : Set (barCentralizerBTwo b₂)) := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr
    ⟨x, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hxcomm : (x : G) * b₀ = b₀ * (x : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hxH : (⟨b₀, hb0⟩ : ↥(centralizerBTwo b₂)) * x = x * ⟨b₀, hb0⟩ :=
    Subtype.ext hxcomm.symm
  show twD5BarBZero b₂ b₀ hb0 * twD5BarMap b₂ x =
    twD5BarMap b₂ x * twD5BarBZero b₂ b₀ hb0
  rw [show twD5BarBZero b₂ b₀ hb0 = twD5BarMap b₂ ⟨b₀, hb0⟩ from rfl, ← map_mul,
    hxH, map_mul]

theorem conj_mem_inf_primeCore {G : Type} [Group G] {b₀ b₂ : G} {L : Subgroup G}
    {y : ↥(centralizerBTwo b₂)} (hy : y ∈ L.subgroupOf (centralizerBTwo b₂))
    (hb0 : b₀ ∈ centralizerBTwo b₂)
    (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G))
    (hcomm : twD5BarBZero b₂ b₀ hb0 * twD5BarMap b₂ y =
      twD5BarMap b₂ y * twD5BarBZero b₂ b₀ hb0) :
    y.1⁻¹ * b₀ * y.1 * b₀⁻¹ ∈ L ⊓ primeCoreCentralizerBTwo b₂ := by
  have hyL : y.1 ∈ L := Subgroup.mem_subgroupOf.mp hy
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hb0y : b₀ * y.1 * b₀⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hb0N y.1).mp hyL
    simpa only [mul_assoc] using L.mul_mem (L.inv_mem hyL) hb0y
  · have hmemH : y.1⁻¹ * b₀ * y.1 * b₀⁻¹ ∈ centralizerBTwo b₂ :=
      (centralizerBTwo b₂).mul_mem ((centralizerBTwo b₂).mul_mem
        ((centralizerBTwo b₂).mul_mem ((centralizerBTwo b₂).inv_mem y.2) hb0) y.2)
        ((centralizerBTwo b₂).inv_mem hb0)
    have hq : twD5BarMap b₂ ⟨y.1⁻¹ * b₀ * y.1 * b₀⁻¹, hmemH⟩ = 1 := by
      have hk_eq : (⟨y.1⁻¹ * b₀ * y.1 * b₀⁻¹, hmemH⟩ : ↥(centralizerBTwo b₂)) =
          y⁻¹ * ⟨b₀, hb0⟩ * y * ⟨b₀, hb0⟩⁻¹ := rfl
      rw [hk_eq, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [show twD5BarBZero b₂ b₀ hb0 = twD5BarMap b₂ ⟨b₀, hb0⟩ from rfl] at hcomm
      calc (twD5BarMap b₂ y)⁻¹ * twD5BarMap b₂ ⟨b₀, hb0⟩ * twD5BarMap b₂ y *
            (twD5BarMap b₂ ⟨b₀, hb0⟩)⁻¹
          = (twD5BarMap b₂ y)⁻¹ *
              (twD5BarMap b₂ ⟨b₀, hb0⟩ * twD5BarMap b₂ y) *
              (twD5BarMap b₂ ⟨b₀, hb0⟩)⁻¹ := by group
        _ = (twD5BarMap b₂ y)⁻¹ *
              (twD5BarMap b₂ y * twD5BarMap b₂ ⟨b₀, hb0⟩) *
              (twD5BarMap b₂ ⟨b₀, hb0⟩)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)

theorem exists_mul_mem_inf_centralizer_of_twD5Bar {G : Type} [Group G] [Finite G] {b₀ b₂ : G}
    {L : Subgroup G} (hLH : L ≤ centralizerBTwo b₂)
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G))
    (h3b0 : orderOf b₀ = 3) {y : ↥(centralizerBTwo b₂)}
    (hy : y ∈ L.subgroupOf (centralizerBTwo b₂))
    (hcomm : twD5BarBZero b₂ b₀ hb0 * twD5BarMap b₂ y =
      twD5BarMap b₂ y * twD5BarBZero b₂ b₀ hb0) :
    ∃ w ∈ (L ⊓ Subgroup.centralizer ({b₀} : Set G)).subgroupOf (centralizerBTwo b₂),
      twD5BarMap b₂ w = twD5BarMap b₂ y := by
  classical
  let H : Subgroup G := centralizerBTwo b₂
  let O : Subgroup G := primeCoreCentralizerBTwo b₂
  let K : Subgroup G := L ⊓ O
  have hKH : K ≤ H := inf_le_right.trans (primeCoreCentralizerBTwo_le b₂)
  have hkK : y.1⁻¹ * b₀ * y.1 * b₀⁻¹ ∈ K := conj_mem_inf_primeCore hy hb0 hb0N hcomm
  have hKcard : ¬ 3 ∣ Nat.card K :=
    Nat.prime_three.coprime_iff_not_dvd.mp (coprime_card_inf_primeCore (L := L))
  obtain ⟨k, hkK', hkC⟩ :=
    CFSG.RankThree.PartTwo.Sec5.Bender.exists_mul_mem_centralizer
      (p := 3) (K := K) (b := b₀) (s := y.1) hKcard
      (by rw [← h3b0]; exact pow_orderOf_eq_one b₀)
      (mem_normalizer_inf_primeCore hb0 hb0N) hkK
  have hkL : k ∈ L := hkK'.1
  have hkO : k ∈ O := hkK'.2
  have hkH : k ∈ H := hKH hkK'
  have hyk : y.1 * k ∈ L ⊓ Subgroup.centralizer ({b₀} : Set G) :=
    ⟨L.mul_mem (Subgroup.mem_subgroupOf.mp hy) hkL, hkC⟩
  refine ⟨⟨y.1 * k, hLH hyk.1⟩, Subgroup.mem_subgroupOf.mpr hyk, ?_⟩
  have hkbar : twD5BarMap b₂ ⟨k, hkH⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hkO)
  have hw : (⟨y.1 * k, hLH hyk.1⟩ : ↥H) = y * ⟨k, hkH⟩ := Subtype.ext rfl
  rw [hw, map_mul, hkbar, mul_one]

theorem twD5BarPi_fixed_eq {G : Type} [Group G] [Finite G] {b₀ b₂ : G}
    {L : Subgroup G} (hLH : L ≤ centralizerBTwo b₂)
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G))
    (h3b0 : orderOf b₀ = 3) :
    twD5BarSub b₂ ((L ⊓ Subgroup.centralizer ({b₀} : Set G)).subgroupOf (centralizerBTwo b₂)) =
      twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂)) ⊓
        Subgroup.centralizer ({twD5BarBZero b₂ b₀ hb0} : Set (barCentralizerBTwo b₂)) := by
  classical
  refine le_antisymm (twD5BarSub_inf_centralizer_le hb0) ?_
  rintro z ⟨hzm, hzc⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hzm
  obtain ⟨w, hw, hwz⟩ := exists_mul_mem_inf_centralizer_of_twD5Bar hLH hb0 hb0N h3b0 hy
    ((Subgroup.mem_centralizer_iff.mp hzc) _ (Set.mem_singleton _))
  exact Subgroup.mem_map.mpr ⟨w, hw, hwz⟩

theorem twD5BarPi_map_subgroup {G : Type} [Group G] {b₂ : G} {L J : Subgroup G}
    (hLH : L ≤ centralizerBTwo b₂) (hJL : J ≤ L) :
    ((J.subgroupOf L).map (twD5BarPi L hLH)).map (twD5BarLbar (b₂ := b₂) L).subtype =
      twD5BarSub b₂ (J.subgroupOf (centralizerBTwo b₂)) := by
  rw [Subgroup.map_map]
  ext z
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨j.1, hLH j.2⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hj), rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwJ : w.1 ∈ J := Subgroup.mem_subgroupOf.mp hw
    have hwL : w.1 ∈ L := hJL hwJ
    exact Subgroup.mem_map.mpr ⟨⟨w.1, hwL⟩, Subgroup.mem_subgroupOf.mpr hwJ, rfl⟩

theorem glaPComponent_twD5BarSub_inf_centralizer {G : Type} [Group G] [Finite G]
    {b₀ b₂ : G} {L J : Subgroup G} (hLH : L ≤ centralizerBTwo b₂)
    (hb0 : b₀ ∈ centralizerBTwo b₂) (hb0N : b₀ ∈ Subgroup.normalizer (L : Set G))
    (h3b0 : orderOf b₀ = 3)
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b₀} : Set G)) J) :
    GLAPComponent 3
      (twD5BarSub b₂ (L.subgroupOf (centralizerBTwo b₂)) ⊓
        Subgroup.centralizer
          ({twD5BarBZero b₂ b₀ hb0} : Set (barCentralizerBTwo b₂)))
      (twD5BarSub b₂ (J.subgroupOf (centralizerBTwo b₂))) := by
  classical
  let A : Subgroup G := L ⊓ Subgroup.centralizer ({b₀} : Set G)
  have hJ_L : GLAPComponent 3 (A.subgroupOf L) (J.subgroupOf L) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ
  have hcopO : Nat.Coprime 3 (Nat.card (primeCoreCentralizerBTwo b₂)) := by
    change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥(centralizerBTwo b₂)).map
      (centralizerBTwo b₂).subtype))
    rw [Subgroup.card_map_of_injective (centralizerBTwo b₂).subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥(centralizerBTwo b₂)
  have hker : Nat.Coprime 3 (Nat.card ↥(A.subgroupOf L ⊓ (twD5BarPi L hLH).ker)) := by
    have hle : A.subgroupOf L ⊓ (twD5BarPi L hLH).ker ≤
        (L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L := by
      intro x hx
      rw [← twD5BarPi_ker_eq hLH]
      exact (Subgroup.mem_inf.mp hx).2
    have h1 : Nat.card ↥(A.subgroupOf L ⊓ (twD5BarPi L hLH).ker) ∣
        Nat.card ↥((L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L) :=
      Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥((L ⊓ primeCoreCentralizerBTwo b₂).subgroupOf L) =
        Nat.card ↥(L ⊓ primeCoreCentralizerBTwo b₂) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h3 : Nat.card ↥(L ⊓ primeCoreCentralizerBTwo b₂) ∣
        Nat.card (primeCoreCentralizerBTwo b₂) := Subgroup.card_dvd_of_le inf_le_right
    exact hcopO.coprime_dvd_right (h1.trans (h2 ▸ h3))
  have hmain := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map Nat.prime_three
    (twD5BarPi L hLH) hker hJ_L
  have hmainA := (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff Nat.prime_three
    (twD5BarLbar (b₂ := b₂) L).subtype_injective).mpr hmain
  rw [twD5BarPi_map_subgroup hLH (inf_le_left : A ≤ L),
    twD5BarPi_map_subgroup (b₂ := b₂) (J := J) hLH (hJ.1.trans inf_le_left),
    twD5BarPi_fixed_eq hLH hb0 hb0N h3b0] at hmainA
  exact hmainA

end CFSG.StandardType.FrameRoute.FS81

end
