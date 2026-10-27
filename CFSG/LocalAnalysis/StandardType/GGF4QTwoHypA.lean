module

import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThree
import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple
import CFSG.LocalAnalysis.WeakClosure81.NineTwoF
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreDeltaTransfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a2
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.CGT.PushingUpLit.CGT6.SixFour
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Walter.J1
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
import CFSG.GroupTheory.PCore.Transport
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
import CFSG.LocalAnalysis.WeakClosure81.SixSix
import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint.Multiplier

theorem center_eq_bot_of_f4EndMarking
    {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : LargeEvenLabel → Prop}
    (hP : ∀ lab, P lab → ((lab.tag = .A ∧ lab.rank = 5) ∨ (lab.tag = .A ∧ lab.rank = 6) ∨
      (lab.tag = .twD ∧ lab.rank = 4)) ∧ lab.n = 1)
    (h : LargeEvenMarking ↥K (fun lab _ _ _ _ _ => P lab)) : Subgroup.center K = ⊥ := by
  have hq : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp
      (isQuasisimple_of_largeEvenMarking h)
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, -, -, θ, hPl, hm⟩ := largeEvenRawDatum_exists hraw
  have hmod := CFSG.LocalAnalysis.GLTheoremA.I161aNames.lieModel_models_of_blueprint hm
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement R _ _ _ _ hmod
  have hlab := hP lab hPl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier R) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨ht, hn⟩ := hlab
    dsimp only at ht hn
    subst hn
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [markTag, markRank, markChar, markDeg, genericOrders, exceptionalOrders,
        Nat.card_congr Multiplicative.toAdd]
  haveI : Finite (CFSG.Open.griessHopfMultiplier R) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact one_ne_zero)
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq θ
  rw [hcard, Nat.dvd_one] at hd
  exact Subgroup.eq_bot_of_card_eq _ hd

theorem statedClassicalModel_of_markingA {X : Type} [Group X] {n : ℕ}
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1))
    (hZ : Subgroup.center X = ⊥) : StatedClassicalModel X .PSL (n + 1) 2 1 := by
  obtain ⟨lab, hlab, hHas, -, -, -, -, -, hP⟩ := largeEvenMarking_exists_hasLabel h
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨ht, hr, hm⟩ := hP
  dsimp only at ht hr hm
  subst ht hr hm
  have hM := statedClassicalModel_of_hasLabel_typeA hlab hHas
  have e : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM

theorem le_normalizer_of_sstar_markingA {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar 3 B x L) {n : ℕ} (hn : 5 ≤ n)
    (h : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  refine mem_normalizer_of_sstar hS ?_ hg
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at h
  obtain ⟨hL, lab, -, hraw⟩ := h
  obtain ⟨-, -, -, -, -, -, -, hlab⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨ht, hr, hm⟩ := hlab
  dsimp only at ht hr hm
  subst ht hr hm
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK
  exact UnitTB.exists_noncyclic_of_torusLift Nat.prime_three (show 2 ≤ (r + 1) / 2 by omega) hL θ
    (TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (r + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega)))

theorem ffNotWeaklyClosed_of_conj {G : Type} [Group G] {y : G}
    (h : ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ∧
      g * y * g⁻¹ ∉ Subgroup.zpowers y) :
    CFSG.RankThree.PartTwo.Sec21.FFNotWeaklyClosed y := by
  obtain ⟨g, hgC, hgn⟩ := h
  have hmap : conjugate (Subgroup.zpowers y) g⁻¹ = Subgroup.zpowers (g * y * g⁻¹) := by
    rw [conjugate, inv_inv, MonoidHom.map_zpowers]
    rfl
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [hmap, Subgroup.zpowers_le]
    exact hgC
  · rw [hmap]
    intro heq
    apply hgn
    rw [← heq]
    exact Subgroup.mem_zpowers _

theorem isCyclic_sylow_of_le_centralizer_of_forall {G : Type} [Group G] {p : ℕ}
    {L : Subgroup G}
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    {H : Subgroup G} (hH : H ≤ Subgroup.centralizer (L : Set G)) (P : Sylow p ↥H) : IsCyclic P := by
  have hle : (P : Subgroup H).map H.subtype ≤ Subgroup.centralizer (L : Set G) :=
    (Subgroup.map_subtype_le _).trans hH
  have hc := hcyc _ hle (P.isPGroup'.map H.subtype)
  exact isCyclic_of_surjective
    ((P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem twoLocalPrimeRank_centralizer_eq_of_config {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J) :
    twoLocalPrimeRank p (Subgroup.centralizer ({x} : Set G)) = twoLocalPrimeRank p G := by
  obtain ⟨⟨-, -, -, -, -, hβ, hS, hst⟩, -, -⟩ := hC
  have hp : p.Prime := hβ.1
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hst.2.1
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  refine le_antisymm
    (CFSG.LargeEvenClassification.Helpers.twoLocalPRank_subgroup_le hp.one_lt C) ?_
  have hBab := hS.1.1
  have hxB : x ∈ B := hS.2.1
  have hBC : B ≤ C := fun b hb => by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact congrArg Subtype.val (hBab.1.is_comm.comm ⟨z, hxB⟩ ⟨b, hb⟩)
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    exact hTB (Subgroup.commutator_bot_left B)
  have hT'1 : T.subgroupOf C ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro t ht
    have h1 : (⟨t, hTx ht⟩ : C) ∈ T.subgroupOf C := ht
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hT'2 : IsPGroup 2 (T.subgroupOf C) := hT2.comap_subtype
  have hB'el : IsElemAbelian p (B.subgroupOf C) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val
        (hBab.1.is_comm.comm (⟨((a : C) : G), a.2⟩ : B) ⟨((b : C) : G), b.2⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hBab.2 _ ha
  have hB'card : Nat.card (B.subgroupOf C) = p ^ twoLocalPrimeRank p G := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]
    exact hS.1.2.1
  have hB'T' : B.subgroupOf C ≤ Subgroup.normalizer ((T.subgroupOf C : Subgroup C) : Set C) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    have h1 := (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
    exact h1
  exact CFSG.LocalAnalysis.GLTheoremA.le_twoLocalPrimeRank_of_normalizer hp hT'1 hT'2 hB'el
    hB'card hB'T'

theorem exists_torus_of_markingA {G : Type} [Group G] [Finite G] {M : Subgroup G} {n : ℕ}
    (hn : 5 ≤ n)
    (h : LargeEvenMarking ↥M (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) :
    ∃ U E : Subgroup G, U ≤ M ∧ E ≤ M ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ ((n + 1) / 2) := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at h
  obtain ⟨hL, lab, -, hraw⟩ := h
  obtain ⟨-, -, -, -, -, -, -, hlab⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨ht, hr, hm⟩ := hlab
  dsimp only at ht hr hm
  subst ht hr hm
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK
  have hlift := TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (r + 1) K)
    (TwoThree.ggTorusLift_two hK2 (by omega))
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, -⟩ := hlift M (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  refine ⟨U.map M.subtype, E.map M.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, hU2.map _, ?_, TableB.isElemAbelian_map hE _, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
  · exact (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)
  · rw [← hEcard]
    exact Subgroup.card_map_of_injective M.subtype_injective

theorem isCyclic_of_le_centralizer_of_torus {G : Type} [Group G] [Finite G] {M U E : Subgroup G}
    {r : ℕ} (hZ : Subgroup.center M = ⊥) (hUM : U ≤ M) (hEM : E ≤ M) (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hEU : E ≤ Subgroup.normalizer (U : Set G)) (hE : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ r) (hm : twoLocalPrimeRank 3 G ≤ r + 1) {S : Subgroup G}
    (hS : S ≤ Subgroup.centralizer (M : Set G)) (hS3 : IsPGroup 3 S) : IsCyclic S := by
  by_contra hnc
  obtain ⟨F, hFS, hF, hFcard⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.nineTwoF_exists_elemAbelian_sq Nat.prime_three (by norm_num)
      hS3 hnc
  have hFM : F ≤ Subgroup.centralizer (M : Set G) := hFS.trans hS
  have hc : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f := fun f hf e he =>
    (Subgroup.mem_centralizer_iff.mp (hFM hf) e (hEM he)).symm
  have hFE : F ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgF, hgE⟩
    have hgZ : (⟨g, hEM hgE⟩ : M) ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hFM hgF) m m.2)
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hgZ)
  obtain ⟨hFEe, hFEcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.t113_sup_elemAbelian hF hE hc hFE
  have hN : F ⊔ E ≤ Subgroup.normalizer (U : Set G) := by
    refine sup_le ?_ hEU
    exact (hFM.trans (Subgroup.centralizer_le (fun _ hx => hUM hx))).trans
      (Subgroup.centralizer_le_normalizer _)
  have := CFSG.LocalAnalysis.GLTheoremA.le_twoLocalPrimeRank_of_normalizer Nat.prime_three hU hU2
    hFEe (k := r + 2) (by rw [hFEcard, hFcard, hEcard]; ring) hN
  omega

theorem le_normalizer_of_isComponentOf_cyclic {G : Type} [Group G] [Finite G] {b : G}
    {M : Subgroup G}
    (hcomp : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({b} : Set G)))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ({b} : Set G) →
      S ≤ Subgroup.centralizer (M : Set G) → IsPGroup 3 S → IsCyclic S)
    (hnc : ∃ S : Subgroup G, S ≤ M ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  intro g hg
  have hcomp' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp g
  rw [map_conj_eq_of_mem hg] at hcomp'
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hcomp' hcomp with h | h
  · exact mem_normalizer_iff_map_conj.mpr h
  · exfalso
    obtain ⟨S, hSM, hSp, hSnc⟩ := hnc
    have hle : M.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (M : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hleb : M.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({b} : Set G) :=
      hcomp'.1
    have hc := hcyc (S.map (MulAut.conj g).toMonoidHom) ((Subgroup.map_mono hSM).trans hleb)
      ((Subgroup.map_mono hSM).trans hle) (hSp.map _)
    exact hSnc (isCyclic_of_surjective
      (S.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.toMonoidHom
      (MulEquiv.surjective _))

theorem le_twoLocalPrimeRank_centralizer_of_torus {G : Type} [Group G] [Finite G] {b : G}
    {M U E : Subgroup G} {r : ℕ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hMb : M ≤ Subgroup.centralizer ({b} : Set G)) (hbM : b ∉ M) (hUM : U ≤ M) (hEM : E ≤ M)
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hEU : E ≤ Subgroup.normalizer (U : Set G))
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ r) :
    r + 1 ≤ twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({b} : Set G)) := by
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hbC : ∀ m ∈ M, b * m = m * b := fun m hm =>
    (Subgroup.mem_centralizer_iff.mp (hMb hm) b (Set.mem_singleton b))
  have hZ : IsElemAbelian 3 (Subgroup.zpowers b) := by
    refine ⟨⟨⟨fun a c => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp c.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hc : ∀ z ∈ Subgroup.zpowers b, ∀ e ∈ E, z * e = e * z := by
    intro z hz e he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (hbC e (hEM he)) i)
  have hZE : Subgroup.zpowers b ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgZ, hgE⟩
    by_contra hg1
    rw [Subgroup.mem_bot] at hg1
    have hgen : Subgroup.zpowers g = Subgroup.zpowers b := by
      apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgZ)
      rw [Nat.card_zpowers, Nat.card_zpowers, hob]
      have hg3 : g ^ 3 = 1 := hZ.2 g hgZ
      rw [orderOf_eq_prime hg3 hg1]
    apply hbM
    apply hEM
    have : b ∈ Subgroup.zpowers g := hgen ▸ Subgroup.mem_zpowers b
    exact (Subgroup.zpowers_le.mpr hgE) this
  obtain ⟨hZEe, hZEcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.t113_sup_elemAbelian hZ hE hc hZE
  have hZEC : Subgroup.zpowers b ⊔ E ≤ C := by
    refine sup_le ((Subgroup.zpowers_le).mpr ?_) (hEM.trans hMb)
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
  have hZEU : Subgroup.zpowers b ⊔ E ≤ Subgroup.normalizer (U : Set G) := by
    refine sup_le ?_ hEU
    refine (Subgroup.zpowers_le).mpr ?_
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hbC u (hUM hu)).symm
  have hUC : U ≤ C := hUM.trans hMb
  have hT1 : U.subgroupOf C ≠ ⊥ := by
    intro h
    apply hU
    rw [eq_bot_iff]
    intro t ht
    have h1 : (⟨t, hUC ht⟩ : C) ∈ U.subgroupOf C := ht
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hT2 : IsPGroup 2 (U.subgroupOf C) := hU2.comap_subtype
  have hE'el : IsElemAbelian 3 ((Subgroup.zpowers b ⊔ E).subgroupOf C) := by
    refine ⟨⟨⟨fun a c => ?_⟩⟩, fun a ha => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val
        (hZEe.1.is_comm.comm (⟨((a : C) : G), a.2⟩ : ↥(Subgroup.zpowers b ⊔ E))
          ⟨((c : C) : G), c.2⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hZEe.2 _ ha
  have hE'card : Nat.card ((Subgroup.zpowers b ⊔ E).subgroupOf C) = 3 ^ (r + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZEC).toEquiv, hZEcard, Nat.card_zpowers,
      hob, hEcard, pow_succ, mul_comm]
  have hE'T : (Subgroup.zpowers b ⊔ E).subgroupOf C ≤
      Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg t ht
    exact (Subgroup.mem_normalizer_iff.mp (hZEU hg) t).mp ht
  exact CFSG.LocalAnalysis.GLTheoremA.le_twoLocalPrimeRank_of_normalizer Nat.prime_three hT1 hT2
    hE'el hE'card hE'T

end CFSG.StandardType

end
