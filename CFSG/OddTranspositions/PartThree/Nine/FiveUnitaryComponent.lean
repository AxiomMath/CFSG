module

public import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryLocal
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizer
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.OddTranspositions.InvertMember
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.OddTranspositions.SevenThreeQuotient
import CFSG.Timmesfeld.Bridge.OddTranspGenL2
import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryTranslationAux
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
import CFSG.Foundations
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.StatementsH
import CFSG.LieType.Chevalley.RootCommutator
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoords
import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryPartition
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.Schreier.J4SSylow
import CFSG.Walter.J1Recog
import CFSG.Walter.Ree.Thompson2.BaseFin
import CFSG.Walter.ReeOrder.WardLocal
import CFSG.Walter.W67.Section8.Prop83
import CFSG.Walter.W67.W2Lemma26A
import Certificates.Certificate7000
import Certificates.Certificate7001
import Certificates.Certificate7002
import Certificates.Certificate7003
import Certificates.Certificate7004
import Certificates.Certificate7005
import Certificates.Certificate7006
import Certificates.Certificate7007
import Certificates.Certificate7008
import Certificates.Certificate7009
import Certificates.Certificate7010
import Certificates.Certificate7011
import Certificates.Certificate8026Base

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

section DihedralKernel

open CFSG.SeitzReduction.RankOne
open scoped commutatorElement Pointwise

omit [Finite G] in
theorem conj_mem_of_dihedral_ker {m : ℕ} {B T : Subgroup G} (χ : B →* DihedralGroup m)
    (hχ : ∀ b, χ b = 1 ↔ (b : G) ∈ T) (hTB : T ≤ B) {b t : G} (hb : b ∈ B) (ht : t ∈ T) :
    b * t * b⁻¹ ∈ T := by
  have h1 : χ ⟨t, hTB ht⟩ = 1 := (hχ _).mpr ht
  have h2 : χ (⟨b, hb⟩ * ⟨t, hTB ht⟩ * (⟨b, hb⟩ : B)⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (hχ _).mp h2

omit [Finite G] in
theorem conj_mem_of_dihedral_ker_of_odd {m : ℕ} (hm : Odd m) {B T N : Subgroup G}
    (hTB : T ≤ B) (hT : IsPGroup 2 T) (hNB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    (χ : B →* DihedralGroup m) (hχ : ∀ b, χ b = 1 ↔ (b : G) ∈ T)
    {k₀ : B} (hk₀ : χ k₀ ≠ 1) {e : ℕ} (he : Odd e) (hk₀e : k₀ ^ e = 1)
    {g : G} (hg : g ∈ N) {t : G} (ht : t ∈ T) : g * t * g⁻¹ ∈ T := by
  have hgB : g * t * g⁻¹ ∈ B := hNB g hg t (hTB ht)
  set x : B := ⟨g * t * g⁻¹, hgB⟩ with hx
  obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
  have hta : t ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hxa : x ^ (2 ^ a) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hx, conj_pow, hta, mul_one, mul_inv_cancel, OneMemClass.coe_one]
  have hk' : g⁻¹ * (k₀ : G) * g ∈ B := by
    have := hNB g⁻¹ (inv_mem hg) k₀ k₀.2
    simpa using this
  have ht' : (g⁻¹ * k₀ * g) * t⁻¹ * (g⁻¹ * k₀ * g)⁻¹ ∈ T :=
    conj_mem_of_dihedral_ker χ hχ hTB hk' (inv_mem ht)
  have hcomm : ((⁅x, k₀⁆ : B) : G) =
      g * (t * ((g⁻¹ * k₀ * g) * t⁻¹ * (g⁻¹ * k₀ * g)⁻¹)) * g⁻¹ := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
    group
  obtain ⟨c, hc⟩ := hT ⟨_, mul_mem ht ht'⟩
  have hcc : (⁅x, k₀⁆ : B) ^ (2 ^ c) = 1 := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val hc
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [SubgroupClass.coe_pow, hcomm, conj_pow, h1, mul_one, mul_inv_cancel,
      OneMemClass.coe_one]
  have hχx : (χ x) ^ (2 ^ a) = 1 := by rw [← map_pow, hxa, map_one]
  have hχk : (χ k₀) ^ e = 1 := by rw [← map_pow, hk₀e, map_one]
  have hχc : ⁅χ x, χ k₀⁆ ^ (2 ^ c) = 1 := by
    rw [← map_commutatorElement, ← map_pow, hcc, map_one]
  rcases dihedral_eq_one_or_eq_one_of_commutator hm hχx hχk he hχc with h1 | h1
  · exact (hχ x).mp h1
  · exact absurd h1 hk₀

omit [Finite G] in
theorem exists_r_iff_of_dihedral_ker {m : ℕ} (hm : Odd m) {B T : Subgroup G}
    (χ : B →* DihedralGroup m) (hχ : ∀ b, χ b = 1 ↔ (b : G) ∈ T) (b : B) :
    (∃ i, χ b = DihedralGroup.r i) ↔ ∃ k, Odd k ∧ (b : G) ^ k ∈ T := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨m, hm, ?_⟩
    have h1 : χ (b ^ m) = 1 := by
      rw [map_pow, hi, DihedralGroup.r_pow, DihedralGroup.one_def, ZMod.natCast_self, mul_zero]
    have h2 := (hχ (b ^ m)).mp h1
    rwa [SubgroupClass.coe_pow] at h2
  · rintro ⟨k, hk, hbk⟩
    have h1 : (χ b) ^ k = 1 := by
      rw [← map_pow]
      exact (hχ _).mpr (by rwa [SubgroupClass.coe_pow])
    exact dihedral_exists_r_of_pow_odd h1 hk

theorem exists_complement_of_dihedral_ker {m : ℕ} (hm : Odd m) {B T N : Subgroup G}
    (hTB : T ≤ B) (hT : IsPGroup 2 T) (hBN : B ≤ N)
    (hNB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B) (hNT : ∀ g ∈ N, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (χ : B →* DihedralGroup m) (hχ : ∀ b, χ b = 1 ↔ (b : G) ∈ T) :
    ∃ L : Subgroup G, L ≤ B ∧ Odd (Nat.card L) ∧ Disjoint L T ∧
      (∀ b : B, (∃ i, χ b = DihedralGroup.r i) ↔ (b : G) ∈ T ⊔ L) ∧
      ∀ g ∈ N, ∃ t ∈ T, t * g ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Rot : Subgroup (DihedralGroup m) :=
    { carrier := {x | ∃ i, x = DihedralGroup.r i}
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        exact ⟨i + j, DihedralGroup.r_mul_r i j⟩
      one_mem' := ⟨0, DihedralGroup.one_def⟩
      inv_mem' := by
        rintro _ ⟨i, rfl⟩
        exact ⟨-i, DihedralGroup.inv_r i⟩ }
  set B₀ : Subgroup G := (Rot.comap χ).map B.subtype with hB₀
  have hmemB₀ : ∀ b : B, (b : G) ∈ B₀ ↔ ∃ i, χ b = DihedralGroup.r i := by
    intro b
    constructor
    · rintro ⟨b', hb', hbb'⟩
      have : b' = b := Subtype.ext hbb'
      subst this
      exact hb'
    · intro h
      exact ⟨b, h, rfl⟩
  have hB₀B : B₀ ≤ B := Subgroup.map_subtype_le _
  have hTB₀ : T ≤ B₀ := fun t ht =>
    (hmemB₀ ⟨t, hTB ht⟩).mpr ⟨0, by rw [(hχ _).mpr ht, DihedralGroup.one_def]⟩
  have hNB₀ : ∀ g ∈ N, ∀ x ∈ B₀, g * x * g⁻¹ ∈ B₀ := by
    intro g hg x hx
    have hxB := hB₀B hx
    have hgx := hNB g hg x hxB
    obtain ⟨k, hk, hxk⟩ := (exists_r_iff_of_dihedral_ker hm χ hχ ⟨x, hxB⟩).mp
      ((hmemB₀ ⟨x, hxB⟩).mp hx)
    refine (hmemB₀ ⟨_, hgx⟩).mpr ((exists_r_iff_of_dihedral_ker hm χ hχ ⟨_, hgx⟩).mpr
      ⟨k, hk, ?_⟩)
    change (g * x * g⁻¹) ^ k ∈ T
    rw [conj_pow]
    exact hNT g hg _ hxk
  set N₀ : Subgroup B₀ := T.subgroupOf B₀ with hN₀
  have hN₀n : N₀.Normal :=
    ⟨fun x hx y => hNT y (hBN (hB₀B y.2)) x hx⟩
  have hN₀p : IsPGroup 2 N₀ := hT.comap_subtype
  obtain ⟨a, ha⟩ := hN₀p.exists_card_eq
  have hidx : Odd N₀.index := by
    by_contra hev
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := B₀ ⧸ N₀) 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx2 : x ^ 2 ∈ N₀ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one]
    have hx1 : x ∉ N₀ := by
      intro hxN
      rw [← QuotientGroup.eq_one_iff] at hxN
      rw [hxN, orderOf_one] at hy
      exact absurd hy (by decide)
    have hxB := hB₀B x.2
    obtain ⟨i, hi⟩ := (hmemB₀ ⟨x, hxB⟩).mp x.2
    have h2 : (DihedralGroup.r i) ^ (2 ^ 1) = 1 := by
      rw [← hi, ← map_pow]
      refine (hχ _).mpr ?_
      have : ((x : G) ^ 2) ∈ T := by
        have := (Subgroup.mem_subgroupOf).mp hx2
        rwa [SubgroupClass.coe_pow] at this
      simpa using this
    have hi0 := dihedral_eq_one_of_two_pow_eq_one_r hm h2
    apply hx1
    rw [Subgroup.mem_subgroupOf]
    refine (hχ ⟨x, hxB⟩).mp ?_
    rw [hi, hi0, DihedralGroup.r_zero]
  have hcop : Nat.Coprime (Nat.card N₀) N₀.index := by
    rw [ha]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hidx)
  obtain ⟨L', hL'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set L : Subgroup G := L'.map B₀.subtype with hL
  have hLB₀ : L ≤ B₀ := Subgroup.map_subtype_le _
  have hcardL : Nat.card L = Nat.card L' :=
    Subgroup.card_map_of_injective B₀.subtype_injective
  have hcardL' : Nat.card L' = N₀.index := hL'.symm.index_eq_card.symm
  have hLT : Disjoint L T := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨y, hy, rfl⟩ hyT
    have : y ∈ N₀ ⊓ L' := ⟨hyT, hy⟩
    rw [hL'.disjoint.eq_bot, Subgroup.mem_bot] at this
    rw [this, map_one]
  have hsupB₀ : T ⊔ L = B₀ := by
    refine le_antisymm (sup_le hTB₀ hLB₀) fun x hx => ?_
    have hx' : (⟨x, hx⟩ : B₀) ∈ N₀ ⊔ L' := by
      rw [hL'.sup_eq_top]
      exact Subgroup.mem_top _
    have h1 := Subgroup.mem_map_of_mem B₀.subtype hx'
    rw [Subgroup.map_sup, hN₀, Subgroup.subgroupOf_map_subtype] at h1
    exact (sup_le_sup_right inf_le_left L) h1
  refine ⟨L, hLB₀.trans hB₀B, ?_, hLT, fun b => ?_, fun g hg => ?_⟩
  · rw [hcardL, hcardL']
    exact hidx
  · rw [hsupB₀, hmemB₀]
  ·
    set L₁ : Subgroup G := L.map (MulAut.conj g).toMonoidHom with hL₁
    have hL₁B₀ : L₁ ≤ B₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact hNB₀ g hg y (hLB₀ hy)
    set L₁' : Subgroup B₀ := L₁.subgroupOf B₀ with hL₁'
    have hcardL₁' : Nat.card L₁' = Nat.card L' := by
      rw [← hcardL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁B₀).toEquiv, hL₁,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hdisj : Disjoint N₀ L₁' := by
      rw [Subgroup.disjoint_def]
      intro z hzT hzL
      have hzL₁ : (z : G) ∈ L₁ := Subgroup.mem_subgroupOf.mp hzL
      obtain ⟨y, hy, hyz⟩ := hzL₁
      have hyT : y ∈ T := by
        have := hNT g⁻¹ (inv_mem hg) _ (Subgroup.mem_subgroupOf.mp hzT)
        rw [← hyz] at this
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
      have hy1 : y = 1 := Subgroup.disjoint_def.mp hLT hy hyT
      apply Subtype.ext
      rw [← hyz, hy1, map_one, OneMemClass.coe_one]
    have hL₁c : Subgroup.IsComplement' N₀ L₁' :=
      Subgroup.isComplement'_of_card_mul_and_disjoint
        (by rw [hcardL₁']; exact hL'.card_mul_card) hdisj
    have hsolv : Group.IsSolvable N₀ := by
      have : Group.IsNilpotent N₀ := hN₀p.isNilpotent
      infer_instance
    have hmulL' : (N₀ : Set B₀) * (L' : Set B₀) = Set.univ := by
      rw [← Subgroup.normal_mul, hL'.sup_eq_top, Subgroup.coe_top]
    have hmulL₁' : (N₀ : Set B₀) * (L₁' : Set B₀) = Set.univ := by
      rw [← Subgroup.normal_mul, hL₁c.sup_eq_top, Subgroup.coe_top]
    obtain ⟨n, hnN, hn⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N₀ hsolv
      hcop hmulL' hmulL₁' hL'.disjoint.eq_bot hdisj.eq_bot
    refine ⟨(n : G), Subgroup.mem_subgroupOf.mp hnN,
      Subgroup.mem_normalizer_fintype fun x hx => ?_⟩
    have hgx : (⟨g * x * g⁻¹, hL₁B₀ ⟨x, hx, rfl⟩⟩ : B₀) ∈ L₁' :=
      Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    rw [hn] at hgx
    obtain ⟨y, hy, hyx⟩ := hgx
    have hyx' : (n : G)⁻¹ * y * n = g * x * g⁻¹ := by
      have := congrArg Subtype.val hyx
      simpa [MulAut.conj_apply] using this
    have : (n : G) * g * x * ((n : G) * g)⁻¹ = y := by
      calc (n : G) * g * x * ((n : G) * g)⁻¹ = n * (g * x * g⁻¹) * (n : G)⁻¹ := by group
        _ = n * ((n : G)⁻¹ * y * n) * (n : G)⁻¹ := by rw [hyx']
        _ = y := by group
    rw [this]
    exact ⟨y, hy, rfl⟩

theorem dihedral_sr_ne_one {m : ℕ} (j : ZMod m) : DihedralGroup.sr j ≠ 1 := by
  intro h
  rw [DihedralGroup.one_def] at h
  cases h

omit [Finite G] in
theorem exists_dihedral_sup_of_complement {m : ℕ} {B T L : Subgroup G}
    (hTB : T ≤ B) (χ : B →* DihedralGroup m) (hχ : ∀ b, χ b = 1 ↔ (b : G) ∈ T)
    (hLB : L ≤ B) (hLT : Disjoint L T)
    (hrot : ∀ b : B, (∃ i, χ b = DihedralGroup.r i) ↔ (b : G) ∈ T ⊔ L)
    (hnorm : ∀ g ∈ B, ∃ t ∈ T, t * g ∈ Subgroup.normalizer (L : Set G))
    (hsq : ∀ b ∈ B, b * b ∈ T → (∀ l ∈ L, Commute (b * b) l) → b ∉ T → b * b = 1) :
    ∃ L₀ : Subgroup G, B = T ⊔ L₀ ∧ L ≤ L₀ ∧
      (L₀ = L ∨ ∃ a ∈ L₀, a * a = 1 ∧ a ∉ L ∧ (∀ l ∈ L, a * l * a⁻¹ = l⁻¹) ∧
        L₀ = L ⊔ Subgroup.zpowers a) ∧
      ∃ f : L₀ →* DihedralGroup m, Function.Injective f := by
  classical
  have hsupB : T ⊔ L ≤ B := sup_le hTB hLB
  have hLinj : ∀ x (hx : x ∈ L), χ ⟨x, hLB hx⟩ = 1 → x = 1 := fun x hx h1 =>
    Subgroup.disjoint_def.mp hLT hx ((hχ _).mp h1)
  have hLrot : ∀ x (hx : x ∈ L), ∃ i, χ ⟨x, hLB hx⟩ = DihedralGroup.r i := fun x hx =>
    (hrot ⟨x, hLB hx⟩).mpr (Subgroup.mem_sup_right hx)
  by_cases hall : ∀ b : B, ∃ i, χ b = DihedralGroup.r i
  · refine ⟨L, le_antisymm (fun b hb => (hrot ⟨b, hb⟩).mp (hall ⟨b, hb⟩)) hsupB, le_rfl,
      Or.inl rfl, χ.comp (Subgroup.inclusion hLB), ?_⟩
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hLinj x x.2 hx)
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  obtain ⟨j, hj⟩ : ∃ j, χ b = DihedralGroup.sr j := by
    rcases hχb : χ b with i | i
    · exact absurd hχb (hb i)
    · exact ⟨i, rfl⟩
  obtain ⟨t, ht, htN⟩ := hnorm b b.2
  set a : B := ⟨t, hTB ht⟩ * b with ha
  have hχa : χ a = DihedralGroup.sr j := by
    rw [ha, map_mul, (hχ _).mpr ht, one_mul, hj]
  have haN : (a : G) ∈ Subgroup.normalizer (L : Set G) := htN
  have haT : (a : G) ∉ T := fun h => dihedral_sr_ne_one j (hχa ▸ (hχ a).mpr h)
  have hasq : (a : G) * a ∈ T := by
    have : χ (a * a) = 1 := by rw [map_mul, hχa, DihedralGroup.sr_mul_self]
    exact (hχ _).mp this
  have hac : ∀ l ∈ L, Commute ((a : G) * a) l := by
    intro l hl
    have hxN : (a : G) * a ∈ Subgroup.normalizer (L : Set G) := mul_mem haN haN
    have h1 : (a : G) * a * l * ((a : G) * a)⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl) (inv_mem hl)
    have h2 : (a : G) * a * l * ((a : G) * a)⁻¹ * l⁻¹ ∈ T := by
      have h3 : l * ((a : G) * a)⁻¹ * l⁻¹ ∈ T :=
        conj_mem_of_dihedral_ker χ hχ hTB (hLB hl) (inv_mem hasq)
      have := mul_mem hasq h3
      simpa only [mul_assoc] using this
    have h4 := Subgroup.disjoint_def.mp hLT h1 h2
    have h5 : (a : G) * a * l * ((a : G) * a)⁻¹ = l := mul_inv_eq_one.mp h4
    calc (a : G) * a * l = (a : G) * a * l * ((a : G) * a)⁻¹ * ((a : G) * a) := by group
      _ = l * ((a : G) * a) := by rw [h5]
  have ha2 := hsq _ a.2 hasq hac haT
  have haL : (a : G) ∉ L := by
    intro h
    obtain ⟨i, hi⟩ := hLrot _ h
    have : χ a = DihedralGroup.r i := hi
    rw [hχa] at this
    cases this
  have hinv : ∀ l ∈ L, (a : G) * l * (a : G)⁻¹ = l⁻¹ := by
    intro l hl
    obtain ⟨i, hi⟩ := hLrot l hl
    have hy : (a : G) * l * (a : G)⁻¹ * l ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp haN l).mp hl) hl
    have h1 : χ ⟨(a : G) * l * (a : G)⁻¹ * l, hLB hy⟩ = 1 := by
      have e : (⟨(a : G) * l * (a : G)⁻¹ * l, hLB hy⟩ : B) =
          a * ⟨l, hLB hl⟩ * a⁻¹ * ⟨l, hLB hl⟩ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, hχa, hi, DihedralGroup.inv_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r,
        DihedralGroup.one_def]
      congr 1
      ring
    exact eq_inv_of_mul_eq_one_left (hLinj _ hy h1)
  set L₀ : Subgroup G := L ⊔ Subgroup.zpowers (a : G) with hL₀
  have hL₀B : L₀ ≤ B := sup_le hLB (Subgroup.zpowers_le.mpr a.2)
  have ha2' : (a : G) ^ 2 = 1 := by rw [sq, ha2]
  have hzN : Subgroup.zpowers (a : G) ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr haN
  refine ⟨L₀, le_antisymm (fun x hx => ?_) (sup_le hTB hL₀B), le_sup_left,
    Or.inr ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), ha2, haL, hinv, rfl⟩,
    χ.comp (Subgroup.inclusion hL₀B), ?_⟩
  · by_cases hxr : ∃ i, χ ⟨x, hx⟩ = DihedralGroup.r i
    · exact sup_le_sup_left le_sup_left T ((hrot ⟨x, hx⟩).mp hxr)
    · push Not at hxr
      obtain ⟨j', hj'⟩ : ∃ j', χ ⟨x, hx⟩ = DihedralGroup.sr j' := by
        rcases hχx : χ ⟨x, hx⟩ with i | i
        · exact absurd hχx (hxr i)
        · exact ⟨i, rfl⟩
      have hxa : x * a ∈ T ⊔ L := by
        refine (hrot (⟨x, hx⟩ * a)).mp ⟨j - j', ?_⟩
        rw [map_mul, hj', hχa, DihedralGroup.sr_mul_sr]
      have e : x = x * a * a := by
        rw [mul_assoc, ha2, mul_one]
      rw [e]
      exact mul_mem (sup_le_sup_left le_sup_left T hxa)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : G) ∈ ((L ⊔ Subgroup.zpowers (a : G) : Subgroup G) : Set G) := x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hzN] at hx'
    obtain ⟨l, hl, z, hz, hlz⟩ := hx'
    have hχx : χ ⟨x, hL₀B x.2⟩ = 1 := hx
    rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq ha2' hz with
      rfl | rfl
    · have hxl : (x : G) = l := by rw [← hlz]; simp only [mul_one]
      have h1 : χ ⟨l, hLB hl⟩ = 1 := by
        have e : (⟨l, hLB hl⟩ : B) = ⟨x, hL₀B x.2⟩ := Subtype.ext hxl.symm
        rw [e, hχx]
      apply Subtype.ext
      rw [hxl, hLinj l hl h1, OneMemClass.coe_one]
    · exfalso
      obtain ⟨i, hi⟩ := hLrot l hl
      have e : (⟨x, hL₀B x.2⟩ : B) = ⟨l, hLB hl⟩ * a := Subtype.ext hlz.symm
      rw [e, map_mul, hi, hχa, DihedralGroup.r_mul_sr] at hχx
      exact dihedral_sr_ne_one _ hχx

theorem le_of_le_sup_of_le_commutator {R C U : Subgroup G} (hCR : C ≤ R) (hUR : U ≤ R)
    (hUc : ∀ z ∈ U, ∀ r ∈ R, z * r = r * z) (hUcomm : U ≤ ⁅R, R⁆) (h : R ≤ C ⊔ U) :
    R ≤ C := by
  have hCN : C ≤ Subgroup.normalizer (U : Set G) := fun c hc =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      rw [← hUc z hz c (hCR hc), mul_inv_cancel_right]
      exact hz
  have key : ∀ c₁ ∈ C, ∀ z₁ ∈ U, ∀ c₂ ∈ C, ∀ z₂ ∈ U, ⁅c₁ * z₁, c₂ * z₂⁆ = ⁅c₁, c₂⁆ := by
    intro c₁ hc₁ z₁ hz₁ c₂ hc₂ z₂ hz₂
    have e1 : z₁ * c₂ = c₂ * z₁ := hUc z₁ hz₁ c₂ (hCR hc₂)
    have e2 : z₂ * z₁ = z₁ * z₂ := hUc z₂ hz₂ z₁ (hUR hz₁)
    have e3 : z₂ * c₁ = c₁ * z₂ := hUc z₂ hz₂ c₁ (hCR hc₁)
    have hab : c₁ * z₁ * (c₂ * z₂) = c₁ * c₂ * (z₁ * z₂) := by
      rw [mul_assoc c₁, ← mul_assoc z₁, e1]
      group
    have hba : c₂ * z₂ * (c₁ * z₁) = c₂ * c₁ * (z₁ * z₂) := by
      rw [mul_assoc c₂, ← mul_assoc z₂, e3, mul_assoc c₁, e2]
      group
    rw [commutatorElement_def, commutatorElement_def,
      show c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹ =
        c₁ * z₁ * (c₂ * z₂) * (c₂ * z₂ * (c₁ * z₁))⁻¹ by group, hab, hba]
    group
  have hUC : U ≤ C := by
    refine hUcomm.trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
    have hx' : x ∈ ((C ⊔ U : Subgroup G) : Set G) := h hx
    have hy' : y ∈ ((C ⊔ U : Subgroup G) : Set G) := h hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C U hCN] at hx' hy'
    obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := hx'
    obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := hy'
    rw [key c₁ hc₁ z₁ hz₁ c₂ hc₂ z₂ hz₂, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
  exact h.trans (sup_le le_rfl hUC)

end DihedralKernel

section Chain

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G} {n : ℕ}

section UnitaryCentralizer

open CFSG.SeitzReduction.RankOne CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

theorem mem_map_conj_or_sq_eq_one_unitary {K : Type} [Group K]
    [Finite K] {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K) {γ : MulAut K}
    (hγ : γ ∈ autCentralizer (rootCenter (Q : Subgroup K)))
    (hγ2 : γ ^ 2 ∈ (rootCenter (Q : Subgroup K)).map (MulAut.conj : K →* MulAut K)) :
    γ ∈ (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) ∨ γ ^ 2 = 1 := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hU : rootCenter (Q : Subgroup K) =
      (CFSG.omega₁ (G := (Q : Subgroup K)) (p := 2)).map (Q : Subgroup K).subtype :=
    hc.omega₁_map_eq_rootCenter.symm
  obtain ⟨-, -, -, -, hsq, -⟩ :=
    CFSG.ProperTwoGeneratedCore.RootCenter.even_unitary_root_center_automorphisms_of_mulEquiv J n
      hn hcard hfixed hJ (e₁.trans e') Q (rootCenter (Q : Subgroup K)) hU
  rw [h.rootCenterAut_eq_autCentralizer Q] at hsq
  exact hsq γ hγ hγ2

theorem exists_benderType_sylow_rootCenter (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n) :
    ∃ e : ℕ, BenderType (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) n 3 e ∧
      ∃ Q : Sylow 2 (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)),
        (Q : Subgroup _).map (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype =
          (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
            CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧
        (∀ y : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), y ∈ (Q : Subgroup _) ↔
          (y : G) ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
            CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∧
        ∀ x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha),
          x ∈ rootCenter (Q : Subgroup _) ↔ (x : G) ∈ U := by
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  have hB : BenderType J n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := .unitary n hn2 eJ
  obtain ⟨Q, hQ⟩ := exists_sylow_pResidualOf T
  have hmemQ : ∀ y : J, y ∈ (Q : Subgroup J) ↔ (y : G) ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ J := by
    intro y
    rw [← hQ]
    exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨y', hy', e⟩ => by rwa [← Subtype.ext e]⟩
  refine ⟨_, hB, Q, hQ, hmemQ, fun x => ?_⟩
  obtain ⟨-, -, hΩ, -⟩ := hB.lemma_3_5_a_unitary Q
  constructor
  · intro hx
    rw [← hΩ] at hx
    have hle : Subgroup.closure {y : J | y ∈ (Q : Subgroup J) ∧ y * y = 1} ≤
        U.comap J.subtype := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyQ, hy2⟩
      by_cases hy1 : y = 1
      · rw [hy1]
        exact U.one_mem
      · change (y : G) ∈ U
        rw [hU.eq_closure]
        refine Subgroup.subset_closure ⟨(hmemQ y).mp hyQ, orderOf_eq_prime ?_
          fun h => hy1 (Subtype.ext h)⟩
        rw [sq]
        exact congrArg Subtype.val hy2
    exact hle hx
  · intro hx
    rw [← hΩ]
    have hle : U ≤ (Subgroup.closure {y : J | y ∈ (Q : Subgroup J) ∧ y * y = 1}).map
        J.subtype := by
      rw [hU.eq_closure, Subgroup.closure_le]
      rintro y ⟨hyR, hy2⟩
      refine ⟨⟨y, hyR.2⟩, Subgroup.subset_closure ⟨(hmemQ _).mpr hyR, Subtype.ext ?_⟩, rfl⟩
      change y * y = 1
      rw [← sq, ← hy2, pow_orderOf_eq_one]
    obtain ⟨x', hx', e⟩ := hle hx
    rwa [← Subtype.ext e]

omit [Finite G] in
theorem commute_of_mem_centralizer_sylow_inter (hU : DeltaSetup hC T S U) {b : G}
    (hb : b ∈ Subgroup.centralizer ((S : Set G) ∩ D)) :
    hC.d * b = b * hC.d ∧ ∀ v ∈ U, v * b = b * v := by
  have huΔ : hC.d ∈ (S : Set G) ∩ D := by
    rw [hU.sylow_inter]
    exact ⟨1, U.one_mem, mul_one _⟩
  have hbu : hC.d * b = b * hC.d := Subgroup.mem_centralizer_iff.mp hb _ huΔ
  refine ⟨hbu, fun v hv => ?_⟩
  have huv : hC.d * v ∈ (S : Set G) ∩ D := by
    rw [hU.sylow_inter]
    exact ⟨v, hv, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hb _ huv
  calc v * b = hC.d⁻¹ * (hC.d * v * b) := by group
    _ = hC.d⁻¹ * (b * (hC.d * v)) := by rw [h1]
    _ = hC.d⁻¹ * (hC.d * b * v) := by rw [hbu]; group
    _ = b * v := by group

theorem centralizer_sylow_inter_le_normalizer_pResidualOf (hU : DeltaSetup hC T S U) :
    Subgroup.centralizer ((S : Set G) ∩ D) ≤
      Subgroup.normalizer (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) : Set G) := by
  intro c hc
  have hcu := (commute_of_mem_centralizer_sylow_inter hU hc).1
  have hgv : c * hC.d * c⁻¹ ∈ hC.alpha := by
    rw [← hcu, mul_inv_cancel_right]
    exact hC.d_mem_alpha
  have hcα : c ∈ Subgroup.normalizer hC.alpha := by
    by_contra hg
    exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hg) hgv
      ⟨hC.d, hC.d_mem_alpha, rfl⟩
  exact CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
    (normalizer_le_normalizer_Halpha hC.setup.normal hcα)

theorem exists_mem_sylow_inter_eq_or_eq (h3 : Conclusion9_3 D hC) {t : G}
    (ht : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    ∃ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), t = r ∨ t = hC.d * r := by
  rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ ht) with htJ | htJ
  · exact ⟨t, ⟨ht, htJ⟩, Or.inl rfl⟩
  · refine ⟨hC.d * t, ⟨mul_mem (d_mem_sylow_map hC h3 T) ht, htJ⟩, Or.inr ?_⟩
    rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul]

theorem mem_zpowers_of_commute_pResidualOf (h3 : Conclusion9_3 D hC)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d) {g : G}
    (hgJ : ∀ j ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), j * g = g * j)
    (hgu : hC.d * g = g * hC.d) : g ∈ Subgroup.zpowers hC.d := by
  rw [← hCH]
  have hle : Halpha D hC.alpha ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [← h3.2.2.1]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) fun j hj => ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgu
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hgJ j hj)
  exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem exists_dihedral_hom_centralizer_sylow_inter
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n) :
    ∃ χ : Subgroup.centralizer ((S : Set G) ∩ D) →* DihedralGroup (2 ^ n + 1),
      (∀ b, χ b = 1 ↔
        (b : G) ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) ∧
      (∃ k₀ : Subgroup.centralizer ((S : Set G) ∩ D), χ k₀ ≠ 1 ∧ ∃ e, Odd e ∧ k₀ ^ e = 1) ∧
      ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D), ∀ v ∈ U, v ≠ 1 →
        (b * b = v ∨ b * b = hC.d * v) →
          b ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  classical
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  set B := Subgroup.centralizer ((S : Set G) ∩ D) with hBdef
  obtain ⟨e₀, hBT, Q, -, hmemQ, hZQ⟩ := exists_benderType_sylow_rootCenter hH h3 hU hCH eH
  have hJH : J ≤ Halpha D hC.alpha := Subgroup.map_subtype_le _
  have huJ : ∀ j ∈ J, j * hC.d = hC.d * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC (hJH hj))
  have hBu : ∀ b ∈ B, hC.d * b = b * hC.d := fun b hb =>
    (commute_of_mem_centralizer_sylow_inter hU hb).1
  have hBU : ∀ b ∈ B, ∀ v ∈ U, v * b = b * v := fun b hb =>
    (commute_of_mem_centralizer_sylow_inter hU hb).2
  have huTG : hC.d ∈ TG := d_mem_sylow_map hC h3 T
  have hBNJ := centralizer_sylow_inter_le_normalizer_pResidualOf (D := D) (T := T) hU
  set ρ : B →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBNJ) with hρdef
  have hρ : ∀ b k, ((ρ b k : J) : G) = (b : G) * k * (b : G)⁻¹ := fun _ _ => rfl
  have hρC : ∀ b, ρ b ∈ autCentralizer (rootCenter (Q : Subgroup J)) := by
    intro b z hz
    apply Subtype.ext
    rw [hρ, ← hBU b b.2 z ((hZQ z).mp hz), mul_inv_cancel_right]
  have hρQ : ∀ b : B, ρ b ∈ (Q : Subgroup J).map (MulAut.conj : J →* MulAut J) ↔
      (b : G) ∈ TG := by
    intro b
    constructor
    · rintro ⟨y, hyQ, hyb⟩
      have hyb' : ∀ k : J, (y : G) * k * (y : G)⁻¹ = (b : G) * k * (b : G)⁻¹ := by
        intro k
        have := congrArg (fun σ : MulAut J => ((σ k : J) : G)) hyb
        simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hρ] using this
      have hc : (y : G)⁻¹ * b ∈ Subgroup.zpowers hC.d := by
        refine mem_zpowers_of_commute_pResidualOf h3 hCH (fun j hj => ?_) ?_
        · have := hyb' ⟨j, hj⟩
          calc j * ((y : G)⁻¹ * b) = (y : G)⁻¹ * ((y : G) * j * (y : G)⁻¹) * b := by group
            _ = (y : G)⁻¹ * ((b : G) * j * (b : G)⁻¹) * b := by rw [this]
            _ = (y : G)⁻¹ * b * j := by group
        · have h1 : Commute (y : G) hC.d := huJ y y.2
          have h2 := hBu b b.2
          calc hC.d * ((y : G)⁻¹ * b) = (y : G)⁻¹ * hC.d * b := by
                rw [← mul_assoc, h1.inv_left.eq.symm]
            _ = (y : G)⁻¹ * b * hC.d := by rw [mul_assoc, h2, ← mul_assoc]
      have hyT : (y : G) ∈ TG := ((hmemQ y).mp hyQ).1
      have e : (b : G) = (y : G) * ((y : G)⁻¹ * b) := by group
      rw [e]
      exact mul_mem hyT (Subgroup.zpowers_le.mpr huTG hc)
    · intro hb
      have hbH : (b : G) ∈ Halpha D hC.alpha := Subgroup.map_subtype_le _ hb
      rcases mem_or_mul_mem_of_conclusion9_3 hC h3 hbH with hbJ | hbJ
      · refine ⟨⟨b, hbJ⟩, (hmemQ _).mpr ⟨hb, hbJ⟩, MulEquiv.ext fun k => Subtype.ext ?_⟩
        rw [hρ]
        rfl
      · refine ⟨⟨hC.d * b, hbJ⟩, (hmemQ _).mpr ⟨mul_mem huTG hb, hbJ⟩,
          MulEquiv.ext fun k => Subtype.ext ?_⟩
        rw [hρ]
        have hbk : (b : G) * k * (b : G)⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.mp (hBNJ b.2) k).mp k.2
        have h1 := huJ _ hbk
        change hC.d * b * k * (hC.d * b)⁻¹ = (b : G) * k * (b : G)⁻¹
        calc hC.d * b * k * (hC.d * b)⁻¹ = hC.d * ((b : G) * k * (b : G)⁻¹) * hC.d⁻¹ := by
              group
          _ = (b : G) * k * (b : G)⁻¹ := by rw [← h1]; group
  obtain ⟨χ₀, hχ₀⟩ := exists_dihedral_autCentralizer_unitary hBT Q
  set χ : B →* DihedralGroup (2 ^ n + 1) :=
    χ₀.comp (ρ.codRestrict (autCentralizer (rootCenter (Q : Subgroup J))) hρC) with hχdef
  have hχ : ∀ b, χ b = 1 ↔ (b : G) ∈ TG := by
    intro b
    rw [hχdef, MonoidHom.comp_apply, hχ₀, MonoidHom.codRestrict_apply, hρQ]
  refine ⟨χ, hχ, ?_, ?_⟩
  · obtain ⟨k, hkC, hkQ, e, he, hke⟩ := exists_odd_centralizer_rootCenter_unitary hBT Q
    have hkB : (k : G) ∈ B := by
      refine Subgroup.mem_centralizer_iff.mpr fun δ hδ => ?_
      rw [hU.sylow_inter] at hδ
      obtain ⟨v, hv, rfl⟩ := hδ
      have hvJ : v ∈ J := hU.le_pResidualOf hv
      have hkv : (k : G) * v = v * k := by
        have := Subgroup.mem_centralizer_iff.mp hkC ⟨v, hvJ⟩ ((hZQ ⟨v, hvJ⟩).mpr hv)
        exact (congrArg Subtype.val this).symm
      have hku := huJ k k.2
      calc hC.d * v * k = hC.d * (k * v) := by rw [mul_assoc, ← hkv]
        _ = k * (hC.d * v) := by rw [← mul_assoc, ← hku, mul_assoc]
    refine ⟨⟨k, hkB⟩, fun h1 => hkQ ((hmemQ k).mpr ⟨(hχ _).mp h1, k.2⟩), e, he, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hke
    simpa using this
  · intro b hb v hv hv1 hbv
    set bB : B := ⟨b, hb⟩
    have hvJ : v ∈ J := hU.le_pResidualOf hv
    have hρ2 : ρ bB ^ 2 = MulAut.conj (⟨v, hvJ⟩ : J) := by
      ext k
      rw [sq, ← map_mul, hρ, MulAut.conj_apply]
      change b * b * (k : G) * (b * b)⁻¹ = v * k * v⁻¹
      rcases hbv with hbv | hbv
      · rw [hbv]
      · have h1 := huJ _ (mul_mem (mul_mem hvJ k.2) (inv_mem hvJ))
        rw [hbv]
        calc hC.d * v * k * (hC.d * v)⁻¹ = hC.d * (v * k * v⁻¹) * hC.d⁻¹ := by group
          _ = v * k * v⁻¹ := by rw [← h1]; group
    have hsqmem : ρ bB ^ 2 ∈ (rootCenter (Q : Subgroup J)).map (MulAut.conj : J →* MulAut J) :=
      ⟨⟨v, hvJ⟩, (hZQ _).mpr hv, hρ2.symm⟩
    have hne : ρ bB ^ 2 ≠ 1 := by
      intro h1
      rw [hρ2] at h1
      have hc : (⟨v, hvJ⟩ : J) ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro x
        have := congrArg (fun σ : MulAut J => σ x) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc x * ⟨v, hvJ⟩ = (⟨v, hvJ⟩ * x * (⟨v, hvJ⟩ : J)⁻¹) * ⟨v, hvJ⟩ := by rw [this]
          _ = ⟨v, hvJ⟩ * x := by group
      rw [hBT.center_eq_bot, Subgroup.mem_bot] at hc
      exact hv1 (congrArg Subtype.val hc)
    rcases mem_map_conj_or_sq_eq_one_unitary hBT Q (hρC bB) hsqmem with h | h
    · exact (hρQ bB).mp h
    · exact absurd h hne

theorem sylow_map_le_centralizer_and_mul_self_mem
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n) :
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
        Subgroup.centralizer ((S : Set G) ∩ D) ∧
      ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype, t * t ∈ U := by
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  obtain ⟨e₀, hBT, Q, -, hmemQ, hZQ⟩ := exists_benderType_sylow_rootCenter hH h3 hU hCH eH
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hdec : ∀ t ∈ TG, ∃ r ∈ TG ⊓ J, t = r ∨ t = hC.d * r := fun t ht =>
    exists_mem_sylow_inter_eq_or_eq h3 ht
  have hut : ∀ t ∈ TG, hC.d * t = t * hC.d := fun t ht =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ ht))).symm
  refine ⟨fun t ht => Subgroup.mem_centralizer_iff.mpr fun δ hδ => ?_, fun t ht => ?_⟩
  · rw [hU.sylow_inter] at hδ
    obtain ⟨v, hv, rfl⟩ := hδ
    obtain ⟨r, hr, hrt⟩ := hdec t ht
    have hvJ : v ∈ J := hU.le_pResidualOf hv
    have hrv : v * r = r * v := by
      have h1 := (mem_rootCenter_iff.mp ((hZQ ⟨v, hvJ⟩).mpr hv)).2 ⟨r, hr.2⟩
        ((hmemQ ⟨r, hr.2⟩).mpr hr)
      exact (congrArg Subtype.val h1).symm
    have huv : hC.d * v = v * hC.d :=
      (Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer v hv).symm
    have htv : v * t = t * v := by
      rcases hrt with rfl | rfl
      · exact hrv
      · rw [← mul_assoc, ← huv, mul_assoc, hrv, ← mul_assoc]
    calc hC.d * v * t = hC.d * (t * v) := by rw [mul_assoc, htv]
      _ = t * (hC.d * v) := by rw [← mul_assoc, hut t ht, mul_assoc]
  · obtain ⟨r, hr, hrt⟩ := hdec t ht
    have hr2 : r * r ∈ U := by
      have h1 := hBT.sq_mem_rootCenter_unitary Q ((hmemQ ⟨r, hr.2⟩).mpr hr)
      exact (hZQ _).mp h1
    rcases hrt with rfl | rfl
    · exact hr2
    · have hur : hC.d * r = r * hC.d := hut r hr.1
      rw [show hC.d * r * (hC.d * r) = (hC.d * hC.d) * (r * r) by
        rw [mul_assoc, ← mul_assoc r, ← hur]; group, hu2, one_mul]
      exact hr2

theorem mem_of_commute_of_odd (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) {L : Subgroup G} (hLo : Odd (Nat.card L)) (hL1 : L ≠ ⊥)
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D)) {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hrL : ∀ l ∈ L, Commute r l) : r ∈ U := by
  by_contra hrU
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL1
  have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
  apply not_commute_conj_of_psu3 hH h3 hU hCH eH hUn hLo hLB hl hl1' hr hrU
  have e : l * r * l⁻¹ = r := by rw [← (hrL l hl).eq, mul_inv_cancel_right]
  rw [e]

theorem centralizer_inf_of_odd (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) {L : Subgroup G} (hLo : Odd (Nat.card L)) (hL1 : L ≠ ⊥)
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D)) :
    ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      (∀ l ∈ L, Commute x l) ↔ x ∈ Subgroup.zpowers hC.d ⊔ U := by
  intro x hx
  constructor
  · intro hxL
    obtain ⟨r, hr, hxr⟩ := exists_mem_sylow_inter_eq_or_eq h3 hx
    have hrL : ∀ l ∈ L, Commute r l := by
      intro l hl
      rcases hxr with rfl | rfl
      · exact hxL l hl
      · have h1 := (hxL l hl).eq
        have h2 := (commute_of_mem_centralizer_sylow_inter hU (hLB hl)).1
        have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
        show r * l = l * r
        calc r * l = hC.d * (hC.d * r * l) := by rw [← mul_assoc, ← mul_assoc, hu2, one_mul]
          _ = hC.d * (l * (hC.d * r)) := by rw [h1]
          _ = hC.d * l * hC.d * r := by group
          _ = l * (hC.d * hC.d) * r := by rw [h2]; group
          _ = l * r := by rw [hu2, mul_one]
    have hrU := mem_of_commute_of_odd hH h3 hU hCH eH hUn hLo hL1 hLB hr hrL
    rcases hxr with rfl | rfl
    · exact Subgroup.mem_sup_right hrU
    · exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right hrU)
  · intro hx' l hl
    obtain ⟨hlu, hlU⟩ := commute_of_mem_centralizer_sylow_inter hU (hLB hl)
    have hle : Subgroup.zpowers hC.d ⊔ U ≤ Subgroup.centralizer ({l} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hlu))
        fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hlU v hv)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx')

theorem commutator_sylow_inter_eq_of_odd (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) {L : Subgroup G} (hLo : Odd (Nat.card L)) (hL1 : L ≠ ⊥)
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D))
    (hLT : ∀ l ∈ L, ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      l * t * l⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    ⁅(T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), L⁆ =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  set R := TG ⊓ J with hR
  obtain ⟨e₀, hBT, Q, hQ, hmemQ, hZQ⟩ := exists_benderType_sylow_rootCenter hH h3 hU hCH eH
  have hRp : IsPGroup 2 R := (T.isPGroup'.map _).to_le inf_le_left
  have hBNJ := centralizer_sylow_inter_le_normalizer_pResidualOf (D := D) (T := T) hU
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun r hr =>
      ⟨hLT l hl r hr.1, (Subgroup.mem_normalizer_iff.mp (hBNJ (hLB hl)) r).mp hr.2⟩
  have hle : ⁅R, L⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro r hr l hl
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hr ?_
    rw [← mul_assoc]
    exact (Subgroup.mem_normalizer_iff.mp (hLR hl) r⁻¹).mp (inv_mem hr)
  have hcopr : R ≤ ⁅R, L⁆ ⊔ R ⊓ Subgroup.centralizer (L : Set G) := by
    have : Group.IsNilpotent R := hRp.isNilpotent
    have hsolv : Group.IsSolvable R := inferInstance
    have hcop : Nat.Coprime (Nat.card L) (Nat.card R) := by
      obtain ⟨k, hk⟩ := hRp.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hLo)
    have : Subgroup.Normalizes L R := ⟨hLR⟩
    have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := R) (A := L) hsolv hcop
    have hcomm : (CFSG.commutatorAction (A := L) (G := R)).map R.subtype = ⁅R, L⁆ :=
      CFSG.commutatorAction_subgroup_conj_map_eq_commutator R L hLR
    have hfix : CFSG.fixedPointSubgroup L R = (CFSG.subgroupCentralizerIn R L).subgroupOf R :=
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R L hLR
    intro x hx
    have h1 : (⟨x, hx⟩ : R) ∈ CFSG.fixedPointSubgroup L R ⊔ CFSG.commutatorAction L R := by
      rw [hsup]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem R.subtype h1
    rw [Subgroup.map_sup, hcomm, hfix, CFSG.subgroupCentralizerIn,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h2
    rw [sup_comm]
    exact h2
  have hCU : R ⊓ Subgroup.centralizer (L : Set G) ≤ U := fun r hr =>
    mem_of_commute_of_odd hH h3 hU hCH eH hUn hLo hL1 hLB hr.1 fun l hl =>
      ((Subgroup.mem_centralizer_iff.mp hr.2 l hl).symm)
  have hUR : U ≤ R := fun v hv => ⟨hU.le_sylow_map hv, hU.le_pResidualOf hv⟩
  have hUc : ∀ z ∈ U, ∀ r ∈ R, z * r = r * z := by
    intro z hz r hr
    have h1 := (mem_rootCenter_iff.mp ((hZQ ⟨z, hU.le_pResidualOf hz⟩).mpr hz)).2 ⟨r, hr.2⟩
      ((hmemQ ⟨r, hr.2⟩).mpr hr)
    exact (congrArg Subtype.val h1).symm
  have hUcomm : U ≤ ⁅R, R⁆ := by
    obtain ⟨hQQ, -⟩ := hBT.lemma_3_5_a_unitary Q
    have hmap := Subgroup.map_commutator (Q : Subgroup J) (Q : Subgroup J) J.subtype
    rw [hQQ, hQ] at hmap
    intro v hv
    rw [← hmap]
    exact ⟨⟨v, hU.le_pResidualOf hv⟩, (hZQ _).mpr hv, rfl⟩
  exact le_antisymm hle (le_of_le_sup_of_le_commutator hle hUR hUc hUcomm
    (hcopr.trans (sup_le_sup_left hCU _)))

theorem conj_mem_sylow_inter_pResidualOf_of_commutator_eq (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U) {L : Subgroup G}
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D))
    (hRL : ⁅(T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), L⁆ =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hBT : ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D),
      ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
        b * t * b⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hNT : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
        g * t * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hNB : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D),
        g * b * g⁻¹ ∈ Subgroup.centralizer ((S : Set G) ∩ D)) :
    ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      ∀ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha),
        g * r * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
          CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  set B := Subgroup.centralizer ((S : Set G) ∩ D) with hB
  have hBNJ := centralizer_sylow_inter_le_normalizer_pResidualOf (D := D) (T := T) hU
  have hJH : J ≤ Halpha D hC.alpha := Subgroup.map_subtype_le _
  have huJ : ∀ j ∈ J, j * hC.d = hC.d * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC (hJH hj))
  have hle1 : ⁅TG, B⁆ ≤ TG ⊓ J := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc b]
      exact mul_mem ht (hBT b hb _ (inv_mem ht))
    · obtain ⟨r, hr, htr⟩ := exists_mem_sylow_inter_eq_or_eq h3 ht
      have hw : r * (b * r⁻¹ * b⁻¹) ∈ J :=
        mul_mem hr.2 ((Subgroup.mem_normalizer_iff.mp (hBNJ hb) r⁻¹).mp (inv_mem hr.2))
      rcases htr with rfl | rfl
      · rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc b]
        exact hw
      · have hub := (commute_of_mem_centralizer_sylow_inter hU hb).1
        have hub' : hC.d⁻¹ * b⁻¹ = b⁻¹ * hC.d⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hub]
        have e : ⁅hC.d * r, b⁆ = hC.d * (r * (b * r⁻¹ * b⁻¹)) * hC.d⁻¹ := by
          rw [commutatorElement_def]
          calc hC.d * r * b * (hC.d * r)⁻¹ * b⁻¹ = hC.d * r * b * r⁻¹ * (hC.d⁻¹ * b⁻¹) := by
                group
            _ = hC.d * r * b * r⁻¹ * (b⁻¹ * hC.d⁻¹) := by rw [hub']
            _ = hC.d * (r * (b * r⁻¹ * b⁻¹)) * hC.d⁻¹ := by group
        rw [e, ← huJ _ hw, mul_inv_cancel_right]
        exact hw
  have hle2 : TG ⊓ J ≤ ⁅TG, B⁆ := by
    rw [← hRL]
    exact Subgroup.commutator_mono inf_le_left hLB
  intro g hg r hr
  have h1 : g * r * g⁻¹ ∈ ⁅TG, B⁆.map (MulAut.conj g).toMonoidHom :=
    ⟨r, hle2 hr, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_commutator] at h1
  refine hle1 (Subgroup.commutator_mono ?_ ?_ h1)
  · rintro _ ⟨t, ht, rfl⟩
    exact hNT g hg t ht
  · rintro _ ⟨b, hb, rfl⟩
    exact hNB g hg b hb

theorem mul_self_eq_one_of_commute_of_odd (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) {L : Subgroup G} (hLo : Odd (Nat.card L)) (hL1 : L ≠ ⊥)
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D))
    (hSF : ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D), ∀ v ∈ U, v ≠ 1 →
      (b * b = v ∨ b * b = hC.d * v) →
        b ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hTsq : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      t * t ∈ U)
    (hNB : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D),
        g * b * g⁻¹ ∈ Subgroup.centralizer ((S : Set G) ∩ D)) :
    ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D),
      b * b ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype →
      (∀ l ∈ L, Commute (b * b) l) →
      b ∉ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype → b * b = 1 := by
  intro b hb hbT hbc hbnT
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hu2' : hC.d ^ 2 = 1 := by rw [sq, hu2]
  have hw := (centralizer_inf_of_odd hH h3 hU hCH eH hUn hLo hL1 hLB _ hbT).mp hbc
  rw [sup_comm] at hw
  obtain ⟨v, hv, z, hz, hvz⟩ :=
    CFSG.SeitzReduction.RankOne.exists_mul_eq_of_mem_sup_zpowers hU.d_mem_centralizer hw
  have huv : v * hC.d = hC.d * v :=
    Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer v hv
  by_cases hv1 : v = 1
  · subst hv1
    rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq hu2' hz with
      rfl | rfl
    · rw [← hvz, one_mul]
    · exfalso
      have hbu : b * b = hC.d := by rw [← hvz, one_mul]
      obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
      have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
      obtain ⟨g, hg, hgu⟩ := hU.transitive hC.d ⟨1, U.one_mem, mul_one _⟩ (hC.d * v₀)
        ⟨v₀, hv₀, rfl⟩
      have hgN : g ∈ Subgroup.normalizer ((S : Set G) ∩ D) := by
        rw [hU.sylow_inter]
        exact hg
      have hb' := hNB g hgN b hb
      have hb'sq : g * b * g⁻¹ * (g * b * g⁻¹) = hC.d * v₀ := by
        rw [show g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ by group, hbu, hgu]
      have h1 := hTsq _ (hSF _ hb' v₀ hv₀ hv₀1' (Or.inr hb'sq))
      rw [hb'sq] at h1
      apply hU.d_not_mem h3
      rw [show hC.d = hC.d * v₀ * v₀⁻¹ by group]
      exact mul_mem h1 (inv_mem hv₀)
  · exfalso
    apply hbnT
    refine hSF b hb v hv hv1 ?_
    rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq hu2' hz with
      rfl | rfl
    · left
      rw [← hvz, mul_one]
    · right
      rw [← hvz, huv]

end UnitaryCentralizer

theorem exists_unitaryCentralizerData (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (_h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) :
    ∃ L L₀ : Subgroup G, UnitaryCentralizerData hC T S U n L L₀ := by
  classical
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  set B := Subgroup.centralizer ((S : Set G) ∩ D) with hB
  set N := Subgroup.normalizer ((S : Set G) ∩ D) with hN
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  have hm : Odd (2 ^ n + 1) := CFSG.SeitzReduction.RankOne.rankOne_odd_two_pow_add_one (by omega)
  obtain ⟨hTB, hTsq⟩ := sylow_map_le_centralizer_and_mul_self_mem hH h3 hU hCH eH
  have hTp : IsPGroup 2 TG := T.isPGroup'.map _
  have hBN : B ≤ N := Subgroup.centralizer_le_normalizer _
  have hNB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro g hg b hb
    refine Subgroup.mem_centralizer_iff.mpr fun δ hδ => ?_
    have h1 : g⁻¹ * δ * g ∈ (S : Set G) ∩ D := (Subgroup.mem_set_normalizer_iff''.mp hg δ).mp hδ
    have h2 := Subgroup.mem_centralizer_iff.mp hb _ h1
    calc δ * (g * b * g⁻¹) = g * ((g⁻¹ * δ * g) * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * δ * g)) * g⁻¹ := by rw [h2]
      _ = g * b * g⁻¹ * δ := by group
  obtain ⟨χ, hχ, ⟨k₀, hk₀, e, he, hk₀e⟩, hSF⟩ :=
    exists_dihedral_hom_centralizer_sylow_inter hH h3 hU hCH eH
  have hNT : ∀ g ∈ N, ∀ t ∈ TG, g * t * g⁻¹ ∈ TG := fun g hg t ht =>
    conj_mem_of_dihedral_ker_of_odd hm hTB hTp hNB χ hχ hk₀ he hk₀e hg ht
  obtain ⟨L, hLB, hLo, hLT, hrot, hnorm⟩ :=
    exists_complement_of_dihedral_ker hm hTB hTp hBN hNB hNT χ hχ
  have hL1 : L ≠ ⊥ := by
    intro hbot
    have hrk : ∃ i, χ k₀ = DihedralGroup.r i :=
      CFSG.SeitzReduction.RankOne.dihedral_exists_r_of_pow_odd (by rw [← map_pow, hk₀e, map_one]) he
    have h1 := (hrot k₀).mp hrk
    rw [hbot, sup_bot_eq] at h1
    exact hk₀ ((hχ k₀).mpr h1)
  have hRL := commutator_sylow_inter_eq_of_odd hH h3 hU hCH eH hUn hLo hL1 hLB
    fun l hl t ht => hNT l (hBN (hLB hl)) t ht
  obtain ⟨L₀, hBL₀, hLL₀, hor, hdih⟩ := exists_dihedral_sup_of_complement hTB χ hχ hLB hLT hrot
    (fun g hg => hnorm g (hBN hg))
    (mul_self_eq_one_of_commute_of_odd hH h3 hU hCH eH hUn hLo hL1 hLB hSF hTsq hNB)
  exact ⟨L, L₀,
    { center_eq := center_Halpha_eq_zpowers_of_centralizer h3 hCH
      sylow_normal := hNT
      odd_card := hLo
      ne_bot := hL1
      le_centralizer := hLB
      centralizer_inf := centralizer_inf_of_odd hH h3 hU hCH eH hUn hLo hL1 hLB
      commutator_eq := hRL
      sylow_inter_normal := conj_mem_sylow_inter_pResidualOf_of_commutator_eq h3 hU hLB hRL
        (fun b hb t ht => hNT b (hBN hb) t ht) hNT hNB
      normalizer_eq := hnorm
      centralizer_eq := hBL₀
      le := hLL₀
      eq_or_eq_sup := hor
      dihedral := hdih }⟩

section ComponentTools

omit [Finite G] in
theorem reach_conj_of_forall_mem {C : Set G} {g : G} (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C)
    {x y : G} (h : Reach C x y) : Reach C (g * x * g⁻¹) (g * y * g⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.tail ih
      ⟨hg _ hbc.1, hg _ hbc.2.1, (Commute.conj_iff g).2 hbc.2.2⟩

omit [Finite G] in
theorem reach_conj_of_reach {C : Set G} {u g c₀ : G} (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C)
    (hc₀ : Reach C u c₀) (hgc₀ : Reach C u (g * c₀ * g⁻¹)) {c : G} (hc : Reach C u c) :
    Reach C u (g * c * g⁻¹) :=
  reach_trans (reach_trans hgc₀ (reach_symm (reach_conj_of_forall_mem hg hc₀)))
    (reach_conj_of_forall_mem hg hc)

omit [Finite G] in
theorem conj_mem_centralizer_inter_of_mem_normalizer (hD : IsNormalSet D) {L : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D) :
    g * x * g⁻¹ ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D := by
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun l hl => ?_, hD g x hx.2⟩
  have hl' : g⁻¹ * l * g ∈ L := (Subgroup.mem_normalizer_iff''.mp hg l).mp hl
  have h1 := Subgroup.mem_centralizer_iff.mp hx.1 _ hl'
  calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * l := by group

omit [Finite G] in
theorem closure_orderOf_eq_two_eq_top {K : Type*} [Group K] [IsSimpleGroup K] {x₀ : K}
    (hx₀ : orderOf x₀ = 2) : Subgroup.closure {x : K | orderOf x = 2} = ⊤ := by
  have hle : Subgroup.normalClosure {x : K | orderOf x = 2} ≤
      Subgroup.closure {x : K | orderOf x = 2} := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hay
    apply Subgroup.subset_closure
    show orderOf (c * a * c⁻¹) = 2
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure {x : K | orderOf x = 2}) with h | h
  · exfalso
    have : x₀ ∈ Subgroup.normalClosure {x : K | orderOf x = 2} := Subgroup.subset_normalClosure hx₀
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hx₀
    exact absurd hx₀ (by decide)
  · exact eq_top_iff.mpr (h ▸ hle)

omit [Finite G] in
theorem eq_and_commute_of_mk_of_odd_center {K : Type*} [Group K] [Finite K]
    (hZ : Odd (Nat.card (Subgroup.center K))) {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    (QuotientGroup.mk' (Subgroup.center K) a = QuotientGroup.mk' (Subgroup.center K) b →
      a = b) ∧
    (Commute (QuotientGroup.mk' (Subgroup.center K) a)
      (QuotientGroup.mk' (Subgroup.center K) b) → Commute a b) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hcen1 : ∀ w ∈ Subgroup.center K, w * w = 1 → w = 1 := by
    intro w hw hw2
    have h1 : orderOf (⟨w, hw⟩ : Subgroup.center K) ∣ Nat.card (Subgroup.center K) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨w, hw⟩ : Subgroup.center K) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simp [sq, hw2]
    have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center K)) := Nat.coprime_two_left.mpr hZ
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
    rw [orderOf_eq_one_iff] at h3
    exact congrArg Subtype.val h3
  constructor
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ha'] at h
    have hc := Subgroup.mem_center_iff.mp h a
    have hb_eq : b = a * b * a := by
      rw [← mul_assoc, ha, one_mul] at hc
      exact hc
    have h2 : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = (a * b * a) * b := by group
        _ = b * b := by rw [← hb_eq]
        _ = 1 := hb
    have h3 := hcen1 _ h h2
    calc a = b⁻¹ := eq_inv_of_mul_eq_one_left h3
      _ = b := hb'
  · intro h
    have h1 : QuotientGroup.mk' (Subgroup.center K) (a * b * a⁻¹ * b⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h.eq]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ha', hb'] at h1
    set w := a * b * a * b with hw
    have hc : a * w = w * a := Subgroup.mem_center_iff.mp h1 a
    have hw_inv : w⁻¹ = b * a * b * a := by
      rw [hw]
      simp only [mul_inv_rev, ha', hb']
      group
    have h4 : a * w * a = b * a * b * a := by
      rw [hw]
      calc a * (a * b * a * b) * a = (a * a) * b * a * b * a := by group
        _ = b * a * b * a := by rw [ha, one_mul]
    have h5 : a * w * a = w := by rw [hc, mul_assoc, ha, mul_one]
    have h6 : w = w⁻¹ := by rw [hw_inv, ← h4, h5]
    have h7 : w * w = 1 := mul_eq_one_iff_eq_inv.mpr h6
    have h8 := hcen1 w h1 h7
    show a * b = b * a
    have h9 : (a * b) * (a * b) = 1 := by
      rw [show (a * b) * (a * b) = w by rw [hw]; group, h8]
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h9
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']

omit [Finite G] in
theorem odd_card_center_of_pCore_eq_bot {K : Type*} [Group K] [Finite K]
    (h : CFSG.pCore 2 K = ⊥) : Odd (Nat.card (Subgroup.center K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
  have hzK : orderOf (z : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hn : (Subgroup.zpowers (z : K)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
  have hp : IsPGroup 2 (Subgroup.zpowers (z : K)) := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h2 : (z : K) ^ 2 = 1 := by rw [← hzK, pow_orderOf_eq_one]
    change ((z : K) ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hle : Subgroup.zpowers (z : K) ≤ CFSG.pCore 2 K := le_sSup ⟨hn, hp⟩
  rw [h] at hle
  have h1 := hle (Subgroup.mem_zpowers (z : K))
  rw [Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hzK
  exact absurd hzK (by decide)

omit [Finite G] in
theorem solvableRadical_eq_center_of_sup_zpowers {K : Type} [Group K] [Finite K] {z : K}
    (hz : z ∈ Subgroup.center K) (hz2 : z * z = 1) {X₀ : Type} [Group X₀] [Finite X₀]
    {n : ℕ} (hn : 2 ≤ n) (e : X₀ ≃* PSL2Model n) (ι : X₀ →* K) (hι : Function.Injective ι)
    (hsup : Subgroup.zpowers z ⊔ ι.range = ⊤) (hzX : z ∉ ι.range) :
    CFSG.solvableRadical K = Subgroup.center K ∧ Subgroup.center K = Subgroup.zpowers z ∧
      Nonempty (K ⧸ Subgroup.center K ≃* PSL2Model n) := by
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType X₀ n 1 1 := .linear n hn e
  have : IsSimpleGroup X₀ := hB.isSimple
  have hZX : Subgroup.center X₀ = ⊥ := hB.center_eq_bot
  have hz2' : z ^ 2 = 1 := by rw [sq, hz2]
  have hzc : z ∈ Subgroup.centralizer (ι.range : Set K) :=
    Subgroup.mem_centralizer_iff.mpr fun x _ => (Subgroup.mem_center_iff.mp hz x)
  have hdec : ∀ k : K, ∃ x ∈ ι.range, ∃ w ∈ Subgroup.zpowers z, x * w = k := fun k =>
    CFSG.SeitzReduction.RankOne.exists_mul_eq_of_mem_sup_zpowers hzc
      (by rw [sup_comm, hsup]; exact Subgroup.mem_top k)
  have hXn : ι.range.Normal := by
    refine ⟨fun x hx k => ?_⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := hdec k
    have hwc : w ∈ Subgroup.center K := Subgroup.zpowers_le.mpr hz hw
    rw [show y * w * x * (y * w)⁻¹ = y * (w * x * w⁻¹) * y⁻¹ by group,
      ← Subgroup.mem_center_iff.mp hwc x, mul_inv_cancel_right]
    exact mul_mem (mul_mem hy hx) (inv_mem hy)
  have hcen : Subgroup.center K = Subgroup.zpowers z := by
    refine le_antisymm (fun k hk => ?_) (Subgroup.zpowers_le.mpr hz)
    obtain ⟨_, ⟨x₀, rfl⟩, w, hw, hxw⟩ := hdec k
    have hwc : w ∈ Subgroup.center K := Subgroup.zpowers_le.mpr hz hw
    have hxc : ι x₀ ∈ Subgroup.center K := by
      rw [show ι x₀ = k * w⁻¹ by rw [← hxw]; group]
      exact mul_mem hk (inv_mem hwc)
    have hx₀ : x₀ ∈ Subgroup.center X₀ := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hι
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hxc (ι y)
    rw [hZX, Subgroup.mem_bot] at hx₀
    rw [← hxw, hx₀, map_one, one_mul]
    exact hw
  have hrad : CFSG.solvableRadical K ≤ Subgroup.center K := by
    set R := CFSG.solvableRadical K with hR
    have hRn : R.Normal := CFSG.Timmesfeld.Bridge.OddTransp.solvableRadical_normal K
    have hRs : Group.IsSolvable R := CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical
    have hcomap : R.comap ι = ⊥ := by
      have hcn : (R.comap ι).Normal := Subgroup.Normal.comap hRn ι
      have hcs : Group.IsSolvable (R.comap ι) := by
        let f : R.comap ι →* R := (ι.comp (R.comap ι).subtype).codRestrict R fun x => x.2
        have hf : Function.Injective f := fun a b hab => by
          apply Subtype.ext
          apply hι
          exact congrArg Subtype.val hab
        exact Group.isSolvable_of_isSolvable_injective hf
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.comap ι) with h | h
      · exact h
      · exfalso
        have hsX : Group.IsSolvable X₀ := by
          have e' : (⊤ : Subgroup X₀) ≃* X₀ := Subgroup.topEquiv
          rw [← h] at e'
          exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective
        have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := X₀)).mpr hsX
        have htop : Subgroup.center X₀ = ⊤ := by
          rw [eq_top_iff]
          intro x _
          exact Subgroup.mem_center_iff.mpr fun y => hcomm y x
        rw [hZX] at htop
        obtain ⟨x, hx⟩ := exists_ne (1 : X₀)
        have : x ∈ (⊥ : Subgroup X₀) := htop ▸ Subgroup.mem_top x
        exact hx (Subgroup.mem_bot.mp this)
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨_, ⟨x₀, rfl⟩, w, hw, rfl⟩ := hdec k
    have hwc : w ∈ Subgroup.center K := Subgroup.zpowers_le.mpr hz hw
    have hc : ι x₀ * r * (ι x₀)⁻¹ * r⁻¹ = 1 := by
      have h1 : ι x₀ * r * (ι x₀)⁻¹ * r⁻¹ ∈ R :=
        mul_mem (hRn.conj_mem r hr (ι x₀)) (inv_mem hr)
      have h2 : ι x₀ * r * (ι x₀)⁻¹ * r⁻¹ ∈ ι.range := by
        rw [show ι x₀ * r * (ι x₀)⁻¹ * r⁻¹ = ι x₀ * (r * (ι x₀)⁻¹ * r⁻¹) by group]
        exact mul_mem ⟨x₀, rfl⟩ (hXn.conj_mem _ (inv_mem ⟨x₀, rfl⟩) r)
      obtain ⟨y, hy⟩ := h2
      have hyR : y ∈ R.comap ι := by
        show ι y ∈ R
        rw [hy]
        exact h1
      rw [hcomap, Subgroup.mem_bot] at hyR
      rw [← hy, hyR, map_one]
    have hxr : ι x₀ * r = r * ι x₀ := by
      calc ι x₀ * r = (ι x₀ * r * (ι x₀)⁻¹ * r⁻¹) * r * ι x₀ := by group
        _ = r * ι x₀ := by rw [hc, one_mul]
    calc ι x₀ * w * r = ι x₀ * (w * r) := by group
      _ = ι x₀ * (r * w) := by rw [Subgroup.mem_center_iff.mp hwc r]
      _ = r * (ι x₀ * w) := by rw [← mul_assoc, hxr, mul_assoc]
  refine ⟨le_antisymm hrad (le_sSup ⟨inferInstance, Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)⟩), hcen, ?_⟩
  set φ : X₀ →* K ⧸ Subgroup.center K := (QuotientGroup.mk' (Subgroup.center K)).comp ι with hφ
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcen] at hx
    rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq hz2' hx with h | h
    · exact hι (by rw [h, map_one])
    · exact absurd ⟨x, h⟩ hzX
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    obtain ⟨_, ⟨x₀, rfl⟩, w, hw, rfl⟩ := hdec k
    refine ⟨x₀, ?_⟩
    have hw1 : QuotientGroup.mk' (Subgroup.center K) w = 1 :=
      (QuotientGroup.eq_one_iff w).mpr (Subgroup.zpowers_le.mpr hz hw)
    rw [hφ, MonoidHom.comp_apply, map_mul, hw1, mul_one]
  exact ⟨(MulEquiv.ofBijective φ ⟨hφi, hφs⟩).symm.trans e⟩

omit [Finite G] in
theorem mem_closure_preimage_of_mem_closure {Y : Subgroup G} {s : Set G} (hs : s ⊆ Y) {x : G}
    (hx : x ∈ Subgroup.closure s) (hxY : x ∈ Y) :
    (⟨x, hxY⟩ : Y) ∈ Subgroup.closure (((↑) : Y → G) ⁻¹' s) := by
  have h : (Subgroup.closure (((↑) : Y → G) ⁻¹' s)).map Y.subtype = Subgroup.closure s := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro hy
      exact ⟨⟨y, hs hy⟩, hy, rfl⟩
  rw [← h] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = ⟨x, hxY⟩ := Subtype.ext hyx
  rwa [← this]

omit [Finite G] in
theorem conj_mem_commSet_of_mem_closure {D : Set G} (hD : IsNormalSet D) {d g e : G}
    (hg : g ∈ Subgroup.closure (commSet D d)) (he : e ∈ commSet D d) :
    g * e * g⁻¹ ∈ commSet D d := by
  have hgd : g ∈ Subgroup.centralizer ({d} : Set G) := by
    refine (Subgroup.closure_le _).mpr (fun x hx => ?_) hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr hx.2.1.eq
  have hgd' : g * d * g⁻¹ = d := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgd, mul_inv_cancel_right]
  refine ⟨hD g e he.1, ?_, fun h => he.2.2 ?_⟩
  · have := (Commute.conj_iff g).2 he.2.1
    rwa [hgd'] at this
  · calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹) * g := by rw [h, hgd']
      _ = d := by group

end ComponentTools

omit [Finite G] in
theorem d_mem_sylow_map_of_center_eq
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d) :
    hC.d ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  have hu2 : hC.d ^ 2 = 1 := by rw [sq, hC.setup.oddT.mul_self_eq_one hC.hd]
  have hp : IsPGroup 2 (Subgroup.center (Halpha D hC.alpha)) := by
    intro z
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hz : ((z : Halpha D hC.alpha) : G) ∈ Subgroup.zpowers hC.d := by
      rw [← hZ]
      exact ⟨z, z.2, rfl⟩
    rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq hu2 hz with h | h
    · simp [h]
    · simp [h, hu2]
  have hu : hC.d ∈ (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [hZ]
    exact Subgroup.mem_zpowers _
  exact Subgroup.map_mono (hp.le_sylow_of_normal T) hu

section Component

variable {L L₀ : Subgroup G} {Γ : Set G} {Y : Subgroup G}

omit [Finite G] in
theorem centralizerComponent_facts (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    (S : Set G) ∩ D ⊆ Γ ∧ Γ ⊆ (Subgroup.centralizer (L : Set G) : Set G) ∩ D ∧
      Y ≤ Subgroup.centralizer (L : Set G) ∧ (∀ y ∈ Y, ∀ c ∈ Γ, y * c * y⁻¹ ∈ Γ) ∧
      ∀ c ∈ Γ, ∀ d ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D, Commute d c → d ∈ Γ := by
  set C := (Subgroup.centralizer (L : Set G) : Set G) ∩ D with hCdef
  have huT := d_mem_sylow_map_of_center_eq (T := T) hL.center_eq
  have hTB : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.centralizer ((S : Set G) ∩ D) := hL.centralizer_eq ▸ le_sup_left
  have huC : hC.d ∈ C := ⟨Subgroup.mem_centralizer_iff.mpr fun l hl =>
    ((hL.centralizer_inf _ huT).mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) l hl).eq.symm,
    hC.hd⟩
  have hΓC : Γ ⊆ C := by
    rw [hΓ]
    intro c hc
    exact mem_of_reach (fun _ _ y hy _ => hy) huC hc
  have hCpres : ∀ g ∈ Subgroup.centralizer (L : Set G), ∀ x ∈ C, g * x * g⁻¹ ∈ C :=
    fun g hg x hx => conj_mem_centralizer_inter_of_mem_normalizer hC.setup.normal
      (Subgroup.centralizer_le_normalizer _ hg) hx
  have hΓpres : ∀ c' ∈ Γ, ∀ c ∈ Γ, c' * c * c'⁻¹ ∈ Γ := by
    intro c' hc' c hc
    have hc'C := hΓC hc'
    rw [hΓ] at hc' hc ⊢
    refine reach_conj_of_reach (hCpres c' hc'C.1) hc' ?_ hc
    rw [mul_inv_cancel_right]
    exact hc'
  refine ⟨fun δ hδ => ?_, hΓC, ?_, ?_, ?_⟩
  · have hδC : δ ∈ C := ⟨Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hL.le_centralizer hl) δ hδ).symm, hδ.2⟩
    rw [hΓ]
    exact reach_of_commute huC hδC (Subgroup.mem_centralizer_iff.mp (hTB huT) δ hδ).symm
  · rw [hY, Subgroup.closure_le]
    exact fun c hc => (hΓC hc).1
  · intro y hy c hc
    rw [hY] at hy
    induction hy using Subgroup.closure_induction'' generalizing c with
    | mem x hx => exact hΓpres x hx c hc
    | inv_mem x hx =>
      rw [hC.setup.oddT.inv_eq (hΓC hx).2]
      exact hΓpres x hx c hc
    | one => simpa using hc
    | mul x y _ _ hx hy =>
      rw [show x * y * c * (x * y)⁻¹ = x * (y * c * y⁻¹) * x⁻¹ by group]
      exact hx _ (hy c hc)
  · intro c hc d hd hdc
    have hcC := hΓC hc
    rw [hΓ] at hc ⊢
    exact Relation.ReflTransGen.tail hc ⟨hcC, hd, hdc.symm⟩

theorem exists_psl2_local (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀) :
    ∃ X : Subgroup G, Nonempty (X ≃* PSL2Model n) ∧ X ≤ Subgroup.centralizer ({hC.d} : Set G) ∧
      X ≤ Subgroup.centralizer (L : Set G) ∧ U ≤ X ∧
      (∀ d : G, (d ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D ∧ Commute d hC.d ∧
        d ≠ hC.d) ↔ (hC.d * d ∈ X ∧ orderOf (hC.d * d) = 2)) ∧
      (∀ x ∈ X, ∀ y ∈ X, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ X, g * x * g⁻¹ = y) ∧
      (∀ x ∈ X, orderOf x = 2 → ∃ s ∈ X, orderOf s = 2 ∧ s ≠ x ∧ s * x = x * s) ∧
      (∀ z ∈ X, (∀ x ∈ X, orderOf x = 2 → z * x = x * z) → z = 1) ∧
      X ≤ Subgroup.closure {x | x ∈ X ∧ orderOf x = 2} := by
  obtain ⟨X, ⟨eX⟩, hXL, hXu, -, hUX, -, hXD⟩ :=
    exists_psl2_centralizer_of_psu3 hH h3 hU hCH eH hUn hL.odd_card hL.ne_bot hL.le_centralizer
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  have hBX : CFSG.GH74.Uniqueness.Bender.BenderType X n 1 1 := .linear n hn2 eX
  have : IsSimpleGroup X := hBX.isSimple
  have hZX : Subgroup.center X = ⊥ := hBX.center_eq_bot
  have hXB : IsBenderGroup X := .isPSL2 n hn2 eX
  have := hU.isElementaryAbelian
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have hUinv : ∀ v ∈ U, v ≠ 1 → orderOf v = 2 := fun v hv hv1 =>
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian v hv) hv1
  have hUcomm : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hthird : ∀ v ∈ U, ∃ w ∈ U, w ≠ 1 ∧ w ≠ v := by
    intro v hv
    by_contra hall
    push Not at hall
    have hsub : (U : Set G) ⊆ {1, v} := fun w hw => by
      by_cases h1 : w = 1
      · exact Or.inl h1
      · exact Or.inr (hall w hw h1)
    have hcard : (U : Set G).ncard ≤ 2 :=
      calc (U : Set G).ncard ≤ ({1, v} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({v} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq] at hcard
    change Nat.card U ≤ 2 at hcard
    rw [hUn] at hcard
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hv₀X : orderOf (⟨v₀, hUX hv₀⟩ : X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hUinv v₀ hv₀ hv₀1'
  have hgen := closure_orderOf_eq_two_eq_top hv₀X
  have hconj : ∀ x ∈ X, ∀ y ∈ X, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ X, g * x * g⁻¹ = y := by
    intro x hx y hy hx2 hy2
    obtain ⟨g, hg⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hXB
      (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk]))
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  refine ⟨X, ⟨eX⟩, hXu, hXL, hUX, fun d => ?_, hconj, ?_, ?_, ?_⟩
  · rw [← hXD d]
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h2, h1, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h1⟩, h3, h4⟩⟩
  · intro x hx hx2
    obtain ⟨g, hg, hgx⟩ := hconj x hx v₀ (hUX hv₀) hx2 (hUinv v₀ hv₀ hv₀1')
    obtain ⟨w, hw, hw1, hwv⟩ := hthird v₀ hv₀
    refine ⟨g⁻¹ * w * g, mul_mem (mul_mem (inv_mem hg) (hUX hw)) hg, ?_, ?_, ?_⟩
    · rw [show g⁻¹ * w * g = g⁻¹ * w * g⁻¹⁻¹ by group, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hUinv w hw hw1
    · intro h
      apply hwv
      rw [← hgx, ← h]
      group
    · have h1 := hUcomm w hw v₀ hv₀
      rw [← hgx] at h1
      calc g⁻¹ * w * g * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * w) * g := by rw [h1]
        _ = x * (g⁻¹ * w * g) := by group
  · intro z hz hzc
    have hle : Subgroup.closure {x : X | orderOf x = 2} ≤
        Subgroup.centralizer ({⟨z, hz⟩} : Set X) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      exact Subtype.ext (hzc x x.2 hx2).symm
    have hzZ : (⟨z, hz⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : y ∈ Subgroup.closure {x : X | orderOf x = 2} := by
        rw [hgen]
        exact Subgroup.mem_top _
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    rw [hZX, Subgroup.mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  · intro x hx
    have hx' : (⟨x, hx⟩ : X) ∈ Subgroup.closure {y : X | orderOf y = 2} := by
      rw [hgen]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure {y : X | orderOf y = 2} ≤
        (Subgroup.closure {x | x ∈ X ∧ orderOf x = 2}).comap X.subtype := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.subset_closure ⟨y.2, by
        change orderOf (y : G) = 2
        rw [Subgroup.orderOf_coe]
        exact hy⟩
    exact hle hx'

theorem exists_conj_eq_of_commute_of_mem_centralizer
    (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀) {c : G}
    (hc : c ∈ (Subgroup.centralizer (L : Set G) : Set G) ∩ D) (hcu : Commute c hC.d)
    (hcu1 : c ≠ hC.d) : ∃ h ∈ Subgroup.normalizer (L : Set G), h * hC.d * h⁻¹ = c := by
  obtain ⟨X, -, hXu, hXL, hUX, hXD, hconj, -, -, -⟩ := exists_psl2_local hH h3 hU hCH eH hUn hL
  obtain ⟨hucX, huc2⟩ := (hXD c).mp ⟨hc, hcu, hcu1⟩
  have := hU.isElementaryAbelian
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have hv₀2 : orderOf v₀ = 2 :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian v₀ hv₀) hv₀1'
  obtain ⟨x, hx, hxc⟩ := hconj _ hucX v₀ (hUX hv₀) huc2 hv₀2
  have hxu : x * hC.d = hC.d * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hxc' : x * c * x⁻¹ = hC.d * v₀ := by
    rw [← hxc]
    calc x * c * x⁻¹ = (x * hC.d) * (hC.d * c) * x⁻¹ := by
          rw [mul_assoc x hC.d, ← mul_assoc hC.d hC.d, hu2, one_mul]
      _ = hC.d * (x * (hC.d * c) * x⁻¹) := by rw [hxu]; group
  have hu : hC.d ∈ (fun v : G => hC.d * v) '' (U : Set G) := ⟨1, U.one_mem, mul_one _⟩
  obtain ⟨g, hg, hgδ⟩ := hU.transitive _ ⟨v₀, hv₀, rfl⟩ _ hu
  have hgN : g ∈ Subgroup.normalizer ((S : Set G) ∩ D) := by
    rw [hU.sylow_inter]
    exact hg
  obtain ⟨t, ht, htg⟩ := hL.normalizer_eq g hgN
  have huΔ : hC.d ∈ (S : Set G) ∩ D := by
    rw [hU.sylow_inter]
    exact hu
  have htB : t ∈ Subgroup.centralizer ((S : Set G) ∩ D) := by
    rw [hL.centralizer_eq]
    exact Subgroup.mem_sup_left ht
  have htu : t * hC.d * t⁻¹ = hC.d := by
    rw [← Subgroup.mem_centralizer_iff.mp htB _ huΔ, mul_inv_cancel_right]
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ (hXL hx)
  refine ⟨(t * g * x)⁻¹, inv_mem (mul_mem htg hxN), ?_⟩
  have key : (t * g * x) * c * (t * g * x)⁻¹ = hC.d := by
    calc (t * g * x) * c * (t * g * x)⁻¹ = t * (g * (x * c * x⁻¹) * g⁻¹) * t⁻¹ := by group
      _ = hC.d := by rw [hxc', hgδ, htu]
  rw [← key]
  group

theorem conj_centralizerComponent_of_mem (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d}) :
    ∀ w ∈ Γ, ∃ g ∈ Subgroup.normalizer (L : Set G), g * hC.d * g⁻¹ = w ∧
      ∀ c ∈ Γ, g * c * g⁻¹ ∈ Γ := by
  set C := (Subgroup.centralizer (L : Set G) : Set G) ∩ D with hCdef
  have hpres : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ x ∈ C, g * x * g⁻¹ ∈ C :=
    fun g hg x hx => conj_mem_centralizer_inter_of_mem_normalizer hC.setup.normal hg hx
  have hstab : ∀ g ∈ Subgroup.normalizer (L : Set G), g * hC.d * g⁻¹ ∈ Γ →
      ∀ c ∈ Γ, g * c * g⁻¹ ∈ Γ := by
    intro g hg hgu c hc
    rw [hΓ] at hgu hc ⊢
    exact reach_conj_of_reach (hpres g hg) Relation.ReflTransGen.refl hgu hc
  suffices h : ∀ w, Reach C hC.d w → ∃ g ∈ Subgroup.normalizer (L : Set G),
      g * hC.d * g⁻¹ = w ∧ ∀ c ∈ Γ, g * c * g⁻¹ ∈ Γ by
    intro w hw
    rw [hΓ] at hw
    exact h w hw
  intro w hw
  induction hw with
  | refl => exact ⟨1, one_mem _, by group, fun c hc => by simpa using hc⟩
  | @tail b c hab hbc ih =>
    obtain ⟨g, hg, hgu, hgΓ⟩ := ih
    have hcΓ : c ∈ Γ := by
      rw [hΓ]
      exact Relation.ReflTransGen.tail hab hbc
    by_cases hcb : c = b
    · subst hcb
      exact ⟨g, hg, hgu, hgΓ⟩
    · have hginv : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hg
      have hc'C : g⁻¹ * c * g⁻¹⁻¹ ∈ C := hpres _ hginv c hbc.2.1
      have hc'u : Commute (g⁻¹ * c * g⁻¹⁻¹) hC.d := by
        have h1 := (Commute.conj_iff g⁻¹).2 hbc.2.2.symm
        rwa [show g⁻¹ * b * g⁻¹⁻¹ = hC.d by rw [← hgu]; group] at h1
      have hc'1 : g⁻¹ * c * g⁻¹⁻¹ ≠ hC.d := by
        intro h
        apply hcb
        rw [← hgu, ← h]
        group
      obtain ⟨h, hh, hhu⟩ :=
        exists_conj_eq_of_commute_of_mem_centralizer hH h3 hU hCH eH hUn hL hc'C hc'u hc'1
      have hgh : g * h ∈ Subgroup.normalizer (L : Set G) := mul_mem hg hh
      have hghu : g * h * hC.d * (g * h)⁻¹ = c := by
        calc g * h * hC.d * (g * h)⁻¹ = g * (h * hC.d * h⁻¹) * g⁻¹ := by group
          _ = c := by rw [hhu]; group
      exact ⟨g * h, hgh, hghu, hstab _ hgh (hghu ▸ hcΓ)⟩

theorem transitive_centralizerComponent (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    ∀ c ∈ Γ, ∃ y ∈ Y, y * hC.d * y⁻¹ = c := by
  set C := (Subgroup.centralizer (L : Set G) : Set G) ∩ D with hCdef
  obtain ⟨-, hΓC, -, -, hΓcl⟩ := centralizerComponent_facts hL hΓ hY
  obtain ⟨X, -, hXu, -, -, hXD, hconj, hsec, -, hXgen⟩ := exists_psl2_local hH h3 hU hCH eH hUn hL
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  have huC := hΓC huΓ
  have hnbrΓ : ∀ d ∈ C, Commute d hC.d → d ∈ Γ := fun d hd hdu => hΓcl _ huΓ d hd hdu
  have hXY : X ≤ Y := by
    refine hXgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro t ⟨htX, ht2⟩
    have hut : hC.d * (hC.d * t) = t := by rw [← mul_assoc, hu2, one_mul]
    obtain ⟨hutC, hutu, -⟩ :=
      (hXD (hC.d * t)).mpr ⟨by rw [hut]; exact htX, by rw [hut]; exact ht2⟩
    rw [SetLike.mem_coe, ← hut, hY]
    exact mul_mem (Subgroup.subset_closure huΓ) (Subgroup.subset_closure (hnbrΓ _ hutC hutu))
  have hYconj : ∀ g : G, (∀ c ∈ Γ, g * c * g⁻¹ ∈ Γ) → ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    rw [hY] at hy ⊢
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hg x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  have hloc : ∀ d ∈ C, Commute d hC.d → d ≠ hC.d → ∀ d' ∈ C, Commute d' hC.d → d' ≠ hC.d →
      ∃ x ∈ X, x * d * x⁻¹ = d' := by
    intro d hd hdu hdu1 d' hd' hd'u hd'u1
    obtain ⟨hudX, hud2⟩ := (hXD d).mp ⟨hd, hdu, hdu1⟩
    obtain ⟨hud'X, hud'2⟩ := (hXD d').mp ⟨hd', hd'u, hd'u1⟩
    obtain ⟨x, hx, hxd⟩ := hconj _ hudX _ hud'X hud2 hud'2
    refine ⟨x, hx, ?_⟩
    have hxu : x * hC.d = hC.d * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
    calc x * d * x⁻¹ = hC.d * (x * (hC.d * d) * x⁻¹) := by
          rw [show x * (hC.d * d) * x⁻¹ = x * hC.d * d * x⁻¹ by group, hxu,
            show hC.d * (hC.d * x * d * x⁻¹) = (hC.d * hC.d) * (x * d * x⁻¹) by group, hu2,
            one_mul]
      _ = d' := by rw [hxd, ← mul_assoc, hu2, one_mul]
  have hstep : ∀ c ∈ C, Commute c hC.d → c ≠ hC.d → ∃ y ∈ Y, y * hC.d * y⁻¹ = c := by
    intro c hc hcu hcu1
    obtain ⟨hucX, huc2⟩ := (hXD c).mp ⟨hc, hcu, hcu1⟩
    obtain ⟨s, hsX, hs2, hst, hscomm⟩ := hsec _ hucX huc2
    have hus : hC.d * (hC.d * s) = s := by rw [← mul_assoc, hu2, one_mul]
    obtain ⟨heC, heu, heu1⟩ :=
      (hXD (hC.d * s)).mpr ⟨by rw [hus]; exact hsX, by rw [hus]; exact hs2⟩
    have hsu : s * hC.d = hC.d * s := Subgroup.mem_centralizer_singleton_iff.mp (hXu hsX)
    have hec : Commute (hC.d * s) c := by
      have h1 : hC.d * s * c = s * (hC.d * c) := by rw [← hsu, mul_assoc]
      have h2 : c * (hC.d * s) = (hC.d * c) * s := by rw [← mul_assoc, hcu.eq]
      show hC.d * s * c = c * (hC.d * s)
      rw [h1, h2, hscomm]
    have hec1 : hC.d * s ≠ c := by
      intro h
      apply hst
      rw [← hus, h]
    obtain ⟨x₁, hx₁, hx₁c⟩ := hloc c hc hcu hcu1 _ heC heu heu1
    obtain ⟨g, hgN, hgu, hgΓ⟩ :=
      conj_centralizerComponent_of_mem hH h3 hU hCH eH hUn hL hΓ c (hnbrΓ c hc hcu)
    have hpres : ∀ x ∈ C, g⁻¹ * x * g⁻¹⁻¹ ∈ C := fun x hx =>
      conj_mem_centralizer_inter_of_mem_normalizer hC.setup.normal (inv_mem hgN) hx
    have hgc : g⁻¹ * c * g⁻¹⁻¹ = hC.d := by rw [← hgu]; group
    have hu' : Commute (g⁻¹ * hC.d * g⁻¹⁻¹) hC.d := by
      have := (Commute.conj_iff g⁻¹).2 hcu.symm
      rwa [hgc] at this
    have hu'1 : g⁻¹ * hC.d * g⁻¹⁻¹ ≠ hC.d := by
      intro h
      apply hcu1
      calc c = g * hC.d * g⁻¹ := hgu.symm
        _ = g * (g⁻¹ * hC.d * g⁻¹⁻¹) * g⁻¹ := by rw [h]
        _ = hC.d := by group
    have he' : Commute (g⁻¹ * (hC.d * s) * g⁻¹⁻¹) hC.d := by
      have := (Commute.conj_iff g⁻¹).2 hec
      rwa [hgc] at this
    have he'1 : g⁻¹ * (hC.d * s) * g⁻¹⁻¹ ≠ hC.d := by
      intro h
      apply hec1
      calc hC.d * s = g * (g⁻¹ * (hC.d * s) * g⁻¹⁻¹) * g⁻¹ := by group
        _ = c := by rw [h, hgu]
    obtain ⟨x₂, hx₂, hx₂e⟩ :=
      hloc _ (hpres _ huC) hu' hu'1 _ (hpres _ heC) he' he'1
    refine ⟨x₁⁻¹ * (g * x₂ * g⁻¹), mul_mem (inv_mem (hXY hx₁)) (hYconj g hgΓ _ (hXY hx₂)), ?_⟩
    have hx' : (g * x₂ * g⁻¹) * hC.d * (g * x₂ * g⁻¹)⁻¹ = hC.d * s := by
      calc (g * x₂ * g⁻¹) * hC.d * (g * x₂ * g⁻¹)⁻¹ =
            g * (x₂ * (g⁻¹ * hC.d * g⁻¹⁻¹) * x₂⁻¹) * g⁻¹ := by group
        _ = hC.d * s := by rw [hx₂e]; group
    calc x₁⁻¹ * (g * x₂ * g⁻¹) * hC.d * (x₁⁻¹ * (g * x₂ * g⁻¹))⁻¹ =
          x₁⁻¹ * ((g * x₂ * g⁻¹) * hC.d * (g * x₂ * g⁻¹)⁻¹) * x₁ := by group
      _ = c := by rw [hx', ← hx₁c]; group
  intro c hc
  have hc' := hc
  rw [hΓ] at hc'
  induction hc' with
  | refl => exact ⟨1, one_mem _, by group⟩
  | @tail b c' hab hbc ih =>
    have hbΓ : b ∈ Γ := by
      rw [hΓ]
      exact hab
    obtain ⟨y, hy, hyb⟩ := ih hbΓ
    by_cases hcb : c' = b
    · subst hcb
      exact ⟨y, hy, hyb⟩
    · have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.centralizer_le_normalizer _
          ((centralizerComponent_facts hL hΓ hY).2.2.1 hy)
      have hc'C : y⁻¹ * c' * y⁻¹⁻¹ ∈ C :=
        conj_mem_centralizer_inter_of_mem_normalizer hC.setup.normal (inv_mem hyL) hbc.2.1
      have hyu : y⁻¹ * b * y⁻¹⁻¹ = hC.d := by rw [← hyb]; group
      have hc'u : Commute (y⁻¹ * c' * y⁻¹⁻¹) hC.d := by
        have := (Commute.conj_iff y⁻¹).2 hbc.2.2.symm
        rwa [hyu] at this
      have hc'1 : y⁻¹ * c' * y⁻¹⁻¹ ≠ hC.d := by
        intro h
        apply hcb
        calc c' = y * (y⁻¹ * c' * y⁻¹⁻¹) * y⁻¹ := by group
          _ = b := by rw [h, hyb]
      obtain ⟨y', hy', hy'u⟩ := hstep _ hc'C hc'u hc'1
      refine ⟨y * y', mul_mem hy hy', ?_⟩
      calc y * y' * hC.d * (y * y')⁻¹ = y * (y' * hC.d * y'⁻¹) * y⁻¹ := by group
        _ = c' := by rw [hy'u]; group

theorem eq_of_commute_iff_centralizerComponent (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d}) :
    ∀ c ∈ Γ, ∀ c' ∈ Γ, (∀ x ∈ Γ, Commute x c ↔ Commute x c') → c = c' := by
  set C := (Subgroup.centralizer (L : Set G) : Set G) ∩ D with hCdef
  obtain ⟨-, hΓC, -, -, hΓcl⟩ := centralizerComponent_facts (Y := Subgroup.closure Γ) hL hΓ rfl
  obtain ⟨X, -, hXu, -, -, hXD, -, -, hZ, -⟩ := exists_psl2_local hH h3 hU hCH eH hUn hL
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  intro c hc c' hc' hcc'
  by_contra hne
  have hcc : Commute c c' := (hcc' c hc).mp (Commute.refl c)
  obtain ⟨g, hgN, hgu, hgΓ⟩ := conj_centralizerComponent_of_mem hH h3 hU hCH eH hUn hL hΓ c hc
  have hgc : g⁻¹ * c * g⁻¹⁻¹ = hC.d := by rw [← hgu]; group
  set e := g⁻¹ * c' * g⁻¹⁻¹ with he
  have heC : e ∈ C :=
    conj_mem_centralizer_inter_of_mem_normalizer hC.setup.normal (inv_mem hgN) (hΓC hc')
  have heu : Commute e hC.d := by
    have := (Commute.conj_iff g⁻¹).2 hcc.symm
    rwa [hgc] at this
  have heu1 : e ≠ hC.d := by
    intro h
    apply hne
    calc c = g * hC.d * g⁻¹ := hgu.symm
      _ = g * e * g⁻¹ := by rw [h]
      _ = c' := by rw [he]; group
  obtain ⟨hueX, hue2⟩ := (hXD e).mp ⟨heC, heu, heu1⟩
  have hcent : ∀ t ∈ X, orderOf t = 2 → (hC.d * e) * t = t * (hC.d * e) := by
    intro t htX ht2
    have hut : hC.d * (hC.d * t) = t := by rw [← mul_assoc, hu2, one_mul]
    obtain ⟨hutC, hutu, -⟩ :=
      (hXD (hC.d * t)).mpr ⟨by rw [hut]; exact htX, by rw [hut]; exact ht2⟩
    have hutΓ : hC.d * t ∈ Γ := hΓcl _ huΓ _ hutC hutu
    have h1 : Commute (g * (hC.d * t) * g⁻¹) c := by
      rw [← hgu]
      exact (Commute.conj_iff g).2 hutu
    have h2 := (hcc' _ (hgΓ _ hutΓ)).mp h1
    have h3' : Commute (hC.d * t) e := by
      have := (Commute.conj_iff g⁻¹).2 h2
      rwa [show g⁻¹ * (g * (hC.d * t) * g⁻¹) * g⁻¹⁻¹ = hC.d * t by group] at this
    have hte : t * hC.d = hC.d * t := Subgroup.mem_centralizer_singleton_iff.mp (hXu htX)
    have hte' : t * e = e * t := by
      have h5 : hC.d * (t * e) = hC.d * (e * t) := by
        calc hC.d * (t * e) = (hC.d * t) * e := by group
          _ = e * (hC.d * t) := h3'.eq
          _ = hC.d * (e * t) := by rw [← mul_assoc, heu.eq, mul_assoc]
      exact mul_left_cancel h5
    calc (hC.d * e) * t = hC.d * (e * t) := by group
      _ = hC.d * (t * e) := by rw [hte']
      _ = t * (hC.d * e) := by rw [← mul_assoc, ← hte, mul_assoc]
  have h1 := hZ _ hueX hcent
  rw [h1, orderOf_one] at hue2
  exact absurd hue2 (by decide)

end Component

theorem pCore_two_le_center_of_commute_iff_injective {X : Type*} [Group X] [Finite X]
    {Θ : Set X} (hodd : IsOddTransp Θ) (hN : IsNormalSet Θ) (hgen : Subgroup.closure Θ = ⊤)
    (hinj : ∀ a ∈ Θ, ∀ b ∈ Θ, (∀ x ∈ Θ, Commute x a ↔ Commute x b) → a = b) :
    CFSG.pCore 2 X ≤ Subgroup.center X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hPp : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hodd1 : ∀ y ∈ CFSG.pCore 2 X, Odd (orderOf y) → y = 1 := by
    intro y hy hyo
    obtain ⟨k, hk⟩ := hPp ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    rcases i with _ | i
    · rwa [pow_zero, orderOf_eq_one_iff] at hi
    · exfalso
      rw [hi] at hyo
      exact Nat.not_even_iff_odd.mpr hyo (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero _⟩)
  have hmemP : ∀ a ∈ Θ, ∀ x ∈ CFSG.pCore 2 X, a * (x * a * x⁻¹) ∈ CFSG.pCore 2 X := by
    intro a ha x hx
    have h1 : a * (x * a * x⁻¹) = (a * x * a⁻¹) * x⁻¹ := by rw [hodd.inv_eq ha]; group
    rw [h1]
    exact mul_mem (hPn.conj_mem x hx a) (inv_mem hx)
  have hcomm : ∀ a ∈ Θ, ∀ x ∈ CFSG.pCore 2 X, Commute a (x * a * x⁻¹) := by
    intro a ha x hx
    rcases hodd.commute_or_odd ha (hN x a ha) with h | h
    · exact h
    · rw [← hodd.eq_of_mul_eq_one ha (hodd1 _ (hmemP a ha x hx) h)]
  have hnb : ∀ a ∈ Θ, ∀ x ∈ CFSG.pCore 2 X, ∀ d ∈ Θ, Commute d a →
      Commute d (x * a * x⁻¹) := by
    intro a ha x hx d hd hda
    have hbΘ : x * a * x⁻¹ ∈ Θ := hN x a ha
    by_contra hdb
    have hodd' : Odd (orderOf (x * a * x⁻¹ * d)) :=
      hodd.odd_of_not_commute hbΘ hd fun h => hdb h.symm
    have hab : a * (x * a * x⁻¹) = (x * a * x⁻¹) * a := (hcomm a ha x hx).eq
    have ha2 := hodd.mul_self_eq_one ha
    have key : (x * a * x⁻¹ * d) ^ 2 =
        (a * (x * a * x⁻¹)) * (d * (a * (x * a * x⁻¹)) * d⁻¹) := by
      rw [hodd.inv_eq hd, sq]
      calc x * a * x⁻¹ * d * (x * a * x⁻¹ * d) =
            (a * a) * (x * a * x⁻¹ * d * (x * a * x⁻¹ * d)) := by rw [ha2, one_mul]
        _ = a * (a * (x * a * x⁻¹)) * d * (x * a * x⁻¹) * d := by group
        _ = a * ((x * a * x⁻¹) * a) * d * (x * a * x⁻¹) * d := by rw [hab]
        _ = a * (x * a * x⁻¹) * (a * d) * (x * a * x⁻¹) * d := by group
        _ = a * (x * a * x⁻¹) * (d * a) * (x * a * x⁻¹) * d := by rw [← hda.eq]
        _ = (a * (x * a * x⁻¹)) * (d * (a * (x * a * x⁻¹)) * d) := by group
    have hmem : (x * a * x⁻¹ * d) ^ 2 ∈ CFSG.pCore 2 X := by
      rw [key]
      exact mul_mem (hmemP a ha x hx) (hPn.conj_mem _ (hmemP a ha x hx) d)
    have h1 := hodd1 _ hmem (hodd'.of_dvd_nat (orderOf_pow_dvd _))
    have h2 : x * a * x⁻¹ * d * (x * a * x⁻¹ * d) = 1 := by rw [← sq]; exact h1
    apply hdb
    show d * (x * a * x⁻¹) = (x * a * x⁻¹) * d
    calc d * (x * a * x⁻¹) = d⁻¹ * (x * a * x⁻¹)⁻¹ := by
          rw [hodd.inv_eq hd, hodd.inv_eq hbΘ]
      _ = (x * a * x⁻¹ * d)⁻¹ := (mul_inv_rev _ _).symm
      _ = x * a * x⁻¹ * d := (eq_inv_of_mul_eq_one_left h2).symm
  have hfix : ∀ a ∈ Θ, ∀ x ∈ CFSG.pCore 2 X, x * a * x⁻¹ = a := by
    intro a ha x hx
    refine (hinj a ha _ (hN x a ha) fun d hd => ⟨fun h => hnb a ha x hx d hd h, fun h => ?_⟩).symm
    have := hnb (x * a * x⁻¹) (hN x a ha) x⁻¹ (inv_mem hx) d hd h
    rwa [show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group] at this
  intro x hx
  have hle : Subgroup.closure Θ ≤ Subgroup.centralizer ({x} : Set X) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc a * x = (x * a * x⁻¹) * x := by rw [hfix a ha x hx]
      _ = x * a := by group
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure Θ := by
    rw [hgen]
    exact Subgroup.mem_top g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

section Component

variable {L L₀ : Subgroup G} {Γ : Set G} {Y : Subgroup G}

theorem setup_centralizerComponent (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    Setup Y (((↑) : Y → G) ⁻¹' Γ) ∧
      ∀ a ∈ (((↑) : Y → G) ⁻¹' Γ), ∀ b ∈ (((↑) : Y → G) ⁻¹' Γ),
        (∀ x ∈ (((↑) : Y → G) ⁻¹' Γ), Commute x a ↔ Commute x b) → a = b := by
  obtain ⟨-, hΓC, -, hYΓ, -⟩ := centralizerComponent_facts hL hΓ hY
  have htrans := transitive_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  have htwin := eq_of_commute_iff_centralizerComponent hH h3 hU hCH eH hUn hL hΓ
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  have hΓY : ∀ c ∈ Γ, c ∈ Y := fun c hc => by
    rw [hY]
    exact Subgroup.subset_closure hc
  refine ⟨⟨⟨⟨hC.d, hΓY _ huΓ⟩, Set.ext fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨y, hy, hyg⟩ := htrans g hg
    exact isConj_iff.mpr ⟨⟨y, hy⟩, Subtype.ext hyg⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.mp hg
    exact hYΓ c c.2 _ huΓ
  · exact (hC.setup.oddT.mono fun c hc => (hΓC hc).2).preimage Y
  · subst hY
    exact Subgroup.closure_closure_coe_preimage
  · intro a ha b hb hab
    apply Subtype.ext
    refine htwin a ha b hb fun x hx => ?_
    have h := hab ⟨x, hΓY x hx⟩ hx
    exact ⟨fun h' => congrArg Subtype.val (h.mp (Subtype.ext h')),
      fun h' => congrArg Subtype.val (h.mpr (Subtype.ext h'))⟩

theorem oddCore_centralizerComponent_le_center (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    CFSG.oddCore Y ≤ Subgroup.center Y := by
  obtain ⟨hS, -⟩ := setup_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  obtain ⟨hΔΓ, -, -, -, -⟩ := centralizerComponent_facts hL hΓ hY
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  have hΓY : ∀ c ∈ Γ, c ∈ Y := fun c hc => by
    rw [hY]
    exact Subgroup.subset_closure hc
  have := hU.isElementaryAbelian
  have hUsq : ∀ v ∈ U, v * v = 1 := fun v hv => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  have hUcomm : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨w, hw⟩)
  have huU : ∀ v ∈ U, v * hC.d = hC.d * v := fun v hv =>
    Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer v hv
  obtain ⟨⟨v₁, hv₁⟩, hv₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hv₁1' : v₁ ≠ 1 := fun h => hv₁1 (Subtype.ext h)
  obtain ⟨v₂, hv₂, hv₂1, hv₂v₁⟩ : ∃ w ∈ U, w ≠ 1 ∧ w ≠ v₁ := by
    by_contra hall
    push Not at hall
    have hsub : (U : Set G) ⊆ {1, v₁} := fun w hw => by
      by_cases h1 : w = 1
      · exact Or.inl h1
      · exact Or.inr (hall w hw h1)
    have hcard : (U : Set G).ncard ≤ 2 :=
      calc (U : Set G).ncard ≤ ({1, v₁} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({v₁} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq] at hcard
    change Nat.card U ≤ 2 at hcard
    rw [hUn] at hcard
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hv₃1 : v₁ * v₂ ≠ 1 := by
    intro h
    apply hv₂v₁
    calc v₂ = v₁ * (v₁ * v₂) := by rw [← mul_assoc, hUsq v₁ hv₁, one_mul]
      _ = v₁ := by rw [h, mul_one]
  have hmemΓ : ∀ v ∈ U, hC.d * v ∈ Γ := fun v hv => hΔΓ (by rw [hU.sylow_inter]; exact ⟨v, hv, rfl⟩)
  have hcs : ∀ v (hv : v ∈ U), v ≠ 1 → (⟨hC.d * v, hΓY _ (hmemΓ v hv)⟩ : Y) ∈
      commSet (((↑) : Y → G) ⁻¹' Γ) ⟨hC.d, hΓY _ huΓ⟩ := by
    intro v hv hv1
    refine ⟨hmemΓ v hv, Subtype.ext ?_, fun h => hv1 ?_⟩
    · change hC.d * v * hC.d = hC.d * (hC.d * v)
      rw [mul_assoc, ← huU v hv]
    · have h' : hC.d * v = hC.d := congrArg Subtype.val h
      calc v = hC.d⁻¹ * (hC.d * v) := by group
        _ = 1 := by rw [h', inv_mul_cancel]
  have hprod : hC.d * v₁ * (hC.d * v₂) * (hC.d * (v₁ * v₂)) = hC.d := by
    have e1 := huU v₁ hv₁
    have e2 := huU v₂ hv₂
    have e12 := hUcomm v₂ hv₂ v₁ hv₁
    calc hC.d * v₁ * (hC.d * v₂) * (hC.d * (v₁ * v₂)) =
          hC.d * (v₁ * hC.d) * v₂ * hC.d * v₁ * v₂ := by group
      _ = hC.d * (hC.d * v₁) * (v₂ * hC.d) * v₁ * v₂ := by rw [e1]; group
      _ = hC.d * (hC.d * v₁) * (hC.d * v₂) * v₁ * v₂ := by rw [e2]
      _ = (hC.d * hC.d) * (v₁ * hC.d) * v₂ * v₁ * v₂ := by group
      _ = (hC.d * hC.d) * (hC.d * v₁) * (v₂ * v₁) * v₂ := by rw [e1]; group
      _ = (hC.d * hC.d) * hC.d * (v₁ * v₁) * (v₂ * v₂) := by rw [e12]; group
      _ = hC.d := by rw [hu2, hUsq v₁ hv₁, hUsq v₂ hv₂]; group
  have huD : (⟨hC.d, hΓY _ huΓ⟩ : Y) ∈
      Subgroup.closure (commSet (((↑) : Y → G) ⁻¹' Γ) ⟨hC.d, hΓY _ huΓ⟩) := by
    have e : (⟨hC.d, hΓY _ huΓ⟩ : Y) = ⟨hC.d * v₁, hΓY _ (hmemΓ v₁ hv₁)⟩ *
        ⟨hC.d * v₂, hΓY _ (hmemΓ v₂ hv₂)⟩ *
          ⟨hC.d * (v₁ * v₂), hΓY _ (hmemΓ _ (mul_mem hv₁ hv₂))⟩ :=
      Subtype.ext hprod.symm
    have h := mul_mem (mul_mem (Subgroup.subset_closure (hcs v₁ hv₁ hv₁1'))
      (Subgroup.subset_closure (hcs v₂ hv₂ hv₂1)))
      (Subgroup.subset_closure (hcs _ (mul_mem hv₁ hv₂) hv₃1))
    rwa [← e] at h
  refine sSup_le fun N hN => ?_
  exact normal_le_center_of_mem_closure_commSet' hS hN.1 hN.2 (show (⟨hC.d, hΓY _ huΓ⟩ : Y) ∈
    ((↑) : Y → G) ⁻¹' Γ from huΓ) huD

theorem solvableRadical_centralizerComponent_eq_center
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    CFSG.solvableRadical Y = Subgroup.center Y := by
  obtain ⟨hS, htwin⟩ := setup_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  have hO2 := pCore_two_le_center_of_commute_iff_injective hS.oddT hS.normal hS.gen htwin
  have hO := oddCore_centralizerComponent_le_center hH h3 hU hCH eH hUn hL hΓ hY
  set R := CFSG.solvableRadical Y with hR
  have hRs : Group.IsSolvable R := CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical
  have hcore : ∀ s ∈ (Nat.card R).primeFactors,
      (CFSG.pCore s R).map R.subtype ≤ Subgroup.center Y := by
    intro s hs
    have hsp : s.Prime := Nat.prime_of_mem_primeFactors hs
    have : Fact s.Prime := ⟨hsp⟩
    have hmn : ((CFSG.pCore s R).map R.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hmp : IsPGroup s ((CFSG.pCore s R).map R.subtype) := CFSG.pCore_isPGroup.map _
    by_cases hs2 : s = 2
    · subst hs2
      exact (le_sSup ⟨hmn, hmp⟩ : _ ≤ CFSG.pCore 2 Y).trans hO2
    · have hodd : Odd (Nat.card ((CFSG.pCore s R).map R.subtype)) := by
        obtain ⟨k, hk⟩ := hmp.exists_card_eq
        rw [hk]
        exact (hsp.odd_of_ne_two hs2).pow
      exact (le_sSup ⟨hmn, hodd⟩ : _ ≤ CFSG.oddCore Y).trans hO
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)⟩)
  have hF : (⊤ : Subgroup Y) ≤
      Subgroup.centralizer (((CFSG.fittingSubgroup R).map R.subtype : Subgroup Y) : Set Y) := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ (fun s g _ => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.1 (hcore s.1.1 s.1.2 hz) g).symm
  intro y hy
  have hyF : (⟨y, hy⟩ : R) ∈ CFSG.fittingSubgroup R := by
    apply CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hRs
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hF (Subgroup.mem_top y)) (f : Y)
      (Subgroup.mem_map_of_mem _ hf)
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.1 (hF (Subgroup.mem_top g)) y
    (Subgroup.mem_map.2 ⟨⟨y, hy⟩, hyF, rfl⟩)).symm

omit [Finite G] in
theorem eq_one_of_mem_of_odd_of_isPGroup {L P : Subgroup G} (hL : Odd (Nat.card L))
    (hP : IsPGroup 2 P) {x : G} (hxL : x ∈ L) (hxP : x ∈ P) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L hxL
    exact this
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (2 ^ k) (Nat.card L) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hL)
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
  rwa [orderOf_eq_one_iff] at this

theorem UnitaryCentralizerData.mem_of_commute_of_pow_eq_one
    (hL : UnitaryCentralizerData hC T S U n L L₀) {w : G}
    (hwB : w ∈ Subgroup.centralizer ((S : Set G) ∩ D)) (hwL : ∀ l ∈ L, Commute w l) {k : ℕ}
    (hwk : w ^ 2 ^ k = 1) :
    w ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have hTp : IsPGroup 2 TG := T.isPGroup'.map _
  have hTn : ∀ b ∈ Subgroup.centralizer ((S : Set G) ∩ D), ∀ t ∈ TG, b * t * b⁻¹ ∈ TG :=
    fun b hb t ht => hL.sylow_normal b (Subgroup.centralizer_le_normalizer _ hb) t ht
  have hL₀B : L₀ ≤ Subgroup.centralizer ((S : Set G) ∩ D) := hL.centralizer_eq ▸ le_sup_right
  have hLB := hL.le_centralizer
  have hLT : ∀ x ∈ L, x ∈ TG → x = 1 := fun x hx hxT =>
    eq_one_of_mem_of_odd_of_isPGroup hL.odd_card hTp hx hxT
  have hpow : ∀ t ∈ TG, ∀ a ∈ Subgroup.centralizer ((S : Set G) ∩ D), ∀ j : ℕ,
      (t * a) ^ j * (a ^ j)⁻¹ ∈ TG := by
    intro t ht a ha j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : a ^ j * t * (a ^ j)⁻¹ ∈ TG := hTn _ (pow_mem ha j) t ht
      rw [show (t * a) ^ (j + 1) * (a ^ (j + 1))⁻¹ =
          ((t * a) ^ j * (a ^ j)⁻¹) * (a ^ j * t * (a ^ j)⁻¹) by
        rw [pow_succ, pow_succ]; group]
      exact mul_mem ih h1
  have hcaseL : ∀ t ∈ TG, ∀ a ∈ L, w = t * a → w ∈ TG := by
    intro t ht a ha hw
    have h1 := hpow t ht a (hLB ha) (2 ^ k)
    rw [← hw, hwk, one_mul] at h1
    have h2 : a ^ 2 ^ k = 1 := by
      have := hLT _ (pow_mem ha _) (by simpa using inv_mem h1)
      exact this
    have h3 : orderOf a ∣ Nat.card L := Subgroup.orderOf_dvd_natCard L ha
    have h4 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    have hcop : Nat.Coprime (2 ^ k) (Nat.card L) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hL.odd_card)
    have h5 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 hcop) h3
    rw [orderOf_eq_one_iff] at h5
    rw [hw, h5, mul_one]
    exact ht
  have hL₀N : L₀ ≤ Subgroup.normalizer (TG : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun t ht => hTn a (hL₀B ha) t ht
  have hw' : w ∈ ((TG ⊔ L₀ : Subgroup G) : Set G) := by
    rw [← hL.centralizer_eq]
    exact hwB
  rw [Subgroup.coe_mul_of_right_le_normalizer_left TG L₀ hL₀N] at hw'
  obtain ⟨t, ht, a, ha, hta⟩ := hw'
  rcases hL.eq_or_eq_sup with hL₀ | ⟨a₀, -, ha₀2, -, ha₀inv, hL₀⟩
  · subst hL₀
    exact hcaseL t ht a ha hta.symm
  · rw [hL₀] at ha
    have ha₀2' : a₀ ^ 2 = 1 := by rw [sq, ha₀2]
    have hzN : Subgroup.zpowers a₀ ≤ Subgroup.normalizer (L : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun l hl => by
        rw [ha₀inv l hl]
        exact inv_mem hl)
    have ha' : a ∈ ((L ⊔ Subgroup.zpowers a₀ : Subgroup G) : Set G) := ha
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hzN] at ha'
    obtain ⟨l, hl, z, hz, hlz⟩ := ha'
    rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq ha₀2' hz with
      hz1 | hz1
    · exact hcaseL t ht l hl (by rw [← hta, ← hlz, hz1]; simp)
    · exfalso
      apply hL.ne_bot
      rw [eq_bot_iff]
      intro l' hl'
      rw [Subgroup.mem_bot]
      have hLab : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
        intro x hx y hy
        have h1 := ha₀inv (x * y) (mul_mem hx hy)
        rw [show a₀ * (x * y) * a₀⁻¹ = (a₀ * x * a₀⁻¹) * (a₀ * y * a₀⁻¹) by group,
          ha₀inv x hx, ha₀inv y hy, mul_inv_rev] at h1
        have := congrArg (·⁻¹) h1
        simpa using this.symm
      have hw : w = t * l * a₀ := by rw [← hta, ← hlz, hz1]; simp [mul_assoc]
      have hconj : w * l' * w⁻¹ = t * l'⁻¹ * t⁻¹ := by
        rw [hw]
        calc t * l * a₀ * l' * (t * l * a₀)⁻¹ = t * (l * (a₀ * l' * a₀⁻¹) * l⁻¹) * t⁻¹ := by
              group
          _ = t * (l * l'⁻¹ * l⁻¹) * t⁻¹ := by rw [ha₀inv l' hl']
          _ = t * l'⁻¹ * t⁻¹ := by
              rw [hLab l hl _ (inv_mem hl'), mul_inv_cancel_right]
      have h1 : w * l' * w⁻¹ = l' := by rw [(hwL l' hl').eq, mul_inv_cancel_right]
      rw [hconj] at h1
      have h2 : l'⁻¹ * l'⁻¹ ∈ TG := by
        have h3 : l'⁻¹ * t⁻¹ * l'⁻¹⁻¹ ∈ TG := hTn _ (hLB (inv_mem hl')) _ (inv_mem ht)
        have h4 : l'⁻¹ * l'⁻¹ = (l'⁻¹ * t⁻¹ * l'⁻¹⁻¹) * t := by
          calc l'⁻¹ * l'⁻¹ = l'⁻¹ * (t⁻¹ * (t * l'⁻¹ * t⁻¹) * t) := by group
            _ = l'⁻¹ * (t⁻¹ * l' * t) := by rw [h1]
            _ = (l'⁻¹ * t⁻¹ * l'⁻¹⁻¹) * t := by group
        rw [h4]
        exact mul_mem h3 ht
      have h5 := hLT _ (mul_mem (inv_mem hl') (inv_mem hl')) h2
      have h6 : l' ^ 2 = 1 := by
        rw [sq, ← inv_inj, mul_inv_rev, inv_one]
        exact h5
      have h7 : orderOf l' ∣ Nat.card L := Subgroup.orderOf_dvd_natCard L hl'
      have h8 : orderOf l' ∣ 2 := orderOf_dvd_of_pow_eq_one h6
      have hcop : Nat.Coprime 2 (Nat.card L) := Nat.coprime_two_left.mpr hL.odd_card
      have h9 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h8 hcop) h7
      rwa [orderOf_eq_one_iff] at h9

theorem pCore_two_centralizerComponent_eq_bot (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    CFSG.pCore 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, htwin⟩ := setup_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  have hO2 := pCore_two_le_center_of_commute_iff_injective hS.oddT hS.normal hS.gen htwin
  obtain ⟨hΔΓ, -, hYL, -, hΓcl⟩ := centralizerComponent_facts hL hΓ hY
  have htrans := transitive_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  obtain ⟨X, -, -, -, hUX, hXD, -, -, hZX, hXgen⟩ := exists_psl2_local hH h3 hU hCH eH hUn hL
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hu2' : hC.d ^ 2 = 1 := by rw [sq, hu2]
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  have hΓY : ∀ c ∈ Γ, c ∈ Y := fun c hc => by
    rw [hY]
    exact Subgroup.subset_closure hc
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hzc := hO2 hz
  have hcomm : ∀ c ∈ Y, c * (z : G) = (z : G) * c := fun c hc =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨c, hc⟩)
  have hw1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 Y)) ⟨z, hz⟩
  have hwk : (z : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : CFSG.pCore 2 Y => ((x : Y) : G)) hk
    simpa using this
  have hwB : (z : G) ∈ Subgroup.centralizer ((S : Set G) ∩ D) :=
    Subgroup.mem_centralizer_iff.mpr fun δ hδ => hcomm δ (hΓY _ (hΔΓ hδ))
  have hwL : ∀ l ∈ L, Commute (z : G) l := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hYL z.2) l hl).symm
  have hwT := hL.mem_of_commute_of_pow_eq_one hwB hwL hwk
  have hwA := (hL.centralizer_inf _ hwT).mp hwL
  rw [sup_comm] at hwA
  obtain ⟨v, hv, c, hc, hvc⟩ :=
    CFSG.SeitzReduction.RankOne.exists_mul_eq_of_mem_sup_zpowers hU.d_mem_centralizer hwA
  rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq hu2' hc with
    hc1 | hc1
  ·
    rw [hc1, mul_one] at hvc
    have hv1 : v ≠ 1 := by
      rw [hvc]
      exact hw1
    obtain ⟨t, htX, ht2, htU⟩ : ∃ t ∈ X, orderOf t = 2 ∧ t ∉ U := by
      by_contra hall
      push Not at hall
      have hXU : X ≤ U :=
        hXgen.trans ((Subgroup.closure_le _).mpr fun t ⟨htX, ht2⟩ => hall t htX ht2)
      have := hU.isElementaryAbelian
      obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
      exact hv₀1 (Subtype.ext (hZX v₀ (hUX hv₀) fun x hx _ =>
        congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨v₀, hv₀⟩ ⟨x, hXU hx⟩)))
    have hut : hC.d * (hC.d * t) = t := by rw [← mul_assoc, hu2, one_mul]
    obtain ⟨hutC, hutu, -⟩ :=
      (hXD (hC.d * t)).mpr ⟨by rw [hut]; exact htX, by rw [hut]; exact ht2⟩
    have hutΓ := hΓcl _ huΓ _ hutC hutu
    have hcomm' : Commute (hC.d * t) v := by
      rw [hvc]
      exact hcomm _ (hΓY _ hutΓ)
    have hmem := DeltaSetup.mem_sylow_inter_of_commute_of_center hH h3 hU hL.center_eq hv hv1
      hutC.2 hcomm'
    rw [hU.sylow_inter] at hmem
    obtain ⟨v', hv', hv'e⟩ := hmem
    apply htU
    have htv : t = v' := by
      calc t = hC.d * (hC.d * t) := hut.symm
        _ = hC.d * (hC.d * v') := by rw [← show hC.d * v' = hC.d * t from hv'e]
        _ = v' := by rw [← mul_assoc, hu2, one_mul]
    rw [htv]
    exact hv'
  ·
    rw [hc1] at hvc
    have huv : v * hC.d = hC.d * v := Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer v hv
    have hzΔ : (z : G) ∈ (S : Set G) ∩ D := by
      rw [hU.sylow_inter, ← hvc, huv]
      exact ⟨v, hv, rfl⟩
    obtain ⟨y, hy, hyu⟩ := htrans _ (hΔΓ hzΔ)
    have huz : hC.d = z := by
      calc hC.d = y⁻¹ * (y * hC.d * y⁻¹) * y := by group
        _ = y⁻¹ * z * y := by rw [hyu]
        _ = z := by rw [mul_assoc, ← hcomm y hy, ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
    have hv₀Δ : hC.d * v₀ ∈ (S : Set G) ∩ D := by
      rw [hU.sylow_inter]
      exact ⟨v₀, hv₀, rfl⟩
    obtain ⟨y', hy', hy'u⟩ := htrans _ (hΔΓ hv₀Δ)
    have h1 : hC.d * v₀ = hC.d := by
      rw [← hy'u, huz, hcomm y' hy', mul_inv_cancel_right]
    apply hv₀1
    apply Subtype.ext
    calc v₀ = hC.d⁻¹ * (hC.d * v₀) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]

theorem exists_psl2_component (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d}) :
    ∃ X : Subgroup G, Nonempty (X ≃* PSL2Model n) ∧ X ≤ Subgroup.centralizer ({hC.d} : Set G) ∧
      (∀ d : G, (d ∈ Γ ∧ Commute d hC.d ∧ d ≠ hC.d) ↔ (hC.d * d ∈ X ∧ orderOf (hC.d * d) = 2)) ∧
      (∀ d ∈ Γ, Commute d hC.d → d ≠ hC.d → ∀ d' ∈ Γ, Commute d' hC.d → d' ≠ hC.d →
        ∃ x ∈ X, x * d * x⁻¹ = d') ∧
      (∀ z ∈ X, (∀ x ∈ X, orderOf x = 2 → z * x = x * z) → z = 1) ∧
      Subgroup.closure {d | d ∈ Γ ∧ Commute d hC.d ∧ d ≠ hC.d} = Subgroup.zpowers hC.d ⊔ X ∧
      hC.d ∉ X := by
  obtain ⟨hΔΓ, hΓC, -, -, hΓcl⟩ :=
    centralizerComponent_facts (Y := Subgroup.closure Γ) hL hΓ rfl
  obtain ⟨X, ⟨eX⟩, hXu, -, hUX, hXD, hconj, -, hZX, hXgen⟩ :=
    exists_psl2_local hH h3 hU hCH eH hUn hL
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  have hXD' : ∀ d : G, (d ∈ Γ ∧ Commute d hC.d ∧ d ≠ hC.d) ↔
      (hC.d * d ∈ X ∧ orderOf (hC.d * d) = 2) := by
    intro d
    rw [← hXD d]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨hΓC h1, h2, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨hΓcl _ huΓ d h1 h2, h2, h3⟩⟩
  have hloc : ∀ d ∈ Γ, Commute d hC.d → d ≠ hC.d → ∀ d' ∈ Γ, Commute d' hC.d → d' ≠ hC.d →
      ∃ x ∈ X, x * d * x⁻¹ = d' := by
    intro d hd hdu hdu1 d' hd' hd'u hd'u1
    obtain ⟨hudX, hud2⟩ := (hXD' d).mp ⟨hd, hdu, hdu1⟩
    obtain ⟨hud'X, hud'2⟩ := (hXD' d').mp ⟨hd', hd'u, hd'u1⟩
    obtain ⟨x, hx, hxd⟩ := hconj _ hudX _ hud'X hud2 hud'2
    refine ⟨x, hx, ?_⟩
    have hxu : x * hC.d = hC.d * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
    calc x * d * x⁻¹ = hC.d * (x * (hC.d * d) * x⁻¹) := by
          rw [show x * (hC.d * d) * x⁻¹ = x * hC.d * d * x⁻¹ by group, hxu,
            show hC.d * (hC.d * x * d * x⁻¹) = (hC.d * hC.d) * (x * d * x⁻¹) by group, hu2,
            one_mul]
      _ = d' := by rw [hxd, ← mul_assoc, hu2, one_mul]
  have := hU.isElementaryAbelian
  have hUsq : ∀ v ∈ U, v * v = 1 := fun v hv => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  have hUcomm : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨w, hw⟩)
  have huU : ∀ v ∈ U, v * hC.d = hC.d * v := fun v hv =>
    Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer v hv
  obtain ⟨⟨v₁, hv₁⟩, hv₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hv₁1' : v₁ ≠ 1 := fun h => hv₁1 (Subtype.ext h)
  obtain ⟨v₂, hv₂, hv₂1, hv₂v₁⟩ : ∃ w ∈ U, w ≠ 1 ∧ w ≠ v₁ := by
    by_contra hall
    push Not at hall
    have hsub : (U : Set G) ⊆ {1, v₁} := fun w hw => by
      by_cases h1 : w = 1
      · exact Or.inl h1
      · exact Or.inr (hall w hw h1)
    have hcard : (U : Set G).ncard ≤ 2 :=
      calc (U : Set G).ncard ≤ ({1, v₁} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({v₁} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq] at hcard
    change Nat.card U ≤ 2 at hcard
    rw [hUn] at hcard
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hv₃1 : v₁ * v₂ ≠ 1 := by
    intro h
    apply hv₂v₁
    calc v₂ = v₁ * (v₁ * v₂) := by rw [← mul_assoc, hUsq v₁ hv₁, one_mul]
      _ = v₁ := by rw [h, mul_one]
  have hnbr : ∀ v ∈ U, v ≠ 1 → hC.d * v ∈ {d | d ∈ Γ ∧ Commute d hC.d ∧ d ≠ hC.d} := by
    intro v hv hv1
    refine ⟨hΔΓ (by rw [hU.sylow_inter]; exact ⟨v, hv, rfl⟩), ?_, fun h => hv1 ?_⟩
    · show hC.d * v * hC.d = hC.d * (hC.d * v)
      rw [mul_assoc, ← huU v hv]
    · calc v = hC.d⁻¹ * (hC.d * v) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
  have hprod : hC.d * v₁ * (hC.d * v₂) * (hC.d * (v₁ * v₂)) = hC.d := by
    have e1 := huU v₁ hv₁
    have e2 := huU v₂ hv₂
    have e12 := hUcomm v₂ hv₂ v₁ hv₁
    calc hC.d * v₁ * (hC.d * v₂) * (hC.d * (v₁ * v₂)) =
          hC.d * (v₁ * hC.d) * v₂ * hC.d * v₁ * v₂ := by group
      _ = hC.d * (hC.d * v₁) * (v₂ * hC.d) * v₁ * v₂ := by rw [e1]; group
      _ = hC.d * (hC.d * v₁) * (hC.d * v₂) * v₁ * v₂ := by rw [e2]
      _ = (hC.d * hC.d) * (v₁ * hC.d) * v₂ * v₁ * v₂ := by group
      _ = (hC.d * hC.d) * (hC.d * v₁) * (v₂ * v₁) * v₂ := by rw [e1]; group
      _ = (hC.d * hC.d) * hC.d * (v₁ * v₁) * (v₂ * v₂) := by rw [e12]; group
      _ = hC.d := by rw [hu2, hUsq v₁ hv₁, hUsq v₂ hv₂]; group
  have hucl : hC.d ∈ Subgroup.closure {d | d ∈ Γ ∧ Commute d hC.d ∧ d ≠ hC.d} := by
    have h := mul_mem (mul_mem (Subgroup.subset_closure (hnbr v₁ hv₁ hv₁1'))
      (Subgroup.subset_closure (hnbr v₂ hv₂ hv₂1)))
      (Subgroup.subset_closure (hnbr _ (mul_mem hv₁ hv₂) hv₃1))
    rwa [hprod] at h
  refine ⟨X, ⟨eX⟩, hXu, hXD', hloc, hZX, le_antisymm ?_ ?_, fun huX => ?_⟩
  · rw [Subgroup.closure_le]
    rintro d ⟨hd, hdu, hdu1⟩
    have h1 := ((hXD' d).mp ⟨hd, hdu, hdu1⟩).1
    rw [show d = hC.d * (hC.d * d) by rw [← mul_assoc, hu2, one_mul]]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_right h1)
  · refine sup_le (Subgroup.zpowers_le.mpr hucl) (hXgen.trans ((Subgroup.closure_le _).mpr ?_))
    rintro t ⟨htX, ht2⟩
    have hut : hC.d * (hC.d * t) = t := by rw [← mul_assoc, hu2, one_mul]
    have h1 := (hXD' (hC.d * t)).mpr ⟨by rw [hut]; exact htX, by rw [hut]; exact ht2⟩
    rw [SetLike.mem_coe, ← hut]
    exact mul_mem hucl (Subgroup.subset_closure h1)
  · have h1 := hZX _ huX fun x hx _ => (Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)).symm
    exact hC.setup.oddT.ne_one hC.hd h1

theorem exists_hypothesisC_quotient_centralizerComponent
    (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    ∃ hC' : HypothesisC ((QuotientGroup.mk' (Subgroup.center Y)) '' (((↑) : Y → G) ⁻¹' Γ)),
      (∃ y : Y, (y : G) = hC.d ∧ hC'.d = QuotientGroup.mk' (Subgroup.center Y) y) ∧
      hC'.alpha = {hC'.d} ∧
      Th91Hyp ((QuotientGroup.mk' (Subgroup.center Y)) '' (((↑) : Y → G) ⁻¹' Γ)) hC' ∧
      Nonempty (Halpha ((QuotientGroup.mk' (Subgroup.center Y)) '' (((↑) : Y → G) ⁻¹' Γ))
          hC'.alpha ⧸ Subgroup.center (Halpha ((QuotientGroup.mk' (Subgroup.center Y)) ''
            (((↑) : Y → G) ⁻¹' Γ)) hC'.alpha) ≃* PSL2Model n) := by
  classical
  obtain ⟨hS, -⟩ := setup_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  obtain ⟨hΔΓ, hΓC, -, hYΓ, -⟩ := centralizerComponent_facts hL hΓ hY
  have htrans := transitive_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  have hO2 := pCore_two_centralizerComponent_eq_bot hH h3 hU hCH eH hUn hL hΓ hY
  have hrad := solvableRadical_centralizerComponent_eq_center hH h3 hU hCH eH hUn hL hΓ hY
  obtain ⟨X, ⟨eX⟩, hXu, hXD, hloc, hZX, hXcl, huX⟩ :=
    exists_psl2_component hH h3 hU hCH eH hUn hL hΓ
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  have hZodd := odd_card_center_of_pCore_eq_bot hO2
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  have hΓY : ∀ c ∈ Γ, c ∈ Y := fun c hc => by
    rw [hY]
    exact Subgroup.subset_closure hc
  set Θ : Set Y := ((↑) : Y → G) ⁻¹' Γ with hΘ
  set π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y) with hπ
  set Db : Set (Y ⧸ Subgroup.center Y) := π '' Θ with hDb
  set u' : Y := ⟨hC.d, hΓY _ huΓ⟩ with hu'
  have hu'Θ : u' ∈ Θ := huΓ
  set Nu : Set G := {d | d ∈ Γ ∧ Commute d hC.d ∧ d ≠ hC.d} with hNu
  have hNuY : Nu ⊆ Y := fun d hd => hΓY d hd.1
  have hKY : Subgroup.closure Nu ≤ Y := (Subgroup.closure_le _).mpr hNuY
  have hXK : X ≤ Subgroup.closure Nu := by
    rw [hXcl]
    exact le_sup_right
  have hXY : X ≤ Y := hXK.trans hKY
  have huK : hC.d ∈ Subgroup.closure Nu := by
    rw [hXcl]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hcommSet : ∀ c : Y, c ∈ commSet Θ u' ↔ (c : G) ∈ Nu := fun c =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, congrArg Subtype.val h2, fun h => h3 (Subtype.ext h)⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h1, Subtype.ext h2, fun h => h3 (congrArg Subtype.val h)⟩⟩
  have hnc : ∀ c ∈ Θ, c ∉ Subgroup.center Y := by
    intro c hc hcZ
    have hcomm : ∀ y' : Y, (y' : G) * c = c * y' := fun y' =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ y')
    obtain ⟨y, hy, hyu⟩ := htrans _ hc
    have huc : hC.d = (c : G) := by
      have h1 := hcomm ⟨y, hy⟩
      calc hC.d = y⁻¹ * (y * hC.d * y⁻¹) * y := by group
        _ = y⁻¹ * c * y := by rw [hyu]
        _ = c := by
          rw [mul_assoc, show (c : G) * y = y * c from h1.symm, ← mul_assoc, inv_mul_cancel,
            one_mul]
    obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
    have hv₀Δ : hC.d * v₀ ∈ (S : Set G) ∩ D := by
      rw [hU.sylow_inter]
      exact ⟨v₀, hv₀, rfl⟩
    obtain ⟨y', hy', hy'u⟩ := htrans _ (hΔΓ hv₀Δ)
    have h3 : hC.d * v₀ = hC.d := by
      rw [← hy'u, huc, show y' * (c : G) = c * y' from hcomm ⟨y', hy'⟩, mul_inv_cancel_right]
    apply hv₀1
    apply Subtype.ext
    calc v₀ = hC.d⁻¹ * (hC.d * v₀) := by group
      _ = 1 := by rw [h3, inv_mul_cancel]
  have hne1 : ∀ c ∈ Θ, π c ≠ 1 := fun c hc h => hnc c hc ((QuotientGroup.eq_one_iff c).mp h)
  have hlift : ∀ a ∈ Θ, ∀ b ∈ Θ, (π a = π b → a = b) ∧ (Commute (π a) (π b) → Commute a b) :=
    fun a ha b hb => eq_and_commute_of_mk_of_odd_center hZodd (hS.oddT.mul_self_eq_one ha)
      (hS.oddT.mul_self_eq_one hb)
  obtain ⟨d₀, hd₀⟩ := hS.isClass
  have hSb : Setup (Y ⧸ Subgroup.center Y) Db :=
    ⟨image_isClass_quotient hd₀ _, image_isOddTransp_quotient _ hS.oddT hne1,
      image_closure_eq_top_quotient _ hS.gen⟩
  have hreach : ∀ w : G, Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d w →
      ∀ hw : w ∈ Y, Reach Db (π u') (π ⟨w, hw⟩) := by
    intro w hw
    induction hw with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @tail b w' hab hbc ih =>
      intro hw'
      have hbΓ : b ∈ Γ := by
        rw [hΓ]
        exact hab
      have hw'Γ : w' ∈ Γ := by
        rw [hΓ]
        exact Relation.ReflTransGen.tail hab hbc
      refine Relation.ReflTransGen.tail (ih (hΓY b hbΓ))
        ⟨⟨⟨b, hΓY b hbΓ⟩, hbΓ, rfl⟩, ⟨⟨w', hw'⟩, hw'Γ, rfl⟩, ?_⟩
      have h1 : Commute (⟨b, hΓY b hbΓ⟩ : Y) ⟨w', hw'⟩ := Subtype.ext hbc.2.2
      exact h1.map π
  have hreach' : ∀ c ∈ Θ, Reach Db (π u') (π c) := by
    intro c hc
    have hc' : Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d (c : G) := by
      have h := hc
      rw [hΘ, Set.mem_preimage, hΓ] at h
      exact h
    exact hreach _ hc' c.2
  have hconn : ¬ Disconnected Db := by
    rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩
    exact hab (reach_trans (reach_symm (hreach' a ha)) (hreach' b hb))
  have hE_iff : ∀ c ∈ Θ, π c ∈ commSet Db (π u') ↔ c ∈ commSet Θ u' := by
    intro c hc
    constructor
    · rintro ⟨-, hcomm, hne⟩
      exact ⟨hc, (hlift c hc u' hu'Θ).2 hcomm, fun h => hne (by rw [h])⟩
    · rintro ⟨-, hcomm, hne⟩
      exact ⟨⟨c, hc, rfl⟩, hcomm.map π, fun h => hne ((hlift c hc u' hu'Θ).1 h)⟩
  have hDbn : IsNormalSet Db := hSb.normal
  have horb_sub : ∀ e ∈ commSet Db (π u'), orbitIn Db (π u') e ⊆ commSet Db (π u') := by
    rintro e he f ⟨g, hg, rfl⟩
    exact conj_mem_commSet_of_mem_closure hDbn hg he
  have hset : ((↑) : Y → G) ⁻¹' Nu = commSet Θ u' := Set.ext fun c => (hcommSet c).symm
  have hclY : ∀ x ∈ Subgroup.closure Nu, ∀ hx : x ∈ Y,
      (⟨x, hx⟩ : Y) ∈ Subgroup.closure (commSet Θ u') := by
    intro x hx hxY
    have h := mem_closure_preimage_of_mem_closure hNuY hx hxY
    rwa [hset] at h
  have hmapK : (Subgroup.closure (commSet Θ u')).map π ≤
      Subgroup.closure (commSet Db (π u')) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨c', hc', rfl⟩
    exact (hE_iff c' hc'.1).mpr hc'
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have hv₀Γ : hC.d * v₀ ∈ Γ := hΔΓ (by rw [hU.sylow_inter]; exact ⟨v₀, hv₀, rfl⟩)
  have hd₀N : hC.d * v₀ ∈ Nu := by
    refine ⟨hv₀Γ, ?_, fun h => hv₀1' ?_⟩
    · show hC.d * v₀ * hC.d = hC.d * (hC.d * v₀)
      rw [mul_assoc, ← Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer v₀ hv₀]
    · calc v₀ = hC.d⁻¹ * (hC.d * v₀) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
  set d₀ : Y := ⟨hC.d * v₀, hΓY _ hv₀Γ⟩ with hd₀
  have hd₀E : π d₀ ∈ commSet Db (π u') := (hE_iff d₀ hv₀Γ).mpr ((hcommSet d₀).mpr hd₀N)
  have hE : IsMaxOrbit Db (π u') (commSet Db (π u')) := by
    refine ⟨π d₀, hd₀E, Set.Subset.antisymm ?_ (horb_sub _ hd₀E), fun e' he' =>
      Set.ncard_le_ncard (horb_sub e' he') (Set.toFinite _)⟩
    rintro f ⟨⟨c, hc, rfl⟩, hfu, hfne⟩
    have hcN : (c : G) ∈ Nu := (hcommSet c).mp ((hE_iff c hc).mp ⟨⟨c, hc, rfl⟩, hfu, hfne⟩)
    obtain ⟨x, hx, hxc⟩ := hloc _ hd₀N.1 hd₀N.2.1 hd₀N.2.2 _ hcN.1 hcN.2.1 hcN.2.2
    refine ⟨π ⟨x, hXY hx⟩, hmapK ⟨_, hclY x (hXK hx) (hXY hx), rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hxc.symm
  let hC' : HypothesisC Db :=
    { setup := hSb, conn := hconn, d := π u', hd := ⟨u', hu'Θ, rfl⟩,
      E := commSet Db (π u'), hE := hE }
  have huKc : ∀ k ∈ Subgroup.closure Nu, k * hC.d = hC.d * k := by
    intro k hk
    have hle : Subgroup.closure Nu ≤ Subgroup.centralizer ({hC.d} : Set G) := by
      rw [Subgroup.closure_le]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr hd.2.1.eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  have hzK : ∀ w ∈ Subgroup.closure Nu, (∀ k ∈ Subgroup.closure Nu, w * k = k * w) →
      w ∈ Subgroup.zpowers hC.d := by
    intro w hw hwc
    have hwX : w ∈ X ⊔ Subgroup.zpowers hC.d := by
      rw [sup_comm, ← hXcl]
      exact hw
    have hXc : hC.d ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hXu hx))
    obtain ⟨x, hx, z', hz', hxz⟩ :=
      CFSG.SeitzReduction.RankOne.exists_mul_eq_of_mem_sup_zpowers hXc hwX
    have hx1 : x = 1 := by
      refine hZX x hx fun t htX _ => ?_
      have h1 := hwc t (hXK htX)
      have h2 : z' * t = t * z' := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
        exact (Commute.zpow_left
          (Subgroup.mem_centralizer_singleton_iff.mp (hXu htX)).symm k).eq
      rw [← hxz] at h1
      calc x * t = x * t * z' * z'⁻¹ := by group
        _ = x * (z' * t) * z'⁻¹ := by rw [mul_assoc x t, ← h2]
        _ = (x * z') * t * z'⁻¹ := by group
        _ = t * (x * z') * z'⁻¹ := by rw [h1]
        _ = t * x := by group
    rw [← hxz, hx1, one_mul]
    exact hz'
  have halpha : hC'.alpha = {hC'.d} := by
    rw [HypothesisC.alpha_eq_normSet_diff]
    ext f
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hfDb, hfN⟩, hfE⟩
      obtain ⟨c, hc, rfl⟩ := hfDb
      have hcN : ∀ d ∈ Nu, (c : G) * d * (c : G)⁻¹ ∈ Nu := by
        intro d hd
        have hdΘ : (⟨d, hNuY hd⟩ : Y) ∈ commSet Θ u' := (hcommSet _).mpr hd
        have h1 := (hE_iff _ hdΘ.1).mpr hdΘ
        have h2 := (Subgroup.mem_set_normalizer_iff.mp hfN _).mp h1
        rw [← map_inv, ← map_mul, ← map_mul] at h2
        have hcdΘ : c * ⟨d, hNuY hd⟩ * c⁻¹ ∈ Θ := hYΓ c c.2 d hd.1
        exact (hcommSet _).mp ((hE_iff _ hcdΘ).mp h2)
      have hcN' : (c : G) ∈ Subgroup.normalizer Nu := Subgroup.mem_normalizer_fintype hcN
      have hcK : ∀ g ∈ Subgroup.normalizer Nu, ∀ k ∈ Subgroup.closure Nu,
          g * k * g⁻¹ ∈ Subgroup.closure Nu := by
        intro g hg k hk
        have h1 : (Subgroup.closure Nu).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure Nu := by
          rw [MonoidHom.map_closure]
          apply Subgroup.closure_mono
          rintro _ ⟨d, hd, rfl⟩
          exact (Subgroup.mem_set_normalizer_iff.mp hg d).mp hd
        exact h1 ⟨k, hk, rfl⟩
      have hw : (c : G) * hC.d * (c : G)⁻¹ ∈ Subgroup.zpowers hC.d := by
        refine hzK _ (hcK _ hcN' _ huK) fun k hk => ?_
        have hk' := hcK _ (inv_mem hcN') k hk
        rw [inv_inv] at hk'
        have h1 := huKc _ hk'
        calc (c : G) * hC.d * (c : G)⁻¹ * k =
              (c : G) * (hC.d * ((c : G)⁻¹ * k * c)) * (c : G)⁻¹ := by group
          _ = (c : G) * (((c : G)⁻¹ * k * c) * hC.d) * (c : G)⁻¹ := by rw [h1]
          _ = k * ((c : G) * hC.d * (c : G)⁻¹) := by group
      have hu2' : hC.d ^ 2 = 1 := by rw [sq, hu2]
      have hwu : (c : G) * hC.d * (c : G)⁻¹ = hC.d := by
        rcases CFSG.SeitzReduction.RankOne.mem_zpowers_involution_eq_one_or_eq hu2' hw with
          h | h
        · exfalso
          apply hC.setup.oddT.ne_one hC.hd
          calc hC.d = (c : G)⁻¹ * ((c : G) * hC.d * (c : G)⁻¹) * c := by group
            _ = 1 := by rw [h]; group
        · exact h
      have hcu : Commute c u' := by
        apply Subtype.ext
        show (c : G) * hC.d = hC.d * c
        calc (c : G) * hC.d = (c : G) * hC.d * (c : G)⁻¹ * c := by group
          _ = hC.d * c := by rw [hwu]
      by_contra hne
      exact hfE ⟨⟨c, hc, rfl⟩, hcu.map π, hne⟩
    · rintro rfl
      refine ⟨⟨hC'.hd, Subgroup.mem_normalizer_fintype fun e he => ?_⟩, fun h => h.2.2 rfl⟩
      rw [show hC'.d * e * hC'.d⁻¹ = e by rw [← he.2.1.eq, mul_inv_cancel_right]]
      exact he
  have hTh : Th91Hyp Db hC' ∧ Nonempty (Halpha Db hC'.alpha ⧸
      Subgroup.center (Halpha Db hC'.alpha) ≃* PSL2Model n) := by
    have hHb : Halpha Db hC'.alpha = Subgroup.closure (commSet Db (π u')) := by
      show Subgroup.closure (DalphaStar Db hC'.alpha) = _
      rw [DalphaStar_eq_commSet hC' halpha]
    have hKH : ∀ y ∈ Subgroup.closure (commSet Θ u'), π y ∈ Halpha Db hC'.alpha := by
      intro y hy
      rw [hHb]
      exact hmapK ⟨y, hy, rfl⟩
    have hu'K : u' ∈ Subgroup.closure (commSet Θ u') := hclY _ huK _
    have hXK' : ∀ x : X, (⟨x, hXY x.2⟩ : Y) ∈ Subgroup.closure (commSet Θ u') := fun x =>
      hclY _ (hXK x.2) _
    set z : Halpha Db hC'.alpha := ⟨π u', hKH _ hu'K⟩ with hz
    have hzc : z ∈ Subgroup.center (Halpha Db hC'.alpha) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hle : Subgroup.closure (commSet Db (π u')) ≤
          Subgroup.centralizer ({π u'} : Set (Y ⧸ Subgroup.center Y)) := by
        rw [Subgroup.closure_le]
        intro e he
        exact Subgroup.mem_centralizer_singleton_iff.mpr he.2.1.eq
      have h1 : (h : Y ⧸ Subgroup.center Y) ∈ Subgroup.closure (commSet Db (π u')) :=
        hHb ▸ h.2
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle h1)
    have hz2 : z * z = 1 := by
      apply Subtype.ext
      show π u' * π u' = 1
      rw [← map_mul, show u' * u' = 1 from Subtype.ext hu2, map_one]
    set ι : X →* Halpha Db hC'.alpha :=
      (π.comp (Subgroup.inclusion hXY)).codRestrict _ fun x => hKH _ (hXK' x) with hι
    have hXZ : ∀ x : X, ∀ y : Y, (⟨x, hXY x.2⟩ : Y)⁻¹ * y ∈ Subgroup.center Y →
        (y : G) ∈ Subgroup.centralizer (X : Set G) → (x : G) = 1 := by
      intro x y hxy hyX
      have hw : ∀ g ∈ Y, g * ((x : G)⁻¹ * y) = ((x : G)⁻¹ * y) * g := fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hxy ⟨g, hg⟩)
      refine hZX x x.2 fun t htX _ => ?_
      have h1 := hw t (hXY htX)
      have h2 : (y : G) * t = t * y := (Subgroup.mem_centralizer_iff.mp hyX t htX).symm
      have h3 : ((x : G)⁻¹ * y)⁻¹ * t = t * ((x : G)⁻¹ * y)⁻¹ := by
        calc ((x : G)⁻¹ * y)⁻¹ * t =
              ((x : G)⁻¹ * y)⁻¹ * (t * ((x : G)⁻¹ * y)) * ((x : G)⁻¹ * y)⁻¹ := by group
          _ = ((x : G)⁻¹ * y)⁻¹ * (((x : G)⁻¹ * y) * t) * ((x : G)⁻¹ * y)⁻¹ := by rw [h1]
          _ = t * ((x : G)⁻¹ * y)⁻¹ := by group
      calc (x : G) * t = (y : G) * ((x : G)⁻¹ * y)⁻¹ * t := by group
        _ = (y : G) * (t * ((x : G)⁻¹ * y)⁻¹) := by rw [mul_assoc, h3]
        _ = (y : G) * t * ((x : G)⁻¹ * y)⁻¹ := by group
        _ = t * y * ((x : G)⁻¹ * y)⁻¹ := by rw [h2]
        _ = t * x := by group
    have hιi : Function.Injective ι := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : π ⟨x, hXY x.2⟩ = 1 := congrArg Subtype.val hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      apply Subtype.ext
      refine hXZ x 1 ?_ (one_mem _)
      rw [mul_one]
      exact inv_mem h1
    have hzX : z ∉ ι.range := by
      rintro ⟨x, hx⟩
      have h1 : π ⟨x, hXY x.2⟩ = π u' := congrArg Subtype.val hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have hx1 := hXZ x u' h1 (Subgroup.mem_centralizer_iff.mpr fun t ht =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hXu ht)))
      apply hnc u' hu'Θ
      have : (⟨x, hXY x.2⟩ : Y) = 1 := Subtype.ext hx1
      rw [this, inv_one, one_mul] at h1
      exact h1
    have hsup : Subgroup.zpowers z ⊔ ι.range = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨h, hh⟩ -
      have hh' : h ∈ Subgroup.closure (commSet Db (π u')) := hHb ▸ hh
      induction hh' using Subgroup.closure_induction with
      | mem e he =>
        obtain ⟨⟨c, hc, rfl⟩, hcu, hcne⟩ := he
        have hcN : (c : G) ∈ Nu := (hcommSet c).mp ((hE_iff c hc).mp ⟨⟨c, hc, rfl⟩, hcu, hcne⟩)
        have hucX : hC.d * c ∈ X := ((hXD c).mp hcN).1
        have e1 : (⟨π c, hh⟩ : Halpha Db hC'.alpha) = z * ι ⟨hC.d * c, hucX⟩ := by
          apply Subtype.ext
          show π c = π u' * π ⟨hC.d * c, hXY hucX⟩
          rw [← map_mul]
          congr 1
          apply Subtype.ext
          show (c : G) = hC.d * (hC.d * c)
          rw [← mul_assoc, hu2, one_mul]
        rw [e1]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right ⟨_, rfl⟩)
      | one => exact one_mem _
      | mul a b ha hb iha ihb =>
        have hah : a ∈ Halpha Db hC'.alpha := hHb ▸ ha
        have hbh : b ∈ Halpha Db hC'.alpha := hHb ▸ hb
        have := mul_mem (iha hah) (ihb hbh)
        exact this
      | inv a ha iha =>
        have hah : a ∈ Halpha Db hC'.alpha := hHb ▸ ha
        exact inv_mem (iha hah)
    obtain ⟨hradH, -, ⟨eH'⟩⟩ :=
      solvableRadical_eq_center_of_sup_zpowers hzc hz2 hn2 eX ι hιi hsup hzX
    refine ⟨⟨fun N hN hNs => ?_, hradH, IsBenderGroup.isPSL2 n hn2 eH'⟩, ⟨eH'⟩⟩
    have : Group.IsSolvable N := hNs
    set e : (Y ⧸ Subgroup.center Y) ≃* (Y ⧸ CFSG.solvableRadical Y) :=
      QuotientGroup.quotientMulEquivOfEq hrad.symm with he
    have h1 : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    have h2 : Group.IsSolvable (N.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective
        (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (MulEquiv.surjective _)
    have h3 := CFSG.Timmesfeld.Bridge.OddTransp.eq_bot_of_quotient_solvableRadical _ h1 h2
    rw [eq_bot_iff]
    intro x hx
    have hxm : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rw [h3, Subgroup.mem_bot] at hxm
    exact Subgroup.mem_bot.mpr (e.injective (by rw [hxm, map_one]))
  exact ⟨hC', ⟨u', rfl, rfl⟩, halpha, hTh.1, hTh.2⟩

theorem orthogonal_of_th91Below (hH : Th91Hyp D hC)
    (hIH : Th91Below (Nat.card G))
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    Nonempty (Y ⧸ Subgroup.center Y ≃* L2Wreath n 2) ∨
      (Nonempty (↥(commutator (Y ⧸ Subgroup.center Y)) ≃* PSL2Model (2 * n)) ∧
        (commutator (Y ⧸ Subgroup.center Y)).index = 2) := by
  obtain ⟨hC', -, -, hTh', ⟨e'⟩⟩ :=
    exists_hypothesisC_quotient_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  have hYne : Y ≠ ⊤ := by
    intro hYtop
    obtain ⟨-, -, hYL, -, -⟩ := centralizerComponent_facts hL hΓ hY
    have hZ : Subgroup.center G = ⊥ := hH.solv _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
    apply hL.ne_bot
    rw [eq_bot_iff, ← hZ]
    intro l hl
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hYL (hYtop ▸ Subgroup.mem_top g)) l hl).symm
  have hcard : Nat.card (Y ⧸ Subgroup.center Y) < Nat.card G := by
    calc Nat.card (Y ⧸ Subgroup.center Y) ≤ Nat.card Y :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      _ < Nat.card G := lt_of_le_of_ne (Subgroup.card_le_card_group Y)
          fun h => hYne ((Subgroup.card_eq_iff_eq_top Y).mp h)
  obtain ⟨f, hf, ⟨ef⟩, hcases⟩ := hIH (Y ⧸ Subgroup.center Y) hcard _ hC' hTh'
  have hfn : f = n := by
    have hcf := Nat.card_congr (ef.symm.trans e').toEquiv
    rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega),
      CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)] at hcf
    have hmono : StrictMono fun k : ℕ => 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [h2]
      have h3 : (2 ^ k) ^ 2 - 1 < (2 * 2 ^ k) ^ 2 - 1 := by
        have : (2 ^ k) ^ 2 < (2 * 2 ^ k) ^ 2 := by nlinarith
        have : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        omega
      calc 2 ^ k * ((2 ^ k) ^ 2 - 1) ≤ 2 ^ k * ((2 * 2 ^ k) ^ 2 - 1) :=
            Nat.mul_le_mul_left _ h3.le
        _ < 2 * 2 ^ k * ((2 * 2 ^ k) ^ 2 - 1) := by
            have : 0 < (2 * 2 ^ k) ^ 2 - 1 := by
              have : 4 ≤ (2 * 2 ^ k) ^ 2 := by nlinarith
              omega
            nlinarith
    exact hmono.injective hcf
  subst hfn
  exact hcases

end Component

theorem exists_sylow_centralizerComponent {L L₀ : Subgroup G} {Γ : Set G} {Y : Subgroup G}
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) :
    ∃ P : Sylow 2 Y, (S : Set G) ∩ D ⊆ ((P : Subgroup Y).map Y.subtype : Set G) ∧
      ((P : Subgroup Y).map Y.subtype : Set G) ∩ D = (S : Set G) ∩ D ∧
      ∃ S' : Sylow 2 G,
        (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S' ∧
        (P : Subgroup Y).map Y.subtype ≤ S' ∧ (S' : Set G) ∩ D = (S : Set G) ∩ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hΔΓ, -, -, -, -⟩ := centralizerComponent_facts hL hΓ hY
  have hΓY : ∀ c ∈ Γ, c ∈ Y := fun c hc => by
    rw [hY]
    exact Subgroup.subset_closure hc
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have huΔ : hC.d ∈ (S : Set G) ∩ D := by
    rw [hU.sylow_inter]
    exact ⟨1, U.one_mem, mul_one _⟩
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have huv₀Δ : hC.d * v₀ ∈ (S : Set G) ∩ D := by
    rw [hU.sylow_inter]
    exact ⟨v₀, hv₀, rfl⟩
  have hcl : ∀ Q : Subgroup G, IsPGroup 2 Q → (S : Set G) ∩ D ⊆ Q →
      ∀ x ∈ D, x ∈ Q → x ∈ (S : Set G) ∩ D := by
    intro Q hQ hΔQ x hxD hxQ
    have hxu : Commute x hC.d :=
      hC.setup.oddT.commute_of_isPGroup hQ hxD hC.hd hxQ (hΔQ huΔ)
    have hxuv : Commute x (hC.d * v₀) :=
      hC.setup.oddT.commute_of_isPGroup hQ hxD huv₀Δ.2 hxQ (hΔQ huv₀Δ)
    have hxv : Commute x v₀ := by
      have e : v₀ = hC.d⁻¹ * (hC.d * v₀) := by group
      rw [e]
      exact hxu.inv_right.mul_right hxuv
    exact DeltaSetup.mem_sylow_inter_of_commute_of_center hH h3 hU hL.center_eq hv₀ hv₀1' hxD hxv
  set A : Subgroup Y := Subgroup.closure (((↑) : Y → G) ⁻¹' ((S : Set G) ∩ D)) with hA
  have hAp : IsPGroup 2 A := by
    refine (S.isPGroup'.comap_subtype (K := Y)).to_le ?_
    rw [hA, Subgroup.closure_le]
    intro x hx
    exact hx.1
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  have hPp : IsPGroup 2 ((P : Subgroup Y).map Y.subtype) := P.isPGroup'.map _
  have hΔP : (S : Set G) ∩ D ⊆ ((P : Subgroup Y).map Y.subtype : Set G) := fun δ hδ =>
    ⟨⟨δ, hΓY δ (hΔΓ hδ)⟩, hAP (Subgroup.subset_closure hδ), rfl⟩
  have hPD : ((P : Subgroup Y).map Y.subtype : Set G) ∩ D = (S : Set G) ∩ D :=
    Set.Subset.antisymm (fun x hx => hcl _ hPp hΔP x hx.2 hx.1) fun δ hδ => ⟨hΔP hδ, hδ.2⟩
  have hPN : (P : Subgroup Y).map Y.subtype ≤ Subgroup.normalizer ((S : Set G) ∩ D) :=
    fun g hg => Subgroup.mem_normalizer_fintype fun δ hδ => by
      rw [← hPD] at hδ ⊢
      exact ⟨mul_mem (mul_mem hg hδ.1) (inv_mem hg), hC.setup.normal g δ hδ.2⟩
  have hPT : (P : Subgroup Y).map Y.subtype ≤ Subgroup.normalizer (TG : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun t ht => hL.sylow_normal g (hPN hg) t ht
  have hsup : IsPGroup 2 ((P : Subgroup Y).map Y.subtype ⊔ TG : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hPp (T.isPGroup'.map _) hPT
  obtain ⟨S', hS'⟩ := hsup.exists_le_sylow
  refine ⟨P, hΔP, hPD, S', le_sup_right.trans hS', le_sup_left.trans hS', ?_⟩
  exact Set.Subset.antisymm (fun x hx => hcl _ S'.isPGroup' (hΔP.trans fun y hy =>
    hS' (Subgroup.mem_sup_left hy)) x hx.2 hx.1) fun δ hδ =>
      ⟨hS' (Subgroup.mem_sup_left (hΔP hδ)), hδ.2⟩

theorem Conclusion9_4.of_inter_eq {S' : Sylow 2 G} (h4 : Conclusion9_4 D hC T S)
    (h : (S' : Set G) ∩ D = (S : Set G) ∩ D) : Conclusion9_4 D hC T S' := by
  obtain ⟨h₁, -, h₃, h₄⟩ := h4
  refine ⟨h.trans h₁, sylow_le_normalizer_inter hC.setup.isClass S', ?_, ?_⟩
  · rw [h]
    exact h₃
  · rw [h]
    exact h₄

omit [Finite G] in
theorem DeltaSetup.of_inter_eq {S' : Sylow 2 G} (hU : DeltaSetup hC T S U)
    (h : (S' : Set G) ∩ D = (S : Set G) ∩ D) : DeltaSetup hC T S' U :=
  { hU with sylow_inter := h.trans hU.sylow_inter }

omit [Finite G] in
theorem UnitaryCentralizerData.of_inter_eq {L L₀ : Subgroup G} {S' : Sylow 2 G}
    (hL : UnitaryCentralizerData hC T S U n L L₀) (h : (S' : Set G) ∩ D = (S : Set G) ∩ D) :
    UnitaryCentralizerData hC T S' U n L L₀ :=
  { hL with
    sylow_normal := by rw [h]; exact hL.sylow_normal
    le_centralizer := by rw [h]; exact hL.le_centralizer
    sylow_inter_normal := by rw [h]; exact hL.sylow_inter_normal
    normalizer_eq := by rw [h]; exact hL.normalizer_eq
    centralizer_eq := by rw [h]; exact hL.centralizer_eq }

theorem exists_translationSubgroup {L L₀ : Subgroup G} {Γ : Set G}
    {Y : Subgroup G}
    (hH : Th91Hyp D hC) (hIH : Th91Below (Nat.card G)) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d})
    (hY : Y = Subgroup.closure Γ) (P : Sylow 2 Y)
    (hΔP : (S : Set G) ∩ D ⊆ ((P : Subgroup Y).map Y.subtype : Set G))
    (hPS : (P : Subgroup Y).map Y.subtype ≤ S) :
    ∃ V : Subgroup G, V ≤ (P : Subgroup Y).map Y.subtype ∧
      IsTranslationSubgroup hC S U Y V n := by
  obtain ⟨hS, -⟩ := setup_centralizerComponent hH h3 hU hCH eH hUn hL hΓ hY
  obtain ⟨hΔΓ, -, hYL, -, -⟩ := centralizerComponent_facts hL hΓ hY
  exact exists_translationSubgroup_of_orthogonal hH h3 hU hUn hL hΔΓ hYL hS
    (pCore_two_centralizerComponent_eq_bot hH h3 hU hCH eH hUn hL hΓ hY)
    (orthogonal_of_th91Below hH hIH h3 hU hCH eH hUn hL hΓ hY) P hΔP hPS

end Chain

end CFSG.OddTranspositions.PartThree.Nine
