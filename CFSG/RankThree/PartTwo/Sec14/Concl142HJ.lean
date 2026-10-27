module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec14.Concl142HJTools
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SL447
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def AllPointsHJ (A : Subgroup G) : Prop :=
  ∀ e : G, Subgroup.zpowers e ∈ omegaA A → ∃ Le ∈ lA A e,
    Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Concl142HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → AllPointsHJ A → Concl142 A (lB A)

section General

omit [Finite G] in
theorem le_centralizer_of_mem_invariantPiSubgroups {A Q : Subgroup G} {c : G} (hcA : c ∈ A)
    (hc3 : orderOf c = 3)
    (hQ : Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxN := hQ.1 hx
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hxN c).mp (Subgroup.mem_zpowers c))
      (inv_mem (Subgroup.mem_zpowers c))
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ Q := by
    have h3 : c * x⁻¹ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQ.2.2 hcA) x⁻¹).mp (inv_mem hx)
    have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [this]
    exact mul_mem hx h3
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.2.1
  have hdisj : Subgroup.zpowers c ⊓ Q = ⊥ := by
    have hd : Disjoint (Subgroup.zpowers c) Q := Subgroup.disjoint_of_coprime_natCard (by
      rw [Nat.card_zpowers, hc3]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
    exact hd.eq_bot
  have h4 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c ⊓ Q := ⟨h1, h2⟩
  rw [hdisj, Subgroup.mem_bot] at h4
  calc x * c = x * c * x⁻¹ * c⁻¹ * (c * x) := by group
    _ = c * x := by rw [h4, one_mul]

theorem inf_centralizer_le_xA {A Q : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hQ : ¬ 3 ∣ Nat.card Q) :
    Q ⊓ Subgroup.centralizer (A : Set G) ≤ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNC, hCN, hN3, hNall⟩ :=
    Sec4.Item4443SL.exists_normal_complement (A := A) (C := Subgroup.centralizer (A : Set G))
      le_rfl fun y hy hy3 => Sec4.mem_of_maximal_of_commute hA hy3
        fun a ha => Subgroup.mem_centralizer_iff.mp hy a ha
  have hNO : N ≤ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
    le_pPrimeCoreOf hNC hCN ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
  intro x hx
  refine hNO (hNall x hx.2 fun h3 => hQ ?_)
  exact h3.trans (Subgroup.orderOf_dvd_natCard Q hx.1)

omit [Finite G] in
theorem mem_centralizer_of_le_sup {A B : Subgroup G} {c x : G}
    (hA : A ≤ B ⊔ Subgroup.zpowers c) (hxB : x ∈ Subgroup.centralizer (B : Set G))
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) :
    x ∈ Subgroup.centralizer (A : Set G) := by
  have hle : B ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxB y hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hA ha))

theorem le_sup_zpowers_of_not_mem {A B : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    {c : G} (hcA : c ∈ A) (hcB : c ∉ B) : A ≤ B ⊔ Subgroup.zpowers c := by
  have hB9 : Nat.card B = 9 := by have := hB.2; rw [hA.2] at this; omega
  have hle : B ⊔ Subgroup.zpowers c ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr hcA)
  have hlt : B < B ⊔ Subgroup.zpowers c :=
    lt_of_le_of_ne le_sup_left fun h => hcB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have h1 : Nat.card B < Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) :=
    Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) ∣ 27 :=
    hA.2 ▸ Subgroup.card_dvd_of_le hle
  have h3 : Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) = 27 := by
    have hpos : 0 < Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) := Nat.card_pos
    have hle27 := Nat.le_of_dvd (by norm_num) h2
    rw [hB9] at h1
    interval_cases h : Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hA.2])).ge

theorem exists_eq_closure_pair {A B E : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    (hEA : E ≤ A) (hE9 : Nat.card E = 9) {c : G} (hcB : c ∈ B) (hcE : c ∉ E) :
    ∃ b ∈ B ⊓ E, b ≠ 1 ∧ B = Subgroup.closure {c, b} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9 : Nat.card B = 9 := by have := hB.2; rw [hA.2] at this; omega
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B E
    fun x hx y hy => hcomm x (hB.1 hx) y (hEA hy)
  have hsup : Nat.card (B ⊔ E : Subgroup G) ≤ 27 :=
    hA.2 ▸ Subgroup.card_le_of_le (sup_le hB.1 hEA)
  have hinf : B ⊓ E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, mul_one, hB9, hE9] at hcard
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  refine ⟨b, hb, hb1', ?_⟩
  have hcA : c ∈ A := hB.1 hcB
  have hc1 : c ≠ 1 := fun h => hcE (h ▸ one_mem E)
  have hoc : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hcA) hc1
  have hob : orderOf b = 3 := orderOf_eq_prime (hA.1.2 b (hEA hb.2)) hb1'
  have hdisj : E ⊓ Subgroup.zpowers c = ⊥ :=
    Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hoc hcE
  have hcb : Subgroup.zpowers c ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff, ← hdisj]
    intro x hx
    exact ⟨(Subgroup.zpowers_le.mpr hb.2) hx.2, hx.1⟩
  obtain ⟨hcard2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers c)
    (Subgroup.zpowers b) fun x hx y hy =>
      hcomm x ((Subgroup.zpowers_le.mpr hcA) hx) y ((Subgroup.zpowers_le.mpr (hEA hb.2)) hy)
  rw [hcb, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoc, hob] at hcard2
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers b ≤ Subgroup.closure {c, b} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c _)))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)))
  have hclB : Subgroup.closure {c, b} ≤ B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcB
    · exact hb.1
  refine (Subgroup.eq_of_le_of_card_ge hclB ?_).symm
  rw [hB9]
  calc 9 = Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers b : Subgroup G) := by omega
    _ ≤ Nat.card (Subgroup.closure {c, b}) := Subgroup.card_le_of_le hle

omit [Finite G] in
theorem exists_commutator_eq_of_eq_zpowers_sup {A L : Subgroup G} {c : G}
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hcA : c ∈ A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    {y : G} (hyc : y ∈ Subgroup.centralizer ({c} : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) {a : G} (ha : a ∈ A) :
    ∃ e ∈ A ⊓ L, ⁅y, a⁆ = y * e * y⁻¹ * e⁻¹ := by
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
    constructor
    · intro hx
      rw [hAab c hcA x hx.1, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h := hAab c hcA (c * x * c⁻¹) hx.1
      have hx' : x = c * x * c⁻¹ := by
        have : c * x * c⁻¹ * c = c * (c * x * c⁻¹) := h.symm
        calc x = c⁻¹ * (c * x * c⁻¹ * c) := by group
          _ = c⁻¹ * (c * (c * x * c⁻¹)) := by rw [this]
          _ = c * x * c⁻¹ := by group
      rw [hx']
      exact hx
  have ha' : a ∈ ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := hAc ▸ ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at ha'
  obtain ⟨z, hz, e, he, rfl⟩ := Set.mem_mul.mp ha'
  refine ⟨e, he, ?_⟩
  have hyz : y * z = z * y := by
    have hz' : z ∈ Subgroup.centralizer ({y} : Set G) := by
      refine (Subgroup.zpowers_le.mpr ?_) hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hyc).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp hz').symm
  have hw : y * e * y⁻¹ * e⁻¹ ∈ L :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hyL e).mp he.2) (inv_mem he.2)
  have hzw : z * (y * e * y⁻¹ * e⁻¹) = (y * e * y⁻¹ * e⁻¹) * z := by
    have hzC : z ∈ Subgroup.centralizer ({y * e * y⁻¹ * e⁻¹} : Set G) := by
      refine (Subgroup.zpowers_le.mpr ?_) hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hLc hw)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp hzC
  rw [commutatorElement_def]
  calc y * (z * e) * y⁻¹ * (z * e)⁻¹ = (y * z) * e * y⁻¹ * e⁻¹ * z⁻¹ := by group
    _ = (z * y) * e * y⁻¹ * e⁻¹ * z⁻¹ := by rw [hyz]
    _ = z * (y * e * y⁻¹ * e⁻¹) * z⁻¹ := by group
    _ = (y * e * y⁻¹ * e⁻¹) * z * z⁻¹ := by rw [hzw]
    _ = y * e * y⁻¹ * e⁻¹ := by group

omit [Finite G] in
theorem commutator_le_of_eq_zpowers_sup_inf {A L M Y : Subgroup G} {c : G}
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hcA : c ∈ A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hYM : Y ≤ Subgroup.normalizer (M : Set G)) (hAM : A ⊓ L ≤ M) : ⁅Y, A⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro y hy a ha
  obtain ⟨e, he, heq⟩ :=
    exists_commutator_eq_of_eq_zpowers_sup hAc hcA hAab hLc (hYc hy) (hYL hy) ha
  rw [heq]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hYM hy) e).mp (hAM he)) (inv_mem (hAM he))

omit [Finite G] in
theorem commutator_le_of_eq_zpowers_sup {A L Y : Subgroup G} {c : G}
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hcA : c ∈ A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hYL : Y ≤ Subgroup.normalizer (L : Set G)) :
    ⁅Y, A⁆ ≤ L :=
  commutator_le_of_eq_zpowers_sup_inf hAc hcA hAab hLc hYc hYL hYL inf_le_right

end General

section Quotient

omit [Finite G] in
theorem not_three_dvd_card_comap {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K)
    {W : Subgroup K} (hW : ¬ 3 ∣ Nat.card W) (hker : ¬ 3 ∣ Nat.card f.ker) :
    ¬ 3 ∣ Nat.card (W.comap f) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hx' : orderOf (x : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hfx : f x ∈ W := x.2
  have hdvd : orderOf (f x) ∣ 3 := by
    rw [← hx']
    exact orderOf_map_dvd f _
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have hker' : (x : H) ∈ f.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)
    exact hker (hx' ▸ Subgroup.orderOf_dvd_natCard f.ker hker')
  · exact hW (h3 ▸ Subgroup.orderOf_dvd_natCard W hfx)

omit [Finite G] in
theorem eq_one_of_mem_aschbacherSolvableCore {L : Subgroup G} [Finite L] {x : ↥L}
    (hx : x ∈ aschbacherSolvableCore 3 ↥L) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  exact eq_one_of_mem_of_pow_three_pow hθ3 hx (k := 1) (by rw [pow_one]; exact hx3)

theorem card_map_mk_subgroupOf {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) =
      Nat.card (A ⊓ L : Subgroup G) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
  have hT : Nat.card (A.subgroupOf L) = Nat.card (A ⊓ L : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  rw [← hT]
  refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap (A.subgroupOf L))
    ⟨fun x y hxy => ?_, π.subgroupMap_surjective _⟩).symm
  have hxy' : π (x : ↥L) = π (y : ↥L) := congrArg Subtype.val hxy
  have h1 : (x : ↥L)⁻¹ * y ∈ aschbacherSolvableCore 3 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    change π ((x : ↥L)⁻¹ * y) = 1
    rw [map_mul, map_inv, hxy', inv_mul_cancel]
  have h3 : ((x : ↥L)⁻¹ * y) ^ 3 = 1 := by
    apply Subtype.ext
    have := hA.2 _ (Subgroup.mem_subgroupOf.mp (mul_mem (inv_mem x.2) y.2))
    simpa using this
  exact Subtype.ext (eq_of_inv_mul_eq_one (eq_one_of_mem_aschbacherSolvableCore h1 h3))

end Quotient

section Point

omit [Finite G] in
theorem three_dvd_card_of_thetaQuot_j2 {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    3 ∣ Nat.card L := by
  obtain ⟨φ⟩ := hJ
  have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
  rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
  exact (by norm_num : (3 : ℕ) ∣ 604800).trans h1

theorem centralizer_le_normalizer_of_j2 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro x hxc
  have hL3 := three_dvd_card_of_thetaQuot_j2 hJ
  refine mem_normalizer_of_map_conj_eq
    ((h.chosen136.2 c h.toSec13Data.zpowers_mem_omegaA L h.toSec13Data.mem_lA).2 _
      (Sec6.map_conj_mem_thetaComponentsAt hxc h.toSec13Data.mem_thetaComponentsAt) ?_)
  rwa [Subgroup.card_map_of_injective (MulAut.conj x).injective]

omit [Finite G] in
theorem mk_mem_centralizer_of_mem_centralizer {L : Subgroup G} {b : G} (hbL : b ∈ L) {g : ↥L}
    (hg : g ∈ Subgroup.centralizer ({(⟨b, hbL⟩ : ↥L)} : Set ↥L)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) g ∈
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩} : Set (↥L ⧸ _)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp hg]

omit [Finite G] in
theorem le_centralizer_of_mk_mem_center {L : Subgroup G} [Finite L] (S : Sylow 3 ↥L) {d : ↥L}
    (hdS : d ∈ (S : Subgroup ↥L))
    (hdZ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) d ∈
      Subgroup.centralizer (((S.mapSurjective (QuotientGroup.mk'_surjective
        (aschbacherSolvableCore 3 ↥L))) : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    (S : Subgroup ↥L) ≤ Subgroup.centralizer ({d} : Set ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hπc : π s * π d = π d * π s :=
    Subgroup.mem_centralizer_iff.mp hdZ (π s)
      (by rw [Sylow.coe_mapSurjective]; exact Subgroup.mem_map_of_mem π hs)
  have hk : s * d * s⁻¹ * d⁻¹ ∈ aschbacherSolvableCore 3 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    change π (s * d * s⁻¹ * d⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπc]
    group
  have hkS : s * d * s⁻¹ * d⁻¹ ∈ (S : Subgroup ↥L) :=
    mul_mem (mul_mem (mul_mem hs hdS) (inv_mem hs)) (inv_mem hdS)
  obtain ⟨m, hm⟩ := S.isPGroup' ⟨_, hkS⟩
  have hk1 : s * d * s⁻¹ * d⁻¹ = 1 :=
    eq_one_of_mem_of_pow_three_pow hθ3 hk (k := m) (by simpa using congrArg Subtype.val hm)
  calc s * d = s * d * s⁻¹ * d⁻¹ * (d * s) := by group
    _ = d * s := by rw [hk1, one_mul]

section Certificates


theorem lA_eq_singleton_of_j2_point {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    lA A c = {L} := by
  obtain ⟨-, h9, -⟩ := j2_point_facts hD hJ
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hD.mem_lA, fun L' hL' => ?_⟩
  by_contra hne
  have hle : A ⊓ L ≤ Subgroup.zpowers c := by
    intro x hx
    have hx' : x ∈ ((A ⊓ Sec4.thetaQuotCentralizer L' : Subgroup G) : Set G) :=
      ⟨hx.1, Sec12.mem_thetaQuotCentralizer_of_ne hD.mem_lA.1 hL'.1 (Ne.symm hne) hx.2
        (hL'.2.1 hx.1)⟩
    rw [← sectionCentralizer_eq_inf hL'.2.1, hL'.2.2.1] at hx'
    exact hx'
  have h3 := Subgroup.card_le_of_le hle
  rw [h9, hD.card_zpowers] at h3
  omega

theorem inf_le_residual_of_central {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {b : G} (hbA : b ∈ A) (hbL : b ∈ L) (hb1 : b ≠ 1)
    (hbc : ∃ P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩ ∈ (P : Subgroup _) ∧
        (P : Subgroup _) ≤ Subgroup.centralizer
          {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩}) :
    A ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  set d' : ↥L := ⟨b, hbL⟩ with hd'
  set CL := Subgroup.centralizer ({d'} : Set ↥L) with hCL
  set J' := inSubgroup perfectResidual CL with hJ'
  have hJeq : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) =
      J'.map L.subtype := by
    rw [hJ', CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      L.subtype L.subtype_injective, hCL,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 b hbA)
  have hd'1 : d' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hd3 : IsPGroup 3 (Subgroup.zpowers d') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hd'3 hd'1, pow_one])
  have hCmap : CL.map π = Subgroup.centralizer ({π d'} : Set (↥L ⧸ θ)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 θ hθ3 (Subgroup.zpowers d')
      hd3
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
    exact h
  set Cbar := Subgroup.centralizer ({π d'} : Set (↥L ⧸ θ)) with hCbar
  have hJQ : J'.map π = inSubgroup perfectResidual Cbar := by
    let ψ : ↥CL →* ↥Cbar := (π.comp CL.subtype).codRestrict Cbar fun c =>
      hCmap ▸ Subgroup.mem_map_of_mem π c.2
    have hψ : Function.Surjective ψ := by
      rintro ⟨q, hq⟩
      rw [← hCmap] at hq
      obtain ⟨c, hc, rfl⟩ := hq
      exact ⟨⟨c, hc⟩, rfl⟩
    have h : (perfectResidual ↥CL).map ψ = perfectResidual ↥Cbar :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
    rw [hJ', inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hπd1 : π d' ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd'1 (eq_one_of_mem_aschbacherSolvableCore h1 hd'3)
  have htop : perfectResidual ↥Cbar = ⊤ :=
    KFacts.KS14.j2_perfectResidual_centralizer_eq_top h415 hJ hπd1 hbc
  have hJQ' : J'.map π = Cbar := by
    rw [hJQ, inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro e he
  rw [hJeq]
  set e' : ↥L := ⟨e, he.2⟩ with he'
  have hcomm : e * b = b * e := congrArg Subtype.val (hA.1.is_comm.comm ⟨e, he.1⟩ ⟨b, hbA⟩)
  have he'C : e' ∈ CL := by
    rw [hCL, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hcomm
  have hπe : π e' ∈ Cbar := hCmap ▸ Subgroup.mem_map_of_mem π he'C
  rw [← hJQ'] at hπe
  obtain ⟨j, hj, hjeq⟩ := hπe
  obtain ⟨j'', hj'', rfl⟩ := hj
  have : (perfectResidual ↥CL).Normal := Subgroup.normal_of_characteristic _
  set N' := perfectResidual ↥CL with hN'
  set e'' : ↥CL := ⟨e', he'C⟩ with he''
  have hv : (((j''⁻¹ * e'' : ↥CL)) : ↥L) ∈ θ := by
    rw [← QuotientGroup.eq_one_iff]
    change π ((j'' : ↥L)⁻¹ * e') = 1
    rw [map_mul, map_inv]
    change (π (CL.subtype j''))⁻¹ * π e' = 1
    rw [hjeq, inv_mul_cancel]
  have hcop : Nat.Coprime 3 (orderOf (j''⁻¹ * e'' : ↥CL)) := by
    rw [← Subgroup.orderOf_coe]
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hθ3 ?_
    have h1 : orderOf (⟨_, hv⟩ : ↥θ) ∣ Nat.card θ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h3.trans h1
  have hj1 : QuotientGroup.mk' N' j'' = 1 := (QuotientGroup.eq_one_iff j'').mpr hj''
  have hmk : QuotientGroup.mk' N' e'' = QuotientGroup.mk' N' (j''⁻¹ * e'') := by
    rw [map_mul, map_inv, hj1, inv_one, one_mul]
  have he3 : e'' ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hA.2 e he.1
  have h1 : orderOf (QuotientGroup.mk' N' e'') ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, he3, map_one])
  have h2 : orderOf (QuotientGroup.mk' N' e'') ∣ orderOf (j''⁻¹ * e'' : ↥CL) := by
    rw [hmk]
    exact orderOf_map_dvd _ _
  have h3 : QuotientGroup.mk' N' e'' = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact ⟨e', ⟨e'', h3, rfl⟩, rfl⟩

theorem le_pPrimeCoreOf_of_not_central {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hAP : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤ P)
    {b : G} (hbA : b ∈ A) (hbL : b ∈ L)
    (hbZ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩ ∉
      (P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ⊓
        Subgroup.centralizer ((P : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    {B : Subgroup G}
    (hBC : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (B : Set G))
    (hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G))
    {Z : Subgroup G} (hZ : Z ≤ L ⊓ Subgroup.centralizer ({b} : Set G)) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) :
    Z ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  set Ebar := (A.subgroupOf L).map π with hEbar
  have hE9 : Nat.card Ebar = 9 := by rw [hEbar, card_map_mk_subgroupOf hA, h9]
  have hbE : π b' ∈ Ebar := ⟨b', Subgroup.mem_subgroupOf.mpr hbA, rfl⟩
  have hEb : Ebar ≤ Subgroup.centralizer ({π b'} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    have hc : (x : G) * b = b * (x : G) := congrArg Subtype.val
      (hA.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ ⟨b, hbA⟩)
    exact Subtype.ext hc
  obtain ⟨W, hW3, hWN, hWle⟩ := j2_le_of_invariant h415 hJ P hAP hE9 hbE hbZ hEb
  have hZL : Z ≤ L := hZ.trans inf_le_left
  set U := (Z.subgroupOf L).map π with hU
  have hUC : U ≤ Subgroup.centralizer ({π b'} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hZ (Subgroup.mem_subgroupOf.mp hx)).2)
  have hU3 : ¬ 3 ∣ Nat.card U := by
    intro h3
    apply hZ3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]
  have hEU : Ebar ≤ Subgroup.normalizer (U : Set (↥L ⧸ θ)) := map_le_normalizer_map π hAZ
  have hUW := hWle U hUC hU3 hEU
  set CL := Subgroup.centralizer ({b'} : Set ↥L) with hCL
  set R := ((W.comap π) ⊓ CL).map L.subtype with hR
  have hZR : Z ≤ R := by
    intro z hz
    have hzL := hZL hz
    have hzC : (⟨z, hzL⟩ : ↥L) ∈ CL := by
      rw [hCL, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hZ hz).2)
    exact ⟨⟨z, hzL⟩, ⟨hUW ⟨⟨z, hzL⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, hzC⟩, rfl⟩
  have hRle : R ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [← CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton L b']
    exact Subgroup.map_mono inf_le_right
  have hR3 : ¬ 3 ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective L.subtype_injective]
    intro h3
    have hker : ¬ 3 ∣ Nat.card π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact hθ3
    exact not_three_dvd_card_comap π hW3 hker (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hRn : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hgL : g ∈ L := hg.1
    set g' : ↥L := ⟨g, hgL⟩
    have hg'C : g' ∈ CL := by
      rw [hCL, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
    have hπg : π g' ∈ Subgroup.normalizer (W : Set (↥L ⧸ θ)) :=
      hWN (mk_mem_centralizer_of_mem_centralizer (L := L) hbL hg'C)
    have hg'N : g' ∈ Subgroup.normalizer (((W.comap π) ⊓ CL : Subgroup ↥L) : Set ↥L) :=
      Late.le_normalizer_inf (A := Subgroup.zpowers g')
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer_comap π hπg))
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hg'C)) (Subgroup.mem_zpowers g')
    exact Subgroup.le_normalizer_map L.subtype ⟨g', hg'N, rfl⟩
  have hRO : R ≤ pPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    le_pPrimeCoreOf hRle hRn ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3)
  have hOO : pPrimeCoreOf 3 (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 _).trans hBC)
      (hCB.trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)) (coprime_card_pPrimeCoreOf 3 _)
  exact hZR.trans (hRO.trans hOO)

theorem inf_centralizer_le_qBound_of_j2 {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Y : Subgroup G} (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {B : Subgroup G} (hB : IsHyperplane A B) :
    Y ⊓ Subgroup.centralizer (B : Set G) ≤ qBound A (lB A) B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hD.isElemAbelian, fun B hB hAB => (hD.eq_of_le hB hAB).le⟩
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hcA := hD.mem_A
  have hLc := hD.le_centralizer
  have hCL := centralizer_le_normalizer_of_j2 h hJ
  obtain ⟨hcL, h9, hAc⟩ := j2_point_facts hD hJ
  set Y' := Y ⊓ Subgroup.centralizer (B : Set G) with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hO : Y' ⊓ Subgroup.centralizer (A : Set G) ≤ qBound A (lB A) B :=
    (inf_centralizer_le_xA hAmax hY'3).trans (le_sup_right.trans le_sup_left)
  by_cases hcB : c ∈ B
  swap
  ·
    have hle : Y' ≤ Y' ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      ⟨hx, mem_centralizer_of_le_sup (le_sup_zpowers_of_not_mem hA hB hcA hcB) hx.2 (hYc hx.1)⟩
    exact hle.trans hO
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hB.1 hy) x hx
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Late.le_normalizer_inf hAY (hAB.trans Subgroup.le_normalizer)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three A Y' hA.isPGroup hAY' ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY'3)
  rw [← hfac]
  refine sup_le ?_ hO
  obtain ⟨b, hbBE, hb1, hBeq⟩ :=
    exists_eq_closure_pair hA hB inf_le_left h9 hcB fun hc => hcL hc.2
  have hbA : b ∈ A := hbBE.2.1
  have hbL : b ∈ L := hbBE.2.2
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) := inf_le_left.trans hYc
  have hCBb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbBE.1)
  have hCBc : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  set Z := ⁅Y', A⁆ with hZ
  have hZY' : Z ≤ Y' :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y' A hAY'
  have hZL : Z ≤ L := commutator_le_of_eq_zpowers_sup hAc hcA hAab hLc hY'c (hY'c.trans hCL)
  have hZb : Z ≤ L ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf hZL (hZY'.trans (inf_le_right.trans hCBb))
  have hBC : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [hBeq, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc hx.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hCBc.trans hCL) (hCBb.trans Subgroup.le_normalizer)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  obtain ⟨S, hAS⟩ := hT3.exists_le_sylow
  set P := S.mapSurjective hπs with hP
  have hAP : (A.subgroupOf L).map π ≤ (P : Subgroup (↥L ⧸ θ)) := by
    rw [hP, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hAS
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have hb'S : b' ∈ (S : Subgroup ↥L) := hAS (Subgroup.mem_subgroupOf.mpr hbA)
  by_cases hbZ : π b' ∈ (P : Subgroup (↥L ⧸ θ)) ⊓
    Subgroup.centralizer ((P : Subgroup (↥L ⧸ θ)) : Set (↥L ⧸ θ))
  ·
    have hSb : (S : Subgroup ↥L) ≤ Subgroup.centralizer ({b'} : Set ↥L) :=
      le_centralizer_of_mk_mem_center S hb'S hbZ.2
    have hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
      have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp
        hD.ne_one (top_le_iff.mp (htop ▸ hLc))
      exact Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
        (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
    have hcfg : IsLBConfig A B c b L :=
      ⟨hBeq, hD.zpowers_mem_omegaA, lA_eq_singleton_of_j2_point hD hJ, hJ2, hbL, S, hb'S, hSb⟩
    have hJB : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ lB A B :=
      le_iSup_of_le c (le_iSup_of_le b (le_iSup_of_le L (le_iSup_of_le hcfg le_rfl)))
    have hπbc : ∃ P' : Sylow 3 (↥L ⧸ θ), π b' ∈ (P' : Subgroup (↥L ⧸ θ)) ∧
        (P' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({π b'} : Set (↥L ⧸ θ)) :=
      ⟨P, hbZ.1, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hbZ.2 x hx)⟩
    have hEJ := inf_le_residual_of_central hD.isElemAbelian hJ hbA hbL hb1 hπbc
    have hY'J : Y' ≤ Subgroup.normalizer
        ((inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) : Subgroup G) :
          Set G) :=
      (inf_le_right.trans hCB).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map _ _
          inferInstance)
    exact (commutator_le_of_eq_zpowers_sup_inf hAc hcA hAab hLc hY'c (hY'c.trans hCL) hY'J
      hEJ).trans (hJB.trans le_sup_right)
  ·
    have hZ3 : ¬ 3 ∣ Nat.card Z := fun h3 => hY'3 (h3.trans (Subgroup.card_dvd_of_le hZY'))
    have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
      CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A Y' hAY'
    exact (le_pPrimeCoreOf_of_not_central hD.isElemAbelian hJ h9 P hAP hbA hbL hbZ hBC hCB hZb hZ3
      hAZ).trans (le_sup_left.trans le_sup_left)

theorem mem_scriptQ_of_hj_point {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Q : Subgroup G}
    (hQ : Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)) := by
  have hD := h.toSec13Data
  have hQc := le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq hQ
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.2.1
  exact ⟨⟨⟨le_top, hQ.2.1, hQ.2.2⟩, fun B hB => inf_centralizer_le_qBound_of_j2 h hJ hQc hQ3
    hQ.2.2 hB⟩, hQc⟩

end Certificates

end Point

section Stage


theorem concl142_of_allPointsHJ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hHJ : AllPointsHJ A) : Concl142 A (lB A) := by
  intro e he Q hQ
  obtain ⟨Le, hLe, hJe⟩ := hHJ e he
  have hS : Sec14Std G A e Le := { h with zpowers_mem_omegaA := he, mem_lA := hLe }
  exact mem_scriptQ_of_hj_point hS hJe hQ.prop

theorem concl142HJ : Concl142HJ :=
  fun _ _ _ _ _ _ h hHJ => concl142_of_allPointsHJ h hHJ

theorem rank3II_14_4_3_HJ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hHJ : AllPointsHJ A) (h143 : Concl143 A (lB A)) : Item1443 A (lB A) :=
  rank3II_14_4_3_reduction (concl142_of_allPointsHJ h hHJ) h143

theorem rank3II_14_4_4_HJ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hHJ : AllPointsHJ A) (h143 : Concl143 A (lB A))
    (h1431 : ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      delta A (lB A) (Subgroup.centralizer {a}) = pPrimeCoreOf 3 (Subgroup.centralizer {a}) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    Item1444 A (lB A) :=
  rank3II_14_4_4_reduction (concl142_of_allPointsHJ h hHJ) h143
    (Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE).1.1 h1431

theorem rank3II_14_4_4_of_mem_omegaA_HJ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hHJ : AllPointsHJ A) {a : G} (hΩ : Subgroup.zpowers a ∈ omegaA A) {Q S : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQZero A (lB A)) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer {a}) :=
  rank3II_14_4_4_of_mem_omegaA (concl142_of_allPointsHJ h hHJ) hΩ hQ hS

end Stage

theorem rank3II_14_4_3_of_concl142HJ (h142 : Concl142HJ) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hHJ : AllPointsHJ A) (h143 : Concl143 A (lB A)) :
    Item1443 A (lB A) :=
  rank3II_14_4_3_reduction (h142 G A c L h hHJ) h143

theorem rank3II_14_4_4_of_concl142HJ (h142 : Concl142HJ) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hHJ : AllPointsHJ A) (h143 : Concl143 A (lB A))
    (h1431 : ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      delta A (lB A) (Subgroup.centralizer {a}) = pPrimeCoreOf 3 (Subgroup.centralizer {a}) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    Item1444 A (lB A) :=
  rank3II_14_4_4_reduction (h142 G A c L h hHJ) h143
    (Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE).1.1 h1431

end CFSG.RankThree.PartTwo.Sec14
