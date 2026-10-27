module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeEvenClassification.ClassTwoPairing
import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniFoundations
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.Literature.SemiExtraspecialRank
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo

section Orders

variable {G : Type*} [Group G] [Finite G]

theorem disjoint_zpowers_of_not_mem {q : ℕ} [Fact q.Prime] {A : Subgroup G} {x : G} (hx : x ∉ A)
    (hxq : x ^ q = 1) : Disjoint A (Subgroup.zpowers x) := by
  have hx1 : x ≠ 1 := fun h => hx (h ▸ A.one_mem)
  have hord : orderOf x = q := orderOf_eq_prime hxq hx1
  rw [disjoint_iff, eq_bot_iff]
  rintro y ⟨hyA, hyx⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  apply hx
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hyx
  have hordy : orderOf y = q := by
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp (hord ▸ orderOf_dvd_of_mem_zpowers hyx)
      with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordy])
  exact (Subgroup.zpowers_le.mpr hyA) (heq ▸ Subgroup.mem_zpowers x)

theorem sup_zpowers_card {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : IsMulCommutative A)
    {x : G} (hx : x ∉ A) (hxp : x ^ p = 1) (hcomm : ∀ a ∈ A, a * x = x * a) :
    IsMulCommutative (A ⊔ Subgroup.zpowers x : Subgroup G) ∧
      Nat.card (A ⊔ Subgroup.zpowers x : Subgroup G) = Nat.card A * p := by
  have hc : ∀ (a : A) (n : Subgroup.zpowers x),
      Commute (A.subtype a) ((Subgroup.zpowers x).subtype n) := by
    rintro ⟨a, ha⟩ ⟨n, hn⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_right (hcomm a ha) k
  set f := MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers x).subtype hc with hf_def
  have hrange : f.range = A ⊔ Subgroup.zpowers x := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hx1 : x ≠ 1 := fun h => hx (h ▸ A.one_mem)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdisj : Disjoint A (Subgroup.zpowers x) := disjoint_zpowers_of_not_mem hx hxp
  have hinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr ⟨A.subtype_injective, Subtype.val_injective,
      by rwa [Subgroup.range_subtype, Subgroup.range_subtype]⟩
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ : (u : G) ∈ f.range := by
      rw [hrange]
      exact u.2
    obtain ⟨b, hb⟩ : (v : G) ∈ f.range := by
      rw [hrange]
      exact v.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact hA.is_comm.comm a.1 b.1
    · exact Subtype.ext (by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
        change (a.2 : G) * b.2 = b.2 * a.2
        rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm])
  · rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
      Nat.card_zpowers, hord]

theorem eq_top_of_lt_of_card_eq_mul {p : ℕ} (hp : p.Prime) {H K : Subgroup G} (hHK : H < K)
    (hcard : Nat.card G = Nat.card H * p) : K = ⊤ := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK.le
  have hdvd : Nat.card H * m ∣ Nat.card H * p := by
    rw [← hm, ← hcard]
    exact Subgroup.card_subgroup_dvd_card K
  have hpos : 0 < Nat.card H := Nat.card_pos
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mul_dvd_mul_left hpos hdvd) with h | h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hHK.le (by rw [hm, h, mul_one])) hHK.ne
  · exact Subgroup.eq_top_of_card_eq K (by rw [hm, h, hcard])

omit [Finite G] in
theorem exists_card_eq_card_inf_centralizer_mul (hclass : commutator G ≤ Subgroup.center G)
    (x : G) (H : Subgroup G) :
    ∃ I : Subgroup G, I ≤ Subgroup.center G ∧ (∀ z ∈ I, ∃ h ∈ H, ⁅x, h⁆ = z) ∧
      (∀ h ∈ H, ⁅x, h⁆ ∈ I) ∧
      Nat.card H = Nat.card (H ⊓ Subgroup.centralizer {x} : Subgroup G) * Nat.card I := by
  set f := (CFSG.RankThreeEvenClassification.Helpers.classTwoCommutatorHomRight hclass x).comp
    H.subtype with hf_def
  have hf : ∀ h : H, (f h : G) = ⁅x, (h : G)⁆ := fun _ => rfl
  have hker : f.ker = (Subgroup.centralizer {x}).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      ← Subtype.val_inj, hf, Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm, eq_comm]
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer {x}) (K := H)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, inf_comm] at h1
  refine ⟨f.range.map (Subgroup.center G).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨h, h.2, (hf h).symm⟩
  · intro h hh
    exact ⟨f ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
  · rw [← h1, mul_comm, Subgroup.card_map_of_injective (Subgroup.center G).subtype_injective]

theorem card_le_card_inf_centralizer_mul (hclass : commutator G ≤ Subgroup.center G) (x : G)
    (H : Subgroup G) :
    Nat.card H ≤ Nat.card (H ⊓ Subgroup.centralizer {x} : Subgroup G) *
      Nat.card (Subgroup.center G) := by
  obtain ⟨I, hI, -, -, hcard⟩ := exists_card_eq_card_inf_centralizer_mul hclass x H
  rw [hcard]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hI)

omit [Finite G] in
theorem commutator_le_of_closure_eq_top (hclass : commutator G ≤ Subgroup.center G) {S : Set G}
    (hS : Subgroup.closure S = ⊤) {C : Subgroup G} (hC : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ C) :
    commutator G ≤ C := by
  have hR := CFSG.RankThreeEvenClassification.Helpers.classTwo_commutator_mul_right hclass
  have hL := CFSG.RankThreeEvenClassification.Helpers.classTwo_commutator_mul_left hclass
  have hRinv : ∀ a b : G, ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
    intro a b
    have h := hR a b⁻¹ b
    rw [inv_mul_cancel, commutatorElement_one_right] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hLinv : ∀ a b : G, ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
    intro a b
    have h := hL a⁻¹ a b
    rw [inv_mul_cancel, commutatorElement_one_left] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have step1 : ∀ s ∈ S, ∀ b : G, ⁅s, b⁆ ∈ C := by
    intro s hs b
    have hb : b ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top b
    induction hb using Subgroup.closure_induction with
    | mem t ht => exact hC s hs t ht
    | one =>
      rw [commutatorElement_one_right]
      exact C.one_mem
    | mul b c _ _ hb hc =>
      rw [hR]
      exact C.mul_mem hb hc
    | inv b _ hb =>
      rw [hRinv]
      exact C.inv_mem hb
  have step2 : ∀ a b : G, ⁅a, b⁆ ∈ C := by
    intro a b
    have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem s hs => exact step1 s hs b
    | one =>
      rw [commutatorElement_one_left]
      exact C.one_mem
    | mul a a' _ _ ha ha' =>
      rw [hL]
      exact C.mul_mem ha ha'
    | inv a _ ha =>
      rw [hLinv]
      exact C.inv_mem ha
  rw [commutator_def]
  exact Subgroup.commutator_le.mpr fun a _ b _ => step2 a b

end Orders

section Rank

variable {p : ℕ} {P : Type*} [Group P]

theorem isMulCommutative_zpowers (z : P) : IsMulCommutative (Subgroup.zpowers z) := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
  change (a : P) * b = b * a
  rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]

theorem zpowers_normal_of_mem_center {z : P} (hz : z ∈ Subgroup.center P) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnZ : n ∈ Subgroup.center P := Subgroup.zpowers_le.mpr hz hn
  rw [Subgroup.mem_center_iff.mp hnZ g, mul_assoc, mul_inv_cancel, mul_one]
  exact hn

theorem isMulCommutative_quotient_commutator : IsMulCommutative (P ⧸ commutator P) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [h, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem commutator_le_of_isMulCommutative_quotient (N : Subgroup P) [N.Normal]
    (h : IsMulCommutative (P ⧸ N)) : commutator P ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' N ⁅a, b⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact h.is_comm.comm _ _

theorem quotient_pow_eq_one (hexp : ∀ x : P, x ^ p = 1) (N : Subgroup P) [N.Normal]
    (q : P ⧸ N) : q ^ p = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, hexp, QuotientGroup.mk_one]

theorem isElementaryAbelian_of_isMulCommutative (hcomm : IsMulCommutative P)
    (hexp : ∀ x : P, x ^ p = 1) : IsElementaryAbelian p P :=
  { toIsMulCommutative := hcomm
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }

variable [Finite P]

theorem le_pRank_of_isMulCommutative (hp : p.Prime) (hexp : ∀ x : P, x ^ p = 1)
    {E : Subgroup P} (hE : IsMulCommutative E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.pRank p P := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top ⟨hE, fun x _ => hexp x⟩ hk

theorem exists_isMulCommutative_card_eq_pRank (hp : p.Prime) :
    ∃ E : Subgroup P, IsMulCommutative E ∧ Nat.card E = p ^ CFSG.pRank p P := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup P)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at hcard
  exact ⟨E, hE.1, hcard⟩

theorem pRank_le_of_forall_isMulCommutative (hp : p.Prime) {k : ℕ}
    (h : ∀ E : Subgroup P, IsMulCommutative E → Nat.card E ≤ p ^ k) : CFSG.pRank p P ≤ k := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => h E hE.1

theorem pRank_le_of_card_le (hp : p.Prime) {k : ℕ} (h : Nat.card P ≤ p ^ k) :
    CFSG.pRank p P ≤ k :=
  pRank_le_of_forall_isMulCommutative hp fun E _ => (Subgroup.card_le_card_group E).trans h

theorem pRank_eq_of_isMulCommutative (hp : p.Prime) (hexp : ∀ x : P, x ^ p = 1)
    (hcomm : IsMulCommutative P) {k : ℕ} (hk : Nat.card P = p ^ k) : CFSG.pRank p P = k := by
  refine le_antisymm (pRank_le_of_card_le hp hk.le) ?_
  have htop : IsMulCommutative (⊤ : Subgroup P) :=
    ⟨⟨fun a b => Subtype.ext (hcomm.is_comm.comm (a : P) b)⟩⟩
  exact le_pRank_of_isMulCommutative hp hexp htop (by rw [Subgroup.card_top, hk])

theorem quotient_commutator_rank (hp : p.Prime) (hexp : ∀ x : P, x ^ p = 1) {k : ℕ}
    (hk : Nat.card (P ⧸ commutator P) = p ^ k) :
    IsElementaryAbelian p (P ⧸ commutator P) ∧ CFSG.pRank p (P ⧸ commutator P) = k :=
  ⟨isElementaryAbelian_of_isMulCommutative isMulCommutative_quotient_commutator
      (quotient_pow_eq_one hexp _),
    pRank_eq_of_isMulCommutative hp (quotient_pow_eq_one hexp _)
      isMulCommutative_quotient_commutator hk⟩

theorem exists_mem_center_ne_one (hP : IsPGroup p P) [Fact p.Prime] [Nontrivial P] :
    ∃ z ∈ Subgroup.center P, z ≠ 1 := by
  have := hP.center_nontrivial
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center P)
  exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩

theorem two_le_pRank (hP : IsPGroup p P) [hp : Fact p.Prime] (hexp : ∀ x : P, x ^ p = 1)
    (hcard : p < Nat.card P) : 2 ≤ CFSG.pRank p P := by
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_trans hp.out.one_lt hcard
  obtain ⟨z, hzZ, hz1⟩ := exists_mem_center_ne_one hP
  have hordz : orderOf z = p := orderOf_eq_prime (hexp z) hz1
  obtain ⟨w, hw⟩ : ∃ w, w ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have : Subgroup.zpowers z = ⊤ := eq_top_iff.mpr fun w _ => h w
    rw [← Subgroup.card_top (G := P), ← this, Nat.card_zpowers, hordz] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨hcomm, hcardE⟩ := sup_zpowers_card (isMulCommutative_zpowers z) hw (hexp w)
    fun a ha => (Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hzZ ha) w).symm
  refine le_pRank_of_isMulCommutative hp.out hexp hcomm (k := 2) ?_
  rw [hcardE, Nat.card_zpowers, hordz, sq]

end Rank

section RankTwo

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

theorem card_le_pow_three_of_pRank_two (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hrank : CFSG.pRank p P = 2) :
    ∃ w : P, Nat.card (Subgroup.centralizer {w}) ≤ p ^ 2 ∧ Nat.card P ≤ p ^ 3 ∧
      p ^ 2 ≤ Nat.card P := by
  have hp' : p.Prime := hp.out
  obtain ⟨E₀, -, hE₀card⟩ := exists_isMulCommutative_card_eq_pRank (P := P) hp'
  rw [hrank] at hE₀card
  have hcard_ge : p ^ 2 ≤ Nat.card P := hE₀card ▸ Subgroup.card_le_card_group E₀
  have hp1 : p < Nat.card P := lt_of_lt_of_le (by
    have := hp'.one_lt
    nlinarith) hcard_ge
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_trans hp'.one_lt hp1
  obtain ⟨z, hzZ, hz1⟩ := exists_mem_center_ne_one hP
  have hordz : orderOf z = p := orderOf_eq_prime (hexp z) hz1
  have hN : (Subgroup.zpowers z).Normal := zpowers_normal_of_mem_center hzZ
  have hQcard : Nat.card P = Nat.card (P ⧸ Subgroup.zpowers z) * p := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z), Nat.card_zpowers,
      hordz]
  have : Nontrivial (P ⧸ Subgroup.zpowers z) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    by_contra h
    push Not at h
    have : Nat.card P ≤ p := by
      rw [hQcard]
      have hpos : 0 < Nat.card (P ⧸ Subgroup.zpowers z) := Nat.card_pos
      nlinarith
    omega
  obtain ⟨q, hqZ, hq1⟩ := exists_mem_center_ne_one (hP.to_quotient (Subgroup.zpowers z))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hwz : w ∉ Subgroup.zpowers z := fun h => hq1 ((QuotientGroup.eq_one_iff w).mpr h)
  have hw : ∀ g : P, g * w * g⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
    intro g
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, Subgroup.mem_center_iff.mp hqZ (g : P ⧸ Subgroup.zpowers z)]
    group
  have hzc : ∀ a ∈ Subgroup.zpowers z, a ∈ Subgroup.center P := fun a ha =>
    Subgroup.zpowers_le.mpr hzZ ha
  obtain ⟨hEcomm, hEcard⟩ := sup_zpowers_card (isMulCommutative_zpowers z) hwz (hexp w)
    fun a ha => (Subgroup.mem_center_iff.mp (hzc a ha) w).symm
  rw [Nat.card_zpowers, hordz] at hEcard
  set E := Subgroup.zpowers z ⊔ Subgroup.zpowers w with hE_def
  have hCE : Subgroup.centralizer {w} ≤ E := by
    intro c hc
    by_contra hcE
    have hEc : ∀ e ∈ E, e * c = c * e := by
      have hle : E ≤ Subgroup.centralizer {c} := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_center_iff.mp hzZ c).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
      exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hle he)
    obtain ⟨hcomm3, hcard3⟩ := sup_zpowers_card hEcomm hcE (hexp c) hEc
    have := le_pRank_of_isMulCommutative hp' hexp hcomm3 (k := 3) (by rw [hcard3, hEcard]; ring)
    omega
  let φ : P →* Subgroup.zpowers z :=
    { toFun := fun g => ⟨g * w * g⁻¹ * w⁻¹, hw g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => by
        apply Subtype.ext
        change g * h * w * (g * h)⁻¹ * w⁻¹ = g * w * g⁻¹ * w⁻¹ * (h * w * h⁻¹ * w⁻¹)
        have hc := Subgroup.mem_center_iff.mp (hzc _ (hw h))
        calc g * h * w * (g * h)⁻¹ * w⁻¹ = g * (h * w * h⁻¹ * w⁻¹) * w * g⁻¹ * w⁻¹ := by group
          _ = (h * w * h⁻¹ * w⁻¹) * g * w * g⁻¹ * w⁻¹ := by rw [hc g]
          _ = (h * w * h⁻¹ * w⁻¹) * (g * w * g⁻¹ * w⁻¹) := by group
          _ = g * w * g⁻¹ * w⁻¹ * (h * w * h⁻¹ * w⁻¹) :=
            (Subgroup.mem_center_iff.mp (hzc _ (hw g)) _) }
  have hker : φ.ker = Subgroup.centralizer {w} := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff, ← Subtype.val_inj]
    change g * w * g⁻¹ * w⁻¹ = 1 ↔ _
    constructor
    · intro h
      calc g * w = g * w * g⁻¹ * w⁻¹ * (w * g) := by group
        _ = w * g := by rw [h, one_mul]
    · intro h
      rw [h]
      group
  have h1 : Nat.card (Subgroup.centralizer {w}) ≤ p ^ 2 := by
    have := Subgroup.card_le_of_le hCE
    rw [hEcard] at this
    rw [sq]
    exact this
  have hcardP : Nat.card P ≤ p ^ 3 := by
    rw [← Subgroup.card_ker_mul_card_range φ, hker]
    have h2 : Nat.card φ.range ≤ p := by
      calc Nat.card φ.range ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_card_group _
        _ = p := by rw [Nat.card_zpowers, hordz]
    calc Nat.card (Subgroup.centralizer {w}) * Nat.card φ.range ≤ p ^ 2 * p :=
          Nat.mul_le_mul h1 h2
      _ = p ^ 3 := by ring
  exact ⟨w, h1, hcardP, hcard_ge⟩

omit [Finite P] in
theorem isMulCommutative_of_card_quotient_center_prime (hp : p.Prime)
    (hcard : Nat.card (P ⧸ Subgroup.center P) = p) : IsMulCommutative P := by
  have : IsCyclic (P ⧸ Subgroup.center P) := isCyclic_of_prime_card (hp := ⟨hp⟩) hcard
  exact (QuotientGroup.mk' (Subgroup.center P)).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [QuotientGroup.ker_mk'])

theorem exponent_prime_rank_two_structure (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hrank : CFSG.pRank p P = 2) :
    ((IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (Nat.card P = p ^ 3 ∧ Nat.card (Subgroup.center P) = p ∧
        commutator P = Subgroup.center P ∧ IsElementaryAbelian p (P ⧸ commutator P) ∧
        Nat.card (P ⧸ commutator P) = p ^ 2)) ∧
    commutator P ≤ Subgroup.center P ∧ CFSG.pRank p (P ⧸ commutator P) = 2 := by
  have hp' : p.Prime := hp.out
  obtain ⟨w, hCw, hle3, hge2⟩ := card_le_pow_three_of_pRank_two hP hexp hrank
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk23 : k = 2 ∨ k = 3 := by
    rw [hk] at hle3 hge2
    have h1 := (Nat.pow_le_pow_iff_right hp'.one_lt).mp hle3
    have h2 := (Nat.pow_le_pow_iff_right hp'.one_lt).mp hge2
    omega
  have hquot : ∀ j, Nat.card (P ⧸ commutator P) = p ^ j →
      IsElementaryAbelian p (P ⧸ commutator P) ∧ CFSG.pRank p (P ⧸ commutator P) = j :=
    fun j hj => quotient_commutator_rank hp' hexp hj
  rcases hk23 with rfl | rfl
  ·
    have hcomm : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hk
    have hbot : commutator P = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcomm.is_comm.comm y x
    have hQcard : Nat.card (P ⧸ commutator P) = p ^ 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator P)
      have hc1 : Nat.card (commutator P) = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hc1, mul_one, hk] at h
      exact h.symm
    refine ⟨Or.inl ⟨isElementaryAbelian_of_isMulCommutative hcomm hexp, hk⟩, ?_,
      (hquot 2 hQcard).2⟩
    rw [hbot]
    exact bot_le
  ·
    have hncomm : ¬ IsMulCommutative P := by
      intro hcomm
      have htop : IsMulCommutative (⊤ : Subgroup P) :=
        ⟨⟨fun a b => Subtype.ext (hcomm.is_comm.comm (a : P) b)⟩⟩
      have := le_pRank_of_isMulCommutative hp' hexp htop (k := 3) (by rw [Subgroup.card_top, hk])
      omega
    have : Nontrivial P := by
      rw [← Finite.one_lt_card_iff_nontrivial, hk]
      exact Nat.one_lt_pow (by norm_num) hp'.one_lt
    have hZle : Nat.card (Subgroup.center P) ≤ p ^ 2 :=
      (Subgroup.card_le_of_le (Subgroup.center_le_centralizer {w})).trans hCw
    obtain ⟨j, hj⟩ := (hP.to_subgroup (Subgroup.center P)).exists_card_eq
    have hZcard : Nat.card (Subgroup.center P) = p := by
      have hj1 : 1 ≤ j := by
        by_contra h0
        push Not at h0
        have : j = 0 := by omega
        subst this
        have := hP.center_nontrivial
        rw [← Finite.one_lt_card_iff_nontrivial, hj, pow_zero] at this
        exact lt_irrefl 1 this
      have hj2 : j ≤ 2 := by
        rw [hj] at hZle
        exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp hZle
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
      · rw [hj, pow_one]
      · exfalso
        apply hncomm
        apply isMulCommutative_of_card_quotient_center_prime hp'
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
        rw [hk, hj] at h
        have hpos : 0 < p ^ 2 := pow_pos hp'.pos 2
        exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← h]; ring)
    have hclass : commutator P ≤ Subgroup.center P := by
      apply commutator_le_of_isMulCommutative_quotient
      apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p)
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
      rw [hk, hZcard] at h
      exact Nat.eq_of_mul_eq_mul_right hp'.pos (by rw [← h]; ring)
    have hne : commutator P ≠ ⊥ := by
      intro hbot
      apply hncomm
      refine ⟨⟨fun a b => ?_⟩⟩
      have h : ⁅a, b⁆ ∈ commutator P := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    have hcomm_eq : commutator P = Subgroup.center P := by
      apply Subgroup.eq_of_le_of_card_ge hclass
      rw [hZcard]
      obtain ⟨i, hi⟩ := (hP.to_subgroup (commutator P)).exists_card_eq
      have hdvd : Nat.card (commutator P) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le hclass
      rcases (Nat.dvd_prime hp').mp hdvd with h | h
      · exact absurd ((Subgroup.card_eq_one).mp h) hne
      · exact h.ge
    have hQcard : Nat.card (P ⧸ commutator P) = p ^ 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator P)
      have hc : Nat.card (commutator P) = p := by rw [hcomm_eq, hZcard]
      rw [hc, hk] at h
      exact Nat.eq_of_mul_eq_mul_right hp'.pos (by rw [← h]; ring)
    exact ⟨Or.inr ⟨hk, hZcard, hcomm_eq, (hquot 2 hQcard).1, hQcard⟩, hclass, (hquot 2 hQcard).2⟩

end RankTwo

section ClassTwo

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

theorem frattini_eq_commutator (hP : IsPGroup p P) [Fact p.Prime] (hexp : ∀ x : P, x ^ p = 1) :
    frattini P = commutator P := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (hy | ⟨x, rfl⟩)
    · exact hy
    · show x ^ p ∈ commutator P
      rw [hexp x]
      exact one_mem _
  · exact fun y hy => Subgroup.subset_closure (Or.inl hy)

omit [Finite P] in
theorem exists_commutatorElement_ne_one {x : P} (hx : x ∉ Subgroup.center P) :
    ∃ y : P, ⁅x, y⁆ ≠ 1 := by
  by_contra h
  push Not at h
  apply hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact ((commutatorElement_eq_one_iff_mul_comm).mp (h y)).symm

theorem rank_data_of_commutator_eq_center (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hcomm : commutator P = Subgroup.center P)
    (hgen : ∀ x ∉ Subgroup.center P,
      Subgroup.closure (Set.range fun y : P => ⁅x, y⁆) = Subgroup.center P) [Nontrivial P] :
    ∃ n : ℕ, 1 ≤ n ∧ (Subgroup.center P).index = p ^ (2 * n) ∧
      ∀ A : Subgroup P, (∀ a ∈ A, ∀ b ∈ A, Commute a b) →
        (Subgroup.center P).relIndex (A ⊔ Subgroup.center P) ≤ p ^ n := by
  have hS := CFSG.RankThree.Literature.isSemiExtraspecial_of_special hp.out hP hcomm
    ((frattini_eq_commutator hP hexp).trans hcomm) hgen
  obtain ⟨n, -, hn, hindex, -, -, -, hA⟩ := hS.rank_data hp.out hP
  exact ⟨n, hn, hindex, hA⟩

theorem four_le_pRank_of_card_center_eq [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hZ : Nat.card (Subgroup.center P) = p) (hcard : p ^ 6 ≤ Nat.card P) :
    4 ≤ CFSG.pRank p P := by
  have hp' : p.Prime := hp.out
  have hZc : IsMulCommutative (Subgroup.center P) := inferInstance
  have hlt : ∀ {a b : ℕ}, a < b → p ^ a < p ^ b := fun h => Nat.pow_lt_pow_right hp'.one_lt h
  obtain ⟨x₁, hx₁⟩ : ∃ x, x ∉ Subgroup.center P := by
    by_contra h
    push Not at h
    have htop : Subgroup.center P = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, Subgroup.card_top] at hZ
    have := hlt (show 1 < 6 by norm_num)
    rw [pow_one] at this
    omega
  obtain ⟨hA₁c, hA₁card⟩ := sup_zpowers_card hZc hx₁ (hexp x₁)
    fun a ha => (Subgroup.mem_center_iff.mp ha x₁).symm
  rw [hZ] at hA₁card
  set A₁ := Subgroup.center P ⊔ Subgroup.zpowers x₁ with hA₁_def
  have hK₁ := card_le_card_inf_centralizer_mul hclass x₁ ⊤
  rw [top_inf_eq, Subgroup.card_top, hZ] at hK₁
  obtain ⟨x₂, hx₂C, hx₂A⟩ : ∃ x₂ ∈ Subgroup.centralizer {x₁}, x₂ ∉ A₁ := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show Subgroup.centralizer {x₁} ≤ A₁ from fun y hy => h y hy)
    have : p ^ 6 ≤ p ^ 3 := by
      calc p ^ 6 ≤ Nat.card P := hcard
        _ ≤ Nat.card (Subgroup.centralizer {x₁}) * p := hK₁
        _ ≤ p * p * p := Nat.mul_le_mul_right _ (hA₁card ▸ hle)
        _ = p ^ 3 := by ring
    have := hlt (show 3 < 6 by norm_num)
    omega
  have hA₁x₂ : ∀ a ∈ A₁, a * x₂ = x₂ * a := by
    have hle : A₁ ≤ Subgroup.centralizer {x₂} :=
      sup_le (Subgroup.center_le_centralizer _) (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx₂C).symm))
    exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  obtain ⟨hA₂c, hA₂card⟩ := sup_zpowers_card hA₁c hx₂A (hexp x₂) hA₁x₂
  rw [hA₁card] at hA₂card
  set A₂ := A₁ ⊔ Subgroup.zpowers x₂ with hA₂_def
  have hK₂ := card_le_card_inf_centralizer_mul hclass x₂ (Subgroup.centralizer {x₁})
  rw [hZ] at hK₂
  obtain ⟨x₃, hx₃C, hx₃A⟩ : ∃ x₃ ∈ Subgroup.centralizer {x₁} ⊓ Subgroup.centralizer {x₂},
      x₃ ∉ A₂ := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show Subgroup.centralizer {x₁} ⊓
      Subgroup.centralizer {x₂} ≤ A₂ from fun y hy => h y hy)
    have : p ^ 6 ≤ p ^ 5 := by
      calc p ^ 6 ≤ Nat.card P := hcard
        _ ≤ Nat.card (Subgroup.centralizer {x₁}) * p := hK₁
        _ ≤ Nat.card (Subgroup.centralizer {x₁} ⊓ Subgroup.centralizer {x₂} : Subgroup P) * p *
            p := Nat.mul_le_mul_right _ hK₂
        _ ≤ p * p * p * p * p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hA₂card ▸ hle))
        _ = p ^ 5 := by ring
    have := hlt (show 5 < 6 by norm_num)
    omega
  have hA₂x₃ : ∀ a ∈ A₂, a * x₃ = x₃ * a := by
    have h1 : x₁ ∈ Subgroup.centralizer {x₃} := Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hx₃C.1).symm
    have h2 : x₂ ∈ Subgroup.centralizer {x₃} := Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hx₃C.2).symm
    have hle : A₂ ≤ Subgroup.centralizer {x₃} :=
      sup_le (sup_le (Subgroup.center_le_centralizer _) (Subgroup.zpowers_le.mpr h1))
        (Subgroup.zpowers_le.mpr h2)
    exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  obtain ⟨hA₃c, hA₃card⟩ := sup_zpowers_card hA₂c hx₃A (hexp x₃) hA₂x₃
  exact le_pRank_of_isMulCommutative hp' hexp hA₃c (k := 4) (by rw [hA₃card, hA₂card]; ring)

theorem card_eq_pow_five_of_card_center_eq (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hrank : CFSG.pRank p P = 3) (hZ : Nat.card (Subgroup.center P) = p) :
    Nat.card P = p ^ 5 ∧ commutator P = Subgroup.center P := by
  have hp' : p.Prime := hp.out
  obtain ⟨E, hE, hEcard⟩ := exists_isMulCommutative_card_eq_pRank (P := P) hp'
  rw [hrank] at hEcard
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp'.one_lt
      _ = Nat.card E := hEcard.symm
      _ ≤ Nat.card P := Subgroup.card_le_card_group E
  have hne : commutator P ≠ ⊥ := by
    intro hbot
    have htop : Subgroup.center P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have h : ⁅y, x⁆ ∈ commutator P := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    have h3 : p ^ 3 ≤ p ^ 1 := by
      calc p ^ 3 = Nat.card E := hEcard.symm
        _ ≤ Nat.card P := Subgroup.card_le_card_group E
        _ = Nat.card (Subgroup.center P) := by rw [htop, Subgroup.card_top]
        _ = p ^ 1 := by rw [hZ, pow_one]
    have := (Nat.pow_le_pow_iff_right hp'.one_lt).mp h3
    omega
  have hcomm : commutator P = Subgroup.center P := by
    apply Subgroup.eq_of_le_of_card_ge hclass
    rw [hZ]
    rcases (Nat.dvd_prime hp').mp (hZ ▸ Subgroup.card_dvd_of_le hclass) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h.ge
  have hgen : ∀ x ∉ Subgroup.center P,
      Subgroup.closure (Set.range fun y : P => ⁅x, y⁆) = Subgroup.center P := by
    intro x hx
    have hle : Subgroup.closure (Set.range fun y : P => ⁅x, y⁆) ≤ Subgroup.center P := by
      rw [Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      rw [← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hZ]
    obtain ⟨y, hy⟩ := exists_commutatorElement_ne_one hx
    have hne' : Subgroup.closure (Set.range fun y : P => ⁅x, y⁆) ≠ ⊥ := by
      intro hbot
      apply hy
      have : ⁅x, y⁆ ∈ Subgroup.closure (Set.range fun y : P => ⁅x, y⁆) :=
        Subgroup.subset_closure ⟨y, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    rcases (Nat.dvd_prime hp').mp (hZ ▸ Subgroup.card_dvd_of_le hle) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne'
    · exact h.ge
  obtain ⟨n, hn, hindex, hbound⟩ := rank_data_of_commutator_eq_center hP hexp hcomm hgen
  have hPcard : Nat.card P = p ^ (2 * n + 1) := by
    rw [← Subgroup.card_mul_index (Subgroup.center P), hZ, hindex]
    ring
  have hn2 : 2 ≤ n := by
    have hb := hbound E fun a ha b hb => congrArg Subtype.val (hE.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have h := Subgroup.relIndex_mul_card (Subgroup.center P) (E ⊔ Subgroup.center P)
    rw [inf_of_le_left le_sup_right, hZ] at h
    have hge : p ^ 3 ≤ Nat.card (E ⊔ Subgroup.center P : Subgroup P) :=
      hEcard ▸ Subgroup.card_le_of_le le_sup_left
    have h2 : p ^ 2 ≤ p ^ n := by
      have : p ^ 2 * p ≤ p ^ n * p := by
        calc p ^ 2 * p = p ^ 3 := by ring
          _ ≤ _ := hge
          _ = _ := h.symm
          _ ≤ p ^ n * p := Nat.mul_le_mul_right _ hb
      exact Nat.le_of_mul_le_mul_right this hp'.pos
    exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp h2
  have hn2' : n ≤ 2 := by
    by_contra h
    push Not at h
    have h6 : p ^ 6 ≤ Nat.card P := by
      rw [hPcard]
      exact Nat.pow_le_pow_right hp'.pos (by omega)
    have := four_le_pRank_of_card_center_eq hexp hclass hZ h6
    omega
  refine ⟨?_, hcomm⟩
  rw [hPcard, show 2 * n + 1 = 5 by omega]

theorem card_eq_pow_four_of_card_center_eq_sq (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hrank : CFSG.pRank p P = 3) (hZ : Nat.card (Subgroup.center P) = p ^ 2) :
    Nat.card P = p ^ 4 ∧ Nat.card (commutator P) = p := by
  have hp' : p.Prime := hp.out
  have hZc : IsMulCommutative (Subgroup.center P) := inferInstance
  have hlt : ∀ {a b : ℕ}, a < b → p ^ a < p ^ b := fun h => Nat.pow_lt_pow_right hp'.one_lt h
  have hC : ∀ x ∉ Subgroup.center P, Subgroup.centralizer {x} =
      Subgroup.center P ⊔ Subgroup.zpowers x ∧ Nat.card (Subgroup.centralizer {x}) = p ^ 3 := by
    intro x hx
    obtain ⟨hAc, hAcard⟩ := sup_zpowers_card hZc hx (hexp x)
      fun a ha => (Subgroup.mem_center_iff.mp ha x).symm
    rw [hZ] at hAcard
    have hle : Subgroup.center P ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {x} :=
      sup_le (Subgroup.center_le_centralizer _)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    have heq : Subgroup.centralizer {x} = Subgroup.center P ⊔ Subgroup.zpowers x := by
      refine le_antisymm (fun c hc => ?_) hle
      by_contra hcA
      have hcomm : ∀ a ∈ Subgroup.center P ⊔ Subgroup.zpowers x, a * c = c * a := by
        have hle' : Subgroup.center P ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {c} :=
          sup_le (Subgroup.center_le_centralizer _) (Subgroup.zpowers_le.mpr
            (Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_singleton_iff.mp hc).symm))
        exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle' ha)
      obtain ⟨hBc, hBcard⟩ := sup_zpowers_card hAc hcA (hexp c) hcomm
      have := le_pRank_of_isMulCommutative hp' hexp hBc (k := 4)
        (by rw [hBcard, hAcard]; ring)
      omega
    exact ⟨heq, by rw [heq, hAcard]; ring⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ Subgroup.center P := by
    obtain ⟨E, -, hEcard⟩ := exists_isMulCommutative_card_eq_pRank (P := P) hp'
    rw [hrank] at hEcard
    by_contra h
    push Not at h
    have htop : Subgroup.center P = ⊤ := eq_top_iff.mpr fun x _ => h x
    have h3 : p ^ 3 ≤ p ^ 2 := by
      rw [← hZ, htop, Subgroup.card_top, ← hEcard]
      exact Subgroup.card_le_card_group E
    have := hlt (show 2 < 3 by norm_num)
    omega
  obtain ⟨hCx₀, hCx₀card⟩ := hC x₀ hx₀
  obtain ⟨y, hy⟩ := exists_commutatorElement_ne_one hx₀
  have hyC : y ∉ Subgroup.centralizer {x₀} := by
    intro h
    apply hy
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hle5 : Nat.card P ≤ p ^ 5 := by
    have h := card_le_card_inf_centralizer_mul hclass x₀ ⊤
    rw [top_inf_eq, Subgroup.card_top, hCx₀card, hZ] at h
    calc Nat.card P ≤ p ^ 3 * p ^ 2 := h
      _ = p ^ 5 := by ring
  have hgt3 : p ^ 3 < Nat.card P := by
    rw [← hCx₀card]
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h => hyC ?_
    rw [Subgroup.eq_top_of_card_eq _ h]
    exact Subgroup.mem_top y
  rw [hk] at hle5 hgt3
  have hk45 : k = 4 ∨ k = 5 := by
    have h1 := (Nat.pow_le_pow_iff_right hp'.one_lt).mp hle5
    have h2 := (Nat.pow_lt_pow_iff_right hp'.one_lt).mp hgt3
    omega
  rcases hk45 with rfl | rfl
  · refine ⟨hk, ?_⟩
    set A := Subgroup.centralizer {x₀} with hA_def
    have hAc : IsMulCommutative A := by
      rw [hCx₀]
      exact (sup_zpowers_card hZc hx₀ (hexp x₀)
        fun a ha => (Subgroup.mem_center_iff.mp ha x₀).symm).1
    have htop : A ⊔ Subgroup.zpowers y = ⊤ :=
      eq_top_of_lt_of_card_eq_mul hp' (lt_of_le_of_ne le_sup_left fun h => hyC (h ▸
        (le_sup_right : Subgroup.zpowers y ≤ A ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)))
        (by rw [hk, hCx₀card]; ring)
    have hS : Subgroup.closure ((A : Set P) ∪ {y}) = ⊤ := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure, htop]
    obtain ⟨I, hIZ, -, hyI, hIcard⟩ := exists_card_eq_card_inf_centralizer_mul hclass y A
    have hcommI : commutator P ≤ I := by
      refine commutator_le_of_closure_eq_top hclass hS fun s hs t ht => ?_
      rcases hs with hs | hs <;> rcases ht with ht | ht
      · have : ⁅s, t⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact congrArg Subtype.val (hAc.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
        rw [this]
        exact I.one_mem
      · rw [Set.mem_singleton_iff.mp ht, ← commutatorElement_inv]
        exact I.inv_mem (hyI s hs)
      · rw [Set.mem_singleton_iff.mp hs]
        exact hyI t ht
      · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht, commutatorElement_self]
        exact I.one_mem
    have hZle : Subgroup.center P ≤ A ⊓ Subgroup.centralizer {y} :=
      le_inf (Subgroup.center_le_centralizer _) (Subgroup.center_le_centralizer _)
    have hx₀A : x₀ ∈ A := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hx₀y : x₀ ∉ A ⊓ Subgroup.centralizer {y} := by
      rintro ⟨-, h⟩
      apply hy
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_singleton_iff.mp h
    have hIp : Nat.card I = p := by
      obtain ⟨j, hj⟩ := (hP.to_subgroup (A ⊓ Subgroup.centralizer {y})).exists_card_eq
      have hj2 : 2 ≤ j := by
        have := Subgroup.card_le_of_le hZle
        rw [hZ, hj] at this
        exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp this
      have hj3 : j < 3 := by
        have hlt' : A ⊓ Subgroup.centralizer {y} < A :=
          lt_of_le_of_ne inf_le_left fun h => hx₀y (by rw [h]; exact hx₀A)
        have := Subgroup.card_lt_of_lt hlt'
        rw [hj, hCx₀card] at this
        exact (Nat.pow_lt_pow_iff_right hp'.one_lt).mp this
      have hj' : j = 2 := by omega
      rw [hCx₀card, hj, hj'] at hIcard
      have h3 : p ^ 2 * Nat.card I = p ^ 2 * p := by rw [← hIcard]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp'.pos 2) h3
    have hne : commutator P ≠ ⊥ := by
      intro hbot
      apply hy
      have h : ⁅x₀, y⁆ ∈ commutator P := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x₀) (Subgroup.mem_top y)
      rwa [hbot, Subgroup.mem_bot] at h
    rcases (Nat.dvd_prime hp').mp (hIp ▸ Subgroup.card_dvd_of_le hcommI) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h
  ·
    exfalso
    have hgen : ∀ x ∉ Subgroup.center P,
        Subgroup.closure (Set.range fun y : P => ⁅x, y⁆) = Subgroup.center P := by
      intro x hx
      obtain ⟨I, hIZ, hIsurj, hxI, hIcard⟩ := exists_card_eq_card_inf_centralizer_mul hclass x ⊤
      rw [top_inf_eq, (hC x hx).2, Subgroup.card_top, hk] at hIcard
      have hI : I = Subgroup.center P := by
        apply Subgroup.eq_of_le_of_card_ge hIZ
        rw [hZ]
        have h3 : p ^ 3 * Nat.card I = p ^ 3 * p ^ 2 := by rw [← hIcard]; ring
        rw [Nat.eq_of_mul_eq_mul_left (pow_pos hp'.pos 3) h3]
      apply le_antisymm
      · rw [Subgroup.closure_le, ← hI]
        rintro _ ⟨y, rfl⟩
        exact hxI y (Subgroup.mem_top y)
      · rw [← hI]
        intro z hz
        obtain ⟨h, -, rfl⟩ := hIsurj z hz
        exact Subgroup.subset_closure ⟨h, rfl⟩
    have hcomm : commutator P = Subgroup.center P := by
      refine le_antisymm hclass ?_
      rw [← hgen x₀ hx₀, Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x₀) (Subgroup.mem_top y)
    have : Nontrivial P := by
      rw [← Finite.one_lt_card_iff_nontrivial, hk]
      exact Nat.one_lt_pow (by norm_num) hp'.one_lt
    obtain ⟨n, -, hindex, -⟩ := rank_data_of_commutator_eq_center hP hexp hcomm hgen
    have h := Subgroup.card_mul_index (Subgroup.center P)
    rw [hZ, hindex, hk, ← pow_add] at h
    have := Nat.pow_right_injective hp'.two_le h
    omega

theorem class_two_small_rank_order_bounds (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hclass : commutator P ≤ Subgroup.center P) :
    (CFSG.pRank p P ≤ 2 → CFSG.pRank p (P ⧸ commutator P) ≤ 2) ∧
    (CFSG.pRank p P = 3 → ∃! i : Fin 3, ![
      IsElementaryAbelian p P ∧ Nat.card P = p ^ 3 ∧ CFSG.pRank p (P ⧸ commutator P) = 3,
      Nat.card P = p ^ 5 ∧ Nat.card (Subgroup.center P) = p ∧
        commutator P = Subgroup.center P ∧ CFSG.pRank p (P ⧸ commutator P) = 4,
      Nat.card P = p ^ 4 ∧ Nat.card (Subgroup.center P) = p ^ 2 ∧
        Nat.card (commutator P) = p ∧ CFSG.pRank p (P ⧸ commutator P) = 3] i) ∧
    (CFSG.pRank p P ≤ 3 → CFSG.pRank p (P ⧸ commutator P) ≤ 4) := by
  have hp' : p.Prime := hp.out
  have hquot : ∀ {k : ℕ}, Nat.card (commutator P) = p ^ k → ∀ {j : ℕ}, Nat.card P = p ^ (j + k) →
      CFSG.pRank p (P ⧸ commutator P) = j := by
    intro k hk j hj
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator P)
    rw [hk, hj, pow_add] at h
    exact (quotient_commutator_rank hp' hexp
      (Nat.eq_of_mul_eq_mul_right (pow_pos hp'.pos k) h).symm).2
  have part1 : CFSG.pRank p P ≤ 2 → CFSG.pRank p (P ⧸ commutator P) ≤ 2 := by
    intro h2
    by_cases hcard : Nat.card P ≤ p
    · apply pRank_le_of_card_le hp'
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator P)
      calc Nat.card (P ⧸ commutator P)
          ≤ Nat.card (P ⧸ commutator P) * Nat.card (commutator P) :=
            Nat.le_mul_of_pos_right _ Nat.card_pos
        _ = Nat.card P := h.symm
        _ ≤ p := hcard
        _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
    · push Not at hcard
      have h2' : CFSG.pRank p P = 2 := le_antisymm h2 (two_le_pRank hP hexp hcard)
      exact (exponent_prime_rank_two_structure hP hexp h2').2.2.le
  have part2 : CFSG.pRank p P = 3 → ∃! i : Fin 3, ![
      IsElementaryAbelian p P ∧ Nat.card P = p ^ 3 ∧ CFSG.pRank p (P ⧸ commutator P) = 3,
      Nat.card P = p ^ 5 ∧ Nat.card (Subgroup.center P) = p ∧
        commutator P = Subgroup.center P ∧ CFSG.pRank p (P ⧸ commutator P) = 4,
      Nat.card P = p ^ 4 ∧ Nat.card (Subgroup.center P) = p ^ 2 ∧
        Nat.card (commutator P) = p ∧ CFSG.pRank p (P ⧸ commutator P) = 3] i := by
    intro h3
    have hinj : ∀ {a b : ℕ}, Nat.card P = p ^ a → Nat.card P = p ^ b → a = b :=
      fun ha hb => Nat.pow_right_injective hp'.two_le (ha.symm.trans hb)
    by_cases hcomm : IsMulCommutative P
    ·
      obtain ⟨k, hk⟩ := hP.exists_card_eq
      have hk3 : k = 3 := by rw [← pRank_eq_of_isMulCommutative hp' hexp hcomm hk, h3]
      subst hk3
      have hbot : Nat.card (commutator P) = p ^ 0 := by
        rw [pow_zero, Subgroup.card_eq_one, commutator_def,
          Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hcomm.is_comm.comm y x
      refine ⟨0, ⟨isElementaryAbelian_of_isMulCommutative hcomm hexp, hk,
        hquot hbot (by rw [hk])⟩, fun j hj => ?_⟩
      fin_cases j
      · rfl
      · simp at hj
        exact absurd (hinj hk hj.1) (by norm_num)
      · simp at hj
        exact absurd (hinj hk hj.1) (by norm_num)
    ·
      have hnc : ∃ x, x ∉ Subgroup.center P := by
        by_contra h
        push Not at h
        exact hcomm ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h b) a⟩⟩
      obtain ⟨x, hx⟩ := hnc
      have : Nontrivial P := ⟨⟨x, 1, fun h => hx (h ▸ Subgroup.one_mem _)⟩⟩
      obtain ⟨j, hj⟩ := (hP.to_subgroup (Subgroup.center P)).exists_card_eq
      have hj1 : 1 ≤ j := by
        by_contra h0
        have : j = 0 := by omega
        subst this
        have := hP.center_nontrivial
        rw [← Finite.one_lt_card_iff_nontrivial, hj, pow_zero] at this
        exact lt_irrefl 1 this
      have hj2 : j ≤ 2 := by
        by_contra h
        push Not at h
        obtain ⟨hc, hcard⟩ := sup_zpowers_card inferInstance hx (hexp x)
          fun a ha => (Subgroup.mem_center_iff.mp ha x).symm
        have := le_pRank_of_isMulCommutative hp' hexp hc (k := j + 1)
          (by rw [hcard, hj, pow_succ])
        omega
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
      · have hZ : Nat.card (Subgroup.center P) = p := by rw [hj, pow_one]
        obtain ⟨h5, hcomm'⟩ := card_eq_pow_five_of_card_center_eq hP hexp hclass h3 hZ
        have hc : Nat.card (commutator P) = p ^ 1 := by rw [hcomm', hZ, pow_one]
        refine ⟨1, ⟨h5, hZ, hcomm', hquot hc (by rw [h5])⟩, fun i hi => ?_⟩
        fin_cases i
        · simp at hi
          exact absurd (hinj h5 hi.2.1) (by norm_num)
        · rfl
        · simp at hi
          exact absurd (hinj h5 hi.1) (by norm_num)
      · obtain ⟨h4, hc⟩ := card_eq_pow_four_of_card_center_eq_sq hP hexp hclass h3 hj
        have hc' : Nat.card (commutator P) = p ^ 1 := by rw [hc, pow_one]
        refine ⟨2, ⟨h4, hj, hc, hquot hc' (by rw [h4])⟩, fun i hi => ?_⟩
        fin_cases i
        · simp at hi
          exact absurd (hinj h4 hi.2.1) (by norm_num)
        · simp at hi
          exact absurd (hinj h4 hi.1) (by norm_num)
        · rfl
  refine ⟨part1, part2, fun h3 => ?_⟩
  rcases Nat.lt_or_ge (CFSG.pRank p P) 3 with h | h
  · exact (part1 (by omega)).trans (by norm_num)
  · obtain ⟨i, hi, -⟩ := part2 (le_antisymm h3 h)
    fin_cases i
    · simp at hi
      rw [hi.2.2]
      norm_num
    · simp at hi
      rw [hi.2.2.2]
    · simp at hi
      rw [hi.2.2.2]
      norm_num

end ClassTwo

section Rank3II

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

omit [Finite P] in
theorem subgroup_pow_eq_one (hexp : ∀ x : P, x ^ p = 1) (M : Subgroup P) (x : M) : x ^ p = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, hexp, Subgroup.coe_one])

theorem isExtraspecialPGroup_of_card_eq_pow_three (hP : IsPGroup p P) [hp : Fact p.Prime]
    (hexp : ∀ x : P, x ^ p = 1) (hcard : Nat.card P = p ^ 3) (hnc : ¬ IsMulCommutative P) :
    CFSG.IsExtraspecialPGroup p P := by
  have hp' : p.Prime := hp.out
  have hrank : CFSG.pRank p P = 2 := by
    refine le_antisymm (pRank_le_of_forall_isMulCommutative hp' fun E hE => ?_)
      (two_le_pRank hP hexp (by rw [hcard]; exact lt_self_pow₀ hp'.one_lt (by norm_num)))
    obtain ⟨i, hi⟩ := (hP.to_subgroup E).exists_card_eq
    have hi3 : i ≤ 3 := by
      have := Subgroup.card_le_card_group E
      rw [hi, hcard] at this
      exact (Nat.pow_le_pow_iff_right hp'.one_lt).mp this
    rw [hi]
    refine Nat.pow_le_pow_right hp'.pos ?_
    by_contra h
    have hi' : i = 3 := by omega
    apply hnc
    have htop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hi, hi', hcard])
    exact ⟨⟨fun a b => congrArg Subtype.val
      (hE.is_comm.comm ⟨a, htop ▸ Subgroup.mem_top a⟩ ⟨b, htop ▸ Subgroup.mem_top b⟩)⟩⟩
  rcases (exponent_prime_rank_two_structure hP hexp hrank).1 with ⟨-, h2⟩ | ⟨-, hZ, hcomm, -⟩
  · rw [hcard] at h2
    have := Nat.pow_right_injective hp'.two_le h2
    omega
  · exact ⟨hP, hcomm, (frattini_eq_commutator hP hexp).trans hcomm, hZ⟩

theorem rank3II_3_2 (hP : IsPGroup p P) [hp : Fact p.Prime] (hexp : ∀ x : P, x ^ p = 1)
    (hclass : commutator P ≤ Subgroup.center P) :
    (CFSG.pRank p P = 2 →
      (CFSG.IsExtraspecialPGroup p P ∧ Nat.card P = p ^ 3) ∨
        (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2)) ∧
    (CFSG.pRank p P = 3 →
      (CFSG.IsExtraspecialPGroup p P ∧ Nat.card P = p ^ 5) ∨
        (IsElementaryAbelian p P ∧ Nat.card P = p ^ 3) ∨
        ∃ A B : Subgroup P, A ≤ Subgroup.center P ∧ Nat.card A = p ∧
          CFSG.IsExtraspecialPGroup p B ∧ Nat.card B = p ^ 3 ∧ A ⊓ B = ⊥ ∧ A ⊔ B = ⊤) := by
  have hp' : p.Prime := hp.out
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · rcases (exponent_prime_rank_two_structure hP hexp h2).1 with h | ⟨h3, hZ, hcomm, -⟩
    · exact Or.inr h
    · exact Or.inl ⟨⟨hP, hcomm, (frattini_eq_commutator hP hexp).trans hcomm, hZ⟩, h3⟩
  obtain ⟨i, hi, -⟩ := (class_two_small_rank_order_bounds hP hexp hclass).2.1 h3
  fin_cases i
  · simp at hi
    exact Or.inr (Or.inl ⟨hi.1, hi.2.1⟩)
  · simp at hi
    obtain ⟨h5, hZ, hcomm, -⟩ := hi
    exact Or.inl ⟨⟨hP, hcomm, (frattini_eq_commutator hP hexp).trans hcomm, hZ⟩, h5⟩
  · simp at hi
    obtain ⟨h4, hZ, hc, -⟩ := hi
    right
    right
    obtain ⟨a, haZ, haP⟩ : ∃ a ∈ Subgroup.center P, a ∉ commutator P := by
      by_contra h
      push Not at h
      have hle := Subgroup.card_le_of_le (show Subgroup.center P ≤ commutator P from h)
      rw [hZ, hc] at hle
      have := (Nat.pow_le_pow_iff_right hp'.one_lt).mp (by rwa [pow_one] : p ^ 2 ≤ p ^ 1)
      omega
    obtain ⟨M, hM, haM⟩ : ∃ M : Subgroup P, IsCoatom M ∧ a ∉ M := by
      by_contra h
      push Not at h
      apply haP
      rw [← frattini_eq_commutator hP hexp]
      change a ∈ ⨅ (M : Subgroup P) (_ : IsCoatom M), M
      rw [Subgroup.mem_iInf]
      intro M
      rw [Subgroup.mem_iInf]
      exact fun hM => h M hM
    have hMindex := CFSG.RankThreeEvenClassification.Helpers.pGroup_coatom_index p hp' hP M hM
    have hMcard : Nat.card M = p ^ 3 := by
      have h := Subgroup.card_mul_index M
      rw [hMindex, h4] at h
      exact Nat.eq_of_mul_eq_mul_right hp'.pos (by rw [h]; ring)
    have ha1 : a ≠ 1 := fun h => haP (h ▸ (commutator P).one_mem)
    have hord_a : orderOf a = p := orderOf_eq_prime (hexp a) ha1
    have hAZ : Subgroup.zpowers a ≤ Subgroup.center P := Subgroup.zpowers_le.mpr haZ
    have hdisj := disjoint_zpowers_of_not_mem haM (hexp a)
    have hsup : Subgroup.zpowers a ⊔ M = ⊤ := by
      rw [sup_comm]
      exact hM.2 _ (lt_of_le_of_ne le_sup_left fun h => haM (h ▸
        (le_sup_right : Subgroup.zpowers a ≤ M ⊔ Subgroup.zpowers a) (Subgroup.mem_zpowers a)))
    have hMnc : ¬ IsMulCommutative M := by
      intro hMc
      have hMZ : M ≤ Subgroup.center P := by
        intro m hm
        rw [Subgroup.mem_center_iff]
        intro g
        have hle : Subgroup.zpowers a ⊔ M ≤ Subgroup.centralizer {m} := by
          refine sup_le (hAZ.trans (Subgroup.center_le_centralizer _)) fun m' hm' => ?_
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (hMc.is_comm.comm ⟨m', hm'⟩ ⟨m, hm⟩)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hsup ▸ Subgroup.mem_top g))
      have htop : Subgroup.center P = ⊤ := by
        rw [eq_top_iff, ← hsup]
        exact sup_le hAZ hMZ
      rw [htop, Subgroup.card_top, h4] at hZ
      have := Nat.pow_right_injective hp'.two_le hZ
      omega
    refine ⟨Subgroup.zpowers a, M, hAZ, by rw [Nat.card_zpowers, hord_a], ?_, hMcard,
      disjoint_iff.mp hdisj.symm, hsup⟩
    exact isExtraspecialPGroup_of_card_eq_pow_three (hP.to_subgroup M) (subgroup_pow_eq_one hexp M)
      hMcard hMnc

end Rank3II

end CFSG.RankThree.PartTwo
