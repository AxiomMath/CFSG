module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofFX
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof152WE

theorem false_of_le_frattini {A X : Subgroup G} {p : ℕ} {P : Subgroup G} (hP : PData152 A X p P)
    (hle : P ≤ (frattini ↥P).map P.subtype) : False := by
  have hp : p.Prime := hP.prime
  have htop : frattini ↥P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hbot : (⊥ : Subgroup ↥P) = ⊤ := frattini_nongenerating (by rw [htop, sup_top_eq])
  have h1 : Nat.card P = 1 := by
    rw [← Subgroup.card_top (G := ↥P), ← hbot, Subgroup.card_bot]
  rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
  · rw [h1] at h
    have := Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) hp.one_lt
    omega
  · rw [h1] at h
    have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hp.one_lt
    omega

omit [Finite G] in
theorem card_closure_pair [Finite G] {A : Subgroup G} (hA : Late.IsE27 A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) * Nat.card (Subgroup.zpowers a ⊓
      Subgroup.zpowers b : Subgroup G) =
      Nat.card (Subgroup.zpowers a) * Nat.card (Subgroup.zpowers b) := by
  have hcd : Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    have hxA : x ∈ A := Subgroup.zpowers_le.mpr ha hx
    have hyA : y ∈ A := Subgroup.zpowers_le.mpr hb hy
    have h := hA.1.1.is_comm.comm ⟨x, hxA⟩ ⟨y, hyA⟩
    exact congrArg Subtype.val h
  rw [hcd]
  exact (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1

omit [Finite G] in
theorem zpowers_inf_eq_bot [Finite G] {a b : G} (hb3 : Nat.card (Subgroup.zpowers b) = 3)
    (hba : b ∉ Subgroup.zpowers a) : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers b : Subgroup G) ∣ 3 :=
    hb3 ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hb3])
    exact hba ((heq ▸ inf_le_left : Subgroup.zpowers b ≤ Subgroup.zpowers a)
      (Subgroup.mem_zpowers b))

omit [Finite G] in
theorem card_zpowers_eq_three [Finite G] {A : Subgroup G} (hA : Late.IsE27 A) {b : G}
    (hb : b ∈ A) (hb1 : b ≠ 1) : Nat.card (Subgroup.zpowers b) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (hA.1.2 b hb) hb1

theorem closure_eq_of_mem {A : Subgroup G} (hA : Late.IsE27 A) {c' d e : G} (hcA : c' ∈ A)
    (hdA : d ∈ A) (hc1 : c' ≠ 1)
    (he : e ∈ Subgroup.closure ({c', d} : Set G)) (hec : e ∉ Subgroup.zpowers c') :
    Subgroup.closure ({e, c'} : Set G) = Subgroup.closure ({c', d} : Set G) := by
  have hEA : Subgroup.closure ({c', d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcA
    · exact hdA
  have heA : e ∈ A := hEA he
  have he1 : e ≠ 1 := fun h => hec (h ▸ Subgroup.one_mem _)
  have hle : Subgroup.closure ({e, c'} : Set G) ≤ Subgroup.closure ({c', d} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact he
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := card_closure_pair hA heA hcA
  rw [inf_comm, zpowers_inf_eq_bot (card_zpowers_eq_three hA heA he1) hec, Subgroup.card_bot,
    mul_one, card_zpowers_eq_three hA heA he1, card_zpowers_eq_three hA hcA hc1] at h1
  have h2 := card_closure_pair hA hcA hdA
  have hpos : 0 < Nat.card (Subgroup.zpowers c' ⊓ Subgroup.zpowers d : Subgroup G) := Nat.card_pos
  have hd3 : Nat.card (Subgroup.zpowers d) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.1.2 d hdA))
  rw [card_zpowers_eq_three hA hcA hc1] at h2
  rw [h1]
  nlinarith

end Proof152WE

open Proof152WE

theorem not_le_centralizer_of_mem_omegaA
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h142 : Item142AllS14) (h135 : Item135) (hmult : KFacts.KS18Mult) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y M X : Subgroup G} {c' : G} {L' : Subgroup G}
    {d : G} {p : ℕ} {P : Subgroup G} (hpt : Pt152 A (lB A) Y M X c' L')
    (hd : DData152 A X c' L' d) (hP : PData152 A X p P) (hp3 : p ≠ 3)
    (hfr : P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype)
    {e : G} (he : e ∈ Subgroup.closure ({c', d} : Set G))
    (heΩ : Subgroup.zpowers e ∈ omegaA A) : ¬ P ≤ Subgroup.centralizer ({e} : Set G) := by
  intro hPe
  have hA := h.isE27
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hpt.omega
  have hc1 : c' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  obtain ⟨heA, he3, -⟩ := zpowers_mem_omegaA_iff.mp heΩ
  by_cases hec : e ∈ Subgroup.zpowers c'
  ·
    have hzeq : Subgroup.zpowers e = Subgroup.zpowers c' :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec) (by rw [hc3, he3])
    rw [centralizer_singleton_eq_of_zpowers_eq hzeq] at hPe
    exact false_of_le_frattini hP (le_inf le_rfl hPe |>.trans hfr)
  · obtain ⟨Le, hLe, hJe⟩ := exists_hj_of_hj_point h134 h48 h415 h hpt.omega hpt.mem_lA hpt.hj
      hd.mem_d hd.ne_d hd.central_d heΩ
    have hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
        (Subgroup.closure ({e, c'} : Set G) : Set G) := by
      rw [hd.cent, closure_eq_of_mem hA hcA hd.mem_d hc1 he hec]
    exact Proof152FX.not_le_centralizer_of h142 h135 hmult h hpt.ctx heΩ hLe hJe hcA hcent hP hp3
      hPe

theorem exists_le_centralizer
    (h415 : Sec4.Item4_15) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {Y M X : Subgroup G} {c' : G} {L' : Subgroup G} {d : G} {p : ℕ} {P : Subgroup G}
    (hpt : Pt152 A (lB A) Y M X c' L') (hd : DData152 A X c' L' d) (hP : PData152 A X p P)
    (hp3 : p ≠ 3)
    (hfr : P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype) :
    ∃ e ∈ Subgroup.closure ({c', d} : Set G), e ∉ Subgroup.zpowers c' ∧
      P ≤ Subgroup.centralizer ({e} : Set G) := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have hA := h.isE27
  obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hpt.omega
  have hc1 : c' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    exact absurd hc3 (by norm_num)
  set E := Subgroup.closure ({c', d} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcA
    · exact hd.mem_d
  have h' : Sec14Std G A c' L' :=
    { h with zpowers_mem_omegaA := hpt.omega, mem_lA := hpt.mem_lA }
  have hcL : c' ∉ L' :=
    not_mem_of_center_eq_bot h'.toSec13Data (KFacts.KS14.center_eq_bot_of_j2 h415 hpt.hj)
  have hdc : d ∉ Subgroup.zpowers c' := by
    intro hdc
    have hzeq : Subgroup.zpowers d = Subgroup.zpowers c' :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
        (by rw [hc3, card_zpowers_eq_three hA hd.mem_d hd.ne_d])
    have hcd : c' ∈ Subgroup.zpowers d := hzeq ▸ Subgroup.mem_zpowers c'
    exact hcL (Subgroup.zpowers_le.mpr hd.central_d.1 hcd)
  have hE9 : 3 ^ (1 + 1) ≤ Nat.card E := by
    have h1 := card_closure_pair hA hcA hd.mem_d
    rw [zpowers_inf_eq_bot (card_zpowers_eq_three hA hd.mem_d hd.ne_d) hdc,
      Subgroup.card_bot, mul_one, card_zpowers_eq_three hA hcA hc1,
      card_zpowers_eq_three hA hd.mem_d hd.ne_d] at h1
    rw [← hE] at h1
    omega
  have hEcomm : ∀ x y : ↥E, x * y = y * x := fun x y => Subtype.ext (by
    have h1 := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hEA x.2⟩ ⟨y, hEA y.2⟩)
    simpa using h1)
  have hEab : CFSG.Open.IsElemAbelian 3 E := ⟨⟨⟨hEcomm⟩⟩, fun x hx => hA.1.2 x (hEA hx)⟩
  have hPcop : Nat.Coprime 3 (Nat.card P) := by
    have hPp : IsPGroup p P := by
      rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
      · exact IsPGroup.of_card h
      · exact IsPGroup.of_card h
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three hP.prime).mpr
      (Ne.symm hp3))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E P hEab hE9 (hEA.trans hP.norm_p) hPcop
  obtain ⟨F, ⟨hFE, hF3⟩, hFΦ⟩ : ∃ F ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
      ¬ P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype := by
    by_contra hno
    have hno' : ∀ F ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
        P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype :=
      fun F hF => by
        by_contra hc
        exact hno ⟨F, hF, hc⟩
    refine false_of_le_frattini hP ?_
    have hle := iSup₂_le hno'
    rw [hgen] at hle
    exact hle
  obtain ⟨e, heF, he1⟩ : ∃ e ∈ F, e ≠ 1 := by
    by_contra hno
    have hno' : ∀ e ∈ F, e = 1 := fun e he => by
      by_contra hc
      exact hno ⟨e, he, hc⟩
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hno'
    rw [hbot, Subgroup.card_bot, pow_one] at hF3
    exact absurd hF3 (by norm_num)
  have heE : e ∈ E := hFE heF
  have heA : e ∈ A := hEA heE
  have heC : e ∈ Sec4.thetaQuotCentralizer X := by
    refine Proof152F.mem_thetaQuotCentralizer_of_mem hpt.ctx.norm_x ?_
    have he' : e ∈ (Subgroup.closure {c', d} : Set G) := heE
    rw [← hd.cent] at he'
    exact he'
  have hPe : P ≤ Subgroup.centralizer ({e} : Set G) := by
    rcases Proof152F.inf_centralizer_le_frattini_or_le_of hpt.ctx heA (hA.1.2 e heA) heC hP hp3
      with hle | hle
    · exfalso
      refine hFΦ ((inf_le_inf_left _ ?_).trans hle)
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heF)
    · exact hle
  refine ⟨e, heE, fun hec => ?_, hPe⟩
  have hzeq : Subgroup.zpowers e = Subgroup.zpowers c' :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec)
      (by rw [hc3, card_zpowers_eq_three hA heA he1])
  rw [centralizer_singleton_eq_of_zpowers_eq hzeq] at hPe
  exact false_of_le_frattini hP ((le_inf le_rfl hPe).trans hfr)

end CFSG.RankThree.PartTwo.Sec15
