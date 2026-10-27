module

public import CFSG.RankThree.PartOne.S10.CentralCoverContract
import CFSG.RankThree.PartOne.S10.CentralCoverPreimageSylow
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionLifting
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.RankThreeEven CFSG.RankThree.CentralCover

namespace CentralCoverObstruction

theorem isElementaryAbelian_of_mulEquiv_of_isElementaryAbelian {p : ℕ} {G G' : Type*} [Group G]
    [Group G'] (e : G ≃* G') (hG : IsElementaryAbelian p G) : IsElementaryAbelian p G' := by
  have hc : IsMulCommutative G' := ⟨⟨fun a b => by
    have h := hG.is_comm.comm (e.symm a) (e.symm b)
    simpa using congrArg e h⟩⟩
  refine { toIsMulCommutative := hc, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun h => ?_
  have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p G) (e.symm h)
  simpa using congrArg e h1

theorem exists_card_omegaOne_eq_pow {P : Type*} [Group P] [Finite P] {A : Subgroup P}
    (hA : A ≤ Subgroup.center P) {p : ℕ} (hp : p.Prime) :
    ∃ d : ℕ, Nat.card {a : P // a ∈ A ∧ a ^ p = 1} = p ^ d := by
  have : Fact p.Prime := ⟨hp⟩
  let Om : Subgroup P :=
    { carrier := {a | a ∈ A ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        have hc : Commute a b := (Subgroup.mem_center_iff.mp (hA ha.1) b).symm
        rw [hc.mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨A.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hOm : IsPGroup p Om := fun x => ⟨1, Subtype.ext (by simpa using x.2.2)⟩
  obtain ⟨d, hd⟩ := hOm.exists_card_eq
  exact ⟨d, hd⟩


section AbstractExactCase

theorem exact_case_of_surjection {P E : Type*} [Group P] [Finite P] [Group E] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : IsPGroup p P) (A : Subgroup P) [A.Normal]
    (hAc : A ≤ Subgroup.center P) (g : P →* E) (hg : Function.Surjective g)
    (hker : g.ker = A) (hE : IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 4)
    (hrk : CFSG.pRank p P ≤ 3) :
    CFSG.pRank p P = 3 ∧ A ≠ ⊥ ∧ ∃ d : ℕ, Nat.card {a : P // a ∈ A ∧ a ^ p = 1} = p ^ d ∧
      (d = 1 ∨ d = 2) ∧ CentralOddExtensionExactlyOneCase A p d := by
  have : Fact p.Prime := ⟨hp⟩
  let eqv : (P ⧸ A) ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have hW : IsElementaryAbelian p (P ⧸ A) :=
    isElementaryAbelian_of_mulEquiv_of_isElementaryAbelian eqv.symm hE
  have hcard : Nat.card (P ⧸ A) = p ^ 4 := (Nat.card_congr eqv.toEquiv).trans hEc
  obtain ⟨d, hd⟩ := exists_card_omegaOne_eq_pow hAc hp
  have hmain := (central_odd_prime_extension_exact_elementary_rank hp hp2 hP A hAc hW
    hd).2.2.2.2.2 hcard
  obtain ⟨h3, hcases⟩ := hmain.1 hrk
  have hd12 : d = 1 ∨ d = 2 := by
    rcases hcases.1 with h1 | h2 | h3'
    · exact Or.inl h1.1
    · exact Or.inl h2.1
    · exact Or.inr h3'.1
  have hA0 : A ≠ ⊥ := by
    intro hA0
    have key : ∀ x : P, x ∈ A → x = 1 := fun x hx => by
      rw [hA0, Subgroup.mem_bot] at hx
      exact hx
    have hone : ∀ a : {a : P // a ∈ A ∧ a ^ p = 1}, (a : P) = 1 := fun a => key a.1 a.2.1
    have hsub : Subsingleton {a : P // a ∈ A ∧ a ^ p = 1} :=
      ⟨fun a b => Subtype.ext ((hone a).trans (hone b).symm)⟩
    have h1 : Nat.card {a : P // a ∈ A ∧ a ^ p = 1} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    rw [hd] at h1
    have hp1 := hp.one_lt
    have hpd : p ≤ p ^ d := by
      rcases hd12 with h | h
      · rw [h, pow_one]
      · rw [h]
        nlinarith
    exact lt_irrefl 1 (lt_of_lt_of_le hp1 (hpd.trans h1))
  exact ⟨h3, hA0, d, hd, hd12, hcases⟩

end AbstractExactCase

section ExactCase

variable {G : Type} [Group G] [Finite G]

theorem preimage_sylow_exact_case {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (G ⧸ Subgroup.center G)) (hE : IsElementaryAbelian p E)
    (hEc : Nat.card E = p ^ 4) (P : Subgroup G)
    (hPW : P ≤ E.comap (centerQuotientMap G)) (hP : IsPGroup p P)
    (hPE : P.map (centerQuotientMap G) = E) (hPZ : P ⊓ Subgroup.center G = centerPCore p G)
    (hrk : CFSG.pRank p ↥P ≤ 3) :
    CFSG.pRank p ↥P = 3 ∧ centerPCore p G ≠ ⊥ ∧ p ∣ Nat.card (Subgroup.center G) ∧
      ∃ d : ℕ, Nat.card {a : ↥P // a ∈ (centerPCore p G).subgroupOf P ∧ a ^ p = 1} = p ^ d ∧
        (d = 1 ∨ d = 2) ∧ ∃ _ : ((centerPCore p G).subgroupOf P).Normal,
          CentralOddExtensionExactlyOneCase ((centerPCore p G).subgroupOf P) p d := by
  have : Fact p.Prime := ⟨hp⟩
  set q := centerQuotientMap G with hq
  set A := centerPCore p G with hAdef
  set A' := A.subgroupOf P with hA'
  have hAZ : A ≤ Subgroup.center G := Subgroup.map_subtype_le _
  have hA'c : A' ≤ Subgroup.center ↥P := fun a ha =>
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_center_iff.mp (hAZ (Subgroup.mem_subgroupOf.mp ha)) (g : G))
  have hA'n : A'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hA'c hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hmem : ∀ x : P, q (x : G) ∈ E := fun x => hPW x.2
  let g : P →* E := (q.comp P.subtype).codRestrict E hmem
  have hg : Function.Surjective g := by
    intro e
    have : (e : G ⧸ Subgroup.center G) ∈ P.map q := hPE ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hker : g.ker = A' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    change q (x : G) = 1 ↔ (x : G) ∈ A
    rw [hq, centerQuotientMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have : (x : G) ∈ P ⊓ Subgroup.center G := ⟨x.2, hx⟩
      rwa [hPZ] at this
    · intro hx
      exact hAZ hx
  have := hA'n
  obtain ⟨h3, hA'0, d, hd, hd12, hcases⟩ :=
    exact_case_of_surjection hp hp2 hP A' hA'c g hg hker hE hEc hrk
  have hA0 : A ≠ ⊥ := by
    intro h0
    apply hA'0
    rw [hA', h0, Subgroup.bot_subgroupOf]
  refine ⟨h3, hA0, ?_, d, hd, hd12, hA'n, hcases⟩
  have hAp : IsPGroup p A := (CFSG.pCore_isPGroup (p := p)).map _
  rcases hAp.card_eq_or_dvd with h1 | h1
  · exact absurd (Subgroup.card_eq_one.mp h1) hA0
  · exact h1.trans (Subgroup.card_dvd_of_le hAZ)

end ExactCase

end CentralCoverObstruction


theorem source_five_two_central_cover_local_rank_four_obstruction :
    SourceFiveTwoCentralCoverLocalRankFourObstruction := by
  intro H _ _ he X
  refine ⟨fun U hU2 hU1 => ?_, fun p hp hp2 => ?_⟩
  · obtain ⟨T, hTW, hT2, hTmax, hTU, hTsup⟩ :=
      CentralCoverSylow.exists_preimage_sylow Nat.prime_two U hU2
    obtain ⟨hnorm1, hnorm2, hcen⟩ :=
      CentralCoverSylow.preimage_normalizer_eq U T hT2 hTmax hTU
    refine ⟨T, hTW, hT2, hTmax, hTU, hTsup, hnorm1, hnorm2, hcen, ?_⟩
    intro p hp hp2 E hEN hE hEc
    have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
    obtain ⟨P, hPW, hP2, hPmax, hPE, -⟩ := CentralCoverSylow.exists_preimage_sylow hp E hEp
    have hPZ := CentralCoverSylow.inf_center_eq_centerPCore hp E P hP2 hPmax
    have hPN : P ≤ Subgroup.normalizer (T : Set ↥X) := by
      rw [← hnorm1]
      exact hPW.trans (Subgroup.comap_mono hEN)
    have hT0 : T ≠ ⊥ := fun h => hU1 (by rw [← hTU, h, Subgroup.map_bot])
    have hT'0 : T.map X.subtype ≠ ⊥ := fun h =>
      hT0 ((Subgroup.map_eq_bot_iff_of_injective T X.subtype_injective).mp h)
    have hT'2 : IsPGroup 2 (T.map X.subtype) := hT2.map _
    have hPle : P.map X.subtype ≤ Subgroup.normalizer ((T.map X.subtype : Subgroup H) : Set H) :=
      (Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map X.subtype)
    have h1 := OddCore37.pRank_le_localRank_of_le_normalizer hp hT'0 hT'2 hPle
    rw [OddCore37.pRank_map_eq X.subtype X.subtype_injective hp P] at h1
    have hrk : CFSG.pRank p ↥P ≤ 3 :=
      h1.trans ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans he)
    obtain ⟨h3, hne, hdvd, d, hd, hd12, hn, hcase⟩ :=
      CentralCoverObstruction.preimage_sylow_exact_case hp hp2 E hE hEc P hPW hP2 hPE hPZ hrk
    exact ⟨P, hPW, hP2, hPmax, hPE, hPZ, hPN, Subgroup.le_normalizer_map X.subtype, h3, hne,
      hdvd, d, hd, hd12, hn, hcase⟩
  · constructor
    · intro h
      by_contra hno
      push Not at hno
      have hle : localRank p (↥X ⧸ Subgroup.center ↥X) ≤ 3 := by
        refine csSup_le' ?_
        rintro k ⟨H', ⟨S, hS0, hS2, rfl⟩, rfl⟩
        by_contra hk
        push Not at hk
        obtain ⟨E, hEN, hE, hEc⟩ := (Planes.le_pRank_iff hp
          (Subgroup.normalizer (S : Set (↥X ⧸ Subgroup.center ↥X))) 4).1 (by omega)
        exact hno S hS2 hS0 E hEN hE hEc
      omega
    · rintro ⟨U, hU2, hU0, E, hEN, hE, hEc⟩
      have h4 : 4 ≤ CFSG.Assembly.pRank p
          (Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X))) :=
        (Planes.le_pRank_iff hp _ 4).2 ⟨E, hEN, hE, hEc⟩
      have h5 := CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt
        (⟨U, hU0, hU2, rfl⟩ : CFSG.Assembly.IsTwoLocal
          (Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X))))
      omega

end CFSG.RankThree.PartOne
