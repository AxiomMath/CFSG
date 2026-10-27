module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
import CFSG.RankThree.PartTwo.Sec16.Item169General
import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof169Theta

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem theta_eq_pCore_two_of_item135Simple
    (h135 : Item135Simple)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L)
    (hL : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L := by
  have hq := h135 G A c L hD hL
  refine Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult hq ?_
  rcases hL with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem not_odd_cube_dvd_l34 : ∀ q < 28, 3 ≤ q → q % 2 = 1 → ¬ q ^ 3 ∣ 20160 := by
  decide

theorem not_isoLThreePi_of_l34 {X : Type} [Group X] (φ : X ≃* projSL 3 (GaloisField 2 2))
    {p e : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) : ¬ Sec4.IsoLThreePi X p e := by
  have hX : Nat.card X = 20160 := by
    rw [Nat.card_congr φ.toEquiv, card_projSL_three_four]
  have hp : p.Prime := hpf.out
  have hq3 : 3 ≤ p ^ e := by
    have h2 := hp.two_le
    have h3 : p ≠ 2 := hp2
    calc 3 ≤ p := by omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  have hqodd : p ^ e % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have key : ∀ q : ℕ, 3 ≤ q → q % 2 = 1 → q ^ 3 ∣ 20160 → False := by
    intro q hq hqo hd
    have hle : q ^ 3 ≤ 20160 := Nat.le_of_dvd (by norm_num) hd
    have hq28 : q < 28 := by
      by_contra hge
      push Not at hge
      have := Nat.pow_le_pow_left hge 3
      omega
    exact not_odd_cube_dvd_l34 q hq28 hq hqo hd
  rintro (⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩)
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr ψ.toEquiv, hX] at hc
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e - 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      have h1 : Nat.Coprime (p ^ e - 1) (p ^ e - 1 + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      rw [Nat.sub_add_cancel (by omega)] at h1
      exact h1.symm
    exact key _ hq3 hqodd (hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl))
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr ψ.toEquiv, hX] at hc
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e + 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    exact key _ hq3 hqodd (hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl))

theorem theta_eq_pCore_two_of_l34
    (h135 : Item135SimpleReduce)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) :
    aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    ⟨2, 2, inferInstance, by norm_num, Or.inl ⟨by norm_num, ⟨φ⟩⟩⟩
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
    by_contra hq
    obtain ⟨-, -, -, p, e, hpf, hp2, he, hiso⟩ := h135 G A c L hD (Or.inl hL3) hq
    exact not_isoLThreePi_of_l34 φ hp2 he hiso
  exact Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult hq (Or.inl hL3)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

@[expose] noncomputable def barHom (hD : Sec13Data G A c L) :
    ↥(A ⊔ L) →* Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion
    (sup_le hD.A_le_normalizer_zpowers (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt)))

theorem barHom_apply (hD : Sec13Data G A c L) (x : ↥(A ⊔ L)) :
    barHom hD x = QuotientGroup.mk' _ ⟨(x : G), (sup_le hD.A_le_normalizer_zpowers
      (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt)) x.2⟩ :=
  rfl

theorem range_barHom (hD : Sec13Data G A c L) : (barHom hD).range = lBarA c L A := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : G), _⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    show (x : G) ∈ L ⊔ A
    rw [sup_comm]
    exact x.2
  · rintro ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ A ⊔ L := by
      have := Subgroup.mem_subgroupOf.mp hw
      rwa [sup_comm] at this
    exact ⟨⟨(w : G), hw'⟩, rfl⟩

theorem ker_barHom (hD : Sec13Data G A c L)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.Open.pCore 2 ↥L) :
    (barHom hD).ker = kerAO2 A L := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hLH : L ≤ H := le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt
  have hAH : A ≤ H := hD.A_le_normalizer_zpowers
  obtain ⟨η, hη⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
  have hLθ : ∀ l : ↥L, QuotientGroup.mk' (aschbacherSolvableCore 3 H) ⟨(l : G), hLH l.2⟩ = 1 ↔
      l ∈ aschbacherSolvableCore 3 ↥L := by
    intro l
    rw [← hη l, ← QuotientGroup.eq_one_iff (N := aschbacherSolvableCore 3 ↥L)]
    constructor
    · intro h1
      have h2 : η (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 := Subtype.ext h1
      exact (MulEquiv.map_eq_one_iff η).mp h2
    · intro h1
      rw [h1, map_one]
      rfl
  ext x
  rw [MonoidHom.mem_ker, barHom_apply, kerAO2, Subgroup.mem_subgroupOf]
  constructor
  · intro hx1
    have hxAL : (x : G) ∈ ((A ⊔ L : Subgroup G) : Set G) := x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A L hD.le_normalizer] at hxAL
    obtain ⟨a, ha, l, hl, hal⟩ := hxAL
    have ha3 : (⟨a, hAH ha⟩ : H) ^ 3 ^ 1 = 1 :=
      Subtype.ext (by simpa using hD.isElemAbelian.2 a ha)
    have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 H) (⟨a, hAH ha⟩ : H) ∈
        Sec12.lBar c L := by
      have hsplit : (⟨(x : G), (sup_le hAH hLH) x.2⟩ : H) = ⟨a, hAH ha⟩ * ⟨l, hLH hl⟩ :=
        Subtype.ext hal.symm
      rw [hsplit, map_mul] at hx1
      have hai : QuotientGroup.mk' (aschbacherSolvableCore 3 H) (⟨a, hAH ha⟩ : H) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 H) (⟨l, hLH hl⟩ : H)⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_left hx1
      rw [hai]
      exact ⟨(⟨l, hLH hl⟩ : H)⁻¹, Subgroup.mem_subgroupOf.mpr (inv_mem hl), rfl⟩
    have haL : a ∈ L := mem_of_mk_mem_lBar hD.mem_thetaComponentsAt ha3 hmem
    have hxL : (x : G) ∈ L := hal ▸ mul_mem haL hl
    have hθx : (⟨(x : G), hxL⟩ : ↥L) ∈ aschbacherSolvableCore 3 ↥L := (hLθ ⟨(x : G), hxL⟩).mp hx1
    rw [hθ] at hθx
    exact ⟨⟨(x : G), hxL⟩, hθx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [← hθ] at hy
    have h1 := (hLθ y).mpr hy
    have hxy : (⟨(x : G), (sup_le hAH hLH) x.2⟩ : H) = ⟨(y : G), hLH y.2⟩ :=
      Subtype.ext hyx.symm
    rw [hxy]
    exact h1

theorem nonempty_quot_equiv_lBarA (hD : Sec13Data G A c L)
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.Open.pCore 2 ↥L) :
    letI := kerAO2_normal hD.le_normalizer
    Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃* lBarA c L A) := by
  let _ := kerAO2_normal hD.le_normalizer
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (ker_barHom hD hθ).symm).trans
    ((QuotientGroup.quotientKerEquivRange (barHom hD)).trans
      (MulEquiv.subgroupCongr (range_barHom hD)))⟩

end CFSG.RankThree.PartTwo.Sec16.Proof169Theta

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169Theta

theorem step169TwoBridge_of
    (h135 : Item135SimpleReduce) : Step169TwoBridge := by
  intro G _ _ A c L h ⟨φ⟩ ⟨ψ⟩
  have hD := h.toSec13Data
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.Open.pCore 2 ↥L :=
    (theta_eq_pCore_two_of_l34 h135 hD φ).trans (CFSG.pCore_eq_open ↥L 2)
  obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
  let _ := kerAO2_normal hD.le_normalizer
  obtain ⟨e⟩ := nonempty_quot_equiv_lBarA hD hθ
  exact ⟨e.trans (ψ.trans (MulEquiv.prodCongr (MulEquiv.refl _) (η.symm.trans φ)))⟩

theorem step169TwoBridge_of_item135Simple
    (h135 : Item135Simple) :
    Step169TwoBridge :=
  step169TwoBridge_of fun G _ _ A c L hD htype hq => absurd (h135 G A c L hD htype) hq

end CFSG.RankThree.PartTwo.Sec16
