module

import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
import CFSG.GroupTheory.AutomorphismAction.CentralDeviation
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHCentralCommutatorLaws.BCHCentralCommutatorLaws
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Heis

open Subgroup CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {X : Type*} [Group X]

open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BCHCentralCommutatorLaws in
theorem conj_commutator_eq_pow {R : Subgroup X}
    (hcl : ⁅R, R⁆ ≤ Subgroup.centralizer (R : Set X)) {g : X} {μ : ℕ}
    (hg : ∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set X), g * x * g⁻¹ = x ^ μ * z) :
    ∀ c ∈ ⁅R, R⁆, g * c * g⁻¹ = c ^ (μ ^ 2) := by
  intro c hc
  have hcomm_le_R : ⁅R, R⁆ ≤ R := Subgroup.commutator_le.mpr fun u hu v hv => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hu hv) (R.inv_mem hu)) (R.inv_mem hv)
  have hgen : ∀ x ∈ R, ∀ y ∈ R, g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ (μ ^ 2) := by
    intro x hx y hy
    obtain ⟨zx, hzx, hzxeq⟩ := hg x hx
    obtain ⟨zy, hzy, hzyeq⟩ := hg y hy
    have hcommR : CentralComm ↥R := by
      intro a b
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (hcl (Subgroup.commutator_mem_commutator a.2 b.2)) (c : X) c.2)
    let x' : ↥R := ⟨x, hx⟩
    let y' : ↥R := ⟨y, hy⟩
    let zx' : ↥R := ⟨zx, hzx.1⟩
    let zy' : ↥R := ⟨zy, hzy.1⟩
    have hzx' : zx' ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzx.2 (c : X) c.2)
    have hzy' : zy' ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzy.2 (c : X) c.2)
    have hR : ⁅x' ^ μ * zx', y' ^ μ * zy'⁆ = ⁅x', y'⁆ ^ (μ ^ 2) := by
      rw [commutator_mul_central_left
        hcommR (x' ^ μ) (y' ^ μ * zy') (c := zx') hzx']
      rw [commutator_mul_central_right
        hcommR (x' ^ μ) (y' ^ μ) (c := zy') hzy']
      rw [commutator_pow_right
        hcommR (x' ^ μ) y' μ]
      rw [commutator_pow_left
        hcommR x' y' μ]
      rw [← pow_mul, sq]
    have hRval := congrArg Subtype.val hR
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, commutatorElement_def,
      x', y', zx', zy'] at hRval
    calc g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x ^ μ * zx, y ^ μ * zy⁆ := by rw [hzxeq, hzyeq]
      _ = ⁅x, y⁆ ^ (μ ^ 2) := hRval
  rw [Subgroup.commutator_def] at hc
  refine Subgroup.closure_induction (p := fun c _ => g * c * g⁻¹ = c ^ (μ ^ 2)) ?_ ?_ ?_ ?_ hc
  · rintro c ⟨x, hx, y, hy, rfl⟩
    exact hgen x hx y hy
  · simp
  · intro a b ha hb ha' hb'
    have haR : a ∈ ⁅R, R⁆ := by rw [Subgroup.commutator_def]; exact ha
    have hbR' : b ∈ ⁅R, R⁆ := by rw [Subgroup.commutator_def]; exact hb
    have hbR : b ∈ R := hcomm_le_R hbR'
    have hcomm : a * b = b * a :=
      (Subgroup.mem_centralizer_iff.mp (hcl haR) b hbR).symm
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = a ^ (μ ^ 2) * b ^ (μ ^ 2) := by rw [ha', hb']
      _ = (a * b) ^ (μ ^ 2) := (Commute.mul_pow hcomm (μ ^ 2)).symm
  · intro a ha ha'
    calc g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      _ = (a ^ (μ ^ 2))⁻¹ := by rw [ha']
      _ = (a⁻¹) ^ (μ ^ 2) := by rw [inv_pow]

theorem eq_one_of_commute_scalar {p : ℕ} [Fact p.Prime] {R : Subgroup X} [Finite X]
    (hRR : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set X))
    (hexp : ∀ r ∈ R, r ^ p = 1) {g : X} {μ : ℕ} (hμ : (μ : ZMod p) ≠ 1)
    (hμ2 : ((μ : ZMod p)) ^ 2 ≠ 1)
    (hg : ∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set X), g * x * g⁻¹ = x ^ μ * z)
    {x : X} (hx : x ∈ R) (hgx : g * x = x * g) : x = 1 := by
  classical
  haveI : Fact p.Prime := inferInstance
  have hp : p.Prime := Fact.out
  have hcl : ⁅R, R⁆ ≤ Subgroup.centralizer (R : Set X) := by rw [hRR]; exact inf_le_right
  have hfix : g * x * g⁻¹ = x := by
    rw [hgx]; group
  obtain ⟨z, hz, hzx⟩ := hg x hx
  have hx_eq : x = x ^ μ * z := by rw [← hzx, hfix]
  have hxZR : (⟨x, hx⟩ : ↥R) ∈ Subgroup.center ↥R := by
    by_cases hμ0 : μ = 0
    · have hx_eq' : x = z := by simpa [hμ0] using hx_eq
      have hzZR : (⟨z, hz.1⟩ : ↥R) ∈ Subgroup.center ↥R := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (y : X) y.2)
      subst x
      simpa using hzZR
    · have hμ1 : 1 ≤ μ := Nat.one_le_iff_ne_zero.mpr hμ0
      let ZR : Subgroup ↥R := Subgroup.center ↥R
      let W := ↥R ⧸ ZR
      have hzW : (QuotientGroup.mk' ZR ⟨z, hz.1⟩ : W) = 1 := by
        change (QuotientGroup.mk ⟨z, hz.1⟩ : W) = 1
        rw [QuotientGroup.eq_one_iff]
        rw [show ZR = Subgroup.center ↥R from rfl, Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (y : X) y.2)
      have hxW : (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) =
          (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) ^ μ := by
        have hxR_eq : (⟨x, hx⟩ : ↥R) = (⟨x, hx⟩ : ↥R) ^ μ * ⟨z, hz.1⟩ := by
          apply Subtype.ext
          exact hx_eq
        have h := congrArg (fun t : ↥R => (QuotientGroup.mk' ZR t : W)) hxR_eq
        rw [map_mul, map_pow, hzW, mul_one] at h
        exact h
      have hxW_p : (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) ^ p = 1 := by
        rw [← map_pow,
          show (⟨x, hx⟩ : ↥R) ^ p = 1 from Subtype.ext (hexp x hx), map_one]
      have hxW_mu1 : (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) ^ (μ - 1) = 1 := by
        let w : W := QuotientGroup.mk' ZR ⟨x, hx⟩
        have hxWw : w = w ^ μ := by simpa [w] using hxW
        have h1 : w = w ^ (μ - 1) * w := by
          calc w = w ^ μ := hxWw
            _ = w ^ ((μ - 1) + 1) := by rw [Nat.sub_add_cancel hμ1]
            _ = w ^ (μ - 1) * w := by rw [pow_succ]
        have h2 : w * w⁻¹ = (w ^ (μ - 1) * w) * w⁻¹ := congrArg (fun t => t * w⁻¹) h1
        have h3 : w ^ (μ - 1) = 1 := by simpa using h2.symm
        simpa [w] using h3
      have hμnotdvd : ¬ p ∣ μ - 1 := by
        intro hdvd
        apply hμ
        have hcast : ((μ : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [ZMod.natCast_eq_natCast_iff]
          exact ((Nat.modEq_iff_dvd' hμ1).mpr hdvd).symm
        simpa using hcast
      have hcop : Nat.Coprime p (μ - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hμnotdvd
      have hdvd1 : orderOf (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) ∣ p :=
        orderOf_dvd_of_pow_eq_one hxW_p
      have hdvd2 : orderOf (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) ∣ μ - 1 :=
        orderOf_dvd_of_pow_eq_one hxW_mu1
      have hord1 : orderOf (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
      have hw1 : (QuotientGroup.mk' ZR ⟨x, hx⟩ : W) = 1 := orderOf_eq_one_iff.mp hord1
      have hw1' : (⟨x, hx⟩ : ↥R) ∈ ZR := by
        have h : (QuotientGroup.mk ⟨x, hx⟩ : W) = 1 := by simpa using hw1
        exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥R)).mp h
      exact hw1'
  have hxZ : x ∈ R ⊓ Subgroup.centralizer (R : Set X) := by
    rw [← CFSG.center_map_subtype_eq_inf_centralizer R]
    exact ⟨⟨x, hx⟩, hxZR, rfl⟩
  have hxcomm : x ∈ ⁅R, R⁆ := by rw [hRR]; exact hxZ
  have hconj := conj_commutator_eq_pow hcl hg x hxcomm
  have hxpow : x = x ^ (μ ^ 2) := by rw [← hconj, hfix]
  by_cases hμ0 : μ = 0
  · simpa [hμ0] using hxpow
  · have hμ2pos : 1 ≤ μ ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hμ0)
    have hxpow1 : x ^ (μ ^ 2 - 1) = 1 := by
      have h1 : x = x ^ (μ ^ 2 - 1) * x := by
        calc x = x ^ (μ ^ 2) := hxpow
          _ = x ^ ((μ ^ 2 - 1) + 1) := by rw [Nat.sub_add_cancel hμ2pos]
          _ = x ^ (μ ^ 2 - 1) * x := by rw [pow_succ]
      have h2 : x * x⁻¹ = (x ^ (μ ^ 2 - 1) * x) * x⁻¹ := congrArg (fun t => t * x⁻¹) h1
      simpa using h2.symm
    have hμ2notdvd : ¬ p ∣ μ ^ 2 - 1 := by
      intro hdvd
      apply hμ2
      have hcast : ((μ ^ 2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact ((Nat.modEq_iff_dvd' hμ2pos).mpr hdvd).symm
      simpa [Nat.cast_pow] using hcast
    have hcop2 : Nat.Coprime p (μ ^ 2 - 1) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hμ2notdvd
    have hdvd3 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hexp x hx)
    have hdvd4 : orderOf x ∣ μ ^ 2 - 1 := orderOf_dvd_of_pow_eq_one hxpow1
    have hordx : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop2 hdvd3 hdvd4
    exact orderOf_eq_one_iff.mp hordx

private theorem commutator_eq_center_of_inf_centralizer {R : Subgroup X}
    (hRR : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set X)) :
    commutator ↥R = Subgroup.center ↥R := by
  have hZmap : Subgroup.map R.subtype (Subgroup.center ↥R) =
      R ⊓ Subgroup.centralizer (R : Set X) :=
    CFSG.center_map_subtype_eq_inf_centralizer R
  have hcommmap : Subgroup.map R.subtype (commutator ↥R) = ⁅R, R⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      show Subgroup.map R.subtype (⊤ : Subgroup ↥R) = R from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]]
  apply Subgroup.map_injective (Subgroup.subtype_injective R)
  rw [hcommmap, hZmap, hRR]

theorem card_normalizer_dvd {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {R : Subgroup X} (hR : Nat.card R = p ^ 3)
    (hZ : Nat.card (R ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) = p)
    (hRR : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set X)) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hC : Subgroup.centralizer (R : Set X) ≤ R) :
    Nat.card (Subgroup.normalizer (R : Set X)) ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 2 - p)) := by
  classical
  have hp : p.Prime := Fact.out
  let Z : Subgroup X := R ⊓ Subgroup.centralizer (R : Set X)
  have hZcard : Nat.card Z = p := hZ
  have hZle : Z ≤ R := inf_le_left
  let ZR : Subgroup ↥R := Subgroup.center ↥R
  have hZReq : ZR = Z.subgroupOf R := by
    apply Subgroup.map_injective (Subgroup.subtype_injective R)
    rw [show ZR = Subgroup.center ↥R from rfl, CFSG.center_map_subtype_eq_inf_centralizer]
    have hmapZ : Subgroup.map R.subtype (Z.subgroupOf R) = Z := by
      rw [← Subgroup.comap_subtype Z R, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_comm, inf_eq_left.mpr hZle]
    rw [hmapZ]
  have hZRcard : Nat.card ZR = p := by
    rw [hZReq]
    calc Nat.card (Z.subgroupOf R) = Nat.card Z :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
      _ = p := hZcard
  have hcommR : commutator ↥R = Subgroup.center ↥R :=
    commutator_eq_center_of_inf_centralizer hRR
  let W := ↥R ⧸ ZR
  have hWcard : Nat.card W = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥R) ZR
    rw [hR, hZRcard, show p ^ 3 = p ^ 2 * p from by rw [pow_succ]] at h
    exact Nat.mul_right_cancel hp.pos h.symm
  have hWcomm : ∀ a b : W, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        have hmemZR : (⁅y, x⁆ : ↥R) ∈ ZR := by
          rw [hZReq]
          refine Subgroup.mem_subgroupOf.mpr ?_
          change (((⁅y, x⁆ : ↥R) : X)) ∈ Z
          rw [show Z = ⁅R, R⁆ from hRR.symm]
          exact Subgroup.commutator_mem_commutator y.2 x.2
        have hmem1 : (QuotientGroup.mk' ZR ⁅y, x⁆ : W) = 1 := by
          change (QuotientGroup.mk (s := ZR) ⁅y, x⁆ : W) = 1
          rw [QuotientGroup.eq_one_iff]
          exact hmemZR
        calc (QuotientGroup.mk' ZR x) * (QuotientGroup.mk' ZR y)
            = QuotientGroup.mk' ZR (x * y) := (map_mul (QuotientGroup.mk' ZR) x y).symm
          _ = QuotientGroup.mk' ZR (y * x) := by
              rw [show y * x = ⁅y, x⁆ * (x * y) from by
                rw [commutatorElement_def]; group]
              rw [map_mul (QuotientGroup.mk' ZR) ⁅y, x⁆ (x * y), hmem1, one_mul]
          _ = (QuotientGroup.mk' ZR y) * (QuotientGroup.mk' ZR x) :=
              map_mul (QuotientGroup.mk' ZR) y x
  have hWexp : ∀ w : W, w ^ p = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H x =>
      change (QuotientGroup.mk' ZR x : W) ^ p = 1
      rw [← map_pow (QuotientGroup.mk' ZR),
        show x ^ p = 1 from Subtype.ext (hexp x x.2), map_one]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWcomm hWexp hWcard
  have hAutWcard : Nat.card (MulAut W) = (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp [Fin.prod_univ_two]
  have hW1 : 1 < Nat.card W := by
    rw [hWcard]
    nlinarith [hp.one_lt]
  haveI : Nontrivial W := (Finite.one_lt_card_iff_nontrivial).mp hW1
  obtain ⟨w₁, hw₁⟩ := exists_ne (1 : W)
  have hw₁p : w₁ ^ p = 1 := hWexp w₁
  have hw₁ord : orderOf w₁ = p := orderOf_eq_prime hw₁p hw₁
  have hAcard : Nat.card (Subgroup.zpowers w₁) = p := by
    rw [Nat.card_zpowers, hw₁ord]
  let A : Subgroup W := Subgroup.zpowers w₁
  have hAne : A ≠ ⊤ := by
    intro h
    have hcard : Nat.card A = Nat.card W := by rw [h, Subgroup.card_top]
    rw [hAcard, hWcard] at hcard
    have hlt : p < p ^ 2 := by nlinarith [hp.one_lt]
    omega
  obtain ⟨w₂, -, hw₂⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hAne)
  have hw₂p : w₂ ^ p = 1 := hWexp w₂
  have hw₂ne : w₂ ≠ 1 := by
    intro h
    exact hw₂ (h ▸ Subgroup.one_mem A)
  have hw₂ord : orderOf w₂ = p := orderOf_eq_prime hw₂p hw₂ne
  have hBcard : Nat.card (Subgroup.zpowers w₂) = p := by
    rw [Nat.card_zpowers, hw₂ord]
  let B : Subgroup W := Subgroup.zpowers w₂
  let H : Subgroup W := A ⊔ B
  have hAgt : Nat.card A < Nat.card H := by
    have hAle : A ≤ H := le_sup_left
    have hne : A ≠ H := by
      intro h
      apply hw₂
      rw [h]
      exact (le_sup_right : B ≤ A ⊔ B) (Subgroup.mem_zpowers w₂)
    have hle : Nat.card A ≤ Nat.card H := Subgroup.card_le_of_le hAle
    exact lt_of_le_of_ne hle fun hcard =>
      hne (Subgroup.eq_of_le_of_card_ge hAle (le_of_eq hcard.symm))
  have hHdvd : Nat.card H ∣ Nat.card W := by
    simpa using Subgroup.card_dvd_of_le (le_top : H ≤ ⊤)
  have hHcard : Nat.card H = p ^ 2 := by
    have hHdvd' : Nat.card H ∣ p ^ 2 := by rwa [hWcard] at hHdvd
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).1 hHdvd'
    have hkgt : 1 < k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      have hle : Nat.card H ≤ p := by
        calc Nat.card H = p ^ k := hk
          _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
          _ = p := pow_one p
      have hAgt' : p < Nat.card H := by simpa [A, hAcard] using hAgt
      omega
    have hk2 : k = 2 := by omega
    rw [hk, hk2]
  have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [hHcard, hWcard])
  have hclosW : Subgroup.closure ({w₁, w₂} : Set W) = ⊤ := by
    rw [show ({w₁, w₂} : Set W) = {w₁} ∪ {w₂} from by ext x; simp [or_comm],
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
    simpa [A, B, H] using hHtop
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective ZR w₁
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective ZR w₂
  have hmap : Subgroup.map (QuotientGroup.mk' ZR) (Subgroup.closure ({a, b} : Set ↥R)) = ⊤ := by
    rw [MonoidHom.map_closure]
    rw [show (QuotientGroup.mk' ZR) '' ({a, b} : Set ↥R) = ({w₁, w₂} : Set W) from by
      rw [Set.image_pair, ha, hb]]
    exact hclosW
  have hgen : Subgroup.closure ({a, b} : Set ↥R) ⊔ ZR = ⊤ := by
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' ZR) (Subgroup.closure ({a, b} : Set ↥R))
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hclosure : Subgroup.closure (({a, b} : Set ↥R) ∪ (ZR : Set ↥R)) = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, hgen]
  let K : Subgroup (MulAut ↥R) := (quotientAutomorphism ZR).ker
  have hfix_center (α : MulAut ↥R) (hα : α ∈ K) : ∀ z ∈ ZR, α z = z := by
    have hquot : ∀ x : ↥R, α x * x⁻¹ ∈ Subgroup.center ↥R := by
      intro x
      have h := (QuotientGroup.eq_iff_div_mem.mp
        ((mem_quotientAutomorphism_kernel ZR α).mp hα x))
      rwa [div_eq_mul_inv] at h
    exact CFSG.GroupTheory.AutomorphismAction.fixes_center_of_derived_eq α hquot hcommR
  have hKcard : Nat.card K ≤ p ^ 2 := by
    let Φ : K → ZR × ZR := fun α =>
      (⟨α.1 a * a⁻¹, by
          have h := QuotientGroup.eq_iff_div_mem.mp
            ((mem_quotientAutomorphism_kernel ZR α.1).mp α.2 a)
          rwa [div_eq_mul_inv] at h⟩,
       ⟨α.1 b * b⁻¹, by
          have h := QuotientGroup.eq_iff_div_mem.mp
            ((mem_quotientAutomorphism_kernel ZR α.1).mp α.2 b)
          rwa [div_eq_mul_inv] at h⟩)
    have hΦinj : Function.Injective Φ := by
      intro α β hαβ
      have h1 : α.1 a * a⁻¹ = β.1 a * a⁻¹ :=
        congrArg (fun q : ZR × ZR => ((q.1 : ZR) : ↥R)) hαβ
      have h2 : α.1 b * b⁻¹ = β.1 b * b⁻¹ :=
        congrArg (fun q : ZR × ZR => ((q.2 : ZR) : ↥R)) hαβ
      have haeq : α.1 a = β.1 a := by
        have := congrArg (fun t : ↥R => t * a) h1
        simpa using this
      have hbeq : α.1 b = β.1 b := by
        have := congrArg (fun t : ↥R => t * b) h2
        simpa using this
      have hEqOn : Set.EqOn (⇑α.1.toMonoidHom) (⇑β.1.toMonoidHom)
          (({a, b} : Set ↥R) ∪ (ZR : Set ↥R)) := by
        intro x hx
        rcases hx with (hxa | hxb) | hxZ
        · rw [hxa]; exact haeq
        · rw [hxb]; exact hbeq
        · change α.1 x = β.1 x
          rw [hfix_center α.1 α.2 x hxZ, hfix_center β.1 β.2 x hxZ]
      have heq : α.1.toMonoidHom = β.1.toMonoidHom :=
        MonoidHom.eq_of_eqOn_dense hclosure hEqOn
      exact Subtype.ext (MulEquiv.ext fun x => DFunLike.congr_fun heq x)
    calc Nat.card K ≤ Nat.card (ZR × ZR) := Nat.card_le_card_of_injective Φ hΦinj
      _ = Nat.card ZR * Nat.card ZR := Nat.card_prod ZR ZR
      _ = p * p := by rw [hZRcard]
      _ = p ^ 2 := by ring
  let Inn : Subgroup (MulAut ↥R) := (MulAut.conj : ↥R →* MulAut ↥R).range
  have hInncard : Nat.card Inn = p ^ 2 := by
    have h := Subgroup.index_ker (MulAut.conj : ↥R →* MulAut ↥R)
    have hker := CFSG.GroupTheory.ker_conj_eq_center (G := ↥R)
    have hmul := Subgroup.card_mul_index (MulAut.conj : ↥R →* MulAut ↥R).ker
    rw [hker, hZRcard, hR, show p ^ 3 = p * p ^ 2 from by ring] at hmul
    have hidx : (MulAut.conj : ↥R →* MulAut ↥R).ker.index = p ^ 2 := by
      rw [hker]
      exact Nat.mul_left_cancel hp.pos hmul
    calc Nat.card Inn = Nat.card ↥(MulAut.conj : ↥R →* MulAut ↥R).range := rfl
      _ = (MulAut.conj : ↥R →* MulAut ↥R).ker.index := h.symm
      _ = p ^ 2 := hidx
  have hInnleK : Inn ≤ K := by
    rintro α ⟨r, rfl⟩
    refine MonoidHom.mem_ker.mpr ?_
    refine (mem_quotientAutomorphism_kernel ZR (MulAut.conj r)).mpr ?_
    intro x
    change (QuotientGroup.mk ((MulAut.conj r) x) : W) = QuotientGroup.mk x
    rw [QuotientGroup.eq_iff_div_mem]
    have hmemZR : (⁅r, x⁆ : ↥R) ∈ ZR := by
      rw [hZReq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change (((⁅r, x⁆ : ↥R) : X)) ∈ Z
      rw [show Z = ⁅R, R⁆ from hRR.symm]
      exact Subgroup.commutator_mem_commutator r.2 x.2
    rw [div_eq_mul_inv, MulAut.conj_apply]
    simpa [commutatorElement_def] using hmemZR
  have hKeqInn : K = Inn := by
    have hKcardeq : Nat.card K = p ^ 2 := by
      apply le_antisymm hKcard
      rw [← hInncard]
      exact Subgroup.card_le_of_le hInnleK
    exact (Subgroup.eq_of_le_of_card_ge hInnleK (by rw [hInncard, hKcardeq])).symm
  let N : Subgroup X := Subgroup.normalizer (R : Set X)
  let ρ : N →* MulAut W :=
    (quotientAutomorphism ZR).comp (Subgroup.normalizerMonoidHom R)
  have hkerρ : ρ.ker = R.subgroupOf N := by
    apply le_antisymm
    · intro n hn
      have hαK : Subgroup.normalizerMonoidHom R n ∈ K := MonoidHom.mem_ker.mp hn
      have hαInn : Subgroup.normalizerMonoidHom R n ∈ Inn := hKeqInn ▸ hαK
      rw [MonoidHom.mem_range] at hαInn
      obtain ⟨r, hr⟩ := hαInn
      have hcent : ((r : ↥R) : X)⁻¹ * (n : X) ∈ Subgroup.centralizer (R : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h := congrArg (fun φ : MulAut ↥R => ((φ ⟨x, hx⟩ : ↥R) : X)) hr.symm
        simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
          Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at h
        have h' : (((r : ↥R) : X)⁻¹ * (n : X)) * x =
            x * (((r : ↥R) : X)⁻¹ * (n : X)) := by
          calc (((r : ↥R) : X)⁻¹ * (n : X)) * x
              = ((r : ↥R) : X)⁻¹ * ((n : X) * x * (n : X)⁻¹) * (n : X) := by group
            _ = ((r : ↥R) : X)⁻¹ * (((r : ↥R) : X) * x * ((r : ↥R) : X)⁻¹) * (n : X) := by
                rw [h]
            _ = x * (((r : ↥R) : X)⁻¹ * (n : X)) := by group
        exact h'.symm
      have hnR : (n : X) ∈ R := by
        have hrR : ((r : ↥R) : X) ∈ R := r.2
        have hcR : ((r : ↥R) : X)⁻¹ * (n : X) ∈ R := hC hcent
        have hn_eq : (n : X) = ((r : ↥R) : X) * (((r : ↥R) : X)⁻¹ * (n : X)) := by group
        rw [hn_eq]
        exact R.mul_mem hrR hcR
      exact Subgroup.mem_subgroupOf.mpr hnR
    · intro n hn
      rw [MonoidHom.mem_ker]
      have hnR : (n : X) ∈ R := Subgroup.mem_subgroupOf.mp hn
      have hαK : Subgroup.normalizerMonoidHom R n ∈ K := by
        have hαInn : Subgroup.normalizerMonoidHom R n ∈ Inn := by
          refine MonoidHom.mem_range.mpr ⟨⟨(n : X), hnR⟩, ?_⟩
          ext x
          rfl
        rwa [hKeqInn]
      change (quotientAutomorphism ZR) (Subgroup.normalizerMonoidHom R n) = 1
      exact MonoidHom.mem_ker.mp hαK
  have hNcard : Nat.card N = p ^ 3 * ρ.ker.index := by
    have hmul := Subgroup.card_mul_index ρ.ker
    have hkercard : Nat.card ρ.ker = p ^ 3 := by
      rw [hkerρ]
      calc Nat.card (R.subgroupOf N) = Nat.card R :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv
        _ = p ^ 3 := hR
    rw [← hmul, hkercard]
  have hindexdvd : ρ.ker.index ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [Subgroup.index_ker]
    have hdvd : Nat.card ↥ρ.range ∣ Nat.card (MulAut W) := by
      simpa using Subgroup.card_dvd_of_le (le_top : ρ.range ≤ ⊤)
    rw [hAutWcard] at hdvd
    exact hdvd
  rw [hNcard]
  exact mul_dvd_mul_left (p ^ 3) hindexdvd

