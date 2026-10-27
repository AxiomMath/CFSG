module

import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ8
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
public import CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof2125

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_three_eq_one_of_mem_tD {A : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    {φ : MulAut A} (hφ : φ ∈ trivOnQuot A (Subgroup.zpowers d) ⊓ fixOn A (Subgroup.zpowers d)) :
    φ ^ 3 = 1 := by
  obtain ⟨h1, h2⟩ := hφ
  ext x
  set m : A := x⁻¹ * φ x with hm
  have hmd : (m : G) ∈ Subgroup.zpowers d := (mem_trivOnQuot_iff.mp h1) x
  have hφm : φ m = m := (mem_fixOn_iff.mp h2) m hmd
  have e1 : φ x = x * m := by rw [hm]; group
  have e2 : φ (φ x) = x * m * m := by rw [e1, map_mul, e1, hφm]
  have e3 : φ (φ (φ x)) = x * m * m * m := by rw [e2, map_mul, map_mul, e1, hφm]
  have hm3 : m ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmd
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hd3, one_zpow, Subgroup.coe_one]
  rw [MulAut.one_apply, pow_three, MulAut.mul_apply, MulAut.mul_apply, e3,
    show x * m * m * m = x * m ^ 3 by simp only [pow_three, mul_assoc], hm3, mul_one]

theorem card_eq_card_ker_mul_card_range {H M : Type*} [Group H] [Group M] [Finite H]
    (ψ : H →* M) : Nat.card H = Nat.card ψ.ker * Nat.card ψ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]

omit [Finite G] in
theorem conj_eq_of_mem_zpowers_of_pow {d p : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hp : p * d * p⁻¹ ∈ Subgroup.zpowers d) {k : ℕ} (hpk : p ^ 3 ^ k = 1) :
    p * d * p⁻¹ = d := by
  obtain ⟨j, hj, hjd⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 hp
  interval_cases j
  · exfalso
    apply hd1
    rw [pow_zero] at hjd
    have : d = p⁻¹ * (p * d * p⁻¹) * p := by group
    rw [this, hjd]
    group
  · rw [pow_one] at hjd
    exact hjd
  · exfalso
    have hinv : p * d * p⁻¹ = d⁻¹ := by
      rw [hjd]
      exact Item21LateProof.sq_eq_inv_of_pow_three hd3
    have h2 : p ^ 2 * d * (p ^ 2)⁻¹ = d := by
      calc p ^ 2 * d * (p ^ 2)⁻¹ = p * (p * d * p⁻¹) * p⁻¹ := by rw [pow_two]; group
        _ = p * d⁻¹ * p⁻¹ := by rw [hinv]
        _ = (p * d * p⁻¹)⁻¹ := by group
        _ = d := by rw [hinv, inv_inv]
    have hc2 : Commute (p ^ 2) d := by
      have : p ^ 2 * d = d * p ^ 2 := by
        calc p ^ 2 * d = p ^ 2 * d * (p ^ 2)⁻¹ * p ^ 2 := by group
          _ = d * p ^ 2 := by rw [h2]
      exact this
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    have hm : 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 :=
      Nat.two_mul_div_two_of_even (Odd.add_one hodd)
    have hpp : p = (p ^ 2) ^ ((3 ^ k + 1) / 2) := by
      rw [← pow_mul, hm, pow_succ, hpk, one_mul]
    have hcp : Commute p d := by
      rw [hpp]
      exact hc2.pow_left _
    have hpd : p * d * p⁻¹ = d := by rw [hcp.eq, mul_inv_cancel_right]
    apply hd1
    have h3 : d = d⁻¹ := by rw [← hinv, hpd]
    have h4 : d * d = 1 := by
      calc d * d = d * d⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel d
    calc d = d ^ 3 * (d * d)⁻¹ := by group
      _ = 1 := by rw [hd3, h4, inv_one, one_mul]

theorem exists_fixed_of_trivOnQuot {A : Subgroup G} {d u : G} (hAe : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (hdA : d ∈ A) (huA : u ∈ Subgroup.normalizer (A : Set G))
    (hu : ∀ x ∈ A, x⁻¹ * (u * x * u⁻¹) ∈ Subgroup.zpowers d) :
    ∃ e ∈ A, e ∉ Subgroup.zpowers d ∧ u * e * u⁻¹ = e := by
  have hAc : ∀ x y : A, x * y = y * x := fun x y => hAe.1.is_comm.comm x y
  set σ := A.normalizerMonoidHom ⟨u, huA⟩ with hσ
  have hσx : ∀ x : A, ((σ x : A) : G) = u * x * u⁻¹ := fun x => rfl
  let ψ : A →* A :=
    { toFun := fun x => x⁻¹ * σ x
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (σ x * σ y) = x⁻¹ * σ x * (y⁻¹ * σ y) * (y⁻¹ * y) := by
              rw [hAc y⁻¹ x⁻¹]
              have h1 := hAc y⁻¹ (σ x)
              calc x⁻¹ * y⁻¹ * (σ x * σ y) = x⁻¹ * (y⁻¹ * σ x) * σ y := by group
                _ = x⁻¹ * (σ x * y⁻¹) * σ y := by rw [h1]
                _ = x⁻¹ * σ x * (y⁻¹ * σ y) * (y⁻¹ * y) := by group
          _ = x⁻¹ * σ x * (y⁻¹ * σ y) := by group }
  have hrange : ψ.range ≤ (Subgroup.zpowers d).subgroupOf A := by
    rintro _ ⟨x, rfl⟩
    exact hu x x.2
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hD3 : Nat.card ((Subgroup.zpowers d).subgroupOf A) ≤ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hdA)).toEquiv,
      Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
  have hcard := card_eq_card_ker_mul_card_range ψ
  have hker9 : 9 ≤ Nat.card ψ.ker := by
    have h1 : Nat.card ψ.range ≤ 3 := (Subgroup.card_le_of_le hrange).trans hD3
    have h2 : 27 ≤ Nat.card ψ.ker * 3 := by
      rw [← h27, hcard]
      exact Nat.mul_le_mul_left _ h1
    omega
  by_contra hne
  have hle : ψ.ker ≤ (Subgroup.zpowers d).subgroupOf A := by
    intro x hx
    by_contra hxd
    apply hne
    refine ⟨x, x.2, hxd, ?_⟩
    have h1 : x⁻¹ * σ x = 1 := hx
    rw [← hσx, ← (inv_mul_eq_one.mp h1)]
  have := (Subgroup.card_le_of_le hle).trans hD3
  omega

theorem exists_ne_one_fix_of_le_tD {A : Subgroup G} {d : G} (hAe : IsElemAbelian 3 A)
    (hdA : d ∈ A) {T₀ : Subgroup (MulAut A)}
    (hT₀ : T₀ ≤ trivOnQuot A (Subgroup.zpowers d) ⊓ fixOn A (Subgroup.zpowers d))
    [Finite T₀] (hT9 : 9 ≤ Nat.card T₀) (e : A) : ∃ τ ∈ T₀, τ ≠ 1 ∧ τ e = e := by
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  let ψ : T₀ →* A :=
    { toFun := fun τ => e⁻¹ * (τ : MulAut A) e
      map_one' := by simp
      map_mul' := fun σ τ => by
        have hτ := (hT₀ τ.2).1
        have hσ := (hT₀ σ.2).2
        have hm : (σ : MulAut A) (e⁻¹ * (τ : MulAut A) e) = e⁻¹ * (τ : MulAut A) e :=
          (mem_fixOn_iff.mp hσ) _ ((mem_trivOnQuot_iff.mp hτ) e)
        change e⁻¹ * ((σ : MulAut A) * τ) e = e⁻¹ * (σ : MulAut A) e * (e⁻¹ * (τ : MulAut A) e)
        rw [MulAut.mul_apply, show (τ : MulAut A) e = e * (e⁻¹ * (τ : MulAut A) e) by group,
          map_mul, hm]
        group }
  have hrange : ψ.range ≤ (Subgroup.zpowers d).subgroupOf A := by
    rintro _ ⟨τ, rfl⟩
    exact (mem_trivOnQuot_iff.mp (hT₀ τ.2).1) e
  have hD3 : Nat.card ((Subgroup.zpowers d).subgroupOf A) ≤ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hdA)).toEquiv,
      Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
  have hcard := card_eq_card_ker_mul_card_range ψ
  have hker3 : 3 ≤ Nat.card ψ.ker := by
    have h1 : Nat.card ψ.range ≤ 3 := (Subgroup.card_le_of_le hrange).trans hD3
    have h2 : 9 ≤ Nat.card ψ.ker * 3 := by
      calc 9 ≤ Nat.card T₀ := hT9
        _ = Nat.card ψ.ker * Nat.card ψ.range := hcard
        _ ≤ Nat.card ψ.ker * 3 := Nat.mul_le_mul_left _ h1
    omega
  have hne : ψ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hker3
    omega
  obtain ⟨τ, hτ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(τ : T₀), (τ : T₀).2, fun h => hτ1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have h1 : e⁻¹ * ((τ : T₀) : MulAut A) e = 1 := τ.2
  exact (inv_mul_eq_one.mp h1).symm

theorem exists_fixed_coset {A P : Subgroup G} {d : G} (hAe : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (hdA : d ∈ A) (hd1 : d ≠ 1) (hP3 : IsPGroup 3 P)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) (hPd : ∀ p ∈ P, p * d * p⁻¹ = d) :
    ∃ e ∈ A, e ∉ Subgroup.zpowers d ∧ ∀ p ∈ P, e⁻¹ * (p * e * p⁻¹) ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ x y : A, x * y = y * x := fun x y => hAe.1.is_comm.comm x y
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  set D' := (Subgroup.zpowers d).subgroupOf A with hD'
  have hDn : D'.Normal := ⟨fun n hn g => by rw [hAc g n, mul_inv_cancel_right]; exact hn⟩
  have hPδ : ∀ p ∈ P, ∀ δ ∈ Subgroup.zpowers d, p * δ * p⁻¹ = δ := fun p hp δ hδ =>
    Item21LateProof.conj_eq_of_mem_zpowers (hPd p hp) hδ
  let σ : P → A →* A := fun p => (A.normalizerMonoidHom ⟨p, hPA p.2⟩).toMonoidHom
  have hσ : ∀ (p : P) (x : A), ((σ p x : A) : G) = (p : G) * x * (p : G)⁻¹ := fun p x => rfl
  have hσD : ∀ p : P, D' ≤ D'.comap (σ p) := by
    intro p x hx
    rw [Subgroup.mem_comap]
    change ((σ p x : A) : G) ∈ Subgroup.zpowers d
    rw [hσ, hPδ p p.2 x hx]
    exact hx
  let _ : MulAction P (A ⧸ D') :=
    { smul := fun p => QuotientGroup.map D' D' (σ p) (hσD p)
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x =>
          change QuotientGroup.map D' D' (σ 1) (hσD 1) (x : A ⧸ D') = x
          rw [QuotientGroup.map_mk]
          congr 1
          apply Subtype.ext
          rw [hσ]
          simp
      mul_smul := fun p q y => by
        induction y using QuotientGroup.induction_on with
        | H x =>
          change QuotientGroup.map D' D' (σ (p * q)) (hσD _) (x : A ⧸ D') =
            QuotientGroup.map D' D' (σ p) (hσD p)
              (QuotientGroup.map D' D' (σ q) (hσD q) (x : A ⧸ D'))
          rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.map_mk]
          congr 1
          apply Subtype.ext
          rw [hσ, hσ, hσ]
          simp only [Subgroup.coe_mul]
          group }
  have hcardQ : Nat.card (A ⧸ D') = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup D'
    have h2 : Nat.card D' = 3 := by
      rw [hD', Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hdA)).toEquiv,
        Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
    rw [h27, h2] at h1
    omega
  have hfix1 : (1 : A ⧸ D') ∈ MulAction.fixedPoints P (A ⧸ D') := by
    intro p
    change QuotientGroup.map D' D' (σ p) (hσD p) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hP3.exists_fixed_point_of_prime_dvd_card_of_fixed_point (A ⧸ D')
    (by rw [hcardQ]; norm_num) hfix1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, x.2, fun hx => hb1 ?_, fun p hp => ?_⟩
  · exact ((QuotientGroup.eq_one_iff x).mpr hx).symm
  · have h1 := hb ⟨p, hp⟩
    change QuotientGroup.map D' D' (σ ⟨p, hp⟩) (hσD _) (x : A ⧸ D') = x at h1
    rw [QuotientGroup.map_mk, QuotientGroup.eq] at h1
    have h2 := D'.inv_mem h1
    rw [mul_inv_rev, inv_inv] at h2
    exact h2

theorem card_le_three_mul_card_centralizer {A P : Subgroup G} {d e : G}
    (hAe : IsElemAbelian 3 A) (hdA : d ∈ A) (hPd : ∀ p ∈ P, p * d * p⁻¹ = d)
    (he : ∀ p ∈ P, e⁻¹ * (p * e * p⁻¹) ∈ Subgroup.zpowers d) :
    Nat.card P ≤ 3 * Nat.card (P ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hPδ : ∀ p ∈ P, ∀ δ ∈ Subgroup.zpowers d, p * δ * p⁻¹ = δ := fun p hp δ hδ =>
    Item21LateProof.conj_eq_of_mem_zpowers (hPd p hp) hδ
  let ψ : P →* G :=
    { toFun := fun p => e⁻¹ * ((p : G) * e * (p : G)⁻¹)
      map_one' := by simp
      map_mul' := fun p q => by
        set δ := e⁻¹ * ((q : G) * e * (q : G)⁻¹) with hδ
        have hδd : δ ∈ Subgroup.zpowers d := he q q.2
        have h1 : (q : G) * e * (q : G)⁻¹ = e * δ := by rw [hδ]; group
        have h2 : (p : G) * δ * (p : G)⁻¹ = δ := hPδ p p.2 δ hδd
        change e⁻¹ * (((p : G) * q) * e * ((p : G) * q)⁻¹) =
          e⁻¹ * ((p : G) * e * (p : G)⁻¹) * δ
        calc e⁻¹ * (((p : G) * q) * e * ((p : G) * q)⁻¹)
            = e⁻¹ * ((p : G) * ((q : G) * e * (q : G)⁻¹) * (p : G)⁻¹) := by group
          _ = e⁻¹ * ((p : G) * (e * δ) * (p : G)⁻¹) := by rw [h1]
          _ = e⁻¹ * ((p : G) * e * (p : G)⁻¹) * ((p : G) * δ * (p : G)⁻¹) := by group
          _ = e⁻¹ * ((p : G) * e * (p : G)⁻¹) * δ := by rw [h2] }
  have hrange : ψ.range ≤ Subgroup.zpowers d := by
    rintro _ ⟨p, rfl⟩
    exact he p p.2
  have hr3 : Nat.card ψ.range ≤ 3 := (Subgroup.card_le_of_le hrange).trans (by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3))
  have hmap : ψ.ker.map P.subtype = P ⊓ Subgroup.centralizer ({e} : Set G) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 : e⁻¹ * ((p : G) * e * (p : G)⁻¹) = 1 := hp
      refine ⟨p.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 : (p : G) * e * (p : G)⁻¹ = e := (inv_mul_eq_one.mp h1).symm
      calc (p : G) * e = (p : G) * e * (p : G)⁻¹ * p := by group
        _ = e * p := by rw [h2]
    · rintro ⟨hxP, hxC⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      change e⁻¹ * (x * e * x⁻¹) = 1
      rw [Subgroup.mem_centralizer_singleton_iff.mp hxC]
      group
  have hker : Nat.card ψ.ker =
      Nat.card (P ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
    rw [← hmap, Subgroup.card_map_of_injective P.subtype_injective]
  rw [card_eq_card_ker_mul_card_range ψ, mul_comm, hker]
  exact Nat.mul_le_mul_right _ hr3

theorem isFOf2127_of_sylow {A Le R : Subgroup G} {d e : G} (hAe : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (heA : e ∈ A) (hdA : d ∈ A) (hdLe : d ∈ Le) (hd1 : d ≠ 1)
    (hed : e ∉ Subgroup.zpowers d) (eLe : lBar Le ≃* projSL 3 (GaloisField 2 2))
    (hLeC : Le ≤ Subgroup.centralizer ({e} : Set G)) (heLe : e ∉ Le)
    (hALe : A ≤ Subgroup.normalizer (Le : Set G)) (hAR : A ≤ R)
    (hRS : Nat.card (R ⊓ Le : Subgroup G) = 9) :
    IsFOf2127 A Le ((R ⊓ Le) ⊔ Subgroup.zpowers e) ∧
      A ⊔ ((R ⊓ Le) ⊔ Subgroup.zpowers e) ≤ R ∧
      Nat.card (A ⊔ ((R ⊓ Le) ⊔ Subgroup.zpowers e) : Subgroup G) ≤ 81 ∧
      ∀ x ∈ A ⊔ ((R ⊓ Le) ⊔ Subgroup.zpowers e), x ^ 3 = 1 := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have he3 : e ^ 3 = 1 := hAe.2 e heA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  set S := R ⊓ Le with hS
  set F := S ⊔ Subgroup.zpowers e with hF
  have hSe := isElemAbelian_of_le_of_card_eq_nine eLe inf_le_right hRS
  have heS : ∀ b ∈ S, e * b = b * e := fun b hb =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLeC hb.2)).symm
  have heSn : e ∉ S := fun h => heLe h.2
  obtain ⟨hFe, hFcard⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hSe he3 heS
  have hF27 : Nat.card F = 27 := by rw [hFcard heSn, hRS]
  have hFAL : F ≤ A ⊔ Le := sup_le (inf_le_right.trans le_sup_right)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left heA))
  have hAF : A ≤ Subgroup.normalizer (F : Set G) := by
    intro a ha
    refine mem_normalizer_sup ?_ (mem_normalizer_zpowers_of_commute (hAc a ha e heA))
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hAR ha), hALe ha⟩
  have hQ8 := nonempty_autIn_sup_zpowers eLe inf_le_right hRS hLeC heLe he3
  have hAFR : A ⊔ F ≤ R :=
    sup_le hAR (sup_le inf_le_left (Subgroup.zpowers_le.mpr (hAR heA)))
  have hdS : d ∈ S := ⟨hAR hdA, hdLe⟩
  have hde : d ∉ Subgroup.zpowers e := Item2119End4Proof.not_mem_zpowers_symm he3 hd1 hed
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  set M := Subgroup.zpowers e ⊔ Subgroup.zpowers d with hM
  have hM9 : Nat.card M = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers (hAc e heA d hdA) he3 hd3 he1 hde
  have hMF : M ≤ F := sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hdS))
  have hMA : M ≤ A := sup_le (Subgroup.zpowers_le.mpr heA) (Subgroup.zpowers_le.mpr hdA)
  have hcardAF : Nat.card (A ⊔ F : Subgroup G) ≤ 81 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer' hAF
    have h2 : 9 ≤ Nat.card (A ⊓ F : Subgroup G) := hM9 ▸ Subgroup.card_le_of_le (le_inf hMA hMF)
    rw [h27, hF27] at h1
    have h3 : Nat.card (A ⊔ F : Subgroup G) * 9 ≤ 27 * 27 := by
      rw [← h1]
      exact Nat.mul_le_mul_left _ h2
    omega
  have hexp : ∀ x ∈ A ⊔ F, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ ((A ⊔ F : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A F hAF] at hx'
    obtain ⟨a, ha, f, hf, rfl⟩ := hx'
    exact pow_three_mul_eq_one hFe hF27 hMF hM9 (hAe.2 a ha) (hAF ha)
      (fun m hm => by rw [hAc a ha m (hMA hm), mul_inv_cancel_right]) hf
  exact ⟨⟨hFe, hF27, hFAL, hAF, hQ8⟩, hAFR, hcardAF, hexp⟩

end CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof
