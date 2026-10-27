module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootFiveGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.GH74.GLS.SP.GenOrder
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentFusion
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
public import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private theorem c2_conj_v : D.c2 * D.v * D.c2⁻¹ = D.t * D.v := by
  have hcm : cM * hM * cM⁻¹ = -hM := by decide
  have h1 : D.c2 = D.i1 1 * D.i2 cM := by rw [map_one, one_mul]; rfl
  have h2 : D.v = D.i1 hM * D.i2 hM := rfl
  rw [h1, h2, D.conj_prod, hcm, D.i2_neg]
  simp only [one_mul, mul_one, inv_one, map_one]
  rw [← mul_assoc, (D.t_commute_i1 hM).eq.symm, mul_assoc]

private theorem commute_t_v : Commute D.t D.v :=
  (D.t_commute_i1 hM).mul_right (D.t_commute_i2 hM)

private theorem v_conj_q1 (a : ZMod 5) :
    D.v⁻¹ * D.q1 (.ofAdd a) * D.v = D.q1 (.ofAdd (-a)) := by
  have hv : D.v = D.h1 * D.h2 := rfl
  rw [hv, mul_inv_rev]
  calc D.h2⁻¹ * D.h1⁻¹ * D.q1 (.ofAdd a) * (D.h1 * D.h2)
      = D.h2⁻¹ * (D.h1⁻¹ * D.q1 (.ofAdd a) * D.h1) * D.h2 := by group
    _ = D.h2⁻¹ * D.q1 (.ofAdd (4 * a)) * D.h2 := by rw [D.h1_conj_q1 a]
    _ = D.q1 (.ofAdd (4 * a)) := D.h2_conj_q1 (.ofAdd (4 * a))
    _ = D.q1 (.ofAdd (-a)) := by
      have h4 : (4 : ZMod 5) * a = -a := by
        rw [show (4 : ZMod 5) = -1 by decide, neg_one_mul]
      rw [h4]

private theorem v_conj_q3 [Finite G] (a : ZMod 5) :
    D.v⁻¹ * D.q3 (.ofAdd a) * D.v = D.q3 (.ofAdd (-a)) := by
  obtain ⟨-, -, -, -, -, ρ, hρ2, hρact⟩ := D.elementary_abelian_three_space
  have hv : D.v = D.h1 * D.h2 := rfl
  have hsq : ρ * (ρ * a) = -a := by
    have h : ρ * (ρ * a) = ρ ^ 2 * a := by ring
    rw [h, hρ2]; ring
  rw [hv, mul_inv_rev]
  calc D.h2⁻¹ * D.h1⁻¹ * D.q3 (.ofAdd a) * (D.h1 * D.h2)
      = D.h2⁻¹ * (D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1) * D.h2 := by group
    _ = D.h2⁻¹ * D.q3 (.ofAdd (ρ * a)) * D.h2 := by rw [(hρact a).1]
    _ = D.q3 (.ofAdd (ρ * (ρ * a))) := (hρact (ρ * a)).2
    _ = D.q3 (.ofAdd (-a)) := by rw [hsq]

private theorem tv_conj_q3 [Finite G] (a : ZMod 5) :
    (D.t * D.v)⁻¹ * D.q3 (.ofAdd a) * (D.t * D.v) = D.q3 (.ofAdd a) := by
  rw [mul_inv_rev]
  calc D.v⁻¹ * D.t⁻¹ * D.q3 (.ofAdd a) * (D.t * D.v)
      = D.v⁻¹ * (D.t⁻¹ * D.q3 (.ofAdd a) * D.t) * D.v := by group
    _ = D.v⁻¹ * D.q3 (.ofAdd (-a)) * D.v := by rw [D.t_conj_q3 a]
    _ = D.q3 (.ofAdd a) := by rw [v_conj_q3 D (-a), neg_neg]

private theorem v_conj_q4 [Finite G] (a : ZMod 5) :
    D.v⁻¹ * D.q4 (.ofAdd a) * D.v = D.q4 (.ofAdd a) := by
  have hq4 : D.q4 (.ofAdd a) = D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2 := D.q4_ofAdd a
  have h1 : D.c2 * D.v⁻¹ * D.c2⁻¹ = (D.t * D.v)⁻¹ := by
    rw [← c2_conj_v D]
    group
  rw [hq4]
  calc D.v⁻¹ * (D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2) * D.v
      = D.c2⁻¹ * ((D.c2 * D.v⁻¹ * D.c2⁻¹) * D.q3 (.ofAdd a) *
          (D.c2 * D.v * D.c2⁻¹)) * D.c2 := by group
    _ = D.c2⁻¹ * ((D.t * D.v)⁻¹ * D.q3 (.ofAdd a) * (D.t * D.v)) * D.c2 := by
        rw [h1, c2_conj_v D]
    _ = D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2 := by rw [tv_conj_q3 D a]

private theorem c2_mem_centralizer_P1 : D.c2 ∈ centralizer (D.P1 : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  calc D.q1 a * D.c2 = D.c2 * (D.c2⁻¹ * D.q1 a * D.c2) := by group
    _ = D.c2 * D.q1 a := by rw [D.c2_conj_q1 a]

private theorem conj_mem_V [Finite G] {x : G} (hx : x ∈ centralizer (D.P1 : Set G))
    {y : G} (hy : y ∈ D.V) : x * y * x⁻¹ ∈ D.V := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have h := (CFSG.oddCore_normal ↥(centralizer (D.P1 : Set G))).conj_mem z hz ⟨x, hx⟩
  exact Subgroup.mem_map_of_mem (centralizer (D.P1 : Set G)).subtype (by simpa using h)

private theorem P4_le_V [Finite G] : D.P4 ≤ D.V := by
  obtain ⟨-, -, -, -, -, -, hQV⟩ := D.first_root_centralizer_odd_core
  have hsupV : D.P1 ⊔ D.P3 ≤ D.V := by
    rw [← hQV]
    exact inf_le_right
  have hP3V : D.P3 ≤ D.V := (le_sup_right : D.P3 ≤ D.P1 ⊔ D.P3).trans hsupV
  intro y hy
  rw [D.P4_eq_map_P3] at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have h := conj_mem_V D (inv_mem D.c2_mem_centralizer_P1) (hP3V hx)
  simpa [MulAut.conj_apply] using h

private theorem R_le_Q [Finite G] : D.R ≤ D.Q := by
  obtain ⟨-, -, -, hQt, -, -, -⟩ := D.odd_complement_of_diagonal_centralizer
  rw [← hQt]
  exact inf_le_left

private theorem P1_le_Q [Finite G] : D.P1 ≤ D.Q :=
  (le_sup_left : D.P1 ≤ D.R).trans (R_le_Q D)

private theorem P2_le_Q [Finite G] : D.P2 ≤ D.Q :=
  (le_sup_right : D.P2 ≤ D.R).trans (R_le_Q D)

private theorem P3_le_Q [Finite G] : D.P3 ≤ D.Q := by
  obtain ⟨-, -, -, -, -, -, hQV⟩ := D.first_root_centralizer_odd_core
  have hsup : D.P1 ⊔ D.P3 ≤ D.Q := by
    rw [← hQV]
    exact inf_le_left
  exact (le_sup_right : D.P3 ≤ D.P1 ⊔ D.P3).trans hsup

private theorem P1_le_V [Finite G] : D.P1 ≤ D.V := by
  obtain ⟨-, -, -, hP1V, -, -, -⟩ := D.first_root_centralizer_odd_core
  exact hP1V

private theorem P3_le_V [Finite G] : D.P3 ≤ D.V := by
  obtain ⟨-, -, -, -, -, -, hQV⟩ := D.first_root_centralizer_odd_core
  have hsupV : D.P1 ⊔ D.P3 ≤ D.V := by
    rw [← hQV]
    exact inf_le_right
  exact (le_sup_right : D.P3 ≤ D.P1 ⊔ D.P3).trans hsupV

private theorem P1_inf_P3 [Finite G] : D.P1 ⊓ D.P3 = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hx1, hx3⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, hxa⟩ := hx1
  have hx1' : x ∈ D.P1 := ⟨a, hxa⟩
  obtain ⟨b, hxb⟩ := hx3
  have hfix : D.t⁻¹ * x * D.t = x := by
    rw [← hxa]
    exact D.t_conj_q1 (.ofAdd a)
  have hinv : D.t⁻¹ * x * D.t = x⁻¹ := by
    rw [← hxb]
    simpa using D.t_conj_q3 b.toAdd
  have hxx : x = x⁻¹ := hfix.symm.trans hinv
  have hsq : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxx]
    exact mul_inv_cancel x
  obtain ⟨hP1, -, -, -, -, -, -⟩ := D.diagonal_unipotent_local_data
  have h5 : orderOf x ∣ 5 := by
    rw [← hP1]
    exact Subgroup.orderOf_dvd_natCard _ hx1'
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf x ∣ 1 := by simpa using Nat.dvd_gcd h5 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

private theorem P2_inf_V [Finite G] : D.P2 ⊓ D.V = ⊥ := by
  obtain ⟨-, hL2V, -⟩ := D.first_root_centralizer_odd_core
  refine eq_bot_iff.mpr fun x hx => ?_
  have hP2L2 : D.P2 ≤ D.i2.range := by
    rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  have hle : D.P2 ⊓ D.V ≤ D.i2.range ⊓ D.V :=
    inf_le_inf hP2L2 le_rfl
  rw [hL2V] at hle
  exact hle hx

private theorem L2_le_centralizer_P1 : D.i2.range ≤ centralizer (D.P1 : Set G) := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨b, rfl⟩ := hy
  exact (D.commute (thetaHom b) a).eq

private theorem L2_le_centralizer_t : D.i2.range ≤ centralizer {D.t} := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (D.t_commute_i2 a).eq.symm

private theorem L2_le_normalizer_V [Finite G] : D.i2.range ≤ normalizer (D.V : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_V D (L2_le_centralizer_P1 D hx) hy
  · intro hy
    have h := conj_mem_V D (inv_mem (L2_le_centralizer_P1 D hx)) hy
    have h' : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [h'] at h

private theorem card_mul_of_inf_eq_bot [Finite G] {H K : Subgroup G} (hbot : H ⊓ K = ⊥) :
    Nat.card ((H : Set G) * (K : Set G)) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥((H : Set G) * (K : Set G)) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Set.mem_mul.mpr ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ h
      have h' : (a : G) * b = c * d := congrArg Subtype.val h
      have hm : c⁻¹ * a ∈ H ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem hc) ha, ?_⟩
        have : c⁻¹ * a = d * b⁻¹ := by
          calc c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
            _ = c⁻¹ * (c * d) * b⁻¹ := by rw [h']
            _ = d * b⁻¹ := by group
        rw [this]
        exact K.mul_mem hd (K.inv_mem hb)
      rw [hbot, Subgroup.mem_bot] at hm
      have hac : (⟨a, ha⟩ : H) = ⟨c, hc⟩ := by
        apply Subtype.ext
        calc (a : G) = c * (c⁻¹ * a) := by group
          _ = c * 1 := by rw [hm]
          _ = c := mul_one c
      have hac' : (a : G) = c := congrArg Subtype.val hac
      have hbd : (⟨b, hb⟩ : K) = ⟨d, hd⟩ := by
        apply Subtype.ext
        have h'' : a * b = a * d := by rw [← hac'] at h'; exact h'
        exact mul_left_cancel h''
      rw [hac, hbd]
    · intro y
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp y.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

private theorem coe_centralizer_P1 [Finite G] :
    (centralizer (D.P1 : Set G) : Set G) = (D.i2.range : Set G) * (D.V : Set G) := by
  obtain ⟨hCP1, -, -, -, -, -, -⟩ := D.first_root_centralizer_odd_core
  rw [hCP1, Subgroup.coe_mul_of_left_le_normalizer_right D.i2.range D.V
    (L2_le_normalizer_V D)]

private theorem coe_centralizer_P1_inf_t [Finite G] :
    ((centralizer (D.P1 : Set G) ⊓ centralizer {D.t}) : Set G) =
      (D.i2.range : Set G) * ((D.V ⊓ centralizer {D.t}) : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxP' : x ∈ (D.i2.range : Set G) * (D.V : Set G) := by
      rw [← coe_centralizer_P1 D]
      exact hxP
    obtain ⟨l, hl, v, hv, rfl⟩ := Set.mem_mul.mp hxP' 
    have hlt : l ∈ centralizer {D.t} := L2_le_centralizer_t D hl
    have hvt : v ∈ centralizer {D.t} := by
      have hv' : v = l⁻¹ * (l * v) := by group
      rw [hv']
      exact mul_mem (inv_mem hlt) hxt
    exact Set.mem_mul.mpr ⟨l, hl, v, ⟨hv, hvt⟩, rfl⟩
  · rintro ⟨l, hl, w, hw, rfl⟩
    obtain ⟨hwV, hwt⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr
      ⟨mul_mem (L2_le_centralizer_P1 D hl) (D.V_le_centralizer hwV),
        mul_mem (L2_le_centralizer_t D hl) hwt⟩

private theorem card_centralizer_P1_inf_t [Finite G] :
    Nat.card ↥(centralizer (D.P1 : Set G) ⊓ centralizer {D.t}) =
      120 * Nat.card ↥(D.V ⊓ centralizer {D.t}) := by
  have hcardL2 : Nat.card D.i2.range = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective D.inj2).toEquiv]
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h := Matrix.card_SL_field (𝔽 := ZMod 5) 2
    rw [ZMod.card] at h
    refine h.trans ?_
    norm_num [Fin.prod_univ_two]
  have hinf : D.i2.range ⊓ (D.V ⊓ centralizer {D.t}) = ⊥ := by
    obtain ⟨-, hL2V, -⟩ := D.first_root_centralizer_odd_core
    calc D.i2.range ⊓ (D.V ⊓ centralizer {D.t}) =
        (D.i2.range ⊓ D.V) ⊓ centralizer {D.t} := (inf_assoc _ _ _).symm
      _ = ⊥ := by rw [hL2V, bot_inf_eq]
  have h1 : Nat.card ↥(centralizer (D.P1 : Set G) ⊓ centralizer {D.t}) =
      Nat.card ↥(((D.i2.range : Set G) * ((D.V ⊓ centralizer {D.t}) : Set G))) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      change x ∈ ((centralizer (D.P1 : Set G) ⊓ centralizer {D.t}) : Set G) ↔
        x ∈ ((D.i2.range : Set G) * ((D.V ⊓ centralizer {D.t}) : Set G))
      rw [coe_centralizer_P1_inf_t D]))
  rw [h1]
  rw [show ((D.V : Set G) ⊓ (centralizer {D.t} : Set G)) =
    ((D.V ⊓ centralizer {D.t} : Subgroup G) : Set G) from rfl]
  rw [card_mul_of_inf_eq_bot hinf, hcardL2]

private theorem card_inf_centralizer_t_dvd [Finite G] :
    Nat.card ↥(D.V ⊓ centralizer {D.t}) ∣ 120 := by
  have hdvd : Nat.card ↥(centralizer (D.P1 : Set G) ⊓ centralizer {D.t}) ∣
      Nat.card ↥(centralizer {D.t}) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [card_centralizer_P1_inf_t D, D.hyp.card_centralizer] at hdvd
  have : 120 * Nat.card ↥(D.V ⊓ centralizer {D.t}) ∣ 120 * 120 := by
    simpa using hdvd
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this

private theorem eq_of_le_of_card_five_of_dvd [Finite G] {H P : Subgroup G} (hPH : P ≤ H)
    (hP : Nat.card P = 5) {m : ℕ} (hm : ¬ 25 ∣ m) (hdvd : Nat.card H ∣ m)
    (hH5 : ∃ k, Nat.card H = 5 ^ k) : H = P := by
  obtain ⟨k, hk⟩ := hH5
  have h5dvd : 5 ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_le hPH
    rwa [hP] at this
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      rw [hk] at h5dvd
      norm_num at h5dvd
    · exact h
  have hk2 : k ≤ 1 := by
    by_contra h
    have h2 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 (by omega)
    have h25 : 25 ∣ m := by
      have := h2.trans (hk ▸ hdvd)
      simpa using this
    exact hm h25
  have hk1' : k = 1 := by omega
  have hHcard : Nat.card H = 5 := by rw [hk, hk1']; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hPH (by rw [hHcard, hP])).symm

private theorem oddCore_map_mulAut_le {H : Type} [Group H] [Finite H] (φ : MulAut H)
    (hodd : Odd (Nat.card (CFSG.oddCore H))) :
    (CFSG.oddCore H).map φ.toMonoidHom ≤ CFSG.oddCore H :=
  CFSG.ABGLocalTools.le_oddCore_of_normal
    (Subgroup.Normal.map (CFSG.oddCore_normal H) φ.toMonoidHom φ.surjective)
    (by rw [Subgroup.card_map_of_injective φ.injective]; exact hodd)

private theorem conj_mem_V_of_mem_normalizer [Finite G] {x : G}
    (hx : x ∈ normalizer (centralizer (D.P1 : Set G) : Set G))
    {y : G} (hy : y ∈ D.V) : x * y * x⁻¹ ∈ D.V := by
  let H : Subgroup G := centralizer (D.P1 : Set G)
  have hodd : Odd (Nat.card (CFSG.oddCore ↥H)) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact D.odd_card_V
  let φ : MulAut ↥H := H.normalizerMonoidHom ⟨x, hx⟩
  have hle := oddCore_map_mulAut_le φ hodd
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hφ : φ z ∈ CFSG.oddCore ↥H := hle (Subgroup.mem_map_of_mem φ.toMonoidHom hz)
  have hco : ((φ z : ↥H) : G) = x * (z : G) * x⁻¹ := rfl
  change x * (z : G) * x⁻¹ ∈ D.V
  rw [← hco]
  exact Subgroup.mem_map_of_mem H.subtype hφ

private theorem v_mul_v : D.v * D.v = 1 := by
  rw [← pow_two, ← D.orderOf_v, pow_orderOf_eq_one]

private theorem v_inv : D.v⁻¹ = D.v := inv_eq_of_mul_eq_one_right (v_mul_v D)

private theorem v_mem_normalizer_P1 : D.v ∈ normalizer (D.P1 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨a, hxa⟩ := hx
    have h := v_conj_q1 D a.toAdd
    rw [v_inv D] at h
    rw [← hxa, v_inv D]
    change D.v * D.q1 (Multiplicative.ofAdd a.toAdd) * D.v ∈ D.P1
    rw [h]
    exact ⟨_, rfl⟩
  · intro hx
    rw [v_inv D] at hx
    obtain ⟨b, hxb⟩ := hx
    have h := v_conj_q1 D b.toAdd
    rw [v_inv D] at h
    have hx' : x = D.v * D.q1 b * D.v := by
      calc x = D.v * (D.v * x * D.v) * D.v := by
            rw [show D.v * (D.v * x * D.v) * D.v = (D.v * D.v) * x * (D.v * D.v) by group]
            rw [v_mul_v D]; group
        _ = D.v * D.q1 b * D.v := by rw [← hxb]
    rw [hx']
    change D.v * D.q1 (Multiplicative.ofAdd b.toAdd) * D.v ∈ D.P1
    rw [h]
    exact ⟨_, rfl⟩

private theorem mem_normalizer_centralizer_P1_of_mem_normalizer {c : G}
    (hc : c ∈ normalizer (D.P1 : Set G)) :
    c ∈ normalizer (centralizer (D.P1 : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc' := Subgroup.mem_normalizer_iff.mp hc
  have hcinv := Subgroup.mem_normalizer_iff.mp (inv_mem hc)
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have hx' : c⁻¹ * x * c ∈ D.P1 := by
      have := (hcinv x).mp hx
      simpa using this
    have hcomm : (c⁻¹ * x * c) * y = y * (c⁻¹ * x * c) := hy _ hx'
    calc x * (c * y * c⁻¹)
        = c * ((c⁻¹ * x * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * x * c)) * c⁻¹ := by rw [hcomm]
      _ = c * y * c⁻¹ * x := by group
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have hx' : c * x * c⁻¹ ∈ D.P1 := (hc' x).mp hx
    have hcomm : (c * x * c⁻¹) * (c * y * c⁻¹) = (c * y * c⁻¹) * (c * x * c⁻¹) :=
      hy _ hx'
    calc x * y
        = c⁻¹ * ((c * x * c⁻¹) * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * (c * x * c⁻¹)) * c := by rw [hcomm]
      _ = y * x := by group

private theorem P1_le_centralizer_t : D.P1 ≤ centralizer {D.t} := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (D.t_commute_i1 (thetaHom a)).eq.symm

private theorem mem_normalizer_V_of_mem_normalizer [Finite G] {x : G}
    (hx : x ∈ normalizer (centralizer (D.P1 : Set G) : Set G)) :
    x ∈ normalizer (D.V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_V_of_mem_normalizer D hx hy
  · intro hy
    have h := conj_mem_V_of_mem_normalizer D (inv_mem hx) hy
    have h' : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [h'] at h

private theorem closure_t_v_le_normalizer_V [Finite G] :
    closure {D.t, D.v} ≤ normalizer (D.V : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · have ht : D.t ∈ centralizer (D.P1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (P1_le_centralizer_t D hy)
    exact mem_normalizer_V_of_mem_normalizer D (le_normalizer ht)
  · exact mem_normalizer_V_of_mem_normalizer D
      (mem_normalizer_centralizer_P1_of_mem_normalizer D (v_mem_normalizer_P1 D))

private theorem v_ne_t : D.v ≠ D.t := by
  intro h
  have h' : D.i1 hM * D.i2 hM = D.i1 (-1) * D.i2 1 := by
    rw [← D.t_eq_i1, map_one, mul_one, show D.i1 hM * D.i2 hM = D.v from rfl, h]
  rcases D.prod_eq_iff.mp h' with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)

private theorem isKleinFour_closure_t_v [Finite G] :
    IsKleinFour ↥(closure {D.t, D.v}) := by
  have hcard : Nat.card ↥(closure {D.t, D.v}) = 4 :=
    card_closure_pair D.orderOf_t D.orderOf_v (commute_t_v D) (v_ne_t D)
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent ↥(closure {D.t, D.v}) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    have hx : (x : G) ^ 2 = 1 := by
      refine sq_eq_one_of_mem_closure ?_ ?_ x.2
      · intro a ha b hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        exacts [Commute.refl _, commute_t_v D, (commute_t_v D).symm, Commute.refl _]
      · intro a ha
        rcases ha with rfl | rfl
        · rw [← D.orderOf_t, pow_orderOf_eq_one]
        · rw [← D.orderOf_v, pow_orderOf_eq_one]
    apply Subtype.ext
    simpa using hx
  have h2dvd : 2 ∣ Monoid.exponent ↥(closure {D.t, D.v}) := by
    have := Monoid.order_dvd_exponent (⟨D.t, subset_closure (by simp)⟩ :
      ↥(closure {D.t, D.v}))
    rw [← Subgroup.orderOf_coe, D.orderOf_t] at this
    exact this
  exact Nat.dvd_antisymm hdvd h2dvd

private theorem V_inf_centralizer_t [Finite G] : D.V ⊓ centralizer {D.t} = D.P1 := by
  obtain ⟨hP1, -, -, -, -, -, -⟩ := D.diagonal_unipotent_local_data
  obtain ⟨-, -, -, hV5⟩ := D.third_root_centralizer_and_five_group
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hH5 : ∃ k, Nat.card ↥(D.V ⊓ centralizer {D.t}) = 5 ^ k :=
    IsPGroup.iff_card.mp (hV5.to_le inf_le_left)
  have hPH : D.P1 ≤ D.V ⊓ centralizer {D.t} := fun x hx =>
    Subgroup.mem_inf.mpr ⟨P1_le_V D hx, P1_le_centralizer_t D hx⟩
  exact eq_of_le_of_card_five_of_dvd hPH hP1 (by norm_num)
    (card_inf_centralizer_t_dvd D) hH5

private theorem card_centralizer_v [Finite G] :
    Nat.card ↥(centralizer {D.v}) = 480 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp D.isConj_u_v
  rw [show D.v = D.i1 hM * D.i2 hM from rfl, ← hc,
    Subgroup.card_centralizer_of_isConj (g := c * D.u * c⁻¹) (h := D.u)
      (isConj_iff.mpr ⟨c⁻¹, by group⟩)]
  exact D.outer.card_X

private theorem card_centralizer_tv [Finite G] :
    Nat.card ↥(centralizer {D.t * D.v}) = 480 := by
  have hconj : IsConj D.u (D.t * D.v) :=
    D.isConj_u_v.trans (isConj_iff.mpr ⟨D.c2, c2_conj_v D⟩)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc,
    Subgroup.card_centralizer_of_isConj (g := c * D.u * c⁻¹) (h := D.u)
      (isConj_iff.mpr ⟨c⁻¹, by group⟩)]
  exact D.outer.card_X

private theorem P3_le_centralizer_tv [Finite G] : D.P3 ≤ centralizer {D.t * D.v} := by
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := tv_conj_q3 D a.toAdd
  have h' : (D.t * D.v)⁻¹ * D.q3 a * (D.t * D.v) = D.q3 a := by
    rw [show D.q3 a = D.q3 (Multiplicative.ofAdd a.toAdd) from rfl]
    exact h
  calc D.q3 a * (D.t * D.v)
      = (D.t * D.v) * ((D.t * D.v)⁻¹ * D.q3 a * (D.t * D.v)) := by group
    _ = (D.t * D.v) * D.q3 a := by rw [h']

private theorem P4_le_centralizer_v [Finite G] : D.P4 ≤ centralizer {D.v} := by
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := v_conj_q4 D a.toAdd
  have h' : D.v⁻¹ * D.q4 a * D.v = D.q4 a := by
    rw [show D.q4 a = D.q4 (Multiplicative.ofAdd a.toAdd) from rfl]
    exact h
  calc D.q4 a * D.v = D.v * (D.v⁻¹ * D.q4 a * D.v) := by group
    _ = D.v * D.q4 a := by rw [h']

private theorem V_inf_centralizer_tv [Finite G] : D.V ⊓ centralizer {D.t * D.v} = D.P3 := by
  obtain ⟨-, -, -, hV5⟩ := D.third_root_centralizer_and_five_group
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hH5 : ∃ k, Nat.card ↥(D.V ⊓ centralizer {D.t * D.v}) = 5 ^ k :=
    IsPGroup.iff_card.mp (hV5.to_le inf_le_left)
  have hdvd : Nat.card ↥(D.V ⊓ centralizer {D.t * D.v}) ∣ 480 := by
    have h := Subgroup.card_dvd_of_le (inf_le_right :
      D.V ⊓ centralizer {D.t * D.v} ≤ centralizer {D.t * D.v})
    rwa [card_centralizer_tv D] at h
  have hPH : D.P3 ≤ D.V ⊓ centralizer {D.t * D.v} := fun x hx =>
    Subgroup.mem_inf.mpr ⟨P3_le_V D hx, P3_le_centralizer_tv D hx⟩
  exact eq_of_le_of_card_five_of_dvd hPH D.card_P3 (by norm_num) hdvd hH5

private theorem V_inf_centralizer_v [Finite G] : D.V ⊓ centralizer {D.v} = D.P4 := by
  obtain ⟨-, -, -, hV5⟩ := D.third_root_centralizer_and_five_group
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hH5 : ∃ k, Nat.card ↥(D.V ⊓ centralizer {D.v}) = 5 ^ k :=
    IsPGroup.iff_card.mp (hV5.to_le inf_le_left)
  have hdvd : Nat.card ↥(D.V ⊓ centralizer {D.v}) ∣ 480 := by
    have h := Subgroup.card_dvd_of_le (inf_le_right :
      D.V ⊓ centralizer {D.v} ≤ centralizer {D.v})
    rwa [card_centralizer_v D] at h
  have hPH : D.P4 ≤ D.V ⊓ centralizer {D.v} := fun x hx =>
    Subgroup.mem_inf.mpr ⟨P4_le_V D hx, P4_le_centralizer_v D hx⟩
  exact eq_of_le_of_card_five_of_dvd hPH D.card_P4 (by norm_num) hdvd hH5

private theorem P1_inf_P4 [Finite G] : D.P1 ⊓ D.P4 = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hx1, hx4⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, hxa⟩ := hx1
  have hx1' : x ∈ D.P1 := ⟨a, hxa⟩
  obtain ⟨b, hxb⟩ := hx4
  have hv1 : D.v⁻¹ * x * D.v = x⁻¹ := by
    rw [← hxa]
    have h := v_conj_q1 D a.toAdd
    rw [show Multiplicative.ofAdd a.toAdd = a from rfl] at h
    rw [h]
    exact map_inv D.q1 a
  have hv4 : D.v⁻¹ * x * D.v = x := by
    rw [← hxb]
    simpa using v_conj_q4 D b.toAdd
  have hxx : x = x⁻¹ := hv4.symm.trans hv1
  have hsq : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxx]
    exact mul_inv_cancel x
  have h5 : orderOf x ∣ 5 := by
    have h := Subgroup.orderOf_dvd_natCard D.P1 hx1'
    rwa [D.card_P1] at h
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf x ∣ 1 := by simpa using Nat.dvd_gcd h5 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

private theorem V_inf_centralizer_closure_t_v [Finite G] :
    D.V ⊓ centralizer (closure {D.t, D.v} : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hxV, hxT⟩ := Subgroup.mem_inf.mp hx
  have hxt : x ∈ centralizer {D.t} :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hxT) D.t (subset_closure (by simp))).symm
  have hxv : x ∈ centralizer {D.v} :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hxT) D.v (subset_closure (by simp))).symm
  have h1 : x ∈ D.P1 := by
    rw [← V_inf_centralizer_t D]
    exact Subgroup.mem_inf.mpr ⟨hxV, hxt⟩
  have h4 : x ∈ D.P4 := by
    rw [← V_inf_centralizer_v D]
    exact Subgroup.mem_inf.mpr ⟨hxV, hxv⟩
  have hmem : x ∈ D.P1 ⊓ D.P4 := Subgroup.mem_inf.mpr ⟨h1, h4⟩
  rw [P1_inf_P4] at hmem
  exact hmem

private theorem t_ne_one : D.t ≠ 1 := by
  intro h
  have ht := D.orderOf_t
  rw [h, orderOf_one] at ht
  exact absurd ht (by norm_num)

private theorem v_ne_one : D.v ≠ 1 := by
  intro h
  have hv := D.orderOf_v
  rw [h, orderOf_one] at hv
  exact absurd hv (by norm_num)

private theorem card_V [Finite G] : Nat.card D.V = 125 := by
  haveI : IsKleinFour ↥(closure {D.t, D.v}) := isKleinFour_closure_t_v D
  have hBV := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq
    (T := closure {D.t, D.v}) (K := D.V) D.odd_card_V (closure_t_v_le_normalizer_V D)
    (subset_closure (by simp)) (subset_closure (by simp)) (t_ne_one D) (v_ne_one D)
    (fun h => v_ne_t D h.symm)
  rw [V_inf_centralizer_closure_t_v D, V_inf_centralizer_t D, V_inf_centralizer_v D,
    V_inf_centralizer_tv D, D.card_P1, D.card_P4, D.card_P3, Subgroup.card_bot] at hBV
  simpa using hBV

private theorem V_eq_mul [Finite G] :
    (D.V : Set G) = (D.P1 : Set G) * (D.P3 : Set G) * (D.P4 : Set G) := by
  haveI : IsKleinFour ↥(closure {D.t, D.v}) := isKleinFour_closure_t_v D
  have htvT : D.t * D.v ∈ closure {D.t, D.v} :=
    Subgroup.mul_mem _ (subset_closure (by simp)) (subset_closure (by simp))
  have htv_ne_one : D.t * D.v ≠ 1 := by
    intro h
    have h1 : D.v = D.t := by
      calc D.v = D.t * (D.t * D.v) := by rw [← mul_assoc, D.t_mul_t, one_mul]
        _ = D.t * 1 := by rw [h]
        _ = D.t := mul_one _
    exact v_ne_t D h1
  have ht_ne_tv : D.t ≠ D.t * D.v := by
    intro h
    have h1 : D.t * 1 = D.t * D.v := by rw [mul_one, ← h]
    exact v_ne_one D (mul_left_cancel h1).symm
  have htv_ne_v : D.t * D.v ≠ D.v := by
    intro h
    have h1 : D.t * D.v = 1 * D.v := by rw [h, one_mul]
    exact t_ne_one D (mul_right_cancel h1)
  have h := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers
    (T := closure {D.t, D.v}) (K := D.V) D.odd_card_V (closure_t_v_le_normalizer_V D)
    (subset_closure (by simp)) htvT (subset_closure (by simp))
    (t_ne_one D) htv_ne_one (v_ne_one D)
    ht_ne_tv (fun h => v_ne_t D h.symm) htv_ne_v
  rw [V_inf_centralizer_t D, V_inf_centralizer_tv D, V_inf_centralizer_v D] at h
  exact h

private theorem card_U [Finite G] : Nat.card D.U = 625 := by
  have hP2L2 : D.P2 ≤ D.i2.range := by
    rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  have hP2V : D.P2 ≤ normalizer (D.V : Set G) := hP2L2.trans (L2_le_normalizer_V D)
  rw [show D.U = D.P2 ⊔ D.V from rfl, sup_comm,
    CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hP2V (by rw [inf_comm]; exact P2_inf_V D)]
  norm_num [D.card_P2, card_V D]

private theorem set_mul_comm_of_commute {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, Commute x y) :
    (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_mul.mpr ⟨b, hb, a, ha, (h a ha b hb).eq.symm⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact Set.mem_mul.mpr ⟨a, ha, b, hb, (h a ha b hb).eq⟩

private theorem Q_eq_mul [Finite G] :
    (D.Q : Set G) = (D.P1 : Set G) * (D.P2 : Set G) * (D.P3 : Set G) := by
  obtain ⟨-, -, -, -, hQcoords, -⟩ := D.elementary_abelian_three_space
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, -⟩ := hQcoords x hx
    rw [ha]
    exact Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr
      ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨p1, hp1, p2, hp2, rfl⟩ := Set.mem_mul.mp hy
    obtain ⟨a1, rfl⟩ := hp1
    obtain ⟨a2, rfl⟩ := hp2
    obtain ⟨a3, rfl⟩ := hz
    exact D.Q.mul_mem (D.Q.mul_mem (P1_le_Q D ⟨a1, rfl⟩) (P2_le_Q D ⟨a2, rfl⟩))
      (P3_le_Q D ⟨a3, rfl⟩)

private theorem U_eq_mul [Finite G] :
    (D.U : Set G) = (D.Q : Set G) * (D.P4 : Set G) := by
  have hP2L2 : D.P2 ≤ D.i2.range := by
    rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  have hP2V : D.P2 ≤ normalizer (D.V : Set G) := hP2L2.trans (L2_le_normalizer_V D)
  have hU : (D.U : Set G) = (D.P2 : Set G) * (D.V : Set G) := by
    rw [show D.U = D.P2 ⊔ D.V from rfl]
    exact Subgroup.coe_mul_of_left_le_normalizer_right D.P2 D.V hP2V
  rw [hU, V_eq_mul D, Q_eq_mul D]
  calc (D.P2 : Set G) * ((D.P1 : Set G) * (D.P3 : Set G) * (D.P4 : Set G))
      = ((D.P2 : Set G) * (D.P1 : Set G)) * ((D.P3 : Set G) * (D.P4 : Set G)) := by
        rw [mul_assoc, mul_assoc]
    _ = ((D.P1 : Set G) * (D.P2 : Set G)) * ((D.P3 : Set G) * (D.P4 : Set G)) := by
        rw [set_mul_comm_of_commute]
        intro x hx y hy
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact (D.commute (thetaHom b) (thetaHom a)).symm
    _ = ((D.P1 : Set G) * (D.P2 : Set G) * (D.P3 : Set G)) * (D.P4 : Set G) := by
        simp only [mul_assoc]

private theorem map_conj_eq_of_map_conj_le [Finite G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hc : Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge h (by rw [hc])

private theorem mem_normalizer_range_of_conj [Finite G] {M : Type*} [Group M] (f : M →* G) {g : G}
    (h : ∀ a : M, g * f a * g⁻¹ ∈ f.range) : g ∈ normalizer (f.range : Set G) := by
  have hle : f.range.map (MulAut.conj g).toMonoidHom ≤ f.range := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := hy
    simpa [MulAut.conj_apply] using h a
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_conj_eq_of_map_conj_le hle

private theorem h1_mem_normalizer_P1 [Finite G] : D.h1 ∈ normalizer (D.P1 : Set G) := by
  have h : ∀ a : Multiplicative (ZMod 5), D.h1 * D.q1 a * D.h1⁻¹ ∈ D.P1 := by
    intro a
    have h44 : (4 : ZMod 5) * 4 = 1 := by decide
    have h4a : (4 : ZMod 5) * (4 * a.toAdd) = a.toAdd := by
      rw [← mul_assoc, h44, one_mul]
    have h' := D.h1_conj_q1 (4 * a.toAdd)
    rw [h4a] at h'
    have heq : D.h1 * D.q1 a * D.h1⁻¹ = D.q1 (.ofAdd (4 * a.toAdd)) := by
      calc D.h1 * D.q1 a * D.h1⁻¹
          = D.h1 * (D.h1⁻¹ * D.q1 (.ofAdd (4 * a.toAdd)) * D.h1) * D.h1⁻¹ := by
            rw [h']; rfl
        _ = D.q1 (.ofAdd (4 * a.toAdd)) := by group
    rw [heq]
    exact ⟨_, rfl⟩
  exact mem_normalizer_range_of_conj D.q1 h

private theorem h2_mem_normalizer_P1 [Finite G] : D.h2 ∈ normalizer (D.P1 : Set G) := by
  have h : ∀ a : Multiplicative (ZMod 5), D.h2 * D.q1 a * D.h2⁻¹ ∈ D.P1 := by
    intro a
    have h' := D.h2_conj_q1 a
    have heq : D.h2 * D.q1 a * D.h2⁻¹ = D.q1 a := by
      calc D.h2 * D.q1 a * D.h2⁻¹
          = D.h2 * (D.h2⁻¹ * D.q1 a * D.h2) * D.h2⁻¹ := by rw [h']
        _ = D.q1 a := by group
    rw [heq]
    exact ⟨_, rfl⟩
  exact mem_normalizer_range_of_conj D.q1 h

private theorem h1_mem_normalizer_P2 [Finite G] : D.h1 ∈ normalizer (D.P2 : Set G) := by
  have h : ∀ a : Multiplicative (ZMod 5), D.h1 * D.q2 a * D.h1⁻¹ ∈ D.P2 := by
    intro a
    have h' := D.h1_conj_q2 a
    have heq : D.h1 * D.q2 a * D.h1⁻¹ = D.q2 a := by
      calc D.h1 * D.q2 a * D.h1⁻¹
          = D.h1 * (D.h1⁻¹ * D.q2 a * D.h1) * D.h1⁻¹ := by rw [h']
        _ = D.q2 a := by group
    rw [heq]
    exact ⟨_, rfl⟩
  exact mem_normalizer_range_of_conj D.q2 h

private theorem h2_mem_normalizer_P2 [Finite G] : D.h2 ∈ normalizer (D.P2 : Set G) := by
  have h : ∀ a : Multiplicative (ZMod 5), D.h2 * D.q2 a * D.h2⁻¹ ∈ D.P2 := by
    intro a
    have h44 : (4 : ZMod 5) * 4 = 1 := by decide
    have h4a : (4 : ZMod 5) * (4 * a.toAdd) = a.toAdd := by
      rw [← mul_assoc, h44, one_mul]
    have h' := D.h2_conj_q2 (4 * a.toAdd)
    rw [h4a] at h'
    have heq : D.h2 * D.q2 a * D.h2⁻¹ = D.q2 (.ofAdd (4 * a.toAdd)) := by
      calc D.h2 * D.q2 a * D.h2⁻¹
          = D.h2 * (D.h2⁻¹ * D.q2 (.ofAdd (4 * a.toAdd)) * D.h2) * D.h2⁻¹ := by
            rw [h']; rfl
        _ = D.q2 (.ofAdd (4 * a.toAdd)) := by group
    rw [heq]
    exact ⟨_, rfl⟩
  exact mem_normalizer_range_of_conj D.q2 h

private theorem h1_conj_q3_mem [Finite G] (a : Multiplicative (ZMod 5)) :
    D.h1 * D.q3 a * D.h1⁻¹ ∈ D.P3 := by
  obtain ⟨-, -, -, -, -, ρ, hρ2, hρact⟩ := D.elementary_abelian_three_space
  have hsq : ρ * (-ρ * a.toAdd) = a.toAdd := by
    have hm : ρ * (-ρ) = 1 := by
      have h : ρ * ρ = -1 := by simpa [pow_two] using hρ2
      rw [mul_neg, h, neg_neg]
    rw [← mul_assoc, hm, one_mul]
  have hρ := (hρact (-ρ * a.toAdd)).1
  rw [hsq] at hρ
  have heq : D.h1 * D.q3 a * D.h1⁻¹ = D.q3 (.ofAdd (-ρ * a.toAdd)) := by
    calc D.h1 * D.q3 a * D.h1⁻¹
        = D.h1 * (D.h1⁻¹ * D.q3 (.ofAdd (-ρ * a.toAdd)) * D.h1) * D.h1⁻¹ := by
          rw [hρ]; rfl
      _ = D.q3 (.ofAdd (-ρ * a.toAdd)) := by group
  rw [heq]
  exact ⟨_, rfl⟩

private theorem h2_conj_q3_mem [Finite G] (a : Multiplicative (ZMod 5)) :
    D.h2 * D.q3 a * D.h2⁻¹ ∈ D.P3 := by
  obtain ⟨-, -, -, -, -, ρ, hρ2, hρact⟩ := D.elementary_abelian_three_space
  have hsq : ρ * (-ρ * a.toAdd) = a.toAdd := by
    have hm : ρ * (-ρ) = 1 := by
      have h : ρ * ρ = -1 := by simpa [pow_two] using hρ2
      rw [mul_neg, h, neg_neg]
    rw [← mul_assoc, hm, one_mul]
  have hρ := (hρact (-ρ * a.toAdd)).2
  rw [hsq] at hρ
  have heq : D.h2 * D.q3 a * D.h2⁻¹ = D.q3 (.ofAdd (-ρ * a.toAdd)) := by
    calc D.h2 * D.q3 a * D.h2⁻¹
        = D.h2 * (D.h2⁻¹ * D.q3 (.ofAdd (-ρ * a.toAdd)) * D.h2) * D.h2⁻¹ := by
          rw [hρ]; rfl
      _ = D.q3 (.ofAdd (-ρ * a.toAdd)) := by group
  rw [heq]
  exact ⟨_, rfl⟩

private theorem h1_mem_normalizer_P3 [Finite G] : D.h1 ∈ normalizer (D.P3 : Set G) :=
  mem_normalizer_range_of_conj D.q3 (h1_conj_q3_mem D)

private theorem h2_mem_normalizer_P3 [Finite G] : D.h2 ∈ normalizer (D.P3 : Set G) :=
  mem_normalizer_range_of_conj D.q3 (h2_conj_q3_mem D)

private theorem h1_conj_q4_mem [Finite G] (a : Multiplicative (ZMod 5)) :
    D.h1 * D.q4 a * D.h1⁻¹ ∈ D.P4 := by
  have hq4 : D.q4 a = D.c2⁻¹ * D.q3 a * D.c2 := by
    rw [show a = Multiplicative.ofAdd a.toAdd from rfl]
    exact D.q4_ofAdd a.toAdd
  have hc : Commute D.h1 D.c2 := D.commute hM cM
  have heq : D.h1 * (D.c2⁻¹ * D.q3 a * D.c2) * D.h1⁻¹ =
      D.c2⁻¹ * (D.h1 * D.q3 a * D.h1⁻¹) * D.c2 := by
    calc D.h1 * (D.c2⁻¹ * D.q3 a * D.c2) * D.h1⁻¹
        = (D.h1 * D.c2⁻¹) * D.q3 a * (D.c2 * D.h1⁻¹) := by group
      _ = (D.c2⁻¹ * D.h1) * D.q3 a * (D.h1⁻¹ * D.c2) := by
          rw [hc.inv_right.eq, hc.inv_left.eq.symm]
      _ = D.c2⁻¹ * (D.h1 * D.q3 a * D.h1⁻¹) * D.c2 := by group
  rw [hq4, heq]
  obtain ⟨b, hb⟩ := h1_conj_q3_mem D a
  rw [← hb]
  exact ⟨b, by rw [show b = Multiplicative.ofAdd b.toAdd from rfl]; exact D.q4_ofAdd b.toAdd⟩

private theorem h1_mem_normalizer_P4 [Finite G] : D.h1 ∈ normalizer (D.P4 : Set G) :=
  mem_normalizer_range_of_conj D.q4 (h1_conj_q4_mem D)

private theorem c2_conj_h2 : D.c2 * D.h2 * D.c2⁻¹ = D.t * D.h2 := by
  have hcm : cM * hM * cM⁻¹ = -hM := by decide
  have h1 : D.c2 = D.i2 cM := rfl
  have h2 : D.h2 = D.i2 hM := rfl
  rw [h1, h2, ← map_mul, ← map_inv, ← map_mul, hcm, D.i2_neg]

private theorem t_mem_normalizer_P3 [Finite G] : D.t ∈ normalizer (D.P3 : Set G) := by
  have h : ∀ a : Multiplicative (ZMod 5), D.t * D.q3 a * D.t⁻¹ ∈ D.P3 := by
    intro a
    have h' := D.t_conj_q3 a.toAdd
    rw [D.t_inv] at h'
    have heq : D.t * D.q3 a * D.t⁻¹ = D.q3 (.ofAdd (-a.toAdd)) := by
      rw [D.t_inv]
      exact h'
    rw [heq]
    exact ⟨_, rfl⟩
  exact mem_normalizer_range_of_conj D.q3 h

private theorem h2_mem_normalizer_P4 [Finite G] : D.h2 ∈ normalizer (D.P4 : Set G) := by
  have hconj : D.c2 * D.h2 * D.c2⁻¹ ∈ normalizer (D.P3 : Set G) := by
    rw [c2_conj_h2 D]
    exact mul_mem (t_mem_normalizer_P3 D) (h2_mem_normalizer_P3 D)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hconj ⊢
  have hcomp : (MulAut.conj D.h2).toMonoidHom.comp (MulAut.conj D.c2⁻¹).toMonoidHom =
      (MulAut.conj D.c2⁻¹).toMonoidHom.comp
        (MulAut.conj (D.c2 * D.h2 * D.c2⁻¹)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  calc D.P4.map (MulAut.conj D.h2).toMonoidHom
      = (D.P3.map (MulAut.conj D.c2⁻¹).toMonoidHom).map
          (MulAut.conj D.h2).toMonoidHom := by rw [D.P4_eq_map_P3]
    _ = D.P3.map ((MulAut.conj D.h2).toMonoidHom.comp
          (MulAut.conj D.c2⁻¹).toMonoidHom) := Subgroup.map_map ..
    _ = D.P3.map ((MulAut.conj D.c2⁻¹).toMonoidHom.comp
          (MulAut.conj (D.c2 * D.h2 * D.c2⁻¹)).toMonoidHom) := by rw [hcomp]
    _ = (D.P3.map (MulAut.conj (D.c2 * D.h2 * D.c2⁻¹)).toMonoidHom).map
          (MulAut.conj D.c2⁻¹).toMonoidHom := (Subgroup.map_map ..).symm
    _ = D.P3.map (MulAut.conj D.c2⁻¹).toMonoidHom := by
        rw [show D.P3.map (MulEquiv.toMonoidHom (MulAut.conj (D.c2 * D.h2 * D.c2⁻¹))) =
          D.P3 from hconj]
    _ = D.P4 := (D.P4_eq_map_P3).symm

private theorem V_eq_sup [Finite G] : D.V = D.P1 ⊔ D.P3 ⊔ D.P4 := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ (D.V : Set G) := hx
    rw [V_eq_mul D] at hx'
    have hx := hx' 
    obtain ⟨y, hy, p4, hp4, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨p1, hp1, p3, hp3, rfl⟩ := Set.mem_mul.mp hy
    have h1 : p1 ∈ D.P1 ⊔ D.P3 := (le_sup_left : D.P1 ≤ D.P1 ⊔ D.P3) hp1
    have h3 : p3 ∈ D.P1 ⊔ D.P3 := (le_sup_right : D.P3 ≤ D.P1 ⊔ D.P3) hp3
    have h13 : p1 * p3 ∈ D.P1 ⊔ D.P3 := Subgroup.mul_mem _ h1 h3
    exact Subgroup.mul_mem _
      ((le_sup_left : D.P1 ⊔ D.P3 ≤ (D.P1 ⊔ D.P3) ⊔ D.P4) h13)
      ((le_sup_right : D.P4 ≤ (D.P1 ⊔ D.P3) ⊔ D.P4) hp4)
  · exact sup_le (sup_le (P1_le_V D) (P3_le_V D)) (P4_le_V D)

private theorem h1_mem_normalizer_U [Finite G] : D.h1 ∈ normalizer (D.U : Set G) := by
  have h := Subgroup.inf_normalizer_le_normalizer_sup (D.P1 ⊔ D.P3) D.P4
    (Subgroup.mem_inf.mpr ⟨Subgroup.inf_normalizer_le_normalizer_sup D.P1 D.P3
      (Subgroup.mem_inf.mpr ⟨h1_mem_normalizer_P1 D, h1_mem_normalizer_P3 D⟩),
      h1_mem_normalizer_P4 D⟩)
  have h' := Subgroup.inf_normalizer_le_normalizer_sup D.P2 (D.P1 ⊔ D.P3 ⊔ D.P4)
    (Subgroup.mem_inf.mpr ⟨h1_mem_normalizer_P2 D, h⟩)
  rwa [show D.P2 ⊔ (D.P1 ⊔ D.P3 ⊔ D.P4) = D.U from by rw [← V_eq_sup]; rfl] at h'

private theorem h2_mem_normalizer_U [Finite G] : D.h2 ∈ normalizer (D.U : Set G) := by
  have h := Subgroup.inf_normalizer_le_normalizer_sup (D.P1 ⊔ D.P3) D.P4
    (Subgroup.mem_inf.mpr ⟨Subgroup.inf_normalizer_le_normalizer_sup D.P1 D.P3
      (Subgroup.mem_inf.mpr ⟨h2_mem_normalizer_P1 D, h2_mem_normalizer_P3 D⟩),
      h2_mem_normalizer_P4 D⟩)
  have h' := Subgroup.inf_normalizer_le_normalizer_sup D.P2 (D.P1 ⊔ D.P3 ⊔ D.P4)
    (Subgroup.mem_inf.mpr ⟨h2_mem_normalizer_P2 D, h⟩)
  rwa [show D.P2 ⊔ (D.P1 ⊔ D.P3 ⊔ D.P4) = D.U from by rw [← V_eq_sup]; rfl] at h'

private theorem H_le_normalizer_U [Finite G] :
    D.H ≤ normalizer (D.U : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact h1_mem_normalizer_U D
  · exact h2_mem_normalizer_U D

private theorem H_le_normalizer_P1 [Finite G] :
    D.H ≤ normalizer (D.P1 : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact h1_mem_normalizer_P1 D
  · exact h2_mem_normalizer_P1 D

private theorem U_le_normalizer_P1 [Finite G] :
    D.U ≤ normalizer (D.P1 : Set G) := by
  rw [show D.U = D.P2 ⊔ D.V from rfl]
  have hP2L2 : D.P2 ≤ D.i2.range := by
    rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  refine sup_le ?_ ?_
  · exact (hP2L2.trans (L2_le_centralizer_P1 D)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact (D.V_le_centralizer).trans (Subgroup.centralizer_le_normalizer _)

private theorem U_inf_L2 [Finite G] : D.U ⊓ D.i2.range = D.P2 := by
  have hP2L2 : D.P2 ≤ D.i2.range := by
    rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  have hP2V : D.P2 ≤ normalizer (D.V : Set G) := hP2L2.trans (L2_le_normalizer_V D)
  have hUset : (D.U : Set G) = (D.P2 : Set G) * (D.V : Set G) := by
    rw [show D.U = D.P2 ⊔ D.V from rfl]
    exact Subgroup.coe_mul_of_left_le_normalizer_right D.P2 D.V hP2V
  refine le_antisymm ?_ (le_inf le_sup_left hP2L2)
  intro x hx
  obtain ⟨hxU, hxL2⟩ := Subgroup.mem_inf.mp hx
  have hxU' : x ∈ (D.P2 : Set G) * (D.V : Set G) := by rwa [← hUset]
  obtain ⟨p, hp, y, hy, rfl⟩ := Set.mem_mul.mp hxU'
  have hyL2 : y ∈ D.i2.range := by
    have hy' : y = p⁻¹ * (p * y) := by group
    rw [hy']
    exact D.i2.range.mul_mem (D.i2.range.inv_mem (hP2L2 hp)) hxL2
  obtain ⟨-, hL2V, -⟩ := D.first_root_centralizer_odd_core
  have hybot : y ∈ D.i2.range ⊓ D.V := Subgroup.mem_inf.mpr ⟨hyL2, hy⟩
  rw [hL2V, Subgroup.mem_bot] at hybot
  rw [hybot, mul_one]
  exact hp

private theorem P1P3_le_V [Finite G] : D.P1 ⊔ D.P3 ≤ D.V :=
  sup_le (P1_le_V D) (P3_le_V D)

private theorem V_le_normalizer_P1P3 [Finite G] :
    D.V ≤ normalizer ((D.P1 ⊔ D.P3 : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  obtain ⟨-, -, -, -, -, hVV, -⟩ := D.first_root_centralizer_odd_core
  exact (Subgroup.commutator_mono (P1P3_le_V D) le_rfl).trans
    (hVV.trans (le_sup_left : D.P1 ≤ D.P1 ⊔ D.P3))

private theorem P2_le_centralizer_P1P3 [Finite G] :
    D.P2 ≤ centralizer ((D.P1 ⊔ D.P3 : Subgroup G) : Set G) := by
  obtain ⟨-, hQcomm, -, -, -, -⟩ := D.elementary_abelian_three_space
  have hP1C : D.P1 ≤ centralizer (D.P3 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hQcomm x (P1_le_Q D hx) y (P3_le_Q D hy)).symm
  have hset : ((D.P1 ⊔ D.P3 : Subgroup G) : Set G) = (D.P1 : Set G) * (D.P3 : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right D.P1 D.P3
      (hP1C.trans (Subgroup.centralizer_le_normalizer _))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hset] at hy
  obtain ⟨p1, hp1, p3, hp3, rfl⟩ := Set.mem_mul.mp hy
  have h1 : Commute x p1 := hQcomm x (P2_le_Q D hx) p1 (P1_le_Q D hp1)
  have h3 : Commute x p3 := hQcomm x (P2_le_Q D hx) p3 (P3_le_Q D hp3)
  exact (h1.mul_right h3).eq.symm

private theorem P2_le_normalizer_P1P3 [Finite G] :
    D.P2 ≤ normalizer ((D.P1 ⊔ D.P3 : Subgroup G) : Set G) :=
  (P2_le_centralizer_P1P3 D).trans (Subgroup.centralizer_le_normalizer _)

private theorem U_le_normalizer_P1P3 [Finite G] :
    D.U ≤ normalizer ((D.P1 ⊔ D.P3 : Subgroup G) : Set G) := by
  rw [show D.U = D.P2 ⊔ D.V from rfl]
  exact sup_le (P2_le_normalizer_P1P3 D) (V_le_normalizer_P1P3 D)

private theorem P1P3_normal_in_U [Finite G] :
    ((D.P1 ⊔ D.P3).subgroupOf D.U).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (show D.P1 ⊔ D.P3 ≤ D.U from
    (P1P3_le_V D).trans (le_sup_right : D.V ≤ D.P2 ⊔ D.V))).mpr (U_le_normalizer_P1P3 D)

private theorem card_P1P3 [Finite G] : Nat.card ↥(D.P1 ⊔ D.P3) = 25 := by
  obtain ⟨-, hQcomm, -, -, -, -⟩ := D.elementary_abelian_three_space
  have hP1C : D.P1 ≤ centralizer (D.P3 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hQcomm x (P1_le_Q D hx) y (P3_le_Q D hy)).symm
  rw [sup_comm, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot
    (hP1C.trans (Subgroup.centralizer_le_normalizer _)) (by rw [inf_comm]; exact P1_inf_P3 D)]
  norm_num [D.card_P3, D.card_P1]

private theorem index_P1P3_U [Finite G] :
    Nat.card (D.U ⧸ (D.P1 ⊔ D.P3).subgroupOf D.U) = 25 := by
  have hHU : D.P1 ⊔ D.P3 ≤ D.U :=
    (P1P3_le_V D).trans (le_sup_right : D.V ≤ D.P2 ⊔ D.V)
  have hcardH : Nat.card ↥((D.P1 ⊔ D.P3).subgroupOf D.U) = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHU).toEquiv]
    exact card_P1P3 D
  have h := Subgroup.card_mul_index ((D.P1 ⊔ D.P3).subgroupOf D.U)
  rw [hcardH, card_U D] at h
  rw [← Subgroup.index_eq_card]
  omega

private theorem commutator_U_le [Finite G] : ⁅D.U, D.U⁆ ≤ D.P1 ⊔ D.P3 := by
  haveI hN : ((D.P1 ⊔ D.P3).subgroupOf D.U).Normal := P1P3_normal_in_U D
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hHU : D.P1 ⊔ D.P3 ≤ D.U :=
    (P1P3_le_V D).trans (le_sup_right : D.V ≤ D.P2 ⊔ D.V)
  have hq : IsMulCommutative (D.U ⧸ (D.P1 ⊔ D.P3).subgroupOf D.U) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by rw [index_P1P3_U D]; norm_num)
  have hcomm : _root_.commutator D.U ≤ (D.P1 ⊔ D.P3).subgroupOf D.U :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hq
  rw [← Subgroup.map_subgroupOf_eq_of_le hHU, ← Subgroup.map_subtype_commutator D.U]
  exact Subgroup.map_mono hcomm

private theorem Q_le_U [Finite G] : D.Q ≤ D.U := by
  intro x hx
  have hx' : x ∈ (D.Q : Set G) * (D.P4 : Set G) :=
    Set.mem_mul.mpr ⟨x, hx, 1, Subgroup.one_mem _, mul_one x⟩
  rwa [← U_eq_mul D] at hx'

private theorem Q_normal_in_U [Finite G] : (D.Q.subgroupOf D.U).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Q_le_U D)).mpr ?_
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  exact ((Subgroup.commutator_mono (Q_le_U D) le_rfl).trans (commutator_U_le D)).trans
    (sup_le (P1_le_Q D) (P3_le_Q D))

private theorem H_eq_sup : D.H = zpowers D.h1 ⊔ zpowers D.h2 := by
  rw [show D.H = closure {D.h1, D.h2} from rfl, Set.insert_eq, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]

private theorem R_sup_H_eq : D.R ⊔ D.H =
    (D.P1 ⊔ zpowers D.h1) ⊔ (D.P2 ⊔ zpowers D.h2) := by
  rw [show D.R = D.P1 ⊔ D.P2 from rfl, H_eq_sup]
  ac_rfl

private theorem u_conj_q1_inv (a : Multiplicative (ZMod 5)) :
    D.u * D.q1 a * D.u⁻¹ = D.q2 a := by
  calc D.u * D.q1 a * D.u⁻¹ = D.u⁻¹ * D.q1 a * D.u := by rw [D.u_inv]
    _ = D.q2 a := D.u_conj_q1 a

private theorem u_conj_q2_inv (a : Multiplicative (ZMod 5)) :
    D.u * D.q2 a * D.u⁻¹ = D.q1 a := by
  calc D.u * D.q2 a * D.u⁻¹ = D.u⁻¹ * D.q2 a * D.u := by rw [D.u_inv]
    _ = D.q1 a := D.u_conj_q2 a

private theorem u_conj_mem_R [Finite G] {x : G} (hx : x ∈ D.R) :
    D.u * x * D.u⁻¹ ∈ D.R := by
  obtain ⟨-, hQcomm, -⟩ := D.elementary_abelian_three_space
  have hR : (D.R : Set G) = (D.P1 : Set G) * (D.P2 : Set G) := by
    rw [show D.R = D.P1 ⊔ D.P2 from rfl]
    refine Subgroup.coe_mul_of_left_le_normalizer_right _ _ ?_
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h : a * b * a⁻¹ = b := by
        rw [(hQcomm a (P1_le_Q D ha) b (P2_le_Q D hb)).eq, mul_assoc, mul_inv_cancel,
          mul_one]
      rw [h]; exact hb
    · intro hb
      have hcomm : Commute a (a * b * a⁻¹) :=
        hQcomm a (P1_le_Q D ha) _ (P2_le_Q D hb)
      have hb' : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [hb', hcomm.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
      exact hb
  have hx0 : x ∈ (D.R : Set G) := hx
  rw [hR] at hx0
  obtain ⟨p1, hp1, p2, hp2, rfl⟩ := Set.mem_mul.mp hx0
  obtain ⟨a, rfl⟩ := hp1
  obtain ⟨b, rfl⟩ := hp2
  rw [show D.u * (D.q1 a * D.q2 b) * D.u⁻¹ =
    (D.u * D.q1 a * D.u⁻¹) * (D.u * D.q2 b * D.u⁻¹) by group,
    u_conj_q1_inv D a, u_conj_q2_inv D b]
  exact Subgroup.mul_mem _ ((le_sup_right : D.P2 ≤ D.R) ⟨a, rfl⟩)
    ((le_sup_left : D.P1 ≤ D.R) ⟨b, rfl⟩)

private theorem u_mem_normalizer_R [Finite G] : D.u ∈ normalizer (D.R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact u_conj_mem_R D
  · intro hx
    have h := u_conj_mem_R D hx
    have hux : D.u * (D.u * x * D.u⁻¹) * D.u⁻¹ = x := by
      rw [show D.u * (D.u * x * D.u⁻¹) * D.u⁻¹ =
        (D.u * D.u) * x * (D.u⁻¹ * D.u⁻¹) by group, D.u_mul_u,
        show D.u⁻¹ * D.u⁻¹ = 1 by rw [D.u_inv, D.u_mul_u]]
      group
    rwa [hux] at h

private theorem u_conj_h1 : D.u * D.h1 * D.u⁻¹ = D.h2 := by
  rw [D.u_inv, show D.h1 = D.i1 hM from rfl, show D.h2 = D.i2 hM from rfl]
  calc D.u * D.i1 hM * D.u = D.i2 hM * D.u * D.u := by rw [D.u_mul_i1]
    _ = D.i2 hM := by rw [mul_assoc, D.u_mul_u, mul_one]

private theorem u_conj_h2 : D.u * D.h2 * D.u⁻¹ = D.h1 := by
  rw [D.u_inv, show D.h1 = D.i1 hM from rfl, show D.h2 = D.i2 hM from rfl]
  calc D.u * D.i2 hM * D.u = D.i1 hM * D.u * D.u := by rw [D.u_mul_i2]
    _ = D.i1 hM := by rw [mul_assoc, D.u_mul_u, mul_one]

private theorem u_conj_zpow_h1 (n : ℤ) : D.u * D.h1 ^ n * D.u⁻¹ = D.h2 ^ n := by
  change (MulAut.conj D.u) (D.h1 ^ n) = D.h2 ^ n
  rw [map_zpow, show (MulAut.conj D.u) D.h1 = D.h2 from u_conj_h1 D]

private theorem u_conj_zpow_h2 (n : ℤ) : D.u * D.h2 ^ n * D.u⁻¹ = D.h1 ^ n := by
  change (MulAut.conj D.u) (D.h2 ^ n) = D.h1 ^ n
  rw [map_zpow, show (MulAut.conj D.u) D.h2 = D.h1 from u_conj_h2 D]

private theorem u_conj_mem_H {x : G} (hx : x ∈ D.H) : D.u * x * D.u⁻¹ ∈ D.H := by
  have hAB : zpowers D.h1 ≤ normalizer ((zpowers D.h2 : Subgroup G) : Set G) := by
    refine zpowers_le.mpr ?_
    exact (Subgroup.centralizer_le_normalizer (Subgroup.zpowers D.h2 : Set G)) (by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ((D.commute hM hM).symm.zpow_left n).eq)
  have hx1 : x ∈ D.H := hx
  rw [H_eq_sup] at hx1
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.GH74.GLS.Th2.HY.mem_sup_iff_mul_of_le_normalizer hAB).mp hx1
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [show D.u * (D.h1 ^ m * D.h2 ^ n) * D.u⁻¹ =
    (D.u * D.h1 ^ m * D.u⁻¹) * (D.u * D.h2 ^ n * D.u⁻¹) by group,
    u_conj_zpow_h1 D, u_conj_zpow_h2 D]
  rw [H_eq_sup]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩))

private theorem u_mem_normalizer_H : D.u ∈ normalizer (D.H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact u_conj_mem_H D
  · intro hx
    have h := u_conj_mem_H D hx
    have hux : D.u * (D.u * x * D.u⁻¹) * D.u⁻¹ = x := by
      rw [show D.u * (D.u * x * D.u⁻¹) * D.u⁻¹ =
        (D.u * D.u) * x * (D.u⁻¹ * D.u⁻¹) by group, D.u_mul_u,
        show D.u⁻¹ * D.u⁻¹ = 1 by rw [D.u_inv, D.u_mul_u]]
      group
    rwa [hux] at h

private theorem mem_RH_of_mem_RHu [Finite G] {x : G} (hx : x ∈ D.R ⊔ D.H ⊔ zpowers D.u)
    (hxK : x ∈ D.K) : x ∈ D.R ⊔ D.H := by
  have huN : zpowers D.u ≤ normalizer ((D.R ⊔ D.H : Subgroup G) : Set G) :=
    zpowers_le.mpr (Subgroup.inf_normalizer_le_normalizer_sup D.R D.H
      (Subgroup.mem_inf.mpr ⟨u_mem_normalizer_R D, u_mem_normalizer_H D⟩))
  have hx1 : x ∈ (zpowers D.u ⊔ (D.R ⊔ D.H) : Subgroup G) := by
    rwa [sup_comm] at hx
  obtain ⟨z, hz, y, hy, rfl⟩ :=
    (CFSG.GH74.GLS.Th2.HY.mem_sup_iff_mul_of_le_normalizer huN).mp hx1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hP1K : D.P1 ≤ D.K := by
    rintro a ha
    obtain ⟨b, hb⟩ := ha
    rw [← hb]
    exact (le_sup_left : D.i1.range ≤ D.K) ⟨thetaHom b, rfl⟩
  have hP2K : D.P2 ≤ D.K := by
    rintro a ha
    obtain ⟨b, hb⟩ := ha
    rw [← hb]
    exact (le_sup_right : D.i2.range ≤ D.K) ⟨thetaHom b, rfl⟩
  have hHK : D.H ≤ D.K := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (rfl | rfl)
    · exact (le_sup_left : D.i1.range ≤ D.K) ⟨hM, rfl⟩
    · exact (le_sup_right : D.i2.range ≤ D.K) ⟨hM, rfl⟩
  have hyK : y ∈ D.K := (sup_le (sup_le hP1K hP2K) hHK) hy
  have huk : D.u ^ k ∈ D.K := by
    have huk' : D.u ^ k = (D.u ^ k * y) * y⁻¹ := by group
    rw [huk']
    exact D.K.mul_mem hxK (D.K.inv_mem hyK)
  have huz : D.u ^ k ∈ zpowers D.u := Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_u).mp huz with h | h
  · rw [h, one_mul]; exact hy
  · rw [h] at huk
    exact absurd huk D.u_not_mem

private theorem P1_sup_zpowers_h1_le_L1 : D.P1 ⊔ zpowers D.h1 ≤ D.i1.range := by
  refine sup_le ?_ ?_
  · rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  · rintro y ⟨n, rfl⟩
    exact ⟨hM ^ n, by rw [map_zpow]; rfl⟩

private theorem P2_sup_zpowers_h2_le_L2 : D.P2 ⊔ zpowers D.h2 ≤ D.i2.range := by
  refine sup_le ?_ ?_
  · rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  · rintro y ⟨n, rfl⟩
    exact ⟨hM ^ n, by rw [map_zpow]; rfl⟩

private theorem commute_P1_sup_h1_P2_sup_h2 :
    ∀ a ∈ D.P1 ⊔ zpowers D.h1, ∀ b ∈ D.P2 ⊔ zpowers D.h2, Commute a b := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := P1_sup_zpowers_h1_le_L1 D ha
  obtain ⟨n, rfl⟩ := P2_sup_zpowers_h2_le_L2 D hb
  exact D.commute m n

private theorem P1_sup_h1_le_centralizer_P2_sup_h2 :
    D.P1 ⊔ zpowers D.h1 ≤ centralizer ((D.P2 ⊔ zpowers D.h2 : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (commute_P1_sup_h1_P2_sup_h2 D a ha b hb).eq.symm

private theorem mem_P2H_of_mem_RH_L2 [Finite G] {x : G} (hx : x ∈ D.R ⊔ D.H)
    (hxL2 : x ∈ D.i2.range) : x ∈ D.P2 ⊔ D.H := by
  have hx1 : x ∈ (D.P1 ⊔ zpowers D.h1 : Subgroup G) ⊔ (D.P2 ⊔ zpowers D.h2) := by
    rw [← R_sup_H_eq]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.GH74.GLS.Th2.HY.mem_sup_iff_mul_of_le_normalizer
      ((P1_sup_h1_le_centralizer_P2_sup_h2 D).trans
        (Subgroup.centralizer_le_normalizer _))).mp hx1
  have haL1 : a ∈ D.i1.range := P1_sup_zpowers_h1_le_L1 D ha
  have hbL2 : b ∈ D.i2.range := P2_sup_zpowers_h2_le_L2 D hb
  have haL2 : a ∈ D.i2.range := by
    have ha' : a = (a * b) * b⁻¹ := by group
    rw [ha']
    exact D.i2.range.mul_mem hxL2 (D.i2.range.inv_mem hbL2)
  have hat : a ∈ zpowers D.t := by
    rw [← D.range_inf]
    exact Subgroup.mem_inf.mpr ⟨haL1, haL2⟩
  have htH : D.t ∈ D.H := by
    have ht : D.t = D.h2 ^ 2 := by
      rw [show D.h2 = D.i2 hM from rfl, ← map_pow, hM_sq, ← D.t_eq_i2]
    rw [ht]
    exact D.H.pow_mem (subset_closure (by simp)) 2
  have haH : a ∈ D.H := (Subgroup.zpowers_le.mpr htH) hat
  have hbPH : b ∈ D.P2 ⊔ D.H := by
    have hle : D.P2 ⊔ zpowers D.h2 ≤ D.P2 ⊔ D.H := by
      refine sup_le le_sup_left ?_
      exact (Subgroup.zpowers_le.mpr (subset_closure (by simp))).trans le_sup_right
    exact hle hb
  exact Subgroup.mul_mem _ ((le_sup_right : D.H ≤ D.P2 ⊔ D.H) haH) hbPH

private theorem exists_decomp_of_mem_normalizer_P1 [Finite G] {g : G}
    (hg : g ∈ normalizer (D.P1 : Set G)) :
    ∃ (k : ℤ) (l x : G), l ∈ D.i2.range ∧ x ∈ D.V ∧ g = D.h1 ^ k * (l * x) := by
  obtain ⟨hCP1, -, hNP1, -, -, -, -⟩ := D.first_root_centralizer_odd_core
  have hzpN : zpowers D.h1 ≤ normalizer (centralizer (D.P1 : Set G) : Set G) :=
    zpowers_le.mpr (mem_normalizer_centralizer_P1_of_mem_normalizer D (h1_mem_normalizer_P1 D))
  have hgK : g ∈ (centralizer (D.P1 : Set G) ⊔ zpowers D.h1 : Subgroup G) := by
    have h1 : g ∈ (D.i2.range ⊔ D.V ⊔ zpowers D.h1 : Subgroup G) := by
      rw [← hNP1]
      exact hg
    rwa [← hCP1] at h1
  have hgK' : g ∈ (zpowers D.h1 ⊔ centralizer (D.P1 : Set G) : Subgroup G) := by
    rwa [sup_comm] at hgK
  obtain ⟨z, hz, m, hm, rfl⟩ :=
    (CFSG.GH74.GLS.Th2.HY.mem_sup_iff_mul_of_le_normalizer hzpN).mp hgK'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hm' : m ∈ (D.i2.range : Set G) * (D.V : Set G) := by
    rw [← coe_centralizer_P1 D]
    exact hm
  obtain ⟨l, hl, x, hxV, rfl⟩ := Set.mem_mul.mp hm'
  exact ⟨k, l, x, hl, hxV, rfl⟩

private theorem mem_normalizer_P2_of_mem_normalizer_U [Finite G] {l : G}
    (hlU : l ∈ normalizer (D.U : Set G)) (hl : l ∈ D.i2.range) :
    l ∈ normalizer (D.P2 : Set G) := by
  have hP2L2 : D.P2 ≤ D.i2.range := by
    rintro y ⟨a, rfl⟩
    exact ⟨thetaHom a, rfl⟩
  have hP2U : D.P2 ≤ D.U := le_sup_left
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    have hU : l * p * l⁻¹ ∈ D.U :=
      ((Subgroup.mem_normalizer_iff.mp hlU) p).mp (hP2U hp)
    have hL2 : l * p * l⁻¹ ∈ D.i2.range :=
      D.i2.range.mul_mem (D.i2.range.mul_mem hl (hP2L2 hp)) (D.i2.range.inv_mem hl)
    have := Subgroup.mem_inf.mpr ⟨hU, hL2⟩
    rwa [U_inf_L2 D] at this
  · intro hp
    have hp' : l * p * l⁻¹ ∈ D.U := hP2U hp
    have hU : p ∈ D.U := by
      have h := ((Subgroup.mem_normalizer_iff.mp (inv_mem hlU)) (l * p * l⁻¹)).mp hp'
      have hp_eq : l⁻¹ * (l * p * l⁻¹) * (l⁻¹)⁻¹ = p := by group
      rwa [hp_eq] at h
    have hL2 : p ∈ D.i2.range := by
      have h := D.i2.range.mul_mem
        (D.i2.range.mul_mem (D.i2.range.inv_mem hl) (hP2L2 hp)) hl
      have hp_eq : l⁻¹ * (l * p * l⁻¹) * l = p := by group
      rwa [hp_eq] at h
    have := Subgroup.mem_inf.mpr ⟨hU, hL2⟩
    rwa [U_inf_L2 D] at this

private theorem mem_P2H_of_mem_normalizer_U [Finite G] {l : G}
    (hlU : l ∈ normalizer (D.U : Set G)) (hl : l ∈ D.i2.range) :
    l ∈ D.P2 ⊔ D.H := by
  have hlNP2 : l ∈ normalizer (D.P2 : Set G) := mem_normalizer_P2_of_mem_normalizer_U D hlU hl
  have hlNP1 : l ∈ normalizer (D.P1 : Set G) :=
    Subgroup.centralizer_le_normalizer _ (L2_le_centralizer_P1 D hl)
  have hlNR : l ∈ normalizer (D.R : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup D.P1 D.P2
      (Subgroup.mem_inf.mpr ⟨hlNP1, hlNP2⟩)
  have hlCt : l ∈ centralizer {D.t} := L2_le_centralizer_t D hl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hNRt⟩ := D.diagonal_unipotent_local_data
  have hlRHu : l ∈ D.R ⊔ D.H ⊔ zpowers D.u := by
    rw [← hNRt]
    exact Subgroup.mem_inf.mpr ⟨hlNR, hlCt⟩
  have hlK : l ∈ D.K := (le_sup_right : D.i2.range ≤ D.i1.range ⊔ D.i2.range) hl
  have hlRH : l ∈ D.R ⊔ D.H := mem_RH_of_mem_RHu D hlRHu hlK
  exact mem_P2H_of_mem_RH_L2 D hlRH hl

private theorem normalizer_U_inf_normalizer_P1_le [Finite G] :
    normalizer (D.U : Set G) ⊓ normalizer (D.P1 : Set G) ≤ D.U ⊔ D.H := by
  intro g hg
  obtain ⟨hgU, hgP1⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨k, l, x, hl, hxV, rfl⟩ := exists_decomp_of_mem_normalizer_P1 D hgP1
  have h1NU : D.h1 ∈ normalizer (D.U : Set G) := h1_mem_normalizer_U D
  have h1zNU : D.h1 ^ k ∈ normalizer (D.U : Set G) := zpow_mem h1NU k
  have hxNU : x ∈ normalizer (D.U : Set G) :=
    le_normalizer ((le_sup_right : D.V ≤ D.P2 ⊔ D.V) hxV)
  have hlNU : l ∈ normalizer (D.U : Set G) := by
    have hl' : l = (D.h1 ^ k)⁻¹ * ((D.h1 ^ k) * (l * x)) * x⁻¹ := by group
    rw [hl']
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1zNU) hgU) (Subgroup.inv_mem _ hxNU)
  have hlP2H : l ∈ D.P2 ⊔ D.H := mem_P2H_of_mem_normalizer_U D hlNU hl
  have hxU : x ∈ D.U := (le_sup_right : D.V ≤ D.P2 ⊔ D.V) hxV
  have hlUH : l ∈ D.U ⊔ D.H :=
    (show D.P2 ⊔ D.H ≤ D.U ⊔ D.H from
      sup_le (le_sup_left.trans le_sup_left) le_sup_right) hlP2H
  have hh1H : D.h1 ^ k ∈ D.H := by
    refine zpow_mem ?_ k
    rw [H_eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hh1UH : D.h1 ^ k ∈ D.U ⊔ D.H :=
    (show D.H ≤ D.U ⊔ D.H from le_sup_right) hh1H
  have hlx : l * x ∈ D.U ⊔ D.H :=
    Subgroup.mul_mem _ hlUH ((le_sup_left : D.U ≤ D.U ⊔ D.H) hxU)
  exact Subgroup.mul_mem _ hh1UH hlx

private theorem normalizer_U_inf_normalizer_P1 [Finite G] :
    normalizer (D.U : Set G) ⊓ normalizer (D.P1 : Set G) = D.U ⊔ D.H := by
  refine le_antisymm (normalizer_U_inf_normalizer_P1_le D) ?_
  refine sup_le ?_ ?_
  · refine fun x hx => Subgroup.mem_inf.mpr
      ⟨(le_normalizer : D.U ≤ normalizer (D.U : Set G)) hx, U_le_normalizer_P1 D hx⟩
  · refine fun x hx => Subgroup.mem_inf.mpr
      ⟨H_le_normalizer_U D hx, H_le_normalizer_P1 D hx⟩

private theorem H_le_normalizer_R [Finite G] : D.H ≤ normalizer (D.R : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact Subgroup.inf_normalizer_le_normalizer_sup D.P1 D.P2
      (Subgroup.mem_inf.mpr ⟨h1_mem_normalizer_P1 D, h1_mem_normalizer_P2 D⟩)
  · exact Subgroup.inf_normalizer_le_normalizer_sup D.P1 D.P2
      (Subgroup.mem_inf.mpr ⟨h2_mem_normalizer_P1 D, h2_mem_normalizer_P2 D⟩)

private theorem H_le_normalizer_Q [Finite G] : D.H ≤ normalizer (D.Q : Set G) := by
  obtain ⟨-, -, -, hNRQ, -, -⟩ := D.elementary_abelian_three_space
  exact (H_le_normalizer_R D).trans hNRQ

private theorem U_le_normalizer_Q [Finite G] : D.U ≤ normalizer (D.Q : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Q_le_U D)).mp (Q_normal_in_U D)

private theorem UH_le_normalizer_Q [Finite G] :
    D.U ⊔ D.H ≤ normalizer (D.Q : Set G) :=
  sup_le (U_le_normalizer_Q D) (H_le_normalizer_Q D)

theorem four_root_order_and_products [Finite G] :
    Nat.card D.V = 125 ∧ Nat.card D.U = 625 ∧
    (D.V : Set G) = (D.P1 : Set G) * (D.P3 : Set G) * (D.P4 : Set G) ∧
    (D.U : Set G) = (D.Q : Set G) * (D.P4 : Set G) ∧
    D.V ⊓ centralizer {D.t} = D.P1 ∧ D.V ⊓ centralizer {D.t * D.v} = D.P3 ∧
    D.V ⊓ centralizer {D.v} = D.P4 ∧
    ((D.P1 ⊔ D.P3).subgroupOf D.U).Normal ∧ ⁅D.U, D.U⁆ ≤ D.P1 ⊔ D.P3 ∧
    normalizer (D.U : Set G) ⊓ normalizer (D.P1 : Set G) = D.U ⊔ D.H ∧
    D.U ⊔ D.H ≤ normalizer (D.Q : Set G) :=
  ⟨card_V D, card_U D, V_eq_mul D, U_eq_mul D, V_inf_centralizer_t D,
    V_inf_centralizer_tv D, V_inf_centralizer_v D, P1P3_normal_in_U D,
    commutator_U_le D, normalizer_U_inf_normalizer_P1 D, UH_le_normalizer_Q D⟩

end CFSG.OddTranspositions.PartThree.Wong.RootData
