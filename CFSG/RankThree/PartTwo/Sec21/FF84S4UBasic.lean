module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4UFacts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8)

theorem isEA2_of {G : Type} [Group G] {H : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hsq : ∀ a ∈ H, a ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 H := by
  have hH : ∀ a : H, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hsq a a.2)
  have hc : IsMulCommutative H := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  exact
    { toIsMulCommutative := hc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hH }

theorem natCard_param {H : Subgroup P8} (p : Fin 2 × Fin 2 × Fin 2 × Fin 2 → Prop)
    [DecidablePred p] (f : Fin 2 × Fin 2 × Fin 2 × Fin 2 → P8) (hf : Function.Injective f)
    (hH : ∀ x, x ∈ H ↔ ∃ t, p t ∧ x = f t) :
    Nat.card H = Fintype.card {t // p t} := by
  let e : {t // p t} → H := fun t => ⟨f t.1, (hH _).2 ⟨t.1, t.2, rfl⟩⟩
  have hbij : Function.Bijective e := by
    refine ⟨fun a b h => ?_, fun y => ?_⟩
    · apply Subtype.ext
      apply hf
      exact congrArg (fun z : H => (z : P8)) h
    · obtain ⟨t, ht, hy⟩ := (hH y.1).1 y.2
      exact ⟨⟨t, ht⟩, Subtype.ext hy.symm⟩
  calc Nat.card H = Nat.card {t // p t} := (Nat.card_congr (Equiv.ofBijective e hbij)).symm
    _ = Fintype.card {t // p t} := Nat.card_eq_fintype_card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tupU_inj : Function.Injective (tup4 pa pb pc pd) := by
  have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 pa pb pc pd t = tup4 pa pb pc pd s → t = s := by decide +kernel
  exact fun t s h => key t s h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tupV_inj : Function.Injective (tup4 qa qb qc qd) := by
  have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 qa qb qc qd t = tup4 qa qb qc qd s → t = s := by decide +kernel
  exact fun t s h => key t s h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_isEA : CFSG.IsElementaryAbelian 2 Ua := by
  refine isEA2_of (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨t, rfl⟩ := (mem_Ua_iff a).1 ha
    obtain ⟨s, rfl⟩ := (mem_Ua_iff b).1 hb
    have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        tup4 pa pb pc pd t * tup4 pa pb pc pd s = tup4 pa pb pc pd s * tup4 pa pb pc pd t := by
      decide +kernel
    exact key t s
  · obtain ⟨t, rfl⟩ := (mem_Ua_iff a).1 ha
    have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 pa pb pc pd t ^ 2 = 1 := by
      decide +kernel
    exact key t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ub_isEA : CFSG.IsElementaryAbelian 2 Ub := by
  refine isEA2_of (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨t, rfl⟩ := (mem_Ub_iff a).1 ha
    obtain ⟨s, rfl⟩ := (mem_Ub_iff b).1 hb
    have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        tup4 qa qb qc qd t * tup4 qa qb qc qd s = tup4 qa qb qc qd s * tup4 qa qb qc qd t := by
      decide +kernel
    exact key t s
  · obtain ⟨t, rfl⟩ := (mem_Ub_iff a).1 ha
    have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 qa qb qc qd t ^ 2 = 1 := by
      decide +kernel
    exact key t

theorem Ua_card : Nat.card Ua = 16 := by
  rw [natCard_param (fun _ => True) (tup4 pa pb pc pd) tupU_inj
    (fun x => by simp only [true_and]; exact mem_Ua_iff x)]
  simp

theorem Ub_card : Nat.card Ub = 16 := by
  rw [natCard_param (fun _ => True) (tup4 qa qb qc qd) tupV_inj
    (fun x => by simp only [true_and]; exact mem_Ub_iff x)]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_ne_Ub : Ua ≠ Ub := by
  intro h
  have hpa : pa ∈ Ua := (mem_Ua_iff pa).2 ⟨(1, 0, 0, 0), by simp [tup4]⟩
  rw [h, mem_Ub_iff] at hpa
  obtain ⟨t, ht⟩ := hpa
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, pa ≠ tup4 qa qb qc qd t := by
    decide +kernel
  exact key t ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_inf_Ub : Ua ⊓ Ub = ⊥ := by
  have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 pa pb pc pd t = tup4 qa qb qc qd s → tup4 pa pb pc pd t = 1 := by
    decide +kernel
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx.1
  obtain ⟨s, hs⟩ := (mem_Ub_iff _).1 hx.2
  rw [Subgroup.mem_bot]
  exact key t s hs

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8)

theorem Ua_comm {a b : P8} (ha : a ∈ Ua) (hb : b ∈ Ua) : a * b = b * a := by
  obtain ⟨t, rfl⟩ := (mem_Ua_iff a).1 ha
  obtain ⟨s, rfl⟩ := (mem_Ua_iff b).1 hb
  have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 pa pb pc pd t * tup4 pa pb pc pd s = tup4 pa pb pc pd s * tup4 pa pb pc pd t := by
    decide +kernel
  exact key t s

theorem Ua_sq {a : P8} (ha : a ∈ Ua) : a ^ 2 = 1 := by
  obtain ⟨t, rfl⟩ := (mem_Ua_iff a).1 ha
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 pa pb pc pd t ^ 2 = 1 := by
    decide +kernel
  exact key t

theorem Ub_comm {a b : P8} (ha : a ∈ Ub) (hb : b ∈ Ub) : a * b = b * a := by
  obtain ⟨t, rfl⟩ := (mem_Ub_iff a).1 ha
  obtain ⟨s, rfl⟩ := (mem_Ub_iff b).1 hb
  have key : ∀ t s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 qa qb qc qd t * tup4 qa qb qc qd s = tup4 qa qb qc qd s * tup4 qa qb qc qd t := by
    decide +kernel
  exact key t s

theorem Ub_sq {a : P8} (ha : a ∈ Ub) : a ^ 2 = 1 := by
  obtain ⟨t, rfl⟩ := (mem_Ub_iff a).1 ha
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 qa qb qc qd t ^ 2 = 1 := by
    decide +kernel
  exact key t

theorem isEA2_of_le_Ua {H : Subgroup P8} (hH : H ≤ Ua) : CFSG.IsElementaryAbelian 2 H :=
  isEA2_of (fun a ha b hb => Ua_comm (hH ha) (hH hb)) (fun a ha => Ua_sq (hH ha))

theorem isEA2_of_le_Ub {H : Subgroup P8} (hH : H ≤ Ub) : CFSG.IsElementaryAbelian 2 H :=
  isEA2_of (fun a ha b hb => Ub_comm (hH ha) (hH hb)) (fun a ha => Ub_sq (hH ha))

theorem mem_Ua_inf_cent (g x : P8) : x ∈ Ua ⊓ Cen g ↔
    ∃ t, tup4 pa pb pc pd t * g = g * tup4 pa pb pc pd t ∧ x = tup4 pa pb pc pd t := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 h1
    exact ⟨t, mem_centralizer_singleton_iff.1 h2, rfl⟩
  · rintro ⟨t, hc, rfl⟩
    exact ⟨(mem_Ua_iff _).2 ⟨t, rfl⟩, mem_centralizer_singleton_iff.2 hc⟩

theorem mem_Ub_inf_cent (g x : P8) : x ∈ Ub ⊓ Cen g ↔
    ∃ t, tup4 qa qb qc qd t * g = g * tup4 qa qb qc qd t ∧ x = tup4 qa qb qc qd t := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 h1
    exact ⟨t, mem_centralizer_singleton_iff.1 h2, rfl⟩
  · rintro ⟨t, hc, rfl⟩
    exact ⟨(mem_Ub_iff _).2 ⟨t, rfl⟩, mem_centralizer_singleton_iff.2 hc⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_cent_cc_card : Nat.card ↥(Ua ⊓ Cen cc) = 4 := by
  rw [natCard_param (fun t => tup4 pa pb pc pd t * cc = cc * tup4 pa pb pc pd t)
    (tup4 pa pb pc pd) tupU_inj (fun x => mem_Ua_inf_cent cc x)]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_cent_dd_card : Nat.card ↥(Ua ⊓ Cen dd) = 4 := by
  rw [natCard_param (fun t => tup4 pa pb pc pd t * dd = dd * tup4 pa pb pc pd t)
    (tup4 pa pb pc pd) tupU_inj (fun x => mem_Ua_inf_cent dd x)]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ub_cent_cc_card : Nat.card ↥(Ub ⊓ Cen cc) = 4 := by
  rw [natCard_param (fun t => tup4 qa qb qc qd t * cc = cc * tup4 qa qb qc qd t)
    (tup4 qa qb qc qd) tupV_inj (fun x => mem_Ub_inf_cent cc x)]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ub_cent_dd_card : Nat.card ↥(Ub ⊓ Cen dd) = 4 := by
  rw [natCard_param (fun t => tup4 qa qb qc qd t * dd = dd * tup4 qa qb qc qd t)
    (tup4 qa qb qc qd) tupV_inj (fun x => mem_Ub_inf_cent dd x)]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_cent_cd : Ua ⊓ Cen (cc * dd) = ⊥ := by
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 pa pb pc pd t * (cc * dd) = cc * dd * tup4 pa pb pc pd t → tup4 pa pb pc pd t = 1 := by
    decide +kernel
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨t, hc, rfl⟩ := (mem_Ua_inf_cent _ x).1 hx
  rw [Subgroup.mem_bot]
  exact key t hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ua_cent_cd2 : Ua ⊓ Cen (cc * dd ^ 2) = ⊥ := by
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 pa pb pc pd t * (cc * dd ^ 2) = cc * dd ^ 2 * tup4 pa pb pc pd t →
        tup4 pa pb pc pd t = 1 := by
    decide +kernel
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨t, hc, rfl⟩ := (mem_Ua_inf_cent _ x).1 hx
  rw [Subgroup.mem_bot]
  exact key t hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ub_cent_cd : Ub ⊓ Cen (cc * dd) = ⊥ := by
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 qa qb qc qd t * (cc * dd) = cc * dd * tup4 qa qb qc qd t → tup4 qa qb qc qd t = 1 := by
    decide +kernel
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨t, hc, rfl⟩ := (mem_Ub_inf_cent _ x).1 hx
  rw [Subgroup.mem_bot]
  exact key t hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Ub_cent_cd2 : Ub ⊓ Cen (cc * dd ^ 2) = ⊥ := by
  have key : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
      tup4 qa qb qc qd t * (cc * dd ^ 2) = cc * dd ^ 2 * tup4 qa qb qc qd t →
        tup4 qa qb qc qd t = 1 := by
    decide +kernel
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨t, hc, rfl⟩ := (mem_Ub_inf_cent _ x).1 hx
  rw [Subgroup.mem_bot]
  exact key t hc

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
