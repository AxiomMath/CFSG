module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open Subgroup
open scoped commutatorElement

section Module

variable {W : Type*} [CommGroup W]

private lemma autPow_two (a : MulAut W) (x : W) : (a ^ 2) x = a (a x) := by
  simp [pow_two, MulAut.mul_apply]

private lemma autPow_three (a : MulAut W) (ha3 : a ^ 3 = 1) (x : W) : a (a (a x)) = x := by
  have := congrArg (fun f : MulAut W => f x) ha3
  simpa [pow_succ, MulAut.mul_apply] using this

private lemma trace_fixed (a : MulAut W) (ha3 : a ^ 3 = 1) (x : W) :
    a (x * a x * (a ^ 2) x) = x * a x * (a ^ 2) x := by
  rw [autPow_two, map_mul, map_mul, autPow_three a ha3]
  ac_rfl

private lemma trace_uform (hsq : ∀ x : W, x * x = 1) (q : MulAut W) (hq3 : q ^ 3 = 1) (v : W) :
    (v * q v) * q (v * q v) * (q ^ 2) (v * q v) = 1 := by
  rw [autPow_two]
  simp only [map_mul]
  rw [autPow_three q hq3]
  calc _ = (v * v) * (q v * q v) * (q (q v) * q (q v)) := by ac_rfl
    _ = 1 := by simp only [hsq, mul_one]

private lemma exists_fixed_mul_uform (hsq : ∀ x : W, x * x = 1) (q : MulAut W) (hq3 : q ^ 3 = 1)
    (x : W) : ∃ t v' : W, q t = t ∧ x = t * (v' * q v') := by
  refine ⟨x * q x * (q ^ 2) x, q x, trace_fixed q hq3 x, ?_⟩
  rw [autPow_two]
  calc x = x * (q x * q x) * (q (q x) * q (q x)) := by simp only [hsq, mul_one]
    _ = _ := by ac_rfl

private lemma eq_of_fixed_uform (hsq : ∀ x : W, x * x = 1) (q : MulAut W) (hq3 : q ^ 3 = 1)
    (v : W) (h : q (v * q v) = v * q v) : q v = v := by
  rw [map_mul] at h
  have h2 : q (q v) = v := mul_left_cancel (a := q v) (h.trans (mul_comm v (q v)))
  have h3 := autPow_three q hq3 v
  rw [h2] at h3
  exact h3

private lemma uform_mem (hsq : ∀ x : W, x * x = 1) (p q : MulAut W) (hpq : p * q = q * p)
    (hp3 : p ^ 3 = 1) (hq3 : q ^ 3 = 1) (Z : Subgroup W)
    (h0 : ∀ x, p x = x → x ∈ Z) (h1 : ∀ x, (p * q) x = x → x ∈ Z)
    (h2 : ∀ x, (p * q ^ 2) x = x → x ∈ Z) (v : W) : v * q v ∈ Z := by
  set u : W := v * q v
  have hcomm : Commute p q := hpq
  have hpq3 : (p * q) ^ 3 = 1 := by rw [hcomm.mul_pow, hp3, hq3, one_mul]
  have hpq23 : (p * q ^ 2) ^ 3 = 1 := by
    rw [(hcomm.pow_right 2).mul_pow, hp3, ← pow_mul, mul_comm, pow_mul, hq3, one_pow, one_mul]
  have hE0 := h0 _ (trace_fixed p hp3 u)
  have hE1 := h1 _ (trace_fixed (p * q) hpq3 u)
  have hE2 := h2 _ (trace_fixed (p * q ^ 2) hpq23 u)
  have hrow : u * q u * q (q u) = 1 := by
    have := trace_uform hsq q hq3 v
    rwa [autPow_two] at this
  have e1 : p u * p (q u) * p (q (q u)) = 1 := by
    have := congrArg p hrow
    simpa [map_mul] using this
  have e2 : p (p u) * p (p (q u)) * p (p (q (q u))) = 1 := by
    have := congrArg p e1
    simpa [map_mul] using this
  have hq4 : ∀ x, q (q (q (q x))) = q x := fun x => by rw [autPow_three q hq3]
  have a1 : ((p * q) ^ 2) u = p (p (q (q u))) := by
    rw [hcomm.mul_pow]; simp [MulAut.mul_apply, pow_two]
  have a2 : ((p * q ^ 2) ^ 2) u = p (p (q u)) := by
    rw [(hcomm.pow_right 2).mul_pow]
    simp only [MulAut.mul_apply, autPow_two]
    rw [hq4]
  have a3 : (p * q ^ 2) u = p (q (q u)) := by
    simp [MulAut.mul_apply, autPow_two]
  have a4 : (p * q) u = p (q u) := by simp [MulAut.mul_apply]
  have key : u = (u * p u * (p ^ 2) u) * (u * (p * q) u * ((p * q) ^ 2) u) *
      (u * (p * q ^ 2) u * ((p * q ^ 2) ^ 2) u) := by
    rw [a1, a2, a3, a4, autPow_two]
    calc u = (u * u * u) * 1 * 1 := by rw [hsq u]; simp
      _ = (u * u * u) * (p u * p (q u) * p (q (q u))) *
          (p (p u) * p (p (q u)) * p (p (q (q u)))) := by rw [e1, e2]
      _ = _ := by ac_rfl
  rw [key]
  exact Z.mul_mem (Z.mul_mem hE0 hE1) hE2

end Module

section Abstract

variable {R : Type*} [Group R]

private lemma comm_of_sq {V : Subgroup R} (hV2 : ∀ v ∈ V, v * v = 1) {x y : R} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hV2 x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hV2 y hy)
  have : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hV2 (x * y) (V.mul_mem hx hy))
  rw [mul_inv_rev, hx', hy'] at this
  exact this.symm

private lemma comm_mem_of_perfect {V Y : Subgroup R} {d : R}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hYV : Y ≤ normalizer (V : Set R)) (hYp : Group.IsPerfect ↥Y)
    (hYd : ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ V) :
    ∀ y ∈ Y, ⁅y, d⁆ ∈ ⁅V, Y⁆ := by
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  set N' : Subgroup ↥V := (⁅V, Y⁆).subgroupOf V
  have hnorm : N'.Normal := Subgroup.normal_of_comm N'
  let f : ↥Y →* ↥V ⧸ N' :=
    { toFun := fun y => QuotientGroup.mk (⟨⁅(y : R), d⁆, hYd y y.2⟩ : ↥V)
      map_one' := by
        have h1 : (⟨⁅((1 : ↥Y) : R), d⁆, hYd 1 (one_mem Y)⟩ : ↥V) = 1 := Subtype.ext (by simp)
        show QuotientGroup.mk _ = 1
        rw [h1]
        exact QuotientGroup.mk_one _
      map_mul' := by
        intro g h
        have ha : ⁅(g : R), d⁆ ∈ V := hYd g g.2
        have hb : ⁅(h : R), d⁆ ∈ V := hYd h h.2
        have hw : (g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹ ∈ V :=
          (mem_normalizer_iff.1 (hYV g.2) _).1 hb
        have hwa : ⁅(g : R), d⁆ * ((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹)⁻¹ =
            ((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹)⁻¹ * ⁅(g : R), d⁆ :=
          hcomm _ ha _ (V.inv_mem hw)
        have hid : ⁅(g : R) * (h : R), d⁆ =
            ((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹) * ⁅(g : R), d⁆ := by
          simp only [commutatorElement_def]; group
        have e : (((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹) * ⁅(g : R), d⁆)⁻¹ *
            (⁅(g : R), d⁆ * ⁅(h : R), d⁆) = ⁅(g : R), (⁅(h : R), d⁆)⁻¹⁆ := by
          calc (((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹) * ⁅(g : R), d⁆)⁻¹ *
                (⁅(g : R), d⁆ * ⁅(h : R), d⁆)
              = ⁅(g : R), d⁆⁻¹ * (((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹)⁻¹ * ⁅(g : R), d⁆) *
                  ⁅(h : R), d⁆ := by rw [mul_inv_rev]; group
            _ = ⁅(g : R), d⁆⁻¹ * (⁅(g : R), d⁆ * ((g : R) * ⁅(h : R), d⁆ * (g : R)⁻¹)⁻¹) *
                  ⁅(h : R), d⁆ := by rw [hwa]
            _ = ⁅(g : R), (⁅(h : R), d⁆)⁻¹⁆ := by simp only [commutatorElement_def]; group
        show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hid, e, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator g.2 (V.inv_mem hb) }
  have hcommQ : ∀ x y : ↥V ⧸ N', x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm]
  have hker : commutator ↥Y ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm).2 (hcommQ _ _)
  intro y hy
  have h1 : f ⟨y, hy⟩ = 1 := hker (by rw [hYp.commutator_eq_top]; trivial)
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  exact (Subgroup.mem_subgroupOf).1 h2

private theorem aux_main {V Y : Subgroup R} {c d : R}
    (hV2 : ∀ v ∈ V, v * v = 1) (hVY : V ≤ Y) (hYV : Y ≤ normalizer (V : Set R))
    (hYp : Group.IsPerfect ↥Y)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hcd : c * d = d * c)
    (hcV : c ∈ normalizer (V : Set R)) (hdV : d ∈ normalizer (V : Set R))
    (hYd : ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ V)
    (hC : ∀ i < 3, Y ≤ centralizer
      ((V ⊓ centralizer ({c * d ^ i} : Set R) : Subgroup R) : Set R)) :
    V ≤ centralizer ({d} : Set R) := by
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => comm_of_sq hV2 hx hy
  have hN := comm_mem_of_perfect hcomm hYV hYp hYd
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hsqW : ∀ x : ↥V, x * x = 1 := fun x => Subtype.ext (hV2 x x.2)
  let σ := V.normalizerMonoidHom
  let cN : ↥(normalizer (V : Set R)) := ⟨c, hcV⟩
  let dN : ↥(normalizer (V : Set R)) := ⟨d, hdV⟩
  have hσ : ∀ (g : ↥(normalizer (V : Set R))) (x : ↥V),
      ((σ g x : ↥V) : R) = g * x * (g : R)⁻¹ := fun g x => rfl
  have hcdN : cN * dN = dN * cN := Subtype.ext hcd
  have hp3 : σ cN ^ 3 = 1 := by
    rw [← map_pow, show cN ^ 3 = 1 from Subtype.ext hc3, map_one]
  have hq3 : σ dN ^ 3 = 1 := by
    rw [← map_pow, show dN ^ 3 = 1 from Subtype.ext hd3, map_one]
  have hpq : σ cN * σ dN = σ dN * σ cN := by rw [← map_mul, ← map_mul, hcdN]
  let Z : Subgroup ↥V := (centralizer (Y : Set R)).subgroupOf V
  have hZ : ∀ x : ↥V, x ∈ Z ↔ ∀ y ∈ Y, y * (x : R) = (x : R) * y := by
    intro x
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff]
    exact Iff.rfl
  have hfix : ∀ i < 3, ∀ x : ↥V, (σ cN * σ dN ^ i) x = x → x ∈ Z := by
    intro i hi x hx
    rw [← map_pow, ← map_mul] at hx
    have hx' := congrArg (fun z : ↥V => (z : R)) hx
    simp only [hσ] at hx'
    have hg : ((cN * dN ^ i : ↥(normalizer (V : Set R))) : R) = c * d ^ i := rfl
    rw [hg] at hx'
    have hx'' : (c * d ^ i) * (x : R) = (x : R) * (c * d ^ i) := by
      calc (c * d ^ i) * (x : R) = ((c * d ^ i) * (x : R) * (c * d ^ i)⁻¹) * (c * d ^ i) := by
            group
        _ = (x : R) * (c * d ^ i) := by rw [hx']
    have hxmem : (x : R) ∈ (V ⊓ centralizer ({c * d ^ i} : Set R) : Subgroup R) := by
      refine ⟨x.2, mem_centralizer_iff.2 ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hx''
    rw [hZ]
    intro y hy
    exact (mem_centralizer_iff.1 (hC i hi hy) x hxmem).symm
  have hU : ∀ v : ↥V, v * σ dN v ∈ Z := fun v =>
    uform_mem hsqW (σ cN) (σ dN) hpq hp3 hq3 Z (by simpa using hfix 0 (by norm_num))
      (by simpa using hfix 1 (by norm_num)) (hfix 2 (by norm_num)) v
  have hNd : ∀ x ∈ V, ∀ y ∈ Y, d * ⁅x, y⁆ = ⁅x, y⁆ * d := by
    intro x hx y hy
    obtain ⟨t, v', htq, hxt⟩ := exists_fixed_mul_uform hsqW (σ dN) hq3 ⟨x, hx⟩
    have hw := (hZ _).1 (hU v') y hy
    have hx_eq : x = (t : R) * ((v' * σ dN v' : ↥V) : R) := congrArg Subtype.val hxt
    have hdt : d * (t : R) * d⁻¹ = t := by
      have := congrArg (fun z : ↥V => (z : R)) htq
      simpa [hσ] using this
    have hdt' : d * (t : R)⁻¹ * d⁻¹ = (t : R)⁻¹ := by
      calc d * (t : R)⁻¹ * d⁻¹ = (d * (t : R) * d⁻¹)⁻¹ := by group
        _ = (t : R)⁻¹ := by rw [hdt]
    have hcxy : ⁅x, y⁆ = (t : R) * y * (t : R)⁻¹ * y⁻¹ := by
      have h1 : ((v' * σ dN v' : ↥V) : R) * y * ((v' * σ dN v' : ↥V) : R)⁻¹ = y := by
        rw [← hw]; group
      calc ⁅x, y⁆ = ⁅(t : R) * ((v' * σ dN v' : ↥V) : R), y⁆ := by rw [hx_eq]
        _ = (t : R) * (((v' * σ dN v' : ↥V) : R) * y * ((v' * σ dN v' : ↥V) : R)⁻¹) *
              (t : R)⁻¹ * y⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = _ := by rw [h1]
    have hz : ⁅y, d⁆ ∈ V := hYd y hy
    have hs : y * (t : R)⁻¹ * y⁻¹ ∈ V :=
      (mem_normalizer_iff.1 (hYV hy) _).1 (V.inv_mem t.2)
    have hdy : d * y * d⁻¹ = (⁅y, d⁆)⁻¹ * y := by
      simp only [commutatorElement_def]; group
    have hzs : (⁅y, d⁆)⁻¹ * (y * (t : R)⁻¹ * y⁻¹) = (y * (t : R)⁻¹ * y⁻¹) * (⁅y, d⁆)⁻¹ :=
      hcomm _ (V.inv_mem hz) _ hs
    have hconj : d * ((t : R) * y * (t : R)⁻¹ * y⁻¹) * d⁻¹ = (t : R) * y * (t : R)⁻¹ * y⁻¹ := by
      calc d * ((t : R) * y * (t : R)⁻¹ * y⁻¹) * d⁻¹
          = (d * (t : R) * d⁻¹) * (d * y * d⁻¹) * (d * (t : R)⁻¹ * d⁻¹) *
              (d * y * d⁻¹)⁻¹ := by group
        _ = (t : R) * ((⁅y, d⁆)⁻¹ * y) * (t : R)⁻¹ * ((⁅y, d⁆)⁻¹ * y)⁻¹ := by
            rw [hdt, hdt', hdy]
        _ = (t : R) * ((⁅y, d⁆)⁻¹ * (y * (t : R)⁻¹ * y⁻¹)) * ⁅y, d⁆ := by group
        _ = (t : R) * ((y * (t : R)⁻¹ * y⁻¹) * (⁅y, d⁆)⁻¹) * ⁅y, d⁆ := by rw [hzs]
        _ = (t : R) * y * (t : R)⁻¹ * y⁻¹ := by group
    rw [hcxy]
    calc d * ((t : R) * y * (t : R)⁻¹ * y⁻¹)
        = (d * ((t : R) * y * (t : R)⁻¹ * y⁻¹) * d⁻¹) * d := by group
      _ = _ := by rw [hconj]
  intro v hv
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  let v' : ↥V := ⟨v, hv⟩
  have hv1 : ⁅v, h⁆ ∈ ⁅V, Y⁆ := hN v (hVY hv)
  have hu : ⁅v, h⁆ = ((v' * σ dN v' : ↥V) : R) := by
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 v hv)
    simp only [commutatorElement_def, hvinv]
    show _ = v * (h * v * h⁻¹)
    group
  have hcent : h * ⁅v, h⁆ = ⁅v, h⁆ * h := by
    have hle : ⁅V, Y⁆ ≤ centralizer ({h} : Set R) := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact hNd x hx y hy
    exact mem_centralizer_iff.1 (hle hv1) h rfl
  have hfixu : σ dN (v' * σ dN v') = v' * σ dN v' := by
    apply Subtype.ext
    rw [hσ]
    show h * ((v' * σ dN v' : ↥V) : R) * h⁻¹ = _
    rw [← hu]
    calc h * ⁅v, h⁆ * h⁻¹ = (⁅v, h⁆ * h) * h⁻¹ := by rw [hcent]
      _ = ⁅v, h⁆ := by group
  have hv2 := eq_of_fixed_uform hsqW (σ dN) hq3 v' hfixu
  have hv3 := congrArg (fun z : ↥V => (z : R)) hv2
  simp only [hσ] at hv3
  show h * v = v * h
  calc h * v = (h * v * h⁻¹) * h := by group
    _ = v * h := by
      have : h * v * h⁻¹ = v := hv3
      rw [this]

private theorem core {G : Type*} [Group G] {Φ P Y : Subgroup G} [Φ.Normal] {c d : G}
    (hPn : P.Normal) (hsq : ∀ x ∈ P, x * x ∈ Φ) (hPY : P ≤ Y) (hYp : Group.IsPerfect ↥Y)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hcd : c * d = d * c)
    (hYd : ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ P)
    (hlift : ∀ i < 3, ∀ x ∈ P, (c * d ^ i) * x * (c * d ^ i)⁻¹ * x⁻¹ ∈ Φ →
      ∃ u ∈ P, (c * d ^ i) * u * (c * d ^ i)⁻¹ = u ∧ x⁻¹ * u ∈ Φ)
    (hY2 : ∀ i < 3, ∀ u ∈ P, (c * d ^ i) * u = u * (c * d ^ i) → ∀ y ∈ Y, ⁅y, u⁆ ∈ Φ) :
    ∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ Φ := by
  let q : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  have hq1 : ∀ a : G, q a = 1 ↔ a ∈ Φ := fun a => QuotientGroup.eq_one_iff a
  have hqe : ∀ a b : G, q a = q b ↔ a⁻¹ * b ∈ Φ := fun a b => QuotientGroup.eq
  haveI hVn : (P.map q).Normal := Subgroup.Normal.map hPn q (QuotientGroup.mk'_surjective Φ)
  have hnorm : ∀ r : G ⧸ Φ, r ∈ normalizer ((P.map q : Subgroup (G ⧸ Φ)) : Set (G ⧸ Φ)) := by
    intro r
    rw [Subgroup.normalizer_eq_top_iff.2 hVn]
    trivial
  haveI : Group.IsPerfect ↥Y := hYp
  haveI hYp' : Group.IsPerfect ↥(Y.map q) := Group.IsPerfect.map q
  have hcomm_iff : ∀ a b : G, q a * q b = q b * q a ↔ ⁅a, b⁆ ∈ Φ := by
    intro a b
    rw [← hq1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have hmain := aux_main (V := P.map q) (Y := Y.map q) (c := q c) (d := q d)
    (by
      rintro v ⟨x, hx, rfl⟩
      rw [← map_mul, hq1]
      exact hsq x hx)
    (Subgroup.map_mono hPY) (fun r _ => hnorm r) hYp'
    (by rw [← map_pow, hc3, map_one]) (by rw [← map_pow, hd3, map_one])
    (by rw [← map_mul, ← map_mul, hcd]) (hnorm _) (hnorm _)
    (by
      rintro r ⟨y, hy, rfl⟩
      have : q y * q d * (q y)⁻¹ * (q d)⁻¹ = q (y * d * y⁻¹ * d⁻¹) := by
        simp only [map_mul, map_inv]
      rw [this]
      exact Subgroup.mem_map_of_mem q (hYd y hy))
    (by
      intro i hi r hr
      obtain ⟨y, hy, rfl⟩ := hr
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨hwV, hwC⟩ := hw
      obtain ⟨x, hx, rfl⟩ := hwV
      have hwe : q c * q d ^ i * q x = q x * (q c * q d ^ i) :=
        mem_centralizer_iff.1 hwC (q c * q d ^ i) rfl
      have hfix : (c * d ^ i) * x * (c * d ^ i)⁻¹ * x⁻¹ ∈ Φ := by
        rw [← hq1]
        simp only [map_mul, map_inv, map_pow]
        rw [hwe]; group
      obtain ⟨u, huP, hu1, hu2⟩ := hlift i hi x hx hfix
      have hqu : q u = q x := ((hqe x u).2 hu2).symm
      have hcu : (c * d ^ i) * u = u * (c * d ^ i) := by
        calc (c * d ^ i) * u = ((c * d ^ i) * u * (c * d ^ i)⁻¹) * (c * d ^ i) := by group
          _ = u * (c * d ^ i) := by rw [hu1]
      have := (hcomm_iff y u).2 (hY2 i hi u huP hcu y hy)
      rw [← hqu]
      exact this.symm)
  intro x hx
  have := hmain ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff] at this
  have h2 := this (q d) rfl
  rw [← hq1]
  simp only [map_mul, map_inv]
  rw [h2]; group

end Abstract

section Frattini

variable {G : Type} [Group G] [Finite G]

private abbrev fr (P : Subgroup G) : Subgroup G := (frattini ↥P).map P.subtype

private lemma fr_le (P : Subgroup G) : fr P ≤ P := Subgroup.map_subtype_le _

private lemma fr_conj {P : Subgroup G} {g x : G} (hg : g ∈ normalizer (P : Set G))
    (hx : x ∈ fr P) : g * x * g⁻¹ ∈ fr P := by
  obtain ⟨f, hf, rfl⟩ := hx
  set α := P.normalizerMonoidHom ⟨g, hg⟩
  have h1 : α f ∈ frattini ↥P := by
    have h := (frattini_characteristic (G := ↥P)).fixed α
    have : f ∈ (frattini ↥P).comap α.toMonoidHom := by rw [h]; exact hf
    exact this
  exact ⟨α f, h1, rfl⟩

private lemma fr_comm {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) : ⁅x, y⁆ ∈ fr P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  have h1 : ⁅(⟨x, hx⟩ : ↥P), (⟨y, hy⟩ : ↥P)⁆ ∈ frattini ↥P :=
    CFSG.commutator_le_frattini_of_isPGroup (p := 2)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact ⟨_, h1, rfl⟩

private lemma fr_sq {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {x : G} (hx : x ∈ P) :
    x * x ∈ fr P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  have h1 : (⟨x, hx⟩ : ↥P) ^ 2 ∈ frattini ↥P :=
    CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _
  exact ⟨_, h1, by simp [pow_two]⟩

private lemma card_fr_not_dvd {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) : ¬ 3 ∣ Nat.card (fr P) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (fr P) = Nat.card (frattini ↥P) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective P)
  obtain ⟨n, hn⟩ := (hP2.to_subgroup (frattini ↥P)).exists_card_eq
  rw [h1, hn]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

private lemma exists_fixed_lift {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {e x : G}
    (he : e ∈ normalizer (P : Set G)) (he3 : e ^ 3 = 1) (hx : x ∈ P)
    (hfix : e * x * e⁻¹ * x⁻¹ ∈ fr P) :
    ∃ u ∈ P, e * u * e⁻¹ = u ∧ x⁻¹ * u ∈ fr P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxn : x⁻¹ ∈ normalizer (P : Set G) :=
    (normalizer (P : Set G)).inv_mem (Subgroup.le_normalizer hx)
  have hmap : ∀ g : G, x⁻¹ * g ∈ fr P → x⁻¹ * (e * g * e⁻¹) ∈ fr P := by
    intro g hg
    have h1 : x⁻¹ * (e * x * e⁻¹ * x⁻¹) * x⁻¹⁻¹ ∈ fr P := fr_conj hxn hfix
    have h2 : e * (x⁻¹ * g) * e⁻¹ ∈ fr P := fr_conj he hg
    have : x⁻¹ * (e * g * e⁻¹) =
        (x⁻¹ * (e * x * e⁻¹ * x⁻¹) * x⁻¹⁻¹) * (e * (x⁻¹ * g) * e⁻¹) := by group
    rw [this]
    exact (fr P).mul_mem h1 h2
  let S : Type := {g : G // x⁻¹ * g ∈ fr P}
  let f : Function.End S := fun g => ⟨e * g * e⁻¹, hmap g g.2⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext g
    apply Subtype.ext
    show e * (e * (e * (g : G) * e⁻¹) * e⁻¹) * e⁻¹ = g
    have he3' : e * e * e = 1 := by rw [← pow_three', he3]
    calc e * (e * (e * (g : G) * e⁻¹) * e⁻¹) * e⁻¹
        = (e * e * e) * (g : G) * (e * e * e)⁻¹ := by group
      _ = g := by rw [he3']; group
  haveI : Finite S := Subtype.finite
  haveI : Fintype S := Fintype.ofFinite S
  let eqv : S ≃ fr P :=
    { toFun := fun g => ⟨x⁻¹ * g, g.2⟩
      invFun := fun φ => ⟨x * φ, by simpa using φ.2⟩
      left_inv := fun g => by apply Subtype.ext; simp
      right_inv := fun φ => by apply Subtype.ext; simp }
  have hcard : Fintype.card S = Nat.card (fr P) := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.card_congr eqv
  have h3 : ¬ 3 ∣ Fintype.card S := by rw [hcard]; exact card_fr_not_dvd hP2
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf3
  have hne : Nonempty (Function.fixedPoints f) := by
    by_contra hcon
    have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
      rw [Fintype.card_eq_zero_iff]; exact not_nonempty_iff.1 hcon
    rw [h0] at hmod
    exact h3 ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨g, hgS⟩, hg⟩ := hne
  have hgP : g ∈ P := by
    have : g = x * (x⁻¹ * g) := by group
    rw [this]
    exact P.mul_mem hx (fr_le P hgS)
  refine ⟨g, hgP, ?_, hgS⟩
  have := congrArg Subtype.val hg
  simpa [f] using this

private lemma centralizes_of_comm_mem_fr {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {d : G}
    (hd : d ∈ normalizer (P : Set G)) (hd3 : d ^ 3 = 1)
    (h : ∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ fr P) : ∀ x ∈ P, d * x = x * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  let C' : Subgroup ↥P := (centralizer ({d} : Set G)).subgroupOf P
  have hsup : C' ⊔ frattini ↥P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, huP, hu, hxu⟩ := exists_fixed_lift hP2 hd hd3 x.2 (h x x.2)
    obtain ⟨φ, hφ, hφx⟩ := hxu
    have hu' : (⟨u, huP⟩ : ↥P) ∈ C' := by
      rw [Subgroup.mem_subgroupOf, mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      calc h' * u = (h' * u * h'⁻¹) * h' := by group
        _ = u * h' := by rw [hu]
    have hxe : x = ⟨u, huP⟩ * φ⁻¹ := by
      apply Subtype.ext
      have : (φ : G) = (x : G)⁻¹ * u := hφx
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, this]
      group
    rw [hxe]
    exact Subgroup.mul_mem_sup hu' (inv_mem hφ)
  have htop : C' = ⊤ := CFSG.lemma_1_7_a (p := 2) C' hsup
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥P) ∈ C' := by rw [htop]; trivial
  rw [Subgroup.mem_subgroupOf, mem_centralizer_iff] at hmem
  exact hmem d rfl

private lemma claim2 {Y P K : Subgroup G} (hP2 : IsPGroup 2 ↥P) (hPY : P ≤ Y)
    (hYP : Y ≤ normalizer (P : Set G)) (hKP : Y ≤ (K ⊓ Y) ⊔ P)
    {u : G} (hu : u ∈ P) (hKu : ∀ k ∈ K, k * u = u * k) :
    ∀ y ∈ Y, ⁅y, u⁆ ∈ fr P := by
  let T : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ⁅y, u⁆ ∈ fr P}
      one_mem' := ⟨Y.one_mem, by simpa using (fr P).one_mem⟩
      mul_mem' := by
        rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
        refine ⟨Y.mul_mem haY hbY, ?_⟩
        have h1 : a * ⁅b, u⁆ * a⁻¹ ∈ fr P := fr_conj (hYP haY) hb
        have : ⁅a * b, u⁆ = (a * ⁅b, u⁆ * a⁻¹) * ⁅a, u⁆ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact (fr P).mul_mem h1 ha
      inv_mem' := by
        rintro a ⟨haY, ha⟩
        refine ⟨Y.inv_mem haY, ?_⟩
        have h1 : a⁻¹ * (⁅a, u⁆)⁻¹ * a⁻¹⁻¹ ∈ fr P :=
          fr_conj (hYP (Y.inv_mem haY)) ((fr P).inv_mem ha)
        have : ⁅a⁻¹, u⁆ = a⁻¹ * (⁅a, u⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact h1 }
  have hKT : K ⊓ Y ≤ T := by
    intro k hk
    refine ⟨hk.2, ?_⟩
    have : ⁅k, u⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]; exact hKu k hk.1
    rw [this]; exact (fr P).one_mem
  have hPT : P ≤ T := fun p hp => ⟨hPY hp, fr_comm hP2 hp hu⟩
  intro y hy
  exact (sup_le hKT hPT (hKP hy)).2

private lemma le_inf_sup_of_le_sup {Y P K : Subgroup G} (hPY : P ≤ Y)
    (hKN : K ≤ normalizer (P : Set G)) (hY : Y ≤ K ⊔ P) : Y ≤ (K ⊓ Y) ⊔ P := by
  let T : Subgroup G :=
    { carrier := {g | ∃ k ∈ K, ∃ p ∈ P, g = k * p}
      one_mem' := ⟨1, K.one_mem, 1, P.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, p₁, hp₁, rfl⟩ ⟨k₂, hk₂, p₂, hp₂, rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, (k₂⁻¹ * p₁ * k₂) * p₂, ?_, by group⟩
        have h1 : k₂⁻¹ * p₁ * k₂⁻¹⁻¹ ∈ P := (mem_normalizer_iff.1 (hKN (K.inv_mem hk₂)) _).1 hp₁
        exact P.mul_mem (by simpa using h1) hp₂
      inv_mem' := by
        rintro _ ⟨k, hk, p, hp, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k * p⁻¹ * k⁻¹, ?_, by group⟩
        exact (mem_normalizer_iff.1 (hKN hk) _).1 (P.inv_mem hp) }
  have hle : K ⊔ P ≤ T := sup_le (fun k hk => ⟨k, hk, 1, P.one_mem, by simp⟩)
    (fun p hp => ⟨1, K.one_mem, p, hp, by simp⟩)
  intro y hy
  obtain ⟨k, hk, p, hp, rfl⟩ := hle (hY hy)
  have hkY : k ∈ Y := by
    have : k = (k * p) * p⁻¹ := by group
    rw [this]
    exact Y.mul_mem hy (Y.inv_mem (hPY hp))
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hk, hkY⟩))
    (Subgroup.mem_sup_right hp)

end Frattini

section Main

variable {G : Type} [Group G] [Finite G]

private lemma not_mem_zpowers_of_card {c d : G} (hd3 : d ^ 3 = 1)
    (hE9 : Nat.card (Subgroup.closure ({c, d} : Set G)) = 9) : c ∉ zpowers d := by
  intro hc
  have hle : Subgroup.closure ({c, d} : Set G) ≤ zpowers d := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hc
    · exact mem_zpowers x
  have h1 : Nat.card (Subgroup.closure ({c, d} : Set G)) ≤ Nat.card (zpowers d) :=
    Subgroup.card_le_of_le hle
  rw [hE9, Nat.card_zpowers] at h1
  have h2 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
  have h3 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem le_centralizer_of_perfect_of_fix_inf {Y P : Subgroup G} {c d : G}
    (hP2 : IsPGroup 2 P) (hPY : P ≤ Y) (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    (hYp : Group.IsPerfect ↥Y)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hcd : c * d = d * c)
    (hE9 : Nat.card (Subgroup.closure ({c, d} : Set G)) = 9)
    (hcP : c ∈ Subgroup.normalizer (P : Set G)) (hdP : d ∈ Subgroup.normalizer (P : Set G))
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (hdY : d ∈ Subgroup.normalizer (Y : Set G))
    (hYE : ∀ y ∈ Y, ∀ e ∈ Subgroup.closure ({c, d} : Set G), y * e * y⁻¹ * e⁻¹ ∈ P)
    (hK : ∀ e ∈ Subgroup.closure ({c, d} : Set G), e ∉ Subgroup.zpowers d →
      ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({e} : Set G) ∧ Y ≤ (K ⊓ Y) ⊔ P ∧
        K ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :
          Set G)) :
    P ≤ Subgroup.centralizer ({d} : Set G) := by
  have _ := hcY
  have _ := hdY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer (P : Set G)
  have hPM : P ≤ M := Subgroup.le_normalizer
  have hEM : Subgroup.closure ({c, d} : Set G) ≤ M := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hcP
    · exact hdP
  have hcd' : c ∉ zpowers d := not_mem_zpowers_of_card hd3 hE9
  have hEmem : ∀ i : ℕ, c * d ^ i ∈ Subgroup.closure ({c, d} : Set G) := fun i =>
    mul_mem (Subgroup.subset_closure (by simp)) (pow_mem (Subgroup.subset_closure (by simp)) i)
  let ΦM : Subgroup ↥M := (fr P).subgroupOf M
  haveI hΦn : ΦM.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact fr_conj g.2 hx⟩
  let P' : Subgroup ↥M := P.subgroupOf M
  let Y' : Subgroup ↥M := Y.subgroupOf M
  haveI hP'n : P'.Normal := Subgroup.normal_in_normalizer
  let c' : ↥M := ⟨c, hcP⟩
  let d' : ↥M := ⟨d, hdP⟩
  haveI : Group.IsPerfect ↥Y := hYp
  haveI hY'p : Group.IsPerfect ↥Y' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYP).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYP).symm.surjective
  have key := core (Φ := ΦM) (P := P') (Y := Y') (c := c') (d := d') hP'n
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using fr_sq hP2 hx)
    (Subgroup.subgroupOf_mono M hPY) hY'p
    (Subtype.ext (by simpa [c'] using hc3)) (Subtype.ext (by simpa [d'] using hd3))
    (Subtype.ext (by simpa [c', d'] using hcd))
    (fun y hy => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have := hYE y hy d (Subgroup.subset_closure (by simp))
      simpa [d'] using this)
    (fun i hi x hx hfix => by
      have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.1 hx
      have he3 : (c * d ^ i) ^ 3 = 1 := by
        rw [((Commute.pow_right (show Commute c d from hcd) i)).mul_pow, hc3, one_mul,
          ← pow_mul, mul_comm, pow_mul, hd3, one_pow]
      have hfix' : (c * d ^ i) * (x : G) * (c * d ^ i)⁻¹ * (x : G)⁻¹ ∈ fr P := by
        have h1 := Subgroup.mem_subgroupOf.1 hfix
        simpa [c', d'] using h1
      obtain ⟨u, huP, hu1, hu2⟩ := exists_fixed_lift hP2 (hEM (hEmem i)) he3 hxP hfix'
      refine ⟨⟨u, hPM huP⟩, Subgroup.mem_subgroupOf.2 huP, Subtype.ext ?_,
        Subgroup.mem_subgroupOf.2 ?_⟩
      · simpa [c', d'] using hu1
      · simpa using hu2)
    (fun i hi u hu hcu y hy => by
      have hen : (c * d ^ i) ∉ zpowers d := by
        intro hmem
        apply hcd'
        have : c = (c * d ^ i) * (d ^ i)⁻¹ := by group
        rw [this]
        exact mul_mem hmem (inv_mem (pow_mem (mem_zpowers d) i))
      obtain ⟨K, hKe, hKP, hKC⟩ := hK (c * d ^ i) (hEmem i) hen
      have hu' : (u : G) ∈ P := Subgroup.mem_subgroupOf.1 hu
      have hcu' : (c * d ^ i) * (u : G) = (u : G) * (c * d ^ i) := by
        have := congrArg Subtype.val hcu
        simpa [c', d'] using this
      have hKu : ∀ k ∈ K, k * (u : G) = (u : G) * k := by
        intro k hk
        have hk' := hKC hk
        rw [mem_centralizer_iff] at hk'
        have hmem : (u : G) ∈ ((P ⊓ centralizer ({c * d ^ i} : Set G) : Subgroup G) : Set G) := by
          refine ⟨hu', mem_centralizer_iff.2 ?_⟩
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact hcu'
        exact (hk' _ hmem).symm
      have := claim2 hP2 hPY hYP hKP hu' hKu y (Subgroup.mem_subgroupOf.1 hy)
      exact Subgroup.mem_subgroupOf.2 (by simpa [commutatorElement_def] using this))
  have hcomm_fr : ∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ fr P := by
    intro x hx
    have := key ⟨x, hPM hx⟩ (Subgroup.mem_subgroupOf.2 hx)
    simpa [d'] using Subgroup.mem_subgroupOf.1 this
  intro x hx
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact centralizes_of_comm_mem_fr hP2 hdP hd3 hcomm_fr x hx

theorem le_centralizer_of_perfect_of_fix {Y P : Subgroup G} {c d : G}
    (hP2 : IsPGroup 2 P) (hPY : P ≤ Y) (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    (hYp : Group.IsPerfect ↥Y)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hcd : c * d = d * c)
    (hE9 : Nat.card (Subgroup.closure ({c, d} : Set G)) = 9)
    (hcP : c ∈ Subgroup.normalizer (P : Set G)) (hdP : d ∈ Subgroup.normalizer (P : Set G))
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (hdY : d ∈ Subgroup.normalizer (Y : Set G))
    (hYE : ∀ y ∈ Y, ∀ e ∈ Subgroup.closure ({c, d} : Set G), y * e * y⁻¹ * e⁻¹ ∈ P)
    (hK : ∀ e ∈ Subgroup.closure ({c, d} : Set G), e ∉ Subgroup.zpowers d →
      ∃ K : Subgroup G, K ≤ Subgroup.normalizer (P : Set G) ∧
        K ≤ Subgroup.centralizer ({e} : Set G) ∧ Y ≤ K ⊔ P ∧
        K ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :
          Set G)) :
    P ≤ Subgroup.centralizer ({d} : Set G) :=
  le_centralizer_of_perfect_of_fix_inf hP2 hPY hYP hYp hc3 hd3 hcd hE9 hcP hdP hcY hdY hYE
    fun e he hen => by
      obtain ⟨K, hKN, hKe, hKP, hKC⟩ := hK e he hen
      exact ⟨K, hKe, le_inf_sup_of_le_sup hPY hKN hKP, hKC⟩

end Main

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
