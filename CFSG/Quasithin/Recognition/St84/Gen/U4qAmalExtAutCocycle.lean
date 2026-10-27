module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F112R.St84

variable {G : Type*} [Group G]

theorem exists_eq_of_cocycle_of_odd_relIndex {V M H : Subgroup G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v * v = 1)
    (hMV : ∀ l ∈ M, ∀ v ∈ V, l * v * l⁻¹ ∈ V) (hodd : Odd (H.relIndex M)) (z : ↥M → ↥V)
    (hz : ∀ l l' : ↥M, (z (l * l') : G) = (l' : G)⁻¹ * z l * l' * z l')
    (hzH : ∀ l : ↥M, (l : G) ∈ H → z l = 1) :
    ∃ v ∈ V, (∀ l ∈ M, l ∈ H → l * v = v * l) ∧
      ∀ l : ↥M, (z l : G) = (l : G)⁻¹ * v⁻¹ * l * v := by
  classical
  let c : ↥M → ↥V →* ↥V := fun l =>
    { toFun := fun v => ⟨l * v * (l : G)⁻¹, hMV _ l.2 _ v.2⟩
      map_one' := Subtype.ext (by
        change (l : G) * 1 * (l : G)⁻¹ = 1
        group)
      map_mul' := fun v w => Subtype.ext (by
        change (l : G) * ((v : G) * w) * (l : G)⁻¹ =
          ((l : G) * v * (l : G)⁻¹) * ((l : G) * w * (l : G)⁻¹)
        group) }
  have hc : ∀ (l : ↥M) (v : ↥V), (c l v : G) = l * v * (l : G)⁻¹ := fun _ _ => rfl
  let ζ : ↥M → ↥V := fun t => c t (z t)
  have hζ : ∀ l t : ↥M, ζ (l * t) = ζ l * c l (ζ t) := by
    intro l t
    apply Subtype.ext
    change ((l * t : ↥M) : G) * (z (l * t) : G) * ((l * t : ↥M) : G)⁻¹ =
      ((l : G) * z l * (l : G)⁻¹) * ((l : G) * ((t : G) * z t * (t : G)⁻¹) * (l : G)⁻¹)
    rw [hz, Subgroup.coe_mul]
    group
  have hζH : ∀ t k : ↥M, (k : G) ∈ H → ζ (t * k) = ζ t := by
    intro t k hk
    have hk1 : ζ k = 1 := by
      change c k (z k) = 1
      rw [hzH k hk, map_one]
    rw [hζ, hk1, map_one, mul_one]
  have hrep : ∀ (l : ↥M) (q : ↥M ⧸ H.subgroupOf M),
      ζ (Quotient.out (l • q)) = ζ l * c l (ζ (Quotient.out q)) := by
    intro l q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf M) (l * Quotient.out q)
    have hq : l • q = (QuotientGroup.mk (l * Quotient.out q) : ↥M ⧸ H.subgroupOf M) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [hq, hk, hζH _ _ (Subgroup.mem_subgroupOf.mp k.2), hζ]
  haveI : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVc _ a.2 _ b.2)⟩⟩
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  haveI : Finite (↥M ⧸ H.subgroupOf M) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  letI : Fintype (↥M ⧸ H.subgroupOf M) := Fintype.ofFinite _
  set w : ↥V := ∏ q : ↥M ⧸ H.subgroupOf M, ζ (Quotient.out q) with hw
  have hcard : Fintype.card (↥M ⧸ H.subgroupOf M) = H.relIndex M := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hpow : ∀ v : ↥V, v ^ Fintype.card (↥M ⧸ H.subgroupOf M) = v := by
    intro v
    obtain ⟨k, hk⟩ := hodd
    have h2 : v ^ 2 = 1 := by
      rw [sq]
      exact Subtype.ext (hV2 _ v.2)
    rw [hcard, hk, pow_succ, pow_mul, h2, one_pow, one_mul]
  have key : ∀ l : ↥M, w = ζ l * c l w := by
    intro l
    have h1 : ∏ q : ↥M ⧸ H.subgroupOf M, ζ (Quotient.out (l • q)) = w := by
      simpa only [MulAction.toPerm_apply] using
        Equiv.prod_comp (MulAction.toPerm l) (fun q : ↥M ⧸ H.subgroupOf M => ζ (Quotient.out q))
    have h2 : ∏ q : ↥M ⧸ H.subgroupOf M, ζ (Quotient.out (l • q)) =
        ∏ q : ↥M ⧸ H.subgroupOf M, (ζ l * c l (ζ (Quotient.out q))) :=
      Finset.prod_congr rfl fun q _ => hrep l q
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← map_prod, h1, hpow,
      ← hw] at h2
    exact h2
  have hform : ∀ l : ↥M, (z l : G) = (l : G)⁻¹ * w * l * (w : G)⁻¹ := by
    intro l
    have hk : (w : G) = ((l : G) * z l * (l : G)⁻¹) * ((l : G) * w * (l : G)⁻¹) :=
      congrArg Subtype.val (key l)
    calc (z l : G) = (l : G)⁻¹ * (((l : G) * z l * (l : G)⁻¹) * ((l : G) * w * (l : G)⁻¹)) *
          l * (w : G)⁻¹ := by group
      _ = (l : G)⁻¹ * w * l * (w : G)⁻¹ := by rw [← hk]
  refine ⟨(w : G)⁻¹, V.inv_mem w.2, fun l hl hlH => ?_, fun l => ?_⟩
  · have e := hform ⟨l, hl⟩
    rw [hzH ⟨l, hl⟩ hlH] at e
    have e2 : l⁻¹ * (w : G) * l = w := mul_inv_eq_one.mp e.symm
    calc l * (w : G)⁻¹ = (w : G)⁻¹ * (l * (l⁻¹ * (w : G) * l) * (w : G)⁻¹) := by group
      _ = (w : G)⁻¹ * l := by rw [e2]; group
  · rw [inv_inv]
    exact hform l

theorem eq_one_of_forall_fix_of_odd_relIndex {P B R V : Subgroup G} (hBP : B ≤ P)
    (hodd : Odd (B.relIndex P)) (hRB : R ≤ B) (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v * v = 1)
    (hVn : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V)
    (hCV : P ⊓ Subgroup.centralizer (R : Set G) ≤ V)
    (hfix : ∀ v ∈ V, (∀ b ∈ B, b * v = v * b) → v = 1)
    (α : MulAut ↥P) (hα : ∀ x : ↥P, (x : G) ∈ B → α x = x) : α = 1 := by
  have hzV : ∀ p : ↥P, (p : G)⁻¹ * (α p : G) ∈ V := by
    intro p
    refine hCV ⟨P.mul_mem (P.inv_mem p.2) (α p).2,
      Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hrP : r ∈ P := hBP (hRB hr)
    have h1 : α ⟨r, hrP⟩ = ⟨r, hrP⟩ := hα _ (hRB hr)
    have h2 : α (p * ⟨r, hrP⟩ * p⁻¹) = p * ⟨r, hrP⟩ * p⁻¹ := hα _ (hRB (hRn _ p.2 _ hr))
    rw [map_mul, map_mul, map_inv, h1] at h2
    have h3 : (α p : G) * r * (α p : G)⁻¹ = (p : G) * r * (p : G)⁻¹ := congrArg Subtype.val h2
    calc r * ((p : G)⁻¹ * α p) = (p : G)⁻¹ * ((p : G) * r * (p : G)⁻¹) * α p := by group
      _ = (p : G)⁻¹ * ((α p : G) * r * (α p : G)⁻¹) * α p := by rw [h3]
      _ = (p : G)⁻¹ * α p * r := by group
  let z : ↥P → ↥V := fun p => ⟨(p : G)⁻¹ * α p, hzV p⟩
  have hz : ∀ p p' : ↥P, (z (p * p') : G) = (p' : G)⁻¹ * z p * p' * z p' := by
    intro p p'
    change ((p * p' : ↥P) : G)⁻¹ * (α (p * p') : G) =
      (p' : G)⁻¹ * ((p : G)⁻¹ * α p) * p' * ((p' : G)⁻¹ * α p')
    rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    group
  have hzB : ∀ p : ↥P, (p : G) ∈ B → z p = 1 := by
    intro p hp
    apply Subtype.ext
    change (p : G)⁻¹ * (α p : G) = 1
    rw [hα p hp, inv_mul_cancel]
  obtain ⟨v, hv, hvB, hzv⟩ := exists_eq_of_cocycle_of_odd_relIndex hVc hV2 hVn hodd z hz hzB
  have hv1 : v = 1 := hfix v hv fun b hb => hvB b (hBP hb) hb
  refine MulEquiv.ext fun p => Subtype.ext ?_
  have e := hzv p
  change (p : G)⁻¹ * (α p : G) = _ at e
  rw [hv1, inv_one, mul_one, mul_one, inv_mul_cancel] at e
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp e).symm

end CFSG.Quasithin.F112R.St84

end
