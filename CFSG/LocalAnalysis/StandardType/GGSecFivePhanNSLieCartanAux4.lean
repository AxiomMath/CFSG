module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux3

public section

namespace CFSG.StandardType

open Finset Module CFSG.Open
open scoped IsMulCommutative

variable {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G}

lemma ggNSLiePI2_reflection_data (hp : p.Prime) (hp2 : p ≠ 2) (hel : IsElemAbelian p Bs)
    [Finite Bs] [IsMulCommutative ↥Bs] [Module (ZMod p) (Additive ↥Bs)]
    (t : MulAut ↥Bs) (ht : GGIsReflection p t) :
    ∃ (x : Additive ↥Bs) (g : Module.Dual (ZMod p) (Additive ↥Bs)),
      x ≠ 0 ∧ g x = 2 ∧
      ∀ v, ggNSLiePI2_linearEquivOfMulAut hp t v = v - g v • x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥Bs := Fintype.ofFinite _
  haveI : Fintype (Additive ↥Bs) := Fintype.ofFinite _
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  let T := ggNSLiePI2_linearEquivOfMulAut hp t
  have hT2 : T * T = 1 := by
    apply LinearEquiv.ext
    intro v
    change T (T v) = v
    rw [ggNSLiePI2_linearEquivOfMulAut_apply, ggNSLiePI2_linearEquivOfMulAut_apply]
    change Additive.ofMul (t (t (Additive.toMul v))) = v
    have h := congrArg (fun f : MulAut ↥Bs => f (Additive.toMul v)) ht.1
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    exact (congrArg Additive.ofMul h).trans rfl
  let W : Submodule (ZMod p) (Additive ↥Bs) := LinearMap.ker (T.toLinearMap - 1)
  have hTfix : ∀ w ∈ W, T w = w := by
    intro w hw
    have h := LinearMap.mem_ker.mp hw
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have hWcard : Nat.card ↥W * p = Nat.card (Additive ↥Bs) := by
    have he : Nat.card ↥W = Nat.card {b : ↥Bs // t b = b} := by
      apply Nat.card_congr
      exact {
        toFun := fun w => ⟨Additive.toMul w.1, by
          have h : T w.1 = w.1 := hTfix w.1 w.2
          rw [ggNSLiePI2_linearEquivOfMulAut_apply] at h
          exact Additive.ofMul.injective h⟩
        invFun := fun b => ⟨Additive.ofMul b.1, by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
          change Additive.ofMul (t b.1) - Additive.ofMul b.1 = 0
          rw [b.2, sub_self]⟩
        left_inv := fun w => by apply Subtype.ext; rfl
        right_inv := fun b => by apply Subtype.ext; rfl }
    rw [he]
    exact ht.2
  have hfinW : Module.finrank (ZMod p) ↥W + 1 = Module.finrank (ZMod p) (Additive ↥Bs) := by
    haveI : Fintype ↥W := Fintype.ofFinite ↥W
    haveI : Fintype (Additive ↥Bs) := Fintype.ofFinite (Additive ↥Bs)
    haveI : Fintype (ZMod p) := ZMod.fintype p
    have hcardW : Nat.card ↥W = p ^ Module.finrank (ZMod p) ↥W := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := ↥W),
        ZMod.card p]
    have hcardV : Nat.card (Additive ↥Bs) = p ^ Module.finrank (ZMod p) (Additive ↥Bs) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := Additive ↥Bs),
        ZMod.card p]
    have hcard : Nat.card ↥W * p = Nat.card (Additive ↥Bs) := hWcard
    rw [hcardW, hcardV, ← pow_succ] at hcard
    exact Nat.pow_right_injective hp.two_le hcard
  haveI : Fintype ↥W := Fintype.ofFinite _
  have hTne : T ≠ 1 := by
    intro hT1
    have hWtop : W = ⊤ := by
      apply top_unique
      intro v _
      rw [LinearMap.mem_ker, LinearMap.sub_apply]
      rw [show T.toLinearMap = 1 from by rw [hT1]; rfl]
      simp
    have hc : Nat.card ↥W * p = Nat.card (Additive ↥Bs) := hWcard
    have htop : Nat.card ↥W = Nat.card (Additive ↥Bs) := by rw [hWtop]; simp
    rw [htop] at hc
    have hpos : 0 < Nat.card (Additive ↥Bs) := Nat.card_pos
    exact hp.ne_one (Nat.mul_left_cancel hpos (by simpa using hc))
  obtain ⟨v0, hv0⟩ : ∃ v0 : Additive ↥Bs, T v0 ≠ v0 := by
    by_contra h
    push Not at h
    exact hTne (LinearEquiv.ext h)
  let x : Additive ↥Bs := T v0 - v0
  have hx0 : x ≠ 0 := sub_ne_zero.mpr hv0
  have hTx : T x = -x := by
    change T (T v0 - v0) = -(T v0 - v0)
    rw [map_sub, show T (T v0) = v0 from by
      rw [← LinearEquiv.mul_apply, hT2]; rfl]
    abel
  have hxW : x ∉ W := by
    intro hxW
    have h : T x = x := hTfix x hxW
    rw [hTx] at h
    have hxx : (2 : ZMod p) • x = 0 := by
      rw [two_smul]
      nth_rewrite 2 [← h]
      abel
    exact hx0 ((smul_eq_zero.mp hxx).resolve_left h2)
  have hrange : LinearMap.range (T.toLinearMap + 1) = W := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
        map_add]
      change T (T v) + T v - (T v + v) = 0
      rw [show T (T v) = v from by rw [← LinearEquiv.mul_apply, hT2]; rfl]
      abel
    · intro w hw
      refine ⟨(2 : ZMod p)⁻¹ • w, ?_⟩
      change T (((2 : ZMod p)⁻¹) • w) + ((2 : ZMod p)⁻¹) • w = w
      rw [map_smul, hTfix w hw, ← add_smul]
      have : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by
        rw [← two_mul, mul_inv_cancel₀ h2]
      rw [this, one_smul]
  have hfinL : Module.finrank (ZMod p) (LinearMap.ker (T.toLinearMap + 1)) = 1 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (T.toLinearMap + 1)
    rw [hrange] at hrk
    omega
  have hxL : x ∈ LinearMap.ker (T.toLinearMap + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    change T x + x = 0
    rw [hTx]
    abel
  have hL : LinearMap.ker (T.toLinearMap + 1) = Submodule.span (ZMod p) {x} := by
    apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxL
    · rw [finrank_span_singleton hx0, hfinL]
  obtain ⟨f, hfx, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW
    (inferInstance : Projective (ZMod p) (Additive ↥Bs ⧸ W))
  let g : Module.Dual (ZMod p) (Additive ↥Bs) := (2 / f x) • f
  have hgx : g x = 2 := by
    simp only [g, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hgW : ∀ w ∈ W, g w = 0 := by
    intro w hw
    have hfw : f w = 0 := by
      have hmem : f w ∈ Submodule.map f W := Submodule.mem_map_of_mem hw
      rw [hfW] at hmem
      simpa using hmem
    simp [g, hfw]
  refine ⟨x, g, hx0, hgx, ?_⟩
  intro v
  have hvW : ((2 : ZMod p)⁻¹) • (v + T v) ∈ W := by
    change (T.toLinearMap - 1) (((2 : ZMod p)⁻¹) • (v + T v)) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply]
    have hTT : T (T v) = v := by rw [← LinearEquiv.mul_apply, hT2]; rfl
    change T (((2 : ZMod p)⁻¹) • (v + T v)) - ((2 : ZMod p)⁻¹) • (v + T v) = 0
    rw [map_smul, map_add, hTT]
    module
  have hvL : ((2 : ZMod p)⁻¹) • (v - T v) ∈ LinearMap.ker (T.toLinearMap + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    have hTT : T (T v) = v := by rw [← LinearEquiv.mul_apply, hT2]; rfl
    change T (((2 : ZMod p)⁻¹) • (v - T v)) + ((2 : ZMod p)⁻¹) • (v - T v) = 0
    rw [map_smul, map_sub, hTT]
    module
  rw [hL, Submodule.mem_span_singleton] at hvL
  obtain ⟨c, hc⟩ := hvL
  have hvc : v - T v = (2 : ZMod p) • (c • x) := by
    rw [hc, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hgv : g v = 2 * c := by
    have hsplit : v = ((2 : ZMod p)⁻¹) • (v + T v) + ((2 : ZMod p)⁻¹) • (v - T v) := by
      rw [← smul_add]
      have hsum : v + T v + (v - T v) = (2 : ZMod p) • v := by
        rw [two_smul]; abel
      rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hsplit, map_add, hgW _ hvW, ← hc, map_smul, hgx]
    ring
  rw [hgv]
  rw [show v - (2 * c) • x = T v by rw [← smul_smul, ← hvc]; abel]

end CFSG.StandardType

end
