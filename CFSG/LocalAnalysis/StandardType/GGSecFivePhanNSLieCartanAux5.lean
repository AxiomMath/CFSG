module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux4

public section

namespace CFSG.StandardType

open Finset Module CFSG.Open
open scoped IsMulCommutative

variable {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G}

lemma ggNSLiePI2_same_line {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {r s : V ≃ₗ[K] V} {x y : V} {f g : Module.Dual K V} (h2 : (2 : K) ≠ 0)
    (hr : ∀ v, r v = v - f v • x) (hs : ∀ v, s v = v - g v • y)
    (hgy : g y = 2) (hfy : f y ≠ 0) (hcomm : r * s = s * r) :
    x ∈ Submodule.span K {y} := by
  have hsy : s y = -y := by rw [hs y, hgy, two_smul]; abel
  have hcomm' := congrArg (fun T : V ≃ₗ[K] V => T y) hcomm
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsy, map_neg] at hcomm'
  have hry : r y ∈ Submodule.span K {y} := by
    have h := hcomm'.symm
    rw [hs] at h
    have h2r : (2 : K) • r y = g (r y) • y := by
      set z := g (r y) • y with hz
      have h' : r y - z = -r y := h
      have hzy : r y + r y = z := by
        rw [← sub_eq_zero]
        rw [add_sub_assoc]
        rw [h']
        abel
      rw [two_smul]
      exact hzy
    rw [Submodule.mem_span_singleton]
    refine ⟨g (r y) / 2, ?_⟩
    rw [div_eq_inv_mul, mul_smul, ← h2r, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hmem : f y • x ∈ Submodule.span K {y} := by
    have h1 : y - f y • x ∈ Submodule.span K {y} := by rw [← hr y]; exact hry
    have h2' : y ∈ Submodule.span K {y} := Submodule.mem_span_singleton_self y
    have := Submodule.sub_mem _ h2' h1
    simpa using this
  have hx : x = (f y)⁻¹ • (f y • x) := by rw [smul_smul, inv_mul_cancel₀ hfy, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hmem

lemma ggNSLiePI2_linearEquivOfMulAut_mul (hp : p.Prime) [IsMulCommutative ↥Bs]
    [Module (ZMod p) (Additive ↥Bs)] (t t' : MulAut ↥Bs) :
    ggNSLiePI2_linearEquivOfMulAut hp (t * t') =
      ggNSLiePI2_linearEquivOfMulAut hp t * ggNSLiePI2_linearEquivOfMulAut hp t' := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, ggNSLiePI2_linearEquivOfMulAut_apply,
    ggNSLiePI2_linearEquivOfMulAut_apply, ggNSLiePI2_linearEquivOfMulAut_apply]
  rfl

lemma ggNSLiePI2_linearEquivOfMulAut_one (hp : p.Prime) [IsMulCommutative ↥Bs]
    [Module (ZMod p) (Additive ↥Bs)] :
    ggNSLiePI2_linearEquivOfMulAut hp (1 : MulAut ↥Bs) = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [ggNSLiePI2_linearEquivOfMulAut_apply]
  simp

lemma ggNSLiePI2_linearEquivOfMulAut_injective (hp : p.Prime) [IsMulCommutative ↥Bs]
    [Module (ZMod p) (Additive ↥Bs)] :
    Function.Injective (ggNSLiePI2_linearEquivOfMulAut (p := p) (Bs := Bs) hp) := by
  intro t t' h
  ext b
  have hv := congrArg (fun T : Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs =>
    T (Additive.ofMul b)) h
  simp only [ggNSLiePI2_linearEquivOfMulAut_apply] at hv
  exact Additive.ofMul.injective (by simpa using hv)

lemma ggNSLiePI2_transvection_of_same_line (hp : p.Prime) (hp2 : p ≠ 2)
    (hel : IsElemAbelian p Bs) [Finite Bs] [IsMulCommutative ↥Bs]
    [Module (ZMod p) (Additive ↥Bs)]
    (t t' : MulAut ↥Bs) (ht : GGIsReflection p t) (ht' : GGIsReflection p t')
    {x x' : Additive ↥Bs} {g g' : Module.Dual (ZMod p) (Additive ↥Bs)}
    (hgx : g x = 2) (hgx' : g' x' = 2)
    (htn : ∀ v, ggNSLiePI2_linearEquivOfMulAut hp t v = v - g v • x)
    (htn' : ∀ v, ggNSLiePI2_linearEquivOfMulAut hp t' v = v - g' v • x')
    (hline : x ∈ Submodule.span (ZMod p) {x'}) :
    t * t' = 1 ∨ GGIsTransvection p (t * t') := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥Bs := Fintype.ofFinite _
  haveI : Fintype (Additive ↥Bs) := Fintype.ofFinite _
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  let T := ggNSLiePI2_linearEquivOfMulAut hp t
  let T' := ggNSLiePI2_linearEquivOfMulAut hp t'
  let U := T * T'
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hgx; exact h2 hgx.symm
  have hTx : T x = -x := by rw [htn, hgx, two_smul]; abel
  have hT'x' : T' x' = -x' := by rw [htn', hgx', two_smul]; abel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hc; exact hx0 hc.symm
  have hx' : x' = c⁻¹ • x := by
    rw [← hc, smul_smul]
    rw [show c⁻¹ * c = 1 from inv_mul_cancel₀ (a := c) hc0, one_smul]
  have hTx' : T x' = -x' := by
    rw [hx', map_smul, hTx, smul_neg, ← hx']
  have hT'x : T' x = -x := by
    rw [← hc, map_smul, hT'x', smul_neg]
  have hUx : U x = x := by
    rw [show U = T * T' from rfl, LinearEquiv.mul_apply, hT'x, map_neg, hTx, neg_neg]
  have hUv : ∀ v, U v - v ∈ Submodule.span (ZMod p) {x} := by
    intro v
    rw [Submodule.mem_span_singleton]
    refine ⟨-g v + g' v * c⁻¹, ?_⟩
    have hUv_eq : U v = v - g v • x + g' v • x' := by
      change T (T' v) = v - g v • x + g' v • x'
      rw [htn', map_sub, map_smul, htn, hTx']
      module
    rw [hUv_eq, hx', smul_smul]
    have hsc : -g v + g' v * c⁻¹ = g' v * c⁻¹ - g v := neg_add_eq_sub _ _
    rw [hsc, sub_smul]
    abel
  have hUsq : ∀ v, U (U v - v) = U v - v := by
    intro v
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hUv v)
    rw [← hk, map_smul, hUx]
  by_cases hU1 : U = 1
  · left
    have hlin : ggNSLiePI2_linearEquivOfMulAut hp (t * t') = 1 := by
      rw [ggNSLiePI2_linearEquivOfMulAut_mul]
      exact hU1
    exact ggNSLiePI2_linearEquivOfMulAut_injective hp
      (by rw [hlin, ggNSLiePI2_linearEquivOfMulAut_one])
  · right
    have hUeq : U = ggNSLiePI2_linearEquivOfMulAut hp (t * t') := by
      rw [show U = T * T' from rfl, ← ggNSLiePI2_linearEquivOfMulAut_mul]
    haveI : Nontrivial (Additive ↥Bs) := ⟨x, 0, hx0⟩
    have hU1' : (U.toLinearMap - 1 : Additive ↥Bs →ₗ[ZMod p] Additive ↥Bs) ≠ 0 := by
      intro h0
      apply hU1
      apply LinearEquiv.ext
      intro v
      have hv : (U.toLinearMap - 1) v = 0 := by rw [h0, LinearMap.zero_apply]
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      exact hv
    have hrange : LinearMap.range (U.toLinearMap - 1) = Submodule.span (ZMod p) {x} := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [LinearMap.sub_apply, Module.End.one_apply]
        exact hUv v
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨v, hv⟩ : ∃ v, (U.toLinearMap - 1) v ≠ 0 := by
          by_contra h
          push Not at h
          exact hU1' (LinearMap.ext h)
        obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hUv v)
        have hk0 : k ≠ 0 := by
          intro hk0; rw [hk0, zero_smul] at hk; exact hv hk.symm
        refine ⟨k⁻¹ • v, ?_⟩
        change (U.toLinearMap - 1) (k⁻¹ • v) = x
        rw [map_smul, LinearMap.sub_apply, Module.End.one_apply]
        change k⁻¹ • (U v - v) = x
        rw [← hk, smul_smul, inv_mul_cancel₀ hk0, one_smul]
    have hfin : Module.finrank (ZMod p) (LinearMap.ker (U.toLinearMap - 1)) =
        Module.finrank (ZMod p) (Additive ↥Bs) - 1 := by
      have hrk := LinearMap.finrank_range_add_finrank_ker (U.toLinearMap - 1)
      rw [hrange, finrank_span_singleton hx0] at hrk
      omega
    have hcardker : Nat.card ↥(LinearMap.ker (U.toLinearMap - 1)) * p = Nat.card (Additive ↥Bs) := by
      haveI : Fintype ↥(LinearMap.ker (U.toLinearMap - 1)) := Fintype.ofFinite _
      haveI : Fintype (ZMod p) := ZMod.fintype p
      have hker : Nat.card ↥(LinearMap.ker (U.toLinearMap - 1)) =
          p ^ Module.finrank (ZMod p) ↥(LinearMap.ker (U.toLinearMap - 1)) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p)
          (V := ↥(LinearMap.ker (U.toLinearMap - 1))), ZMod.card p]
      have hV : Nat.card (Additive ↥Bs) = p ^ Module.finrank (ZMod p) (Additive ↥Bs) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := Additive ↥Bs),
          ZMod.card p]
      rw [hker, hV, hfin, ← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt
        (Module.finrank_pos (R := ZMod p) (M := Additive ↥Bs)))]
    have hfix : Nat.card {b : ↥Bs // (t * t') b = b} =
        Nat.card ↥(LinearMap.ker (U.toLinearMap - 1)) := by
      apply Nat.card_congr
      exact {
        toFun := fun b => ⟨Additive.ofMul b.1, by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hUeq]
          show ggNSLiePI2_linearEquivOfMulAut hp (t * t') (Additive.ofMul b.1) = Additive.ofMul b.1
          rw [ggNSLiePI2_linearEquivOfMulAut_apply]
          exact congrArg Additive.ofMul b.2⟩
        invFun := fun v => ⟨Additive.toMul v.1, by
          have hv : U v.1 = v.1 := by
            have := LinearMap.mem_ker.mp v.2
            rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
          have hv' : ggNSLiePI2_linearEquivOfMulAut hp (t * t') v.1 = v.1 :=
            Eq.mp (congrArg (fun T : Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs => T v.1 = v.1) hUeq) hv
          have h := congrArg Additive.toMul hv'
          rw [ggNSLiePI2_linearEquivOfMulAut_apply] at h
          simpa using h⟩
        left_inv := fun b => by apply Subtype.ext; rfl
        right_inv := fun v => by apply Subtype.ext; rfl }
    refine ⟨?_, ?_⟩
    · rw [hfix]; exact hcardker
    · intro b
      have hv := hUsq (Additive.ofMul b)
      have harg : Additive.ofMul (b⁻¹ * (t * t') b) = U (Additive.ofMul b) - Additive.ofMul b := by
        rw [hUeq, ggNSLiePI2_linearEquivOfMulAut_apply]
        show Additive.ofMul (b⁻¹ * (t * t') b) =
          Additive.ofMul ((t * t') b) - Additive.ofMul b
        first
          | (rw [ofMul_mul, ofMul_inv]; abel)
          | (show -Additive.ofMul b + Additive.ofMul ((t * t') b) =
              Additive.ofMul ((t * t') b) - Additive.ofMul b; abel)
      have hgoal : ggNSLiePI2_linearEquivOfMulAut hp (t * t')
          (Additive.ofMul (b⁻¹ * (t * t') b)) = Additive.ofMul (b⁻¹ * (t * t') b) := by
        rw [harg]
        exact hv
      have h := congrArg Additive.toMul hgoal
      rw [ggNSLiePI2_linearEquivOfMulAut_apply] at h
      simpa using h

end CFSG.StandardType

end
