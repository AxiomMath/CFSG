module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJXRoots
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def ggTBJXRefl (p : ℕ) [Fact p.Prime] (τ : Tag) (β : Fin τ.rank → ℤ)
    (w : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  fun i => w i - ggTBJXFun p τ β w * ggTBJXVec p τ β i

private theorem ggTBJX_refl_aux_inv {R : Type} [CommRing R] (a x v : R) :
    a - x * v - (-x) * v = a := by
  ring

private theorem ggTBJX_refl_aux_sub_eq_self {R : Type} [CommRing R] {a b : R} (h : a - b = a) :
    b = 0 := by
  have h' : a + -b = a + 0 := by simpa using h
  exact neg_eq_zero.mp (add_left_cancel h')

private theorem ggTBJX_refl_aux_sub_zero {R : Type} [CommRing R] (a : R) : a - 0 = a := by
  ring

theorem ggTBJX_reflAut_ofAdd (p : ℕ) [Fact p.Prime] {τ : Tag} {β : Fin τ.rank → ℤ}
    (h : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2) (w : Fin τ.rank → ZMod p) :
    ggTBJXReflAut p τ β (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd (ggTBJXRefl p τ β w) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [ggTBJXReflAut_apply p τ h, toAdd_ofAdd, toAdd_ofAdd]
  rfl

theorem ggTBJX_reflAut_sq (p : ℕ) [Fact p.Prime] {τ : Tag} {β : Fin τ.rank → ℤ}
    (h : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2) :
    ggTBJXReflAut p τ β ^ 2 = 1 := by
  apply MulEquiv.ext
  intro f
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  funext i
  have htoAdd : Multiplicative.toAdd (ggTBJXReflAut p τ β f) =
      fun i => Multiplicative.toAdd f i -
        ggTBJXFun p τ β (Multiplicative.toAdd f) * ggTBJXVec p τ β i :=
    funext fun i => ggTBJXReflAut_apply p τ h f i
  rw [ggTBJXReflAut_apply p τ h (ggTBJXReflAut p τ β f) i, htoAdd,
    ggTBJXFun_sub_smul_vec p τ h (Multiplicative.toAdd f)]
  exact ggTBJX_refl_aux_inv _ _ _

theorem ggTBJX_card_fixed_mul (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {τ : Tag}
    {β : Fin τ.rank → ℤ} (h : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2) :
    Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) // ggTBJXReflAut p τ β f = f} * p =
      p ^ τ.rank := by
  have hv : ggTBJXVec p τ β ≠ 0 := by
    intro h0
    have h2 : ggTBJXFun p τ β (ggTBJXVec p τ β) = 0 := by rw [h0, map_zero]
    rw [h] at h2
    exact zmod_two_ne_zero hp2 h2
  have hvi : ∃ i, ggTBJXVec p τ β i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  have hfix : ∀ a : Multiplicative (Fin τ.rank → ZMod p),
      ggTBJXReflAut p τ β a = a ↔ Multiplicative.toAdd a ∈ LinearMap.ker (ggTBJXFun p τ β) := by
    intro a
    constructor
    · intro ha
      rw [LinearMap.mem_ker]
      obtain ⟨i0, hi0⟩ := hvi
      have hcoord := congrFun (congrArg Multiplicative.toAdd ha) i0
      rw [ggTBJXReflAut_apply p τ h a i0] at hcoord
      have hmul : ggTBJXFun p τ β (Multiplicative.toAdd a) * ggTBJXVec p τ β i0 = 0 :=
        ggTBJX_refl_aux_sub_eq_self hcoord
      exact (mul_eq_zero.mp hmul).resolve_right hi0
    · intro ha
      apply Multiplicative.toAdd.injective
      funext i
      rw [ggTBJXReflAut_apply p τ h a i, LinearMap.mem_ker.mp ha, zero_mul]
      exact ggTBJX_refl_aux_sub_zero _
  have hcard : Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) // ggTBJXReflAut p τ β f = f} =
      Nat.card ↥(LinearMap.ker (ggTBJXFun p τ β)) :=
    Nat.card_congr
      (Equiv.subtypeEquiv
        (Multiplicative.toAdd : Multiplicative (Fin τ.rank → ZMod p) ≃ (Fin τ.rank → ZMod p)) hfix)
  have hne : (ggTBJXFun p τ β : Module.Dual (ZMod p) (Fin τ.rank → ZMod p)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun l : Module.Dual (ZMod p) (Fin τ.rank → ZMod p) =>
      l (ggTBJXVec p τ β)) h0
    simp only [LinearMap.zero_apply] at h1
    rw [h] at h1
    exact zmod_two_ne_zero hp2 h1
  have hsurj : Function.Surjective (ggTBJXFun p τ β) := by
    intro y
    have hx : ∃ x, ggTBJXFun p τ β x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (LinearMap.ext fun x => by simpa using hcon x)
    obtain ⟨x, hx⟩ := hx
    refine ⟨(y * (ggTBJXFun p τ β x)⁻¹) • x, ?_⟩
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]
  have hVcard : Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have heq : Nat.card ↥(LinearMap.ker (ggTBJXFun p τ β)) =
      Nat.card (ggTBJXFun p τ β).toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]; exact LinearMap.mem_ker)
  have hker := AddSubgroup.card_ker_mul_card_range (ggTBJXFun p τ β).toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_zmod, hVcard] at hker
  rw [hcard.trans heq]
  exact hker

end CFSG.StandardType

end
