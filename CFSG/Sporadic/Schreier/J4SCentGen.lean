module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.LinearAlgebra.BinaryReflectionNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import Mathlib.Tactic.NormNum.Prime

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.LinearAlgebra CFSG.LocalAnalysis.ComponentInitial Module
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_one_of_mul_self_eq_one_of_isField {K : Type*} [Semiring K] [Algebra (ZMod 2) K]
    (hK : IsField K) {u : K} (hu : u * u = 1) : u = 1 := by
  have h2 : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two, ← map_ofNat (algebraMap (ZMod 2) K) 2,
      show (2 : ZMod 2) = 0 from rfl, map_zero]
  have huu : u + u = 0 := by rw [← two_mul, ← one_add_one_eq_two, h2, zero_mul]
  have hsq : (u + 1) * (u + 1) = 0 := by
    rw [add_mul, mul_add, mul_add, hu, mul_one, one_mul, one_mul]
    calc 1 + u + (u + 1) = (1 + 1) + (u + u) := by abel
      _ = 0 := by rw [h2, huu, add_zero]
  have hu1 : u + 1 = 0 := by
    by_contra hne
    obtain ⟨v, hv⟩ := hK.mul_inv_cancel hne
    apply hne
    calc u + 1 = (u + 1) * ((u + 1) * v) := by rw [hv, mul_one]
      _ = 0 := by rw [← mul_assoc, hsq, zero_mul]
  calc u = u + (1 + 1) := by rw [h2, add_zero]
    _ = (u + 1) + 1 := by rw [add_assoc]
    _ = 1 := by rw [hu1, zero_add]

theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 11 - 1 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_zmod_two (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem finrank_range_le_one {U W : Submodule (ZMod 2) V} [FiniteDimensional (ZMod 2) V]
    (hUW : IsCompl U W) (hU : finrank (ZMod 2) U = 2) {N : V →ₗ[ZMod 2] V}
    (hW : ∀ w ∈ W, N w = 0) (hNU : LinearMap.range N ≤ U) (hNN : ∀ v, N (N v) = 0)
    (hN : N ≠ 0) : finrank (ZMod 2) (LinearMap.range N) = 1 := by
  have hle : finrank (ZMod 2) (LinearMap.range N) ≤ 2 :=
    calc finrank (ZMod 2) (LinearMap.range N) ≤ finrank (ZMod 2) U := Submodule.finrank_mono hNU
      _ = 2 := hU
  have hne : finrank (ZMod 2) (LinearMap.range N) ≠ 0 := by
    intro h
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    exact hN h
  have hne2 : finrank (ZMod 2) (LinearMap.range N) ≠ 2 := by
    intro h2
    have heq : LinearMap.range N = U := Submodule.eq_of_le_of_finrank_eq hNU (h2.trans hU.symm)
    apply hN
    ext v
    have hv : v ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [← heq] at hu
    obtain ⟨v', rfl⟩ := hu
    rw [map_add, hNN, hW w hw, add_zero, LinearMap.zero_apply]
  omega

theorem odd_card_pointwiseFixingAut_of_realization {G : Type*} [Group G] [Finite G]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    (hnd : (QuadraticMap.polarBilin q).Nondegenerate) (Λ : G →* (V ≃ₗ[ZMod 2] V))
    (hΛ : Function.Injective Λ) (hΛq : Λ.range ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hsmall : ∀ g ∈ Λ.range, (orderOf g = 2 ∨ orderOf g = 3) →
      3 ≤ finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)))
    (ρA : MulAut G →* (V ≃ₗ[ZMod 2] V)) (hρA : Function.Injective ρA)
    (hρAq : ∀ α, ρA α ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hρAc : ∀ α h, Λ (α h) = ρA α * Λ h * (ρA α)⁻¹)
    {Q : Subgroup G} (hQ : IsExtraspecialPGroup 11 Q) (hQc : Nat.card Q = 11 ^ 3)
    (hQe : Monoid.exponent Q = 11) {x y z : Q} (hgen : Subgroup.closure {x, y} = ⊤)
    (hz : z = ⁅x, y⁆) (hV : finrank (ZMod 2) V = 112)
    (hU : finrank (ZMod 2)
      (LinearMap.ker (((Λ z : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1)) = 2) :
    Odd (Nat.card (pointwiseFixingAut Q)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
  by_contra hodd
  have h2 : 2 ∣ Nat.card (pointwiseFixingAut Q) := by
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨⟨α, hα⟩, hord⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [← Subgroup.orderOf_coe] at hord
  dsimp only at hord
  have hα1 : α ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hα2 : α * α = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
  set a := ρA α with ha
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, hα2, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hα1
    apply hρA
    rw [← ha, h, map_one]
  have hfix : ∀ g ∈ Q, α g = g := (mem_pointwiseFixingAut.1 hα)
  have hcomm : ∀ g ∈ Q, a * Λ g = Λ g * a := by
    intro g hg
    have e := hρAc α g
    rw [hfix g hg, ← ha] at e
    calc a * Λ g = a * Λ g * a⁻¹ * a := by rw [inv_mul_cancel_right]
      _ = Λ g * a := by rw [← e]
  set ρ : Representation (ZMod 2) Q V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp (Λ.comp Q.subtype) with hρ
  obtain ⟨hcompl, -, hfield, -, -, -, -, -, e, he⟩ :=
    extraspecial_prime_cyclotomic_minimal_module (p := 11) (by norm_num) orderOf_two_zmod_eleven hQ
      hQc hQe hgen hz ρ (r := 2) (by norm_num) (by rw [hV]) hU
  set a' : LinearMap.GeneralLinearGroup (ZMod 2) V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm a with ha'
  have ha'v : ∀ v, (a' : V →ₗ[ZMod 2] V) v = a v := fun v => rfl
  have hmem : a' ∈ Subgroup.centralizer (Set.range ρ.asGroupHom) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    rw [Units.val_mul, Units.val_mul, Representation.asGroupHom_apply, Module.End.mul_apply,
      Module.End.mul_apply, ha'v, ha'v]
    have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) (hcomm g g.2)
    simp only [LinearEquiv.mul_apply] at h
    exact h.symm
  set c : Subgroup.centralizer (Set.range ρ.asGroupHom) := ⟨a', hmem⟩
  have hc2 : c * c = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    show (a' : V →ₗ[ZMod 2] V) ((a' : V →ₗ[ZMod 2] V) v) = v
    rw [ha'v, ha'v, ← LinearEquiv.mul_apply, ha2]
    rfl
  have hk : (((e c).2 : (centralImageAlgebra ρ z)ˣ) : centralImageAlgebra ρ z) = 1 := by
    refine eq_one_of_mul_self_eq_one_of_isField hfield ?_
    have h1 := congrArg (fun t => ((t.2 : (centralImageAlgebra ρ z)ˣ) : centralImageAlgebra ρ z))
      (map_mul e c c)
    simp only [hc2, map_one, Prod.snd_one, Units.val_one, Prod.snd_mul, Units.val_mul] at h1
    exact h1.symm
  have haW : ∀ w ∈ centralImage ρ z, a w = w := by
    intro w hw
    have h := (he c).2 ⟨w, hw⟩
    rw [hk] at h
    simp only [OneMemClass.coe_one, Module.End.one_apply] at h
    rw [← ha'v]
    exact h.symm
  have haU : ∀ u ∈ centralFixed ρ z, a u ∈ centralFixed ρ z := by
    intro u hu
    have h := (he c).1 ⟨u, hu⟩
    rw [← ha'v, ← h]
    exact Subtype.coe_prop _
  set N : V →ₗ[ZMod 2] V := (a : V →ₗ[ZMod 2] V) - LinearMap.id with hN
  have hNW : ∀ w ∈ centralImage ρ z, N w = 0 := by
    intro w hw
    rw [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, haW w hw, LinearMap.id_apply, sub_self]
  have hNU : LinearMap.range N ≤ centralFixed ρ z := by
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ centralFixed ρ z ⊔ centralImage ρ z := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hNW w hw, add_zero, hN, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply]
    exact (centralFixed ρ z).sub_mem (haU u hu) hu
  have hNN : ∀ v, N (N v) = 0 := by
    intro v
    have e1 : a (a v) = v := by rw [← LinearEquiv.mul_apply, ha2]; rfl
    rw [hN, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.id_apply]
    simp only [LinearEquiv.coe_coe]
    rw [map_sub, e1]
    have key : v - a v - (a v - v) = (v + v) - (a v + a v) := by abel
    rw [key, add_self_zmod_two, add_self_zmod_two, sub_zero]
  have hN0 : N ≠ 0 := by
    intro h
    apply ha1
    apply LinearEquiv.ext
    intro v
    have h1 := congrArg (fun f : V →ₗ[ZMod 2] V => f v) h
    simp only [hN, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero, LinearEquiv.coe_coe,
      LinearMap.id_apply] at h1
    rw [h1]
    rfl
  have hrk : finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) = 1 :=
    finrank_range_le_one hcompl hU hNW hNU hNN hN0
  have haN : a ∈ Subgroup.normalizer (Λ.range : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨α g, by rw [hρAc α g]⟩
    · rintro ⟨g, hg⟩
      refine ⟨α⁻¹ g, ?_⟩
      rw [hρAc α⁻¹ g, map_inv, ← ha, hg]
      group
  have hcent := binary_reflection_normalizer_small_rank_obstruction hnd hΛq hsmall (hρAq α) haN
    hrk
  apply hα1
  apply MulEquiv.ext
  intro h
  apply hΛ
  rw [hρAc α h, ← ha, hcent (Λ h) ⟨h, rfl⟩, mul_inv_cancel_right, MulAut.one_apply]

end CFSG.Sporadic.J4Schreier
