module

public import Mathlib.LinearAlgebra.Charpoly.Basic
import CFSG.LieType.BorelTits.Flag
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec20

namespace L3Linear

theorem sub_one_pow_two_pow {R : Type*} [Ring R] (h2 : (2 : R) = 0) (x : R) (k : ℕ) :
    (x - 1) ^ 2 ^ k = x ^ 2 ^ k - 1 := by
  have h1 : (-1 : R) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, pow_mul, ih]
    set y := x ^ 2 ^ k
    have e : (y - 1) ^ 2 = y ^ 2 - 2 * y + 1 := by noncomm_ring
    rw [e, h2, zero_mul, sub_zero, sub_eq_add_neg, h1]

variable {F : Type*} [Field F] [CharP F 2]

theorem two_eq_zero_end (U : Type*) [AddCommGroup U] [Module F U] :
    (2 : Module.End F U) = 0 := by
  have : (2 : Module.End F U) = algebraMap F (Module.End F U) 2 := (map_ofNat _ 2).symm
  rw [this, CharTwo.two_eq_zero, map_zero]

theorem sq_eq_one_of_pow_two_pow_eq_one {U : Type*} [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] (hU : Module.finrank F U ≤ 2) {φ : Module.End F U} {a : ℕ}
    (hφ : φ ^ 2 ^ a = 1) : φ ^ 2 = 1 := by
  have h2 := two_eq_zero_end (F := F) U
  have hN : IsNilpotent (φ - 1) := ⟨2 ^ a, by rw [sub_one_pow_two_pow h2, hφ, sub_self]⟩
  have hN2 : (φ - 1) ^ Module.finrank F U = 0 := by
    have hc := hN.charpoly_eq_X_pow_finrank
    have h := LinearMap.aeval_self_charpoly (φ - 1)
    rwa [hc, map_pow, Polynomial.aeval_X] at h
  have hsq : (φ - 1) ^ 2 = 0 := by
    rw [← Nat.sub_add_cancel hU, pow_add, hN2, mul_zero]
  have h1 : (-1 : Module.End F U) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  have e : φ ^ 2 = (φ - 1) ^ 2 + 2 * φ - 1 := by noncomm_ring
  rw [e, hsq, h2, zero_mul, add_zero, zero_sub, h1]

variable {V : Type*} [AddCommGroup V] [Module F V]

@[expose] def IsUnipotentRadical (W : Submodule F V) (g : Module.End F V) : Prop :=
  (∀ w ∈ W, g w = w) ∧ ∀ v, g v - v ∈ W

theorem sq_eq_one_of_isUnipotentRadical {W : Submodule F V} {g : Module.End F V}
    (hg : IsUnipotentRadical W g) : g ^ 2 = 1 := by
  have h2 := two_eq_zero_end (F := F) V
  have hsq : (g - 1) ^ 2 = 0 := by
    ext v
    have hv : (g - 1) v ∈ W := by simpa using hg.2 v
    have : ((g - 1) ^ 2 : Module.End F V) v = (g - 1) ((g - 1) v) := by
      rw [sq, Module.End.mul_apply]
    rw [this, LinearMap.zero_apply, LinearMap.sub_apply, Module.End.one_apply, hg.1 _ hv,
      sub_self]
  have h1 : (-1 : Module.End F V) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  have e : g ^ 2 = (g - 1) ^ 2 + 2 * g - 1 := by noncomm_ring
  rw [e, hsq, h2, zero_mul, add_zero, zero_sub, h1]

theorem sq_mem_unipotentRadical_of_pow_two_pow_eq_one [FiniteDimensional F V]
    {W : Submodule F V} (hW : Module.finrank F W ≤ 2) (hVW : Module.finrank F (V ⧸ W) ≤ 2)
    {g : Module.End F V} (hgW : ∀ w ∈ W, g w ∈ W) {a : ℕ} (hg : g ^ 2 ^ a = 1) :
    IsUnipotentRadical W (g ^ 2) := by
  have hle : W ≤ W.comap g := fun w hw => hgW w hw
  constructor
  ·
    intro w hw
    have hr : (g.restrict hgW) ^ 2 ^ a = 1 := by
      rw [Module.End.pow_restrict]
      ext x
      simp [hg]
    have h := sq_eq_one_of_pow_two_pow_eq_one hW hr
    have h' := congrArg (fun f : Module.End F W => ((f ⟨w, hw⟩ : W) : V)) h
    rw [Module.End.pow_restrict] at h'
    simpa using h'
  ·
    intro v
    have hq : (W.mapQ W g hle) ^ 2 ^ a = 1 := by
      rw [← Submodule.mapQ_pow]
      ext x
      simp [hg]
    have h := sq_eq_one_of_pow_two_pow_eq_one hVW hq
    have h' := congrArg (fun f : Module.End F (V ⧸ W) => f (Submodule.Quotient.mk v)) h
    rw [← Submodule.mapQ_pow] at h'
    simp only [Submodule.mapQ_apply, Module.End.one_apply] at h'
    exact (Submodule.Quotient.eq W).mp h'

section SL3

open Matrix
open scoped MatrixGroups

variable (F) in
@[expose] noncomputable def rho3 : SL(3, F) →* Module.End F (Fin 3 → F) where
  toFun g := Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl

theorem rho3_injective : Function.Injective (rho3 F) := by
  intro g h hgh
  exact Subtype.ext (Matrix.toLin'.injective hgh)

@[expose] def fixedSpace (D : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ d ∈ D, rho3 F d v = v}
  add_mem' := by
    intro u v hu hv d hd
    rw [map_add, hu d hd, hv d hd]
  zero_mem' := by
    intro d _
    rw [map_zero]
  smul_mem' := by
    intro c v hv d hd
    rw [map_smul, hv d hd]

@[expose] def unipotentRadical (W : Submodule F (Fin 3 → F)) : Subgroup SL(3, F) where
  carrier := {s | IsUnipotentRadical W (rho3 F s)}
  one_mem' := ⟨fun w _ => by simp, fun v => by simp⟩
  mul_mem' := by
    intro s t hs ht
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [map_mul, Module.End.mul_apply, ht.1 w hw, hs.1 w hw]
    · rw [map_mul, Module.End.mul_apply]
      have e : rho3 F s (rho3 F t v) - v = (rho3 F s (rho3 F t v) - rho3 F t v) +
          (rho3 F t v - v) := by abel
      rw [e]
      exact W.add_mem (hs.2 _) (ht.2 v)
  inv_mem' := by
    intro s hs
    have hss : ∀ v, rho3 F s (rho3 F s⁻¹ v) = v := fun v => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have h := hs.1 (rho3 F s⁻¹ w) ?_
      · rw [hss] at h
        exact h.symm
      ·
        have h1 := hs.2 (rho3 F s⁻¹ w)
        rw [hss] at h1
        have : rho3 F s⁻¹ w = w - (w - rho3 F s⁻¹ w) := by abel
        rw [this]
        exact W.sub_mem hw h1
    · have h1 := hs.2 (rho3 F s⁻¹ v)
      rw [hss] at h1
      have : rho3 F s⁻¹ v - v = -(v - rho3 F s⁻¹ v) := by abel
      rw [this]
      exact W.neg_mem h1

variable [Finite F]

theorem fixedSpace_ne_bot {D : Subgroup SL(3, F)} (hD : IsPGroup 2 D) : fixedSpace D ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv0, hv⟩ :=
    CFSG.LieType.BorelTits.exists_fixed_ne_zero (rho3 F) 2 D hD
  intro hbot
  have hvW : v ∈ fixedSpace D := hv
  rw [hbot, Submodule.mem_bot] at hvW
  exact hv0 hvW

theorem fixedSpace_ne_top {D : Subgroup SL(3, F)} (hD : D ≠ ⊥) : fixedSpace D ≠ ⊤ := by
  intro htop
  apply hD
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  apply rho3_injective
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ fixedSpace D := htop ▸ Submodule.mem_top
  rw [hv d hd, map_one, Module.End.one_apply]

theorem mapsTo_fixedSpace {D : Subgroup SL(3, F)} {s : SL(3, F)}
    (hs : s ∈ Subgroup.normalizer (D : Set SL(3, F))) :
    ∀ w ∈ fixedSpace D, rho3 F s w ∈ fixedSpace D := by
  intro w hw d hd
  have hd' : s⁻¹ * d * s ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) d).mp hd
    simpa using this
  have h := hw _ hd'
  calc rho3 F d (rho3 F s w) = rho3 F s (rho3 F (s⁻¹ * d * s) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = rho3 F s w := by rw [h]

theorem sq_mem_unipotentRadical_of_mem_normalizer {D : Subgroup SL(3, F)} (hD2 : IsPGroup 2 D)
    (hD1 : D ≠ ⊥) {s : SL(3, F)} (hs : s ∈ Subgroup.normalizer (D : Set SL(3, F))) {a : ℕ}
    (ha : s ^ 2 ^ a = 1) : s ^ 2 ∈ unipotentRadical (fixedSpace D) := by
  set W := fixedSpace D with hWdef
  have hW0 : 1 ≤ Module.finrank F W := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact fixedSpace_ne_bot hD2
  have hWt : Module.finrank F W < 3 := by
    have h := Submodule.finrank_lt (s := W) (fixedSpace_ne_top hD1)
    simpa using h
  have hsum := Submodule.finrank_quotient_add_finrank W
  rw [Module.finrank_fin_fun] at hsum
  have hW : Module.finrank F W ≤ 2 := by omega
  have hVW : Module.finrank F ((Fin 3 → F) ⧸ W) ≤ 2 := by omega
  have hg : (rho3 F s) ^ 2 ^ a = 1 := by rw [← map_pow, ha, map_one]
  have h := sq_mem_unipotentRadical_of_pow_two_pow_eq_one hW hVW (mapsTo_fixedSpace hs) hg
  show IsUnipotentRadical W (rho3 F (s ^ 2))
  rwa [map_pow]

theorem sq_mem_pCore_of_le_normalizer {K : Type*} [Group K] [Finite K] (ρ : K →* SL(3, F))
    (hker : IsPGroup 2 ρ.ker) {D : Subgroup SL(3, F)} (hD2 : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hKD : ρ.range ≤ Subgroup.normalizer (D : Set SL(3, F))) {k : K} {a : ℕ}
    (hk : k ^ 2 ^ a = 1) : k ^ 2 ∈ CFSG.pCore 2 K := by
  set W := fixedSpace D with hWdef
  set Q : Subgroup K := (unipotentRadical W).comap ρ with hQdef
  have hQn : Q.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hs : ρ g ∈ Subgroup.normalizer (D : Set SL(3, F)) := hKD ⟨g, rfl⟩
    have hsi : ρ g⁻¹ ∈ Subgroup.normalizer (D : Set SL(3, F)) := hKD ⟨g⁻¹, rfl⟩
    have hx' : IsUnipotentRadical W (rho3 F (ρ x)) := hx
    have hgW := mapsTo_fixedSpace hs
    have hgiW := mapsTo_fixedSpace hsi
    have hgg : ∀ v, rho3 F (ρ g) (rho3 F (ρ g⁻¹) v) = v := fun v => by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
        Module.End.one_apply]
    show IsUnipotentRadical W (rho3 F (ρ (g * x * g⁻¹)))
    have e : ∀ v, rho3 F (ρ (g * x * g⁻¹)) v =
        rho3 F (ρ g) (rho3 F (ρ x) (rho3 F (ρ g⁻¹) v)) := fun v => by
      rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [e, hx'.1 _ (hgiW w hw), hgg]
    · rw [e]
      have h1 := hgW _ (hx'.2 (rho3 F (ρ g⁻¹) v))
      rwa [map_sub, hgg] at h1
  have hQ2 : IsPGroup 2 Q := by
    intro x
    have hx' : IsUnipotentRadical W (rho3 F (ρ x)) := x.2
    have hsq : ρ ((x : K) ^ 2) = 1 := by
      apply rho3_injective
      rw [map_pow, map_pow, sq_eq_one_of_isUnipotentRadical hx', map_one]
    obtain ⟨c, hc⟩ := hker ⟨(x : K) ^ 2, hsq⟩
    refine ⟨c + 1, Subtype.ext ?_⟩
    have hc' : ((x : K) ^ 2) ^ 2 ^ c = 1 := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ, mul_comm, pow_mul]
    exact hc'
  have hQle : Q ≤ CFSG.pCore 2 K := le_sSup ⟨hQn, hQ2⟩
  apply hQle
  have hs : ρ k ∈ Subgroup.normalizer (D : Set SL(3, F)) := hKD ⟨k, rfl⟩
  have hρk : ρ k ^ 2 ^ a = 1 := by rw [← map_pow, hk, map_one]
  have h := sq_mem_unipotentRadical_of_mem_normalizer hD2 hD1 hs hρk
  show ρ (k ^ 2) ∈ unipotentRadical W
  rwa [map_pow]

end SL3

end L3Linear

end CFSG.RankThree.PartTwo.Sec20
