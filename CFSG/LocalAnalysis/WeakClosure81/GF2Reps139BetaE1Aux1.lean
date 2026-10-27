module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {M : Type} [CommGroup M] [Finite M]

@[expose] noncomputable def w1369LinHom (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)] :
    MulAut M →* Module.End (ZMod 2) (Additive M) where
  toFun c := (autAddHom c).toZModLinearMap 2
  map_one' := by
    ext v
    rfl
  map_mul' c d := by
    ext v
    rfl

@[simp] theorem w1369LinHom_apply (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    (c : MulAut M) (v : Additive M) :
    w1369LinHom hw2 c v = autAddHom c v := rfl

@[simp] theorem w1369LinHom_ofMul (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    (c : MulAut M) (m : M) :
    w1369LinHom hw2 c (Additive.ofMul m) = Additive.ofMul (c m) := rfl

@[expose] noncomputable def w1369SubmoduleToSubgroup [Module (ZMod 2) (Additive M)]
    (U : Submodule (ZMod 2) (Additive M)) :
    Subgroup M where
  carrier := {m | Additive.ofMul m ∈ U}
  one_mem' := by simpa using U.zero_mem
  mul_mem' := by
    intro a b ha hb
    change Additive.ofMul (a * b) ∈ U
    rw [ofMul_mul]
    exact U.add_mem ha hb
  inv_mem' := by
    intro a ha
    change Additive.ofMul a⁻¹ ∈ U
    rw [ofMul_inv]
    exact U.neg_mem ha

@[simp] theorem w1369SubmoduleToSubgroup_ofMul [Module (ZMod 2) (Additive M)]
    {U : Submodule (ZMod 2) (Additive M)} {m : M} :
    m ∈ w1369SubmoduleToSubgroup U ↔ Additive.ofMul m ∈ U := Iff.rfl

theorem w1369_hirrSubmodule (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥) :
    ∀ U : Submodule (ZMod 2) (Additive M),
      (∀ k ∈ K, ∀ u ∈ U, w1369LinHom hw2 k u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hS : ∀ k ∈ K, ∀ u ∈ w1369SubmoduleToSubgroup U, k u ∈ w1369SubmoduleToSubgroup U := by
    intro k hk u hu
    rw [w1369SubmoduleToSubgroup_ofMul] at hu ⊢
    have := hU k hk (Additive.ofMul u) hu
    simpa using this
  have hmain : ∀ J : Subgroup M, (∀ k ∈ K, ∀ u ∈ J, k u ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJ => hirr.2.2.2 J hJ bot_le le_top
  rcases hmain (w1369SubmoduleToSubgroup U) hS with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hmem : Additive.toMul v ∈ w1369SubmoduleToSubgroup U := hv
    rw [h, Subgroup.mem_bot] at hmem
    simpa using congrArg Additive.ofMul hmem
  · right
    rw [Submodule.eq_top_iff']
    intro v
    have hmem : Additive.toMul v ∈ w1369SubmoduleToSubgroup U := by
      rw [h]; exact Subgroup.mem_top _
    exact hmem

noncomputable def w1369E (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    (K : Subgroup (MulAut M)) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) (Additive M)) :=
  Subalgebra.centralizer (ZMod 2) (Set.range fun k : K => w1369LinHom hw2 (k : MulAut M))

theorem w1369_mem_E_iff (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {e : Module.End (ZMod 2) (Additive M)} :
    e ∈ w1369E hw2 K ↔ ∀ k ∈ K, w1369LinHom hw2 k * e = e * w1369LinHom hw2 k := by
  unfold w1369E
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro he k hk
    exact he (w1369LinHom hw2 k) ⟨⟨k, hk⟩, rfl⟩
  · intro he g hg
    obtain ⟨⟨k, hk⟩, rfl⟩ := hg
    exact he k hk

theorem w1369_mem_E_iff' (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {e : Module.End (ZMod 2) (Additive M)} :
    e ∈ w1369E hw2 K ↔ ∀ k ∈ K, ∀ v, w1369LinHom hw2 k (e v) = e (w1369LinHom hw2 k v) := by
  rw [w1369_mem_E_iff]
  constructor
  · intro h k hk v
    have := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f v) (h k hk)
    simpa only [Module.End.mul_apply] using this
  · intro h k hk
    ext v
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact h k hk v

theorem w1369_ker_eq_bot_or_top (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥)
    {e : Module.End (ZMod 2) (Additive M)} (he : e ∈ w1369E hw2 K) :
    LinearMap.ker e = ⊥ ∨ LinearMap.ker e = ⊤ := by
  have hcomm := (w1369_mem_E_iff' hw2).mp he
  refine w1369_hirrSubmodule hw2 hirr (LinearMap.ker e) ?_
  intro k hk u hu
  rw [LinearMap.mem_ker] at hu ⊢
  rw [← hcomm k hk u, hu, map_zero]

theorem w1369_range_eq_bot_or_top (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥)
    {e : Module.End (ZMod 2) (Additive M)} (he : e ∈ w1369E hw2 K) :
    LinearMap.range e = ⊥ ∨ LinearMap.range e = ⊤ := by
  have hcomm := (w1369_mem_E_iff' hw2).mp he
  refine w1369_hirrSubmodule hw2 hirr (LinearMap.range e) ?_
  rintro k hk v ⟨u, rfl⟩
  exact ⟨w1369LinHom hw2 k u, (hcomm k hk u).symm⟩

theorem w1369_E_exists_inv (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥) (e : w1369E hw2 K) (he : e ≠ 0) :
    ∃ e' : w1369E hw2 K, e * e' = 1 ∧ e' * e = 1 := by
  have hene : (e : Module.End (ZMod 2) (Additive M)) ≠ 0 := fun h => he (Subtype.ext h)
  have hker : LinearMap.ker (e : Module.End (ZMod 2) (Additive M)) = ⊥ := by
    rcases w1369_ker_eq_bot_or_top hw2 hirr e.2 with h | h
    · exact h
    · exfalso
      apply hene
      ext v
      have hv : v ∈ LinearMap.ker (e : Module.End (ZMod 2) (Additive M)) := by
        rw [h]; exact Submodule.mem_top
      simpa [LinearMap.mem_ker] using hv
  have hran : LinearMap.range (e : Module.End (ZMod 2) (Additive M)) = ⊤ := by
    rcases w1369_range_eq_bot_or_top hw2 hirr e.2 with h | h
    · exfalso
      apply hene
      ext v
      have hv : (e : Module.End (ZMod 2) (Additive M)) v ∈
          LinearMap.range (e : Module.End (ZMod 2) (Additive M)) := ⟨v, rfl⟩
      rw [h] at hv
      simpa using hv
    · exact h
  have hbij : Function.Bijective (e : Module.End (ZMod 2) (Additive M)) :=
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩
  obtain ⟨u, hu⟩ := (Module.End.isUnit_iff (e : Module.End (ZMod 2) (Additive M))).mpr hbij
  have hcomm := (w1369_mem_E_iff hw2).mp e.2
  have hmem : (↑u⁻¹ : Module.End (ZMod 2) (Additive M)) ∈ w1369E hw2 K := by
    rw [w1369_mem_E_iff]
    intro k hk
    have h1 : Commute (↑u : Module.End (ZMod 2) (Additive M)) (w1369LinHom hw2 k) := by
      show (↑u : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 k =
        w1369LinHom hw2 k * (↑u : Module.End (ZMod 2) (Additive M))
      rw [hu]
      exact (hcomm k hk).symm
    exact (h1.units_inv_left).symm
  refine ⟨⟨↑u⁻¹, hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (e : Module.End (ZMod 2) (Additive M)) * ↑u⁻¹ = 1
    rw [← hu]
    exact Units.mul_inv u
  · apply Subtype.ext
    change (↑u⁻¹ : Module.End (ZMod 2) (Additive M)) * (e : Module.End (ZMod 2) (Additive M)) = 1
    rw [← hu]
    exact Units.inv_mul u

theorem w1369LinHom_mul_self (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {d : MulAut M} (hd2 : d ^ 2 = 1) :
    w1369LinHom hw2 d * w1369LinHom hw2 d = 1 := by
  rw [← map_mul, ← pow_two, hd2, map_one]

@[simp] theorem w1369LinHom_apply_apply (hw2 : ∀ m : M, m ^ 2 = 1)
    [Module (ZMod 2) (Additive M)] {d : MulAut M} (hd2 : d ^ 2 = 1) (v : Additive M) :
    w1369LinHom hw2 d (w1369LinHom hw2 d v) = v := by
  have := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f v)
    (w1369LinHom_mul_self hw2 hd2)
  simpa [Module.End.mul_apply] using this

theorem w1369LinHom_injective (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)] :
    Function.Injective (w1369LinHom hw2 (M := M)) := by
  intro c e h
  apply MulEquiv.ext
  intro m
  have := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f (Additive.ofMul m)) h
  exact Additive.ofMul.injective (by simpa using this)

theorem w1369_conj_mem (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K)
    {e : Module.End (ZMod 2) (Additive M)} (he : e ∈ w1369E hw2 K) :
    w1369LinHom hw2 d * e * w1369LinHom hw2 d ∈ w1369E hw2 K := by
  have hcomm := (w1369_mem_E_iff hw2).mp he
  rw [w1369_mem_E_iff]
  intro k hk
  have hk' : d * k * d⁻¹ ∈ K := by
    have hmem : (MulAut.conj d) k ∈ K.map (MulAut.conj d).toMonoidHom := ⟨k, hk, rfl⟩
    rwa [hdN] at hmem
  have hcomm' := hcomm (d * k * d⁻¹) hk'
  have hd'inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hφ : w1369LinHom hw2 (d * k * d⁻¹) =
      w1369LinHom hw2 d * w1369LinHom hw2 k * w1369LinHom hw2 d := by
    rw [map_mul, map_mul, hd'inv]
  rw [hφ] at hcomm'
  have hφφ : w1369LinHom hw2 d * w1369LinHom hw2 d = 1 := w1369LinHom_mul_self hw2 hd2
  have h3 := congrArg (fun x : Module.End (ZMod 2) (Additive M) =>
    w1369LinHom hw2 d * x * w1369LinHom hw2 d) hcomm'
  have hL : w1369LinHom hw2 d *
      ((w1369LinHom hw2 d * w1369LinHom hw2 k * w1369LinHom hw2 d) *
        (e : Module.End (ZMod 2) (Additive M))) * w1369LinHom hw2 d =
      w1369LinHom hw2 k * (w1369LinHom hw2 d *
        (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) := by
    calc w1369LinHom hw2 d *
          ((w1369LinHom hw2 d * w1369LinHom hw2 k * w1369LinHom hw2 d) *
            (e : Module.End (ZMod 2) (Additive M))) * w1369LinHom hw2 d
        = (w1369LinHom hw2 d * w1369LinHom hw2 d) * w1369LinHom hw2 k *
            (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
              w1369LinHom hw2 d) := by noncomm_ring
      _ = w1369LinHom hw2 k * (w1369LinHom hw2 d *
            (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) := by
            rw [hφφ, one_mul]
  have hR : w1369LinHom hw2 d *
      ((e : Module.End (ZMod 2) (Additive M)) *
        (w1369LinHom hw2 d * w1369LinHom hw2 k * w1369LinHom hw2 d)) * w1369LinHom hw2 d =
      (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
        w1369LinHom hw2 d) * w1369LinHom hw2 k := by
    calc w1369LinHom hw2 d *
          ((e : Module.End (ZMod 2) (Additive M)) *
            (w1369LinHom hw2 d * w1369LinHom hw2 k * w1369LinHom hw2 d)) * w1369LinHom hw2 d
        = (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
            w1369LinHom hw2 d) * (w1369LinHom hw2 k *
              (w1369LinHom hw2 d * w1369LinHom hw2 d)) := by noncomm_ring
      _ = (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
            w1369LinHom hw2 d) * w1369LinHom hw2 k := by rw [hφφ, mul_one]
  rw [hL, hR] at h3
  exact h3

@[expose] noncomputable def w1369Alpha (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) :
    w1369E hw2 K →+* w1369E hw2 K where
  toFun e := ⟨w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
    w1369LinHom hw2 d, w1369_conj_mem hw2 hd2 hdN e.2⟩
  map_one' := by
    apply Subtype.ext
    change w1369LinHom hw2 d * 1 * w1369LinHom hw2 d = 1
    rw [mul_one, w1369LinHom_mul_self hw2 hd2]
  map_mul' e f := by
    apply Subtype.ext
    change w1369LinHom hw2 d *
        ((e : Module.End (ZMod 2) (Additive M)) * (f : Module.End (ZMod 2) (Additive M))) *
        w1369LinHom hw2 d =
      (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) *
        (w1369LinHom hw2 d * (f : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d)
    rw [show (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
          w1369LinHom hw2 d) *
        (w1369LinHom hw2 d * (f : Module.End (ZMod 2) (Additive M)) *
          w1369LinHom hw2 d) =
        w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
          (w1369LinHom hw2 d * w1369LinHom hw2 d) *
          (f : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d from by
      noncomm_ring]
    rw [w1369LinHom_mul_self hw2 hd2, mul_one]
    noncomm_ring
  map_zero' := by
    apply Subtype.ext
    change w1369LinHom hw2 d * 0 * w1369LinHom hw2 d = 0
    rw [mul_zero, zero_mul]
  map_add' e f := by
    apply Subtype.ext
    change w1369LinHom hw2 d *
        ((e : Module.End (ZMod 2) (Additive M)) + (f : Module.End (ZMod 2) (Additive M))) *
        w1369LinHom hw2 d =
      w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d +
        w1369LinHom hw2 d * (f : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d
    rw [mul_add, add_mul]

theorem w1369Alpha_apply (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) (e : w1369E hw2 K) :
    (w1369Alpha hw2 hd2 hdN e : Module.End (ZMod 2) (Additive M)) =
      w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d := rfl

theorem w1369Alpha_involutive (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) (e : w1369E hw2 K) :
    w1369Alpha hw2 hd2 hdN (w1369Alpha hw2 hd2 hdN e) = e := by
  apply Subtype.ext
  rw [w1369Alpha_apply, w1369Alpha_apply]
  change w1369LinHom hw2 d *
      (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) *
      w1369LinHom hw2 d = (e : Module.End (ZMod 2) (Additive M))
  rw [show w1369LinHom hw2 d *
      (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) *
      w1369LinHom hw2 d =
      (w1369LinHom hw2 d * w1369LinHom hw2 d) * (e : Module.End (ZMod 2) (Additive M)) *
        (w1369LinHom hw2 d * w1369LinHom hw2 d) from by noncomm_ring]
  rw [w1369LinHom_mul_self hw2 hd2, one_mul, mul_one]

theorem w1369_mem_zpowers_two {d x : MulAut M} (hd2 : d ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers d) : x = 1 ∨ x = d := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : d ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hd2]
  have hmod : d ^ n = d ^ (n % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod n 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rw [hmod]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
  · left; simp
  · right; simp

theorem w1369_commSub_eq (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {d : MulAut M} (hd2 : d ^ 2 = 1) :
    commSub ⊤ (Subgroup.zpowers d) =
      w1369SubmoduleToSubgroup (LinearMap.range (w1369LinHom hw2 d - 1)) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    change Additive.ofMul (x w * w⁻¹) ∈ LinearMap.range (w1369LinHom hw2 d - 1)
    rcases w1369_mem_zpowers_two hd2 hx with hx1 | hxd
    · rw [hx1]
      simpa using Submodule.zero_mem (LinearMap.range (w1369LinHom hw2 d - 1))
    · rw [hxd]
      refine ⟨Additive.ofMul w, ?_⟩
      change w1369LinHom hw2 d (Additive.ofMul w) - Additive.ofMul w =
        Additive.ofMul (d w * w⁻¹)
      rw [w1369LinHom_ofMul, sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
  · intro m hm
    rw [w1369SubmoduleToSubgroup_ofMul] at hm
    obtain ⟨v, hv⟩ := hm
    have hgen : d (Additive.toMul v) * (Additive.toMul v)⁻¹ ∈
        commSub ⊤ (Subgroup.zpowers d) :=
      Subgroup.subset_closure ⟨d, Subgroup.mem_zpowers d, Additive.toMul v, Subgroup.mem_top _,
        rfl⟩
    convert hgen using 1
    have hv' : (w1369LinHom hw2 d - 1) v =
        Additive.ofMul (d (Additive.toMul v) * (Additive.toMul v)⁻¹) := by
      conv_lhs => rw [show v = Additive.ofMul (Additive.toMul v) from rfl]
      change w1369LinHom hw2 d (Additive.ofMul (Additive.toMul v)) -
        Additive.ofMul (Additive.toMul v) =
        Additive.ofMul (d (Additive.toMul v) * (Additive.toMul v)⁻¹)
      rw [w1369LinHom_ofMul, sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
    exact Additive.ofMul.injective (hv'.symm.trans hv).symm

theorem w1369_card_submoduleToSubgroup [Module (ZMod 2) (Additive M)]
    (U : Submodule (ZMod 2) (Additive M)) :
    Nat.card ↥(w1369SubmoduleToSubgroup U) = Nat.card ↥U :=
  Nat.card_congr
    { toFun := fun m => ⟨Additive.ofMul m.1, m.2⟩
      invFun := fun v => ⟨Additive.toMul v.1, v.2⟩
      left_inv := fun m => by ext; simp
      right_inv := fun v => by ext; simp }

theorem w1369_card_range (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {d : MulAut M} (hd2 : d ^ 2 = 1) (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 1) :
    Nat.card ↥(LinearMap.range (w1369LinHom hw2 d - 1)) = 2 := by
  rw [← w1369_card_submoduleToSubgroup (LinearMap.range (w1369LinHom hw2 d - 1)),
    ← w1369_commSub_eq hw2 hd2, card_eq_two_pow hw2 (commSub ⊤ (Subgroup.zpowers d)), hcost,
    pow_one]

theorem w1369_card_eq_ker_mul_range [Module (ZMod 2) (Additive M)]
    (f : Additive M →ₗ[ZMod 2] Additive M) :
    Nat.card (Additive M) = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := by
  have h := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 : Nat.card (Additive M ⧸ LinearMap.ker f) = Nat.card ↥(LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  rw [h2] at h
  simpa [Nat.mul_comm] using h

theorem w1369_linHom_mem_E (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {c : MulAut M} (hc : ∀ k ∈ K, c * k = k * c) :
    w1369LinHom hw2 c ∈ w1369E hw2 K := by
  rw [w1369_mem_E_iff]
  intro k hk
  rw [← map_mul, ← map_mul, hc k hk]

theorem w1369_linHom_eq_one (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {c : MulAut M} (h : w1369LinHom hw2 c = 1) : c = 1 := by
  apply MulEquiv.ext
  intro m
  have := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f (Additive.ofMul m)) h
  exact Additive.ofMul.injective (by simpa using this)

theorem w1369_alpha_eq_self_comm (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) {e : w1369E hw2 K}
    (he : w1369Alpha hw2 hd2 hdN e = e) :
    w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) =
      (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d := by
  have h := congrArg (fun x : w1369E hw2 K =>
    (x : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) he
  rw [w1369Alpha_apply] at h
  rwa [show w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) *
      w1369LinHom hw2 d * w1369LinHom hw2 d =
      w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) from by
    rw [mul_assoc, w1369LinHom_mul_self hw2 hd2, mul_one]] at h

theorem w1369_range_sub_mem (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {d : MulAut M} {e : Module.End (ZMod 2) (Additive M)}
    (hφe : w1369LinHom hw2 d * e = e * w1369LinHom hw2 d)
    {v : Additive M} (hv : v ∈ LinearMap.range (w1369LinHom hw2 d - 1)) :
    e v ∈ LinearMap.range (w1369LinHom hw2 d - 1) := by
  obtain ⟨u, rfl⟩ := hv
  have hφeu : w1369LinHom hw2 d (e u) = e (w1369LinHom hw2 d u) := by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End (ZMod 2) (Additive M) =>
      f u) hφe
  refine ⟨e u, ?_⟩
  show w1369LinHom hw2 d (e u) - e u = e (w1369LinHom hw2 d u - u)
  rw [map_sub, hφeu]

theorem w1369_card_E_le_two (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥) {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K)
    (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 1)
    (hα : ∀ e : w1369E hw2 K, w1369Alpha hw2 hd2 hdN e = e) :
    Nat.card (w1369E hw2 K) ≤ 2 := by
  have hcard := w1369_card_range hw2 hd2 hcost
  have hne : LinearMap.range (w1369LinHom hw2 d - 1) ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨q, hq, hq0⟩ := (Submodule.ne_bot_iff (LinearMap.range (w1369LinHom hw2 d - 1))).mp hne
  let f : w1369E hw2 K → ↥(LinearMap.range (w1369LinHom hw2 d - 1)) :=
    fun e => ⟨(e : Module.End (ZMod 2) (Additive M)) q,
      w1369_range_sub_mem hw2 (w1369_alpha_eq_self_comm hw2 hd2 hdN (hα e)) hq⟩
  have hf : Function.Injective f := by
    intro e e' h
    have hq_eq : (e : Module.End (ZMod 2) (Additive M)) q =
        (e' : Module.End (ZMod 2) (Additive M)) q := congrArg Subtype.val h
    have hsub : (((e - e' : w1369E hw2 K)) : Module.End (ZMod 2) (Additive M)) q = 0 := by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, hq_eq, sub_self]
    rcases w1369_ker_eq_bot_or_top hw2 hirr (e - e').2 with hker | hker
    · exfalso
      have hmem : q ∈ LinearMap.ker
          (((e - e' : w1369E hw2 K)) : Module.End (ZMod 2) (Additive M)) := by
        rw [LinearMap.mem_ker]; exact hsub
      rw [hker, Submodule.mem_bot] at hmem
      exact hq0 hmem
    · have hzero : (e - e' : w1369E hw2 K) = 0 := by
        apply Subtype.ext
        ext v
        have hmem : v ∈ LinearMap.ker
            (((e - e' : w1369E hw2 K)) : Module.End (ZMod 2) (Additive M)) := by
          rw [hker]; exact Submodule.mem_top
        exact LinearMap.mem_ker.mp hmem
      exact sub_eq_zero.mp hzero
  calc Nat.card (w1369E hw2 K) ≤ Nat.card ↥(LinearMap.range (w1369LinHom hw2 d - 1)) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 := hcard

theorem w1369_alpha_mul_phi (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) (e : w1369E hw2 K) :
    (w1369Alpha hw2 hd2 hdN e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d =
      w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) := by
  rw [w1369Alpha_apply]
  rw [show w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d *
      w1369LinHom hw2 d = w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) from by
    rw [mul_assoc, w1369LinHom_mul_self hw2 hd2, mul_one]]

theorem w1369_phi_alpha_mul (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) (e : w1369E hw2 K) :
    w1369LinHom hw2 d * (w1369Alpha hw2 hd2 hdN e : Module.End (ZMod 2) (Additive M)) =
      (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d := by
  rw [w1369Alpha_apply]
  rw [show w1369LinHom hw2 d *
      (w1369LinHom hw2 d * (e : Module.End (ZMod 2) (Additive M)) * w1369LinHom hw2 d) =
      (w1369LinHom hw2 d * w1369LinHom hw2 d) * (e : Module.End (ZMod 2) (Additive M)) *
        w1369LinHom hw2 d from by noncomm_ring]
  rw [w1369LinHom_mul_self hw2 hd2, one_mul]

theorem w1369_alpha_phi_apply (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) (e : w1369E hw2 K) (v : Additive M) :
    (w1369Alpha hw2 hd2 hdN e : Module.End (ZMod 2) (Additive M)) (w1369LinHom hw2 d v) =
      w1369LinHom hw2 d ((e : Module.End (ZMod 2) (Additive M)) v) := by
  have h := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f v)
    (w1369_alpha_mul_phi hw2 hd2 hdN e)
  simpa [Module.End.mul_apply] using h

theorem w1369_phi_alpha_apply (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K) (e : w1369E hw2 K) (v : Additive M) :
    w1369LinHom hw2 d
        ((w1369Alpha hw2 hd2 hdN e : Module.End (ZMod 2) (Additive M)) v) =
      (e : Module.End (ZMod 2) (Additive M)) (w1369LinHom hw2 d v) := by
  have h := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f v)
    (w1369_phi_alpha_mul hw2 hd2 hdN e)
  simpa [Module.End.mul_apply] using h

theorem w1369_add_self (hw2 : ∀ m : M, m ^ 2 = 1) (v : Additive M) : v + v = 0 := by
  apply Additive.toMul.injective
  rw [toMul_add, toMul_zero, ← pow_two]
  exact hw2 (Additive.toMul v)

theorem w1369_E_add_self (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (x : w1369E hw2 K) : x + x = 0 := by
  apply Subtype.ext
  ext v
  change (x : Module.End (ZMod 2) (Additive M)) v + (x : Module.End (ZMod 2) (Additive M)) v = 0
  exact w1369_add_self hw2 ((x : Module.End (ZMod 2) (Additive M)) v)

theorem w1369_card_eq_ker_sq (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥) {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K)
    (hne : ∃ e₁ : w1369E hw2 K, w1369Alpha hw2 hd2 hdN e₁ ≠ e₁) :
    Nat.card (Additive M) = Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) ^ 2 := by
  classical
  obtain ⟨e₁, he₁⟩ := hne
  let t : w1369E hw2 K := e₁ + w1369Alpha hw2 hd2 hdN e₁
  have ht_fix : w1369Alpha hw2 hd2 hdN t = t := by
    show w1369Alpha hw2 hd2 hdN (e₁ + w1369Alpha hw2 hd2 hdN e₁) =
      e₁ + w1369Alpha hw2 hd2 hdN e₁
    rw [(w1369Alpha hw2 hd2 hdN).map_add, w1369Alpha_involutive, add_comm]
  have ht_ne : t ≠ 0 := by
    intro h
    apply he₁
    have h1 : e₁ + w1369Alpha hw2 hd2 hdN e₁ = 0 := h
    have h2 : e₁ = w1369Alpha hw2 hd2 hdN e₁ := by
      have := congrArg (fun x : w1369E hw2 K => x + w1369Alpha hw2 hd2 hdN e₁) h1
      rw [zero_add, add_assoc, w1369_E_add_self hw2, add_zero] at this
      exact this
    exact h2.symm
  obtain ⟨t', ht', ht''⟩ := w1369_E_exists_inv hw2 hirr t ht_ne
  have hαt' : w1369Alpha hw2 hd2 hdN t' = t' := by
    have h1 : t * w1369Alpha hw2 hd2 hdN t' = 1 := by
      have h : w1369Alpha hw2 hd2 hdN t * w1369Alpha hw2 hd2 hdN t' =
          w1369Alpha hw2 hd2 hdN (t * t') :=
        ((w1369Alpha hw2 hd2 hdN).map_mul t t').symm
      rw [ht', map_one] at h
      rw [ht_fix] at h
      exact h
    have h2 := congrArg (fun x : w1369E hw2 K => t' * x) h1
    rw [mul_one, ← mul_assoc, ht'', one_mul] at h2
    exact h2
  let ε : w1369E hw2 K := t' * e₁
  have hε : ε + w1369Alpha hw2 hd2 hdN ε = 1 := by
    have hεα : w1369Alpha hw2 hd2 hdN ε = t' * w1369Alpha hw2 hd2 hdN e₁ := by
      show w1369Alpha hw2 hd2 hdN (t' * e₁) = t' * w1369Alpha hw2 hd2 hdN e₁
      rw [map_mul, hαt']
    change t' * e₁ + w1369Alpha hw2 hd2 hdN (t' * e₁) = 1
    rw [hεα, ← mul_add]
    change t' * t = 1
    exact ht''
  let V₀ := LinearMap.ker (w1369LinHom hw2 d - 1)
  let εe : Module.End (ZMod 2) (Additive M) := ε
  let αε : Module.End (ZMod 2) (Additive M) := w1369Alpha hw2 hd2 hdN ε
  have hsum : ∀ v : Additive M, εe v + αε v = v := by
    intro v
    have h := congrArg (fun f : w1369E hw2 K => (f : Module.End (ZMod 2) (Additive M)) v) hε
    simpa [εe, αε, Module.End.mul_apply] using h
  let Θ : ↥V₀ × ↥V₀ → Additive M := fun p => αε p.1.1 + p.2.1
  have hsurj : Function.Surjective Θ := by
    intro v
    have hu : v + w1369LinHom hw2 d v ∈ V₀ := by
      rw [LinearMap.mem_ker]
      show w1369LinHom hw2 d (v + w1369LinHom hw2 d v) -
        (v + w1369LinHom hw2 d v) = 0
      rw [map_add, w1369LinHom_apply_apply hw2 hd2]
      abel
    have hw : εe v + w1369LinHom hw2 d (εe v) ∈ V₀ := by
      rw [LinearMap.mem_ker]
      show w1369LinHom hw2 d (εe v + w1369LinHom hw2 d (εe v)) -
        (εe v + w1369LinHom hw2 d (εe v)) = 0
      rw [map_add, w1369LinHom_apply_apply hw2 hd2]
      abel
    refine ⟨(⟨v + w1369LinHom hw2 d v, hu⟩,
      ⟨εe v + w1369LinHom hw2 d (εe v), hw⟩), ?_⟩
    show αε (v + w1369LinHom hw2 d v) + (εe v + w1369LinHom hw2 d (εe v)) = v
    rw [map_add, w1369_alpha_phi_apply hw2 hd2 hdN ε v]
    rw [show αε v + w1369LinHom hw2 d (εe v) + (εe v + w1369LinHom hw2 d (εe v)) =
      (αε v + εe v) + (w1369LinHom hw2 d (εe v) + w1369LinHom hw2 d (εe v)) from by abel,
      w1369_add_self hw2, add_zero]
    rw [add_comm (αε v) (εe v)]
    exact hsum v
  have hinj : Function.Injective Θ := by
    intro p q hpq
    obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := p
    obtain ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩ := q
    have hpq' : αε u + w = αε u' + w' := hpq
    have hu_fix : w1369LinHom hw2 d u = u := by
      have := LinearMap.mem_ker.mp hu
      rw [LinearMap.sub_apply] at this
      exact sub_eq_zero.mp this
    have hu'_fix : w1369LinHom hw2 d u' = u' := by
      have := LinearMap.mem_ker.mp hu'
      rw [LinearMap.sub_apply] at this
      exact sub_eq_zero.mp this
    have hw_fix : w1369LinHom hw2 d w = w := by
      have := LinearMap.mem_ker.mp hw
      rw [LinearMap.sub_apply] at this
      exact sub_eq_zero.mp this
    have hw'_fix : w1369LinHom hw2 d w' = w' := by
      have := LinearMap.mem_ker.mp hw'
      rw [LinearMap.sub_apply] at this
      exact sub_eq_zero.mp this
    have h2 : εe u + w = εe u' + w' := by
      have h := congrArg (w1369LinHom hw2 d) hpq'
      rw [map_add, map_add, w1369_phi_alpha_apply hw2 hd2 hdN ε u,
        w1369_phi_alpha_apply hw2 hd2 hdN ε u', hu_fix, hu'_fix, hw_fix, hw'_fix] at h
      exact h
    have h3 : u = u' := by
      have h4 : (εe u + αε u) + (w + w) = (εe u' + αε u') + (w' + w') := by
        have h : (αε u + w) + (εe u + w) = (αε u' + w') + (εe u' + w') := by
          rw [hpq', h2]
        rw [show (εe u + αε u) + (w + w) = (αε u + w) + (εe u + w) from by abel,
          show (εe u' + αε u') + (w' + w') = (αε u' + w') + (εe u' + w') from by abel]
        exact h
      rw [hsum u, hsum u', w1369_add_self hw2 w, w1369_add_self hw2 w',
        add_zero, add_zero] at h4
      exact h4
    have hww : w = w' := by
      rw [h3] at hpq'
      exact add_left_cancel hpq'
    subst h3
    subst hww
    exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  have hcard : Nat.card (↥V₀ × ↥V₀) = Nat.card (Additive M) :=
    Nat.card_congr (Equiv.ofBijective Θ ⟨hinj, hsurj⟩)
  rw [Nat.card_prod, ← pow_two] at hcard
  exact hcard.symm

theorem w1369_card_eq_four (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥) {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K)
    (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 1)
    (hne : ∃ e₁ : w1369E hw2 K, w1369Alpha hw2 hd2 hdN e₁ ≠ e₁) :
    Nat.card M = 4 := by
  have hsq := w1369_card_eq_ker_sq hw2 hirr hd2 hdN hne
  have hrn := w1369_card_eq_ker_mul_range (w1369LinHom hw2 d - 1)
  have hrange := w1369_card_range hw2 hd2 hcost
  have hker : Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) = 2 := by
    have h : Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) ^ 2 =
        Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) * 2 := by
      rw [← hsq, hrn, hrange]
    rw [pow_two] at h
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥(LinearMap.ker (w1369LinHom hw2 d - 1)))) h
  have hA : Nat.card (Additive M) = 4 := by
    rw [hsq, hker]; norm_num
  exact hA

theorem w1369_false_of_card_four (hw2 : ∀ m : M, m ^ 2 = 1) {K : Subgroup (MulAut M)}
    (hperf : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) (hcard : Nat.card M = 4) : False := by
  classical
  let S := {m : M // m ≠ 1}
  have hScard : Nat.card S = 3 := by
    haveI : Fintype M := Fintype.ofFinite M
    have h1 : Nat.card S = Nat.card M - Nat.card {m : M // m = 1} := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_compl (fun m : M => m = 1)
    have h2 : Nat.card {m : M // m = 1} = 1 :=
      Nat.card_eq_one_iff_unique.mpr
        ⟨⟨fun a b => Subtype.ext (by rw [a.2, b.2])⟩, ⟨⟨1, rfl⟩⟩⟩
    omega
  letI : MulAction (MulAut M) S :=
    { smul := fun g s => ⟨g s.1, fun h => s.2 (g.injective (h.trans (map_one g).symm))⟩
      one_smul := fun s => by ext; rfl
      mul_smul := fun g h s => by ext; rfl }
  have hinj : Function.Injective (MulAction.toPermHom (MulAut M) S) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    apply MulEquiv.ext
    intro m
    by_cases hm : m = 1
    · subst hm
      exact map_one g
    · have := congrArg (fun e : Equiv.Perm S => e ⟨m, hm⟩) hg
      exact congrArg Subtype.val this
  have hdvd : Nat.card (MulAut M) ∣ Nat.card (Equiv.Perm S) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_perm, hScard] at hdvd
  norm_num at hdvd
  have hsq : Squarefree (Nat.card (MulAut M)) :=
    (show Squarefree 6 by decide +kernel).squarefree_of_dvd hdvd
  haveI : IsZGroup (MulAut M) := IsZGroup.of_squarefree hsq
  haveI : Group.IsSolvable (MulAut M) := inferInstance
  exact absurd hperf (ne_of_lt (Group.IsSolvable.commutator_lt_of_ne_bot hK1))

theorem w1369_eq_or_eq_of_card_le_two {α : Type} [Finite α] {a b : α} (hab : a ≠ b)
    (h : Nat.card α ≤ 2) (x : α) : x = a ∨ x = b := by
  classical
  by_contra hx
  rw [not_or] at hx
  obtain ⟨hxa, hxb⟩ := hx
  have h3 : 3 ≤ Nat.card α := by
    haveI : Fintype α := Fintype.ofFinite α
    have hcard : ({a, b, x} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hab, Ne.symm hxa⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact Ne.symm hxb),
          Finset.card_singleton]
    have hle : ({a, b, x} : Finset α).card ≤ Fintype.card α :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [hcard, ← Nat.card_eq_fintype_card] at hle
    exact hle
  omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
