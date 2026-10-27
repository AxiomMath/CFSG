module

public import CFSG.Quasithin.Background.SzG11B49Lin

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting
open B49Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure B49Tv (B : LinearMap.BilinForm (ZMod 2) V) (H : Subgroup (GLV V))
    (U : Submodule (ZMod 2) V) (t : GLV V) (v z : V) : Prop where
  z_mem : z ∈ U
  vz : B v z = 0
  mem : t ∈ H
  act : ∀ u ∈ U, t u = u + B v u • z

namespace B49Tv

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} {t t' : GLV V} {v v' z z' : V}

theorem D_U (h : B49Tv B H U t v z) {u : V} (hu : u ∈ U) : t u + u = B v u • z := by
  rw [h.act u hu]
  match_scalars <;> ring_nf
  reduce_mod_char

theorem congr (h : B49Tv B H U t v z) (hv : ∀ u ∈ U, B v' u = B v u) (hv'z : B v' z = 0) :
    B49Tv B H U t v' z :=
  ⟨h.z_mem, hv'z, h.mem, fun u hu => by rw [h.act u hu, hv u hu]⟩

theorem mul_centre (h : B49Tv B H U t v z) (h' : B49Tv B H U t' v z') :
    B49Tv B H U (t * t') v (z + z') := by
  have hz : t z' = z' := by rw [h.act z' h'.z_mem, h'.vz, zero_smul, add_zero]
  refine ⟨U.add_mem h.z_mem h'.z_mem, by rw [map_add, h.vz, h'.vz, add_zero],
    H.mul_mem h.mem h'.mem, fun u hu => ?_⟩
  change t (t' u) = u + B v u • (z + z')
  rw [h'.act u hu, map_add, map_smul, hz, h.act u hu, smul_add]
  match_scalars <;> ring_nf

theorem mul_axis (h : B49Tv B H U t v z) (h' : B49Tv B H U t' v' z) :
    B49Tv B H U (t * t') (v + v') z := by
  have hz : t z = z := by rw [h.act z h.z_mem, h.vz, zero_smul, add_zero]
  refine ⟨h.z_mem, by rw [map_add, LinearMap.add_apply, h.vz, h'.vz, add_zero],
    H.mul_mem h.mem h'.mem, fun u hu => ?_⟩
  change t (t' u) = u + B (v + v') u • z
  rw [h'.act u hu, map_add, map_smul, hz, h.act u hu]
  simp only [map_add, LinearMap.add_apply, add_smul]
  match_scalars <;> ring_nf

end B49Tv

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U) {t t' : GLV V} {v v' z z' : V}

include hy

theorem exists_isTv (hz : z ∈ U) (hvz : B v z = 0) : ∃ t, B49Tv B H U t v z := by
  have h0 : ((B v).comp U.subtype) ⟨z, hz⟩ = 0 := by simpa using hvz
  obtain ⟨k, hk, hk'⟩ := hy.aut (LinearEquiv.transvection h0)
  refine ⟨k, hz, hvz, hk, fun u hu => ?_⟩
  have := hk' ⟨u, hu⟩
  rw [this, transvection_apply]
  simp

theorem tv_eq (h : B49Tv B H U t v z) (h' : B49Tv B H U t' v' z')
    (hact : ∀ u ∈ U, B v u • z = B v' u • z') : t = t' :=
  hy.eq_of_eqOn h.mem h'.mem fun u hu => by rw [h.act u hu, h'.act u hu, hact u hu]

theorem tv_apply_apply (h : B49Tv B H U t v z) (x : V) : t (t x) = x := by
  have hz : t z = z := by rw [h.act z h.z_mem, h.vz, zero_smul, add_zero]
  have h1 : t * t = 1 := by
    refine hy.eq_one_of_eqOn (H.mul_mem h.mem h.mem) fun u hu => ?_
    change t (t u) = u
    rw [h.act u hu, map_add, map_smul, hz, h.act u hu]
    match_scalars <;> ring_nf
    reduce_mod_char
  have := congrArg (fun g : GLV V => g x) h1
  simpa using this

theorem tv_selfadj (h : B49Tv B H U t v z) (x y : V) : B (t x + x) y = B x (t y + y) := by
  have e : B (t x) y = B x (t y) := by
    have := hy.isom t h.mem x (t y)
    rwa [hy.tv_apply_apply h y] at this
  simp only [map_add, LinearMap.add_apply, e]

theorem tv_D_self (h : B49Tv B H U t v z) (x : V) : t (t x + x) = t x + x := by
  rw [map_add, hy.tv_apply_apply h x, add_comm]

theorem tv_D_cls [Finite V] (h : B49Tv B H U t v z) (x : V) : t x + x + B x z • v ∈ U := by
  refine hy.mem_of_orth fun u hu => ?_
  have e1 : B (t x + x) u = B x (B v u • z) := by
    rw [hy.tv_selfadj h x u, h.D_U hu]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at e1 ⊢
  rw [e1]
  generalize B x z = a
  generalize B v u = b
  revert a b
  decide

theorem tv_conj (h : B49Tv B H U t v z) {g : GLV V} (hg : g ∈ H) :
    B49Tv B H U (g * t * g⁻¹) (g v) (g z) := by
  refine ⟨hy.apply_mem hg h.z_mem, ?_, H.mul_mem (H.mul_mem hg h.mem) (H.inv_mem hg), ?_⟩
  · rw [hy.isom g hg]
    exact h.vz
  · intro u hu
    change g (t (g⁻¹ u)) = u + B (g v) u • g z
    rw [h.act _ (hy.inv_apply_mem hg hu), map_add, map_smul, apply_inv_apply, hy.B_apply_left hg]

theorem tv_eq_one (h : B49Tv B H U t v z) (hv : ∀ u ∈ U, B v u = 0) : t = 1 :=
  hy.eq_one_of_eqOn h.mem fun u hu => by rw [h.act u hu, hv u hu, zero_smul, add_zero]

end B49Hyp

end CFSG.Quasithin.G11.SzG11S
