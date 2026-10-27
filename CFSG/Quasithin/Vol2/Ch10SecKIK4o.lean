module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4m

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem le_one_of_dvd {k : ℕ} (h : 60 * 2 ^ k ∣ 2520) : k ≤ 1 := by
  by_contra hk
  have h4 : 4 ∣ 2 ^ k := (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by omega)
  have : 240 ∣ 2520 := (mul_dvd_mul_left 60 h4).trans h
  norm_num at this

variable {W L : Subgroup G} {F : Subgroup (MulAut ↥W)} {π : Equiv.Perm (Fin 7) →* ↥F}

theorem conj_mem_comap {δ : Equiv.Perm (Fin 7)} {g : Subgroup.normalizer (W : Set G)}
    (hg : (g : G) ∈ Subgroup.normalizer (L : Set G))
    (hδ : ((π δ : ↥F) : MulAut ↥W) = conjAct W g) :
    ∀ k ∈ ((autOn L W).subgroupOf F).comap π, δ * k * δ⁻¹ ∈ ((autOn L W).subgroupOf F).comap π := by
  intro k hk
  have hk' : ((π k : ↥F) : MulAut ↥W) ∈ autOn L W := Subgroup.mem_subgroupOf.1 hk
  show π (δ * k * δ⁻¹) ∈ (autOn L W).subgroupOf F
  rw [Subgroup.mem_subgroupOf, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hδ]
  exact conjAct_mul_mem_autOn hg hk'

theorem mem_normalizer_comap {δ : Equiv.Perm (Fin 7)} {g : Subgroup.normalizer (W : Set G)}
    (hg : (g : G) ∈ Subgroup.normalizer (L : Set G))
    (hδ : ((π δ : ↥F) : MulAut ↥W) = conjAct W g) :
    δ ∈ Subgroup.normalizer ((((autOn L W).subgroupOf F).comap π : Subgroup _) :
      Set (Equiv.Perm (Fin 7))) := by
  have hδ' : ((π δ⁻¹ : ↥F) : MulAut ↥W) = conjAct W g⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, hδ, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_comap hg hδ x hx, fun hx => ?_⟩
  have := conj_mem_comap (Subgroup.inv_mem _ hg) hδ' _ hx
  have e : δ⁻¹ * (δ * x * δ⁻¹) * δ⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem perfect_comap (hπ : Function.Bijective π) (hLF : autOn L W ≤ F)
    (hLN : L ≤ Subgroup.normalizer (W : Set G)) (hperf : ⁅L, L⁆ = L) :
    ⁅((autOn L W).subgroupOf F).comap π, ((autOn L W).subgroupOf F).comap π⁆ =
      ((autOn L W).subgroupOf F).comap π := by
  set K := ((autOn L W).subgroupOf F).comap π with hK
  have hmap : K.map π = (autOn L W).subgroupOf F :=
    Subgroup.map_comap_eq_self_of_surjective hπ.2 _
  let e : ↥K ≃* ↥(autOn L W) :=
    ((K.equivMapOfInjective π hπ.1).trans (MulEquiv.subgroupCongr hmap)).trans
      (Subgroup.subgroupOfEquivOfLe hLF)
  have hpL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  have hpA : Group.IsPerfect ↥(autOn L W) :=
    Group.IsPerfect.ofSurjective (f := InternalSec.autOnHom hLN)
      (InternalSec.autOnHom_surjective hLN)
  have hpK : Group.IsPerfect ↥K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact commutator_self_eq hpK.commutator_eq_top

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
