module

public import CFSG.Quasithin.MS93.MSPNorm
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open scoped Matrix

variable {G : Type} [Group G]

structure Sp4NatData (L U A : Subgroup G) (F : Type) [Field F] where
  α : ↥L →* Sp4 F
  α_surj : Function.Surjective α
  hLU : L ≤ Subgroup.normalizer (U : Set G)
  hAU : A ≤ U
  β : ↥U →* Multiplicative (V4 F)
  β_surj : Function.Surjective β
  β_ker : ∀ u : ↥U, β u = 1 ↔ (u : G) ∈ A
  β_equiv : ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ →
    Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u)

namespace Sp4NatData

variable {L U A : Subgroup G} {F : Type} [Field F]

@[expose] noncomputable def ofIsSum {α : ↥L →* ↥(StatedSp 2 F)} (hα : Function.Surjective α)
    (hn : IsSumOfNaturalModulesVia L U A α false 1) : Sp4NatData L U A F where
  α := α
  α_surj := hα
  hLU := hn.1
  hAU := hn.2.1
  β := (AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (V4 F))).toMonoidHom.comp
    (Classical.choose hn.2.2)
  β_surj := (AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (V4 F))).surjective.comp
    (Classical.choose_spec hn.2.2).1
  β_ker := fun u => by
    have hk := (Classical.choose_spec hn.2.2).2.1
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      ← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf]
  β_equiv := fun a u v huv => by
    have h := (Classical.choose_spec hn.2.2).2.2 a u v huv 0
    simpa [moduleAct] using h

theorem ofIsSum_α {α : ↥L →* ↥(StatedSp 2 F)} (hα : Function.Surjective α)
    (hn : IsSumOfNaturalModulesVia L U A α false 1) : (ofIsSum hα hn).α = α := rfl

abbrev co (N : Sp4NatData L U A F) (u : ↥U) : V4 F := Multiplicative.toAdd (N.β u)

theorem co_mul (N : Sp4NatData L U A F) (u v : ↥U) : N.co (u * v) = N.co u + N.co v := by
  simp [co]

theorem co_one (N : Sp4NatData L U A F) : N.co 1 = 0 := by simp [co]

theorem co_inv (N : Sp4NatData L U A F) (u : ↥U) : N.co u⁻¹ = -N.co u := by simp [co]

theorem co_eq_zero_iff (N : Sp4NatData L U A F) (u : ↥U) : N.co u = 0 ↔ (u : G) ∈ A := by
  rw [← N.β_ker u, co]
  exact ⟨fun h => by simpa using congrArg Multiplicative.ofAdd h, fun h => by simp [h]⟩

theorem co_surj (N : Sp4NatData L U A F) (w : V4 F) : ∃ u : ↥U, N.co u = w := by
  obtain ⟨u, hu⟩ := N.β_surj (Multiplicative.ofAdd w)
  exact ⟨u, by simp [co, hu]⟩

theorem co_eq_co_iff (N : Sp4NatData L U A F) (u v : ↥U) :
    N.co u = N.co v ↔ ((u⁻¹ * v : ↥U) : G) ∈ A := by
  rw [← N.co_eq_zero_iff, co_mul, co_inv, neg_add_eq_zero, eq_comm]

variable {M : Subgroup G}

theorem conj_mem (hMU : M ≤ Subgroup.normalizer (U : Set G)) {x : G} (hx : x ∈ M) (u : ↥U) :
    x * (u : G) * x⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.1 (hMU hx) u).1 u.2

def conjU (hMU : M ≤ Subgroup.normalizer (U : Set G)) {x : G} (hx : x ∈ M) (u : ↥U) : ↥U :=
  ⟨x * u * x⁻¹, conj_mem hMU hx u⟩

noncomputable def actFun (N : Sp4NatData L U A F) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    {x : G} (hx : x ∈ M) (w : V4 F) : V4 F :=
  N.co (conjU hMU hx (Classical.choose (N.co_surj w)))

variable (N : Sp4NatData L U A F) (hMU : M ≤ Subgroup.normalizer (U : Set G))
  (hMA : M ≤ Subgroup.normalizer (A : Set G))

include hMA in
theorem co_conjU_eq_of_co_eq {x : G} (hx : x ∈ M) {u v : ↥U} (h : N.co u = N.co v) :
    N.co (conjU hMU hx u) = N.co (conjU hMU hx v) := by
  rw [co_eq_co_iff] at h ⊢
  have : ((conjU hMU hx u)⁻¹ * conjU hMU hx v : ↥U) = conjU hMU hx (u⁻¹ * v) := by
    ext
    simp [conjU, mul_assoc]
  rw [this]
  exact (Subgroup.mem_normalizer_iff.1 (hMA hx) _).1 h

include hMA in
theorem actFun_spec {x : G} (hx : x ∈ M) (u : ↥U) :
    N.actFun hMU hx (N.co u) = N.co (conjU hMU hx u) :=
  co_conjU_eq_of_co_eq N hMU hMA hx (Classical.choose_spec (N.co_surj (N.co u)))

theorem conjU_mul {x : G} (hx : x ∈ M) (u v : ↥U) :
    conjU hMU hx (u * v) = conjU hMU hx u * conjU hMU hx v := by
  ext
  simp [conjU, mul_assoc]

theorem conjU_one {x : G} (hx : x ∈ M) : conjU hMU hx 1 = 1 := by
  ext
  simp [conjU]

noncomputable def act {x : G} (hx : x ∈ M) : V4 F →+ V4 F where
  toFun := N.actFun hMU hx
  map_zero' := by
    have h := actFun_spec N hMU hMA hx 1
    rwa [co_one, conjU_one, co_one] at h
  map_add' := fun w₁ w₂ => by
    obtain ⟨u₁, rfl⟩ := N.co_surj w₁
    obtain ⟨u₂, rfl⟩ := N.co_surj w₂
    rw [← co_mul, actFun_spec N hMU hMA, actFun_spec N hMU hMA, actFun_spec N hMU hMA,
      conjU_mul, co_mul]

theorem act_congr {x y : G} (hxy : x = y) (hx : x ∈ M) (hy : y ∈ M) :
    N.act hMU hMA hx = N.act hMU hMA hy := by
  subst hxy
  rfl

theorem act_spec {x : G} (hx : x ∈ M) (u : ↥U) :
    N.act hMU hMA hx (N.co u) = N.co (conjU hMU hx u) :=
  actFun_spec N hMU hMA hx u

theorem act_co {x : G} (hx : x ∈ M) {u v : ↥U} (huv : (v : G) = x * u * x⁻¹) :
    N.act hMU hMA hx (N.co u) = N.co v := by
  rw [act_spec]
  congr 1
  exact Subtype.ext huv.symm

theorem ext_co {f g : V4 F →+ V4 F} (h : ∀ u : ↥U, f (N.co u) = g (N.co u)) : f = g :=
  AddMonoidHom.ext fun w => by
    obtain ⟨u, rfl⟩ := N.co_surj w
    exact h u

theorem act_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    N.act hMU hMA (M.mul_mem hx hy) = (N.act hMU hMA hx).comp (N.act hMU hMA hy) := by
  refine N.ext_co fun u => ?_
  rw [AddMonoidHom.comp_apply, act_spec, act_spec, act_spec]
  congr 1
  ext
  simp [conjU, mul_assoc]

theorem act_one : N.act hMU hMA M.one_mem = AddMonoidHom.id (V4 F) := by
  refine N.ext_co fun u => ?_
  rw [act_spec, AddMonoidHom.id_apply]
  congr 1
  ext
  simp [conjU]

theorem act_inv_act {x : G} (hx : x ∈ M) (w : V4 F) :
    N.act hMU hMA (M.inv_mem hx) (N.act hMU hMA hx w) = w := by
  have h := congrArg (fun f => f w) (N.act_mul hMU hMA (M.inv_mem hx) hx)
  simp only [AddMonoidHom.comp_apply] at h
  rw [← h]
  have e : N.act hMU hMA (M.mul_mem (M.inv_mem hx) hx) = N.act hMU hMA M.one_mem :=
    N.act_congr hMU hMA (inv_mul_cancel x) _ _
  rw [e, act_one, AddMonoidHom.id_apply]

theorem act_act_inv {x : G} (hx : x ∈ M) (w : V4 F) :
    N.act hMU hMA hx (N.act hMU hMA (M.inv_mem hx) w) = w := by
  have := N.act_inv_act hMU hMA (M.inv_mem hx) w
  simpa using this

theorem act_bijective {x : G} (hx : x ∈ M) : Function.Bijective (N.act hMU hMA hx) :=
  ⟨Function.LeftInverse.injective (N.act_inv_act hMU hMA hx),
    Function.RightInverse.surjective (N.act_act_inv hMU hMA hx)⟩

theorem act_of_mem {ℓ : G} (hℓM : ℓ ∈ M) (hℓ : ℓ ∈ L) (w : V4 F) :
    N.act hMU hMA hℓM w = mat (N.α ⟨ℓ, hℓ⟩) *ᵥ w := by
  obtain ⟨u, rfl⟩ := N.co_surj w
  rw [act_spec]
  exact N.β_equiv ⟨ℓ, hℓ⟩ u _ rfl

theorem act_normalizes (hLM : L ≤ M) (hML : M ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ M) : Normalizes (N.act hMU hMA hx) := by
  intro g
  obtain ⟨ℓ, rfl⟩ := N.α_surj g
  have hxl : x * (ℓ : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hML hx) ℓ).1 ℓ.2
  refine ⟨N.α ⟨_, hxl⟩, fun v => ?_⟩
  rw [← N.act_of_mem hMU hMA (hLM ℓ.2) ℓ.2, ← N.act_of_mem hMU hMA (hLM hxl) hxl]
  have h1 := congrArg (fun f => f v) (N.act_mul hMU hMA hx (hLM ℓ.2))
  have h2 := congrArg (fun f => f v) (N.act_mul hMU hMA (hLM hxl) hx)
  simp only [AddMonoidHom.comp_apply] at h1 h2
  rw [← h1, ← h2]
  exact congrArg (fun f => f v)
    (N.act_congr hMU hMA (show x * (ℓ : G) = x * ℓ * x⁻¹ * x by group) _ _)

theorem act_semilinear [Finite F] (hLM : L ≤ M) (hML : M ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ M) :
    ∃ σ : F →+* F, ∀ (c : F) (v : V4 F), N.act hMU hMA hx (c • v) = σ c • N.act hMU hMA hx v :=
  exists_semilinear (N.act_bijective hMU hMA hx) (N.act_normalizes hMU hMA hLM hML hx)

end Sp4NatData

end CFSG.Quasithin.MS93.S37
