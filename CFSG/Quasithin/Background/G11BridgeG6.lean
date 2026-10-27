module

public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isQuotientOfSQTK_of_tauCeti {X : Type*} [Group X] (h : IsQuotientOfSQTKTauCeti X) :
    IsQuotientOfSQTK X := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h
  exact ⟨S, inferInstance, inferInstance, ⟨isStronglyQuasithin_of_tc hst, hkg⟩, φ, hφ⟩

theorem isQuotientOfSQTK_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsQuotientOfSQTK X) : IsQuotientOfSQTK Y := by
  obtain ⟨S, _, _, hS, φ, hφ⟩ := h
  exact ⟨S, inferInstance, inferInstance, hS, e.toMonoidHom.comp φ, e.surjective.comp hφ⟩

theorem isQuotientOfSQTK_toMulSub_iff (K : Subgroup (GLV V)) :
    IsQuotientOfSQTK ↥(toMulSub K) ↔ IsQuotientOfSQTK ↥K :=
  ⟨isQuotientOfSQTK_congr (toMulSubEquiv K).symm, isQuotientOfSQTK_congr (toMulSubEquiv K)⟩

theorem pCoreOf_toMulSub (K : Subgroup (GLV V)) :
    pCoreOf 2 (toMulSub K) = (pCoreOf 2 K).map linEquivMulAut.toMonoidHom :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 linEquivMulAut K

theorem pCoreOf_toMulSub_eq_bot_iff (K : Subgroup (GLV V)) :
    pCoreOf 2 (toMulSub K) = ⊥ ↔ pCoreOf 2 K = ⊥ := by
  rw [pCoreOf_toMulSub]
  exact Subgroup.map_eq_bot_iff_of_injective _ linEquivMulAut.injective

section Vocabulary

variable {K : Subgroup (GLV V)} {U W : Submodule (ZMod 2) V}

theorem isHSubmodule_toMulSub_iff :
    G6.IsHSubmodule (toMulSub K) (subToSubgroup U) ↔ Invariant K U := by
  constructor
  · intro h k hk u hu
    exact h (linEquivMulAut k) (linEquivMulAut_mem_toMulSub.2 hk) (Multiplicative.ofAdd u) hu
  · intro h f hf q hq
    obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
    exact h g (linEquivMulAut_mem_toMulSub.1 hf) (Multiplicative.toAdd q) hq

theorem submoduleClosure_toMulSub (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) :
    G6.submoduleClosure (toMulSub K) (subToSubgroup W) =
      subToSubgroup (⨆ g ∈ K, conjSub g W) := by
  rw [G6.submoduleClosure]
  apply le_antisymm
  · refine iSup₂_le fun f hf => ?_
    obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
    have h1 : (subToSubgroup W).map (linEquivMulAut g).toMonoidHom =
        subToSubgroup (conjSub g W) := (subToSubgroup_conjSub_toMulSub g W).symm
    rw [h1]
    exact subToSubgroup.monotone
      (le_iSup₂ (f := fun g (_ : g ∈ K) => conjSub g W) g (linEquivMulAut_mem_toMulSub.1 hf))
  · refine subToSubgroup.le_symm_apply.1 ?_
    refine iSup₂_le fun g hg => ?_
    refine subToSubgroup.le_symm_apply.2 ?_
    rw [subToSubgroup_conjSub_toMulSub]
    exact le_iSup₂_of_le (linEquivMulAut g) (linEquivMulAut_mem_toMulSub.2 hg) le_rfl

theorem conjClosure_toMulSub (K L : Subgroup (GLV V)) :
    conjClosure (toMulSub L) (toMulSub K) = toMulSub (normalClosure K L) := by
  have h1 : toMulSub (normalClosure K L) = Subgroup.closure
      (linEquivMulAut.toMonoidHom '' {x | ∃ γ ∈ K, ∃ l ∈ L, x = γ * l * γ⁻¹}) := by
    unfold toMulSub normalClosure
    rw [MonoidHom.map_closure]
  rw [h1, conjClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨h, ⟨g, hg, rfl⟩, z, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨g * l * g⁻¹, ⟨g, hg, l, hl, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨γ, hγ, l, hl, rfl⟩, rfl⟩
    exact ⟨linEquivMulAut γ, ⟨γ, hγ, rfl⟩, linEquivMulAut l, ⟨l, hl, rfl⟩, by simp⟩

theorem zpowers_linEquivMulAut (a : GLV V) :
    Subgroup.zpowers (linEquivMulAut a) = toMulSub (Subgroup.zpowers a) :=
  (MonoidHom.map_zpowers linEquivMulAut.toMonoidHom a).symm

theorem classClosure_toMulSub (K : Subgroup (GLV V)) (a : GLV V) :
    G6.classClosure (toMulSub K) (linEquivMulAut a) =
      toMulSub (normalClosure K (Subgroup.zpowers a)) := by
  rw [G6.classClosure, zpowers_linEquivMulAut, conjClosure_toMulSub]

theorem classClosure_eq_iff (K : Subgroup (GLV V)) (a : GLV V) :
    toMulSub K = G6.classClosure (toMulSub K) (linEquivMulAut a) ↔
      K = normalClosure K (Subgroup.zpowers a) := by
  rw [classClosure_toMulSub]
  exact toMulSub_injective.eq_iff

end Vocabulary

structure Hypothesis61 (K : Subgroup (GLV V)) (a : GLV V) : Prop where
  pCoreOf_eq_bot : pCoreOf 2 K = ⊥
  isQuotientOfSQTK : IsQuotientOfSQTKTauCeti ↥K
  mem : a ∈ K
  ne_one : a ≠ 1
  mul_self : a * a = 1
  finrank_le : Module.finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 2
  span : (⨆ g ∈ K, conjSub g (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id))) = ⊤

theorem Hypothesis61.toMulSub [Finite V] {K : Subgroup (GLV V)} {a : GLV V}
    (h : Hypothesis61 K a) : G6.Hypothesis61 (toMulSub K) (linEquivMulAut a) where
  sq_eq_one := fun v => multiplicative_sq_eq_one v
  pCoreOf_eq_bot := (pCoreOf_toMulSub_eq_bot_iff K).2 h.pCoreOf_eq_bot
  isQuotientOfSQTK :=
    (isQuotientOfSQTK_toMulSub_iff K).2 (isQuotientOfSQTK_of_tauCeti h.isQuotientOfSQTK)
  mem := linEquivMulAut_mem_toMulSub.2 h.mem
  ne_one := fun h1 => h.ne_one (linEquivMulAut.injective (by rw [h1, map_one]))
  mul_self := by rw [← map_mul, h.mul_self, map_one]
  card_commV_le := by
    rw [commV_zpowers_toMulSub]
    have := (natCard_subToSubgroup_le_iff
      (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) 2).2 h.finrank_le
    simpa using this
  span := by
    rw [commV_zpowers_toMulSub, submoduleClosure_toMulSub, h.span, OrderIso.map_top]

theorem card_commV_zpowers_toMulSub_eq_two_iff [Finite V] (a : GLV V) :
    Nat.card (commV (Subgroup.zpowers (linEquivMulAut a))) = 2 ↔
      Module.finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) = 1 := by
  rw [commV_zpowers_toMulSub]
  simpa using natCard_subToSubgroup_eq_iff (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) 1

end G11

end CFSG.Quasithin
