module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinPair

public section

namespace CFSG.Quasithin.NoE9Z4MinGrp

open scoped commutatorElement

variable {G : Type*} [Group G]

structure WtCtx {Q U Z Hs : Subgroup G} {z : G} (_P : PairCtx Q U Z Hs z)
    (a b : G) (Ua Ub : Subgroup G) : Prop where
  a_mem : a ∈ Hs
  b_mem : b ∈ Hs
  Ua_le : Ua ≤ U
  Ub_le : Ub ≤ U
  Z_le_Ua : Z ≤ Ua
  Z_le_Ub : Z ≤ Ub
  decomp : ∀ u ∈ U, ∃ ua ∈ Ua, ∃ ub ∈ Ub, u = ua * ub
  b_triv : ∀ u ∈ Ua, ⁅b, u⁆ ∈ Z
  a_triv : ∀ u ∈ Ub, ⁅a, u⁆ ∈ Z
  a_kill : ∀ u ∈ Ua, u * (a * u * a⁻¹) * (a * a * u * a⁻¹ * a⁻¹) ∈ Z
  b_kill : ∀ u ∈ Ub, u * (b * u * b⁻¹) * (b * b * u * b⁻¹ * b⁻¹) ∈ Z
  a_inv : ∀ u ∈ Ua, a⁻¹ * u * a ∈ Ua
  b_inv : ∀ u ∈ Ub, b⁻¹ * u * b ∈ Ub
  a_gen : ∃ w₁ ∈ Ua, ∃ w₂ ∈ Ua, ∀ u ∈ Ua,
    ∃ c ∈ Z, u = c ∨ u = w₁ * c ∨ u = w₂ * c ∨ u = w₁ * w₂ * c
  b_gen : ∃ w₁ ∈ Ub, ∃ w₂ ∈ Ub, ∀ u ∈ Ub,
    ∃ c ∈ Z, u = c ∨ u = w₁ * c ∨ u = w₂ * c ∨ u = w₁ * w₂ * c

namespace WtCtx

variable {Q U Z Hs : Subgroup G} {z : G} {P : PairCtx Q U Z Hs z} {a b : G} {Ua Ub : Subgroup G}

theorem symm (W : WtCtx P a b Ua Ub) : WtCtx P b a Ub Ua where
  a_mem := W.b_mem
  b_mem := W.a_mem
  Ua_le := W.Ub_le
  Ub_le := W.Ua_le
  Z_le_Ua := W.Z_le_Ub
  Z_le_Ub := W.Z_le_Ua
  decomp u hu := by
    obtain ⟨ua, hua, ub, hub, rfl⟩ := W.decomp u hu
    exact ⟨ub, hub, ua, hua, P.U_comm ua (W.Ua_le hua) ub (W.Ub_le hub)⟩
  b_triv := W.a_triv
  a_triv := W.b_triv
  a_kill := W.b_kill
  b_kill := W.a_kill
  a_inv := W.b_inv
  b_inv := W.a_inv
  a_gen := W.b_gen
  b_gen := W.a_gen

end WtCtx

structure ClsData {Q U Z Hs : Subgroup G} {z : G} (_P : PairCtx Q U Z Hs z)
    {K : Type*} [CommGroup K] (β : ↥Hs →* MulAut K) (cls : G → K) : Prop where
  mul : ∀ u ∈ U, ∀ u' ∈ U, cls (u * u') = cls u * cls u'
  eq_one : ∀ u ∈ U, (cls u = 1 ↔ u ∈ Z)
  conj : ∀ x : ↥Hs, ∀ u ∈ U, cls ((x : G) * u * (x : G)⁻¹) = β x (cls u)
  surj : ∀ k : K, ∃ u ∈ U, cls u = k

end CFSG.Quasithin.NoE9Z4MinGrp
