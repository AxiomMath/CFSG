module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique

structure Ctx1 (W : Type) [CommGroup W] [Finite W] (G₀ K : Subgroup (MulAut W)) (a : MulAut W)
    (S : Subgroup (MulAut W)) (z : W) : Prop where
  exp : ∀ w : W, w ^ 2 = 1
  simple : IsSimpleGroup ↥K
  nab : ∃ x y : ↥K, x * y ≠ y * x
  irr : IsIrrOn153 K ⊤
  big : 2 ^ 6 ≤ Nat.card W
  G₀eq : G₀ = K ⊔ Subgroup.zpowers a
  aN : ∀ k ∈ K, a * k * a⁻¹ ∈ K
  a1 : a ≠ 1
  a2 : a ^ 2 = 1
  rk : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2
  syl : IsSylowTwoOf S K
  cent : ∀ x ∈ S, x * a = a * x
  zS : ∀ x ∈ S, x z = z
  z1 : z ≠ 1
  three : ∀ k ∈ K, orderOf k = 3 → k z ≠ z

structure Ctx2 (W : Type) [CommGroup W] [Finite W] (K : Subgroup (MulAut W)) (a : MulAut W)
    (S : Subgroup (MulAut W)) : Prop where
  exp : ∀ w : W, w ^ 2 = 1
  irr : IsIrrOn153 K ⊤
  big : 2 ^ 6 ≤ Nat.card W
  aN : ∀ k ∈ K, a * k * a⁻¹ ∈ K
  a1 : a ≠ 1
  a2 : a ^ 2 = 1
  rk : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2
  syl : IsSylowTwoOf S K
  cent : ∀ x ∈ S, x * a = a * x

theorem Ctx1.toCtx2 {W : Type} [CommGroup W] [Finite W] {G₀ K : Subgroup (MulAut W)} {a : MulAut W}
    {S : Subgroup (MulAut W)} {z : W} (h : Ctx1 W G₀ K a S z) : Ctx2 W K a S :=
  ⟨h.exp, h.irr, h.big, h.aN, h.a1, h.a2, h.rk, h.syl, h.cent⟩

theorem Ctx1.a_mem {W : Type} [CommGroup W] [Finite W] {G₀ K : Subgroup (MulAut W)} {a : MulAut W}
    {S : Subgroup (MulAut W)} {z : W} (h : Ctx1 W G₀ K a S z) : a ∈ G₀ := by
  rw [h.G₀eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)

theorem Ctx1.K_le {W : Type} [CommGroup W] [Finite W] {G₀ K : Subgroup (MulAut W)} {a : MulAut W}
    {S : Subgroup (MulAut W)} {z : W} (h : Ctx1 W G₀ K a S z) : K ≤ G₀ := by
  rw [h.G₀eq]
  exact le_sup_left

end S153G93D

end CFSG.Quasithin
