module

public import CFSG.Quasithin.EmptyFaithful.S153E61CA
public import CFSG.Quasithin.EmptyFaithful.S153E61CD

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem fuse_V (cx : Ctx15350 T Mc M V₁ V₂ t) {z v : G}
    (hz : Subgroup.zpowers z = quasithinOmegaOneCenter T) (hv : Subgroup.zpowers v = ZS153 T M V₁ ⊓ V₁)
    (hv1 : v ≠ 1) :
    ∀ w ∈ VZ T M, w ≠ 1 → (∃ m ∈ M, m * z * m⁻¹ = w) ∨ (∃ m ∈ M, m * v * m⁻¹ = w) :=
  S153E61C.fuse_V_of_gens cx hz hv hv1

theorem Pi_elemAbelian (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁) :
    (∀ a ∈ Pi153 T Mc M V₁ N₁ g, ∀ b ∈ Pi153 T Mc M V₁ N₁ g, a * b = b * a ∧ a * a = 1) ∧
    (∀ a ∈ Pi153 T Mc M V₁ N₂ g, ∀ b ∈ Pi153 T Mc M V₁ N₂ g, a * b = b * a ∧ a * a = 1) := by
  obtain ⟨h₁, h₂⟩ := S153E61C.Pi_sq_eq_one cx c.toChain15354
  exact ⟨fun a ha b hb => ⟨S153E61C.comm_of_sq_eq_one h₁ ha hb, h₁ a ha⟩,
    fun a ha b hb => ⟨S153E61C.comm_of_sq_eq_one h₂ ha hb, h₂ a ha⟩⟩

theorem inv_P_mem_Pi (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∀ x ∈ Pgp153 T M V₁ Mc g, x * x = 1 →
      x ∈ Pi153 T Mc M V₁ N₁ g ∨ x ∈ Pi153 T Mc M V₁ N₂ g :=
  S153E61C.inv_P_mem_Pi_of_chain cx c

end S153E

end CFSG.Quasithin
