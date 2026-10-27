module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Swap
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Ext

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace X1512

variable {G : Type} [Group G] {n : ℕ}

@[expose] def kerSub {K : Subgroup G} {Y : Type*} [Group Y] (Ψ : ↥K →* Y) : Subgroup G :=
  Ψ.ker.map K.subtype

theorem mem_kerSub {K : Subgroup G} {Y : Type*} [Group Y] {Ψ : ↥K →* Y} {g : G} :
    g ∈ kerSub Ψ ↔ ∃ h : g ∈ K, Ψ ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem kerSub_le {K : Subgroup G} {Y : Type*} [Group Y] (Ψ : ↥K →* Y) : kerSub Ψ ≤ K := by
  intro g hg
  obtain ⟨h, -⟩ := mem_kerSub.mp hg
  exact h

theorem kerSub_normalizer {K : Subgroup G} {Y : Type*} [Group Y] (Ψ : ↥K →* Y) :
    K ≤ Subgroup.normalizer (kerSub Ψ : Set G) := by
  refine le_normalizer_of_forall fun k hk x hx => ?_
  obtain ⟨hxK, hx1⟩ := mem_kerSub.mp hx
  refine mem_kerSub.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩
  have : (⟨k * x * k⁻¹, K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩ : ↥K) =
      ⟨k, hk⟩ * ⟨x, hxK⟩ * ⟨k, hk⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, hx1, mul_one, map_inv, mul_inv_cancel]

theorem subgroupOf_kerSub {K : Subgroup G} {Y : Type*} [Group Y] (Ψ : ↥K →* Y) :
    (kerSub Ψ).subgroupOf K = Ψ.ker := by
  ext k
  rw [Subgroup.mem_subgroupOf, mem_kerSub, MonoidHom.mem_ker]
  exact ⟨fun ⟨h, h1⟩ => h1, fun h => ⟨k.2, h⟩⟩

variable {H U L N K F₁ F₂ X₁ X₂ : Subgroup G}

namespace WrStep

variable (P : WrStep H U L N K F₁ F₂ X₁ X₂)

include P

theorem ψ₂_eq_one_of_mem_F₁ (hn : n = 3 ∨ n = 5) [(L.subgroupOf X₂).Normal]
    {Ψ₂ : ↥K →* Equiv.Perm (Fin n)} {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂}
    (M : NatMod n K L X₂ Ψ₂ β₂) {f : G} (hf : f ∈ F₁) : Ψ₂ ⟨f, P.F₁_le_K hf⟩ = 1 :=
  (M.ψ_eq_one_iff hn P.L_le₂ _).mpr fun x hx => P.F₁_triv f hf x hx

theorem ker_prod (hn : n = 3 ∨ n = 5) [(L.subgroupOf X₁).Normal] [(L.subgroupOf X₂).Normal]
    {Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n)} {β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁}
    {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂} (M₁ : NatMod n K L X₁ Ψ₁ β₁)
    (M₂ : NatMod n K L X₂ Ψ₂ β₂) :
    (Ψ₁.prod Ψ₂).ker = (cSecIn H L N).subgroupOf K := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_forall P.H_norm_L
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.prod_apply, Prod.mk_eq_one,
    M₁.ψ_eq_one_iff hn P.L_le₁, M₂.ψ_eq_one_iff hn P.L_le₂]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine Subgroup.subset_closure ⟨P.K_le k.2, fun x hx => ?_⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := P.exists_mul_of_mem_N hx
    rw [P.conj_comm_mul (P.K_le k.2) (P.X₁_le hu₁) (P.X₂_le hu₂)]
    exact L.mul_mem (h₁ u₁ hu₁) (h₂ u₂ hu₂)
  · intro hk
    have := (mem_cSecIn_of_normalizes hHL hk).2
    exact ⟨fun x hx => this x (P.X₁_le hx), fun x hx => this x (P.X₂_le hx)⟩

end WrStep

end X1512

end CFSG.Quasithin
