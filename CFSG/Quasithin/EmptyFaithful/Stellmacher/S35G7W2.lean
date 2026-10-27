module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7W1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChLat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S35.G7

open CosetGeom F53

variable {G : Type} [Group G]

namespace WM

theorem card_map_eq_relIndex_ker {A B : Type} [Group A] [Group B] (f : A →* B) (T : Subgroup A) :
    Nat.card (T.map f) = f.ker.relIndex T := by
  have h1 : T.map f = (f.comp T.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h1, ← Subgroup.index_ker]
  have h2 : (f.comp T.subtype).ker = f.ker.subgroupOf T := by
    ext x; simp [Subgroup.mem_subgroupOf]
  rw [h2]
  rfl

theorem card_map_eq_of_inj {A B : Type} [Group A] [Group B] (f : A →* B) (U : Subgroup A)
    (h : ∀ u ∈ U, f u = 1 → u = 1) : Nat.card (U.map f) = Nat.card U := by
  rw [card_map_eq_relIndex_ker]
  have : f.ker.subgroupOf U = ⊥ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_bot]
    exact ⟨fun hx => Subtype.ext (h x x.2 hx), fun hx => by rw [hx]; simp⟩
  rw [Subgroup.relIndex, this, Subgroup.index_bot]

theorem relIndex_mul_card_inf (H K : Subgroup G) :
    H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card ↥K := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective,
    mul_comm]
  exact (H.subgroupOf K).card_mul_index

variable [Finite G] {H M S : Subgroup G} {β : Geo H M} {c : Ch.Chart β} {E K : Subgroup G}

@[expose] def fm (b : WBase (stab β) E K (Wb β) c.θ) : ↥(Wb β) →* orth.W := b.π.comp b.proj

variable (b : WBase (stab β) E K (Wb β) c.θ)

omit [Finite G] in
theorem fm_eq_one_iff (w : ↥(Wb β)) : fm b w = 1 ↔ (w : G) ∈ E := b.π_proj w

omit [Finite G] in
theorem fm_ker : (fm b).ker = E.subgroupOf (Wb β) := by
  ext w
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, fm_eq_one_iff]

omit [Finite G] in
theorem fm_conj (g : ↥(stab β)) (w : ↥(Wb β)) (h : (g : G) * (w : G) * (g : G)⁻¹ ∈ Wb β) :
    orth.act (c.θ g) (fm b w) = fm b ⟨(g : G) * (w : G) * (g : G)⁻¹, h⟩ := by
  show orth.act (c.θ g) (b.π (b.proj w)) = b.π (b.proj _)
  rw [← b.π_act, b.proj_conj g w h]

omit [Finite G] in
theorem card_map_fm {T : Subgroup G} (hT : T ≤ Wb β) :
    Nat.card ((T.subgroupOf (Wb β)).map (fm b)) = E.relIndex T := by
  rw [card_map_eq_relIndex_ker, fm_ker, Subgroup.relIndex_subgroupOf hT]

variable (hS : Sit H M S)
include hS

theorem exists_mem_Qv_of_mem_S5Syl (hβ : vtype β = false) {l₀ : Geo H M} (hl₀ : l₀ ∈ nbrs β)
    (hS5 : ((stab β ⊓ stab l₀).subgroupOf (stab β)).map c.θ = S5Syl) {s : Perm (Fin 5)}
    (hs : s ∈ S5Syl) : ∃ q : ↥(stab β), (q : G) ∈ Qv l₀ ∧ c.θ q = s := by
  have hle : Qv l₀ ≤ stab β := Std.Qv_le_stab hS (Std.mem_nbrs_symm.mp hl₀)
  rw [← hS5, Std.stab_inf_eq hS hβ hl₀, Subgroup.subgroupOf_sup (Ch.Qv_le_stab' β) hle,
    Subgroup.map_sup] at hs
  have hbot : ((Qv β).subgroupOf (stab β)).map c.θ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, c.ker_eq_Qv hS hβ]
  rw [hbot, bot_sup_eq] at hs
  obtain ⟨q, hq, rfl⟩ := hs
  exact ⟨q, Subgroup.mem_subgroupOf.mp hq, rfl⟩

end WM

end F53.Stellmacher.S35.G7

end CFSG.Quasithin
