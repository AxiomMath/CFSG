module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem mem_ker_or {x y : V} (hxy : Γ.Adj x y) (hy3 : Fan86.valence Γ y = 3) {g₀ : G}
    (hx₀ : g₀ • x = x) (hy₀ : g₀ • y = y) (hK₀ : g₀ ∉ nbrStab Γ G y) {k : G} (hxk : k • x = x)
    (hyk : k • y = y) : k ∈ nbrStab Γ G y ∨ g₀⁻¹ * k ∈ nbrStab Γ G y := by
  obtain ⟨φ, key, -⟩ := F.exists_edge_char hxy.symm
  let e₀ : ↥(MulAction.stabilizer G y ⊓ MulAction.stabilizer G x) :=
    ⟨g₀, MulAction.mem_stabilizer_iff.2 hy₀, MulAction.mem_stabilizer_iff.2 hx₀⟩
  let ek : ↥(MulAction.stabilizer G y ⊓ MulAction.stabilizer G x) :=
    ⟨k, MulAction.mem_stabilizer_iff.2 hyk, MulAction.mem_stabilizer_iff.2 hxk⟩
  have h0 : φ e₀ ≠ 1 := fun h => hK₀ ((key e₀).2 h)
  by_cases hk : φ ek = 1
  · exact Or.inl ((key ek).2 hk)
  · refine Or.inr ((key (e₀⁻¹ * ek)).2 ?_ : ((e₀⁻¹ * ek : ↥(MulAction.stabilizer G y ⊓
      MulAction.stabilizer G x)) : G) ∈ nbrStab Γ G y)
    rw [map_mul, map_inv, units_three hy3 _ _ hk h0, inv_mul_cancel]

theorem edge_mem_of_ker (h40 : Fan40 F) {x y : V} (hxy : Γ.Adj x y)
    (hy3 : Fan86.valence Γ y = 3) {M : Subgroup G} (hKx : ∀ k ∈ nbrStab Γ G x, k ∈ M)
    (hKy : ∀ k ∈ nbrStab Γ G y, k ∈ M) {g : G} (hgx : g • x = x) (hgy : g • y = y) : g ∈ M := by
  obtain ⟨g₀, hg₀x, hg₀y⟩ := IsConcreteLE.not_le_iff_exists.1 (F.not_nbrStab_le_nbrStab h40 hxy)
  have hx₀ : g₀ • x = x := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer x hg₀x)
  have hy₀ : g₀ • y = y := mem_nbrStab.1 hg₀x y hxy
  rcases F.mem_ker_or hxy hy3 hx₀ hy₀ hg₀y hgx hgy with h | h
  · exact hKy g h
  · have := M.mul_mem (hKx g₀ hg₀x) (hKy _ h)
    simpa using this

theorem ker_mem_of_elt {x y : V} (hxy : Γ.Adj x y) (hy3 : Fan86.valence Γ y = 3)
    {M : Subgroup G} (hKy : ∀ k ∈ nbrStab Γ G y, k ∈ M) {g₀ : G} (hg₀M : g₀ ∈ M)
    (hx₀ : g₀ • x = x) (hy₀ : g₀ • y = y) (hK₀ : g₀ ∉ nbrStab Γ G y) {k : G}
    (hk : k ∈ nbrStab Γ G x) : k ∈ M := by
  have hxk : k • x = x := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer x hk)
  have hyk : k • y = y := mem_nbrStab.1 hk y hxy
  rcases F.mem_ker_or hxy hy3 hx₀ hy₀ hK₀ hxk hyk with h | h
  · exact hKy k h
  · have := M.mul_mem hg₀M (hKy _ h)
    simpa using this

theorem gcirc_mem_of_elt {u w : V} (huw : Γ.Adj u w) (h5 : Fan86.valence Γ u = 5)
    {M : Subgroup G} (hKu : ∀ k ∈ nbrStab Γ G u, k ∈ M) {t : G} (htM : t ∈ M) (htu : t • u = u)
    (htw : t • w = w) (htK : t ∉ nbrStab Γ G u) {g : G} (hg : g ∈ Gcirc Γ G u w) : g ∈ M := by
  obtain ⟨φ, key, -⟩ := F.exists_edge_char huw
  obtain ⟨⟨hgu, hgw⟩, hgg⟩ := hg
  let et : ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G w) :=
    ⟨t, MulAction.mem_stabilizer_iff.2 htu, MulAction.mem_stabilizer_iff.2 htw⟩
  let eg : ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G w) := ⟨g, hgu, hgw⟩
  have ht1 : φ et ≠ 1 := fun h => htK ((key et).2 h)
  have hg2 : φ eg ^ 2 = 1 := by
    rw [← map_pow, pow_two]
    exact (key (eg * eg)).1 hgg
  obtain ⟨j, hj⟩ := units_five_mem h5 (φ et) (φ eg) ht1 hg2
  have hmem : (((et ^ (j : ℕ))⁻¹ * eg : ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G w)) :
      G) ∈ nbrStab Γ G u := by
    refine (key _).2 ?_
    rw [map_mul, map_inv, map_pow, hj, inv_mul_cancel]
  have hmem' : (t ^ (j : ℕ))⁻¹ * g ∈ nbrStab Γ G u := by
    simpa using hmem
  have := M.mul_mem (M.pow_mem htM j) (hKu _ hmem')
  simpa using this

end FanTree

end CFSG.Quasithin.Fan86
