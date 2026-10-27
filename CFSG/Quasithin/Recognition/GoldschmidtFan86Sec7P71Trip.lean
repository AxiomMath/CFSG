module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Tri

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_nbr_of_prod_one (F : FanTree Γ G) (L : ZLab Γ G)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    (h517 : ∀ α, Fan86.valence Γ α = 5 → ∀ l₁ l₂ l₃ : V, Γ.dist α l₁ = 2 → Γ.dist α l₂ = 2 →
      Γ.dist α l₃ = 2 → L.z l₁ * L.z l₂ * L.z l₃ ∉ Subgroup.zpowers (L.z α))
    {a b c : V} (ha : Fan86.valence Γ a = 5) (hb : Fan86.valence Γ b = 5)
    (hc : Fan86.valence Γ c = 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hprod : L.z a * L.z b * L.z c = 1) : ∃ β, ({a, b, c} : Set V) = Γ.neighborSet β := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := tri_rel (L.isCentral a ha).2.2.1 (L.isCentral b hb).2.2.1
    (L.isCentral c hc).2.2.1 hprod
  have dab := dist_le_four F L hfix ha hb (r1.trans r2.symm)
  have dac := dist_le_four F L hfix ha hc (r5.trans r6.symm)
  have h2or4 : ∀ x y : V, Fan86.valence Γ x = 5 → Fan86.valence Γ y = 5 → x ≠ y →
      Γ.dist x y ≤ 4 → Γ.dist x y = 2 ∨ Γ.dist x y = 4 := by
    intro x y hx hy hxy hd
    have h1 := dist_even F hx hy
    have h2 := F.isTree.connected.pos_dist_of_ne hxy
    omega
  by_cases d1 : Γ.dist a b = 2
  · exact pair_two F L hfix ha hb hc hab hac hbc r1 d1
  by_cases d2 : Γ.dist a c = 2
  · obtain ⟨β, hβ⟩ := pair_two F L hfix ha hc hb hac hab (Ne.symm hbc) r5 d2
    refine ⟨β, ?_⟩
    rw [← hβ]
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  by_cases d3 : Γ.dist b c = 2
  · obtain ⟨β, hβ⟩ := pair_two F L hfix hb hc ha hbc (Ne.symm hab) (Ne.symm hac) r3 d3
    refine ⟨β, ?_⟩
    rw [← hβ]
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  exfalso
  have e1 : Γ.dist a b = 4 := (h2or4 a b ha hb hab dab).resolve_left d1
  have e2 : Γ.dist a c = 4 := (h2or4 a c ha hc hac dac).resolve_left d2
  obtain ⟨m, hm, hma, hmb, hmc⟩ := pair_four F L hfix ha hb hc r1 e1 e2
  apply h517 m hm a b c hma hmb hmc
  rw [hprod]
  exact Subgroup.one_mem _

end P71

end CFSG.Quasithin.Fan86
