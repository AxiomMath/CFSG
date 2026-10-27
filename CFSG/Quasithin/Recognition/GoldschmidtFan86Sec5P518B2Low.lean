module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86B2LayersMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem normal_subgroupOf_of_conj {M N : Subgroup G}
    (h : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) : (N.subgroupOf M).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h g g.2 n hn⟩

theorem ballStab_two_le_nbr (v : V) : ballStab Γ G 2 v ≤ nbrStab Γ G v := by
  intro g hg
  rw [mem_ballStab] at hg
  rw [mem_nbrStab]
  intro w hw
  exact hg w (by rw [SimpleGraph.dist_eq_one_iff_adj.2 hw]; norm_num)

theorem lowerBound_of_layers (F : FanTree Γ G) {v : V} {x : G}
    (hx : x ∈ MulAction.stabilizer G v) (hxo : orderOf x = 5) {N : Subgroup G}
    (hN : N ≤ ballStab Γ G 2 v) (hNn : ∀ g ∈ MulAction.stabilizer G v, ∀ h ∈ N, g * h * g⁻¹ ∈ N)
    (e1 : ∃ q ∈ nbrStab Γ G v, x * q * x⁻¹ * q⁻¹ ∉ ballStab Γ G 2 v)
    (e2 : ∃ g ∈ ballStab Γ G 2 v, x * g * x⁻¹ * g⁻¹ ∉ N)
    (e3 : ∃ h ∈ N, x * h * x⁻¹ * h⁻¹ ≠ 1) :
    2 ^ 12 ≤ cIdx Γ x v := by
  have hKst : nbrStab Γ G v ≤ MulAction.stabilizer G v := F.nbrStab_le_stabilizer v
  have hxv : x • v = v := hx
  have : Finite (MulAction.stabilizer G v) := F.loc_finite v
  have : Finite (nbrStab Γ G v) :=
    Finite.of_injective (Subgroup.inclusion hKst) (Subgroup.inclusion_injective hKst)
  have hB1 : ballStab Γ G 2 v ≤ nbrStab Γ G v := ballStab_two_le_nbr v
  have hBst : ballStab Γ G 2 v ≤ MulAction.stabilizer G v := hB1.trans hKst
  have hBconj : ∀ g ∈ MulAction.stabilizer G v, ∀ y ∈ ballStab Γ G 2 v,
      g * y * g⁻¹ ∈ ballStab Γ G 2 v := by
    intro g hg y hy
    have := ballStab_conj F g hy
    rwa [show g • v = v from hg] at this
  have hx5 : x ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  exact three_layers (F.nbrStab_isPGroup v) hx5 hB1 hN
    (normal_subgroupOf_of_conj fun m hm n hn => hBconj m (hKst hm) n hn)
    (normal_subgroupOf_of_conj fun m hm n hn => hNn m (hBst hm) n hn)
    (fun q hq => nbrStab_conj_mem F hxv hq)
    (fun n hn => hBconj x hx n hn)
    (fun n hn => hNn x hx n hn) e1 e2 e3

end P518

end CFSG.Quasithin.Fan86
