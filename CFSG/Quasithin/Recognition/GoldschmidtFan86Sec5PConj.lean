module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem valence_smul_eq (g : G) (v : V) : Fan86.valence Γ (g • v) = Fan86.valence Γ v := by
  unfold Fan86.valence
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun w => ?_)
  have := F.adj_smul g⁻¹ (g • v) w
  simp only [inv_smul_smul] at this
  simp only [mem_neighborSet, MulAction.toPerm_apply]
  exact this.symm

theorem conj_mem_nbrStab_smul (k : G) {β : V} {y : G} (hy : y ∈ nbrStab Γ G β) :
    k * y * k⁻¹ ∈ nbrStab Γ G (k • β) := by
  intro u hu
  have hu' : Γ.Adj β (k⁻¹ • u) := by
    have := (F.adj_smul k⁻¹ (k • β) u).2 hu
    rwa [inv_smul_smul] at this
  have := mem_nbrStab.1 hy _ hu'
  rw [mul_smul, mul_smul, this, smul_inv_smul]

theorem nbrStab_smul (k : G) (β : V) :
    nbrStab Γ G (k • β) = (nbrStab Γ G β).map (MulAut.conj k).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hz
    refine ⟨k⁻¹ * z * k, ?_, by group⟩
    have := F.conj_mem_nbrStab_smul k⁻¹ hz
    rw [inv_smul_smul, inv_inv] at this
    exact this
  · rintro ⟨y, hy, rfl⟩
    exact F.conj_mem_nbrStab_smul k hy

theorem map_conj_nbrStab {v : V} {g : G} (hg : g • v = v) :
    (nbrStab Γ G v).map (MulAut.conj g).toMonoidHom = nbrStab Γ G v := by
  have := F.nbrStab_smul g v
  rw [hg] at this
  exact this.symm

end FanTree

end CFSG.Quasithin.Fan86
