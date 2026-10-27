module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α) (F : FanTree Γ G) (g : G)

@[expose] def translate : D10Set L (g • α) where
  P i := Arc.act F g (D.P i)
  val := (valence_smul F g α).trans D.val
  start i := by rw [Arc.act_vert, D.start]
  inj := by
    intro i j hij
    apply D.inj
    have h1 : L.z (g • D.delta i) = L.z (g • D.delta j) := hij
    rw [L.equivariant g _ (D.valence_delta F i), L.equivariant g _ (D.valence_delta F j)] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  dih := by
    have hmap : (Subgroup.closure (Set.range fun i => L.z ((Arc.act F g (D.P i)).vert 4))) =
        (Subgroup.closure (Set.range fun i => L.z ((D.P i).vert 4))).map
          (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      congr 2
      funext i
      exact L.equivariant g _ (D.valence_delta F i)
    obtain ⟨e⟩ := D.dih
    exact ⟨((MulEquiv.subgroupCongr hmap).trans
      (MulEquiv.subgroupMap (MulAut.conj g) _).symm).trans e⟩
  conj := by
    intro i
    have hz : ∀ k : Fin 5, L.z ((Arc.act F g (D.P k)).vert 4) = g * L.z (D.delta k) * g⁻¹ :=
      fun k => L.equivariant g _ (D.valence_delta F k)
    have h : (L.z (D.delta 2) * L.z (D.delta 0))⁻¹ * L.z (D.delta i) *
        (L.z (D.delta 2) * L.z (D.delta 0)) = L.z (D.delta (i + 1)) := D.conj i
    simp only [hz]
    calc (g * L.z (D.delta 2) * g⁻¹ * (g * L.z (D.delta 0) * g⁻¹))⁻¹ *
          (g * L.z (D.delta i) * g⁻¹) * (g * L.z (D.delta 2) * g⁻¹ * (g * L.z (D.delta 0) * g⁻¹))
        = g * ((L.z (D.delta 2) * L.z (D.delta 0))⁻¹ * L.z (D.delta i) *
          (L.z (D.delta 2) * L.z (D.delta 0))) * g⁻¹ := by group
      _ = g * L.z (D.delta (i + 1)) * g⁻¹ := by rw [h]

variable {F g}

theorem translate_alpha (i : Fin 5) : (D.translate F g).alpha i = g • D.alpha i := rfl

theorem translate_delta (i : Fin 5) : (D.translate F g).delta i = g • D.delta i := rfl

end D10Set

end CFSG.Quasithin.Fan86
