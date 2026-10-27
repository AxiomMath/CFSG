module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65Up
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65Low

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62 P63

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P65

variable {L : ZLab Γ G} {ℓ : Line Γ} {j : ℤ}

theorem core (F : FanTree Γ G) (h40 : Fan40 F) (h33 : Fan33 F) (h63 : Fan63 F) (h64 : Fan64 F)
    (h517a : Fan517a F) (D : LineData L ℓ j) :
    (∀ x ∈ MulAction.stabilizer G (ℓ.vert j), orderOf x = 5 →
      (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G (ℓ.vert j)) = 2 ^ 8) ∧
    (nbrStab Γ G (ℓ.vert j)).relIndex
      (MulAction.stabilizer G (ℓ.vert j) ⊓ MulAction.stabilizer G (ℓ.vert (j + 1))) = 4 := by
  have hv5 : valence Γ (ℓ.vert j) = 5 := D.val_five_j F
  have hz : L.z (ℓ.vert j) ∈ Cinv G (ℓ.vert j) := cinv_iff.2 (L.isCentral _ hv5)
  obtain ⟨x₀, hx₀, hx₀o, hle⟩ := exists_x0_bound F D
  have hlow := index_ge F h40 h33 h63 h64 h517a hv5 hz hx₀ hx₀o
  have hh := F.relIndex_nbrStab_mem_two_four (ℓ.adj j)
  have h4 : (nbrStab Γ G (ℓ.vert j)).relIndex
      (MulAction.stabilizer G (ℓ.vert j) ⊓ MulAction.stabilizer G (ℓ.vert (j + 1))) = 4 := by
    rcases hh with h | h
    · rw [h] at hle
      omega
    · exact h
  refine ⟨fun x hx hxo => le_antisymm ?_ ?_, h4⟩
  · have := F.centralizer_relIndex_le hx₀ hx (by rw [hx₀o, hv5]) (by rw [hxo, hv5])
    rw [h4] at hle
    omega
  · exact index_ge F h40 h33 h63 h64 h517a hv5 hz hx hxo

theorem core_at (F : FanTree Γ G) (h40 : Fan40 F) (h33 : Fan33 F) (h63 : Fan63 F)
    (h64 : Fan64 F) (h517a : Fan517a F) (D : LineData L ℓ j) {α : V} (hα : valence Γ α = 5) :
    (∀ x ∈ MulAction.stabilizer G α, orderOf x = 5 →
      (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G α) = 2 ^ 8) ∧
    ∀ β, Γ.Adj α β →
      (nbrStab Γ G α).relIndex (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 4 := by
  obtain ⟨g, hg⟩ := exists_smul_of_valence_eq F (u := ℓ.vert j) (w := α)
    (by rw [hα, D.val_five_j F])
  have hD := D.smul F g
  have e : (Line.smul F.adj_smul g ℓ).vert j = α := hg
  have hadj : Γ.Adj α ((Line.smul F.adj_smul g ℓ).vert (j + 1)) := by
    have := (Line.smul F.adj_smul g ℓ).adj j
    rwa [e] at this
  obtain ⟨hc1, hc2⟩ := core F h40 h33 h63 h64 h517a hD
  rw [e] at hc1 hc2
  refine ⟨hc1, fun β hαβ => ?_⟩
  rw [F.relIndex_edge_eq hadj hαβ rfl]
  exact hc2

end P65

end CFSG.Quasithin.Fan86
