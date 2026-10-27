module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Main

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P63

theorem exists_arc_map (F : FanTree Γ G) (h40 : Fan40 F) {a v b a' v' b' : V}
    (hv : valence Γ v = 3) (hv' : valence Γ v' = 3) (hav : Γ.Adj a v) (hvb : Γ.Adj v b)
    (hab : a ≠ b) (hav' : Γ.Adj a' v') (hvb' : Γ.Adj v' b') (hab' : a' ≠ b') :
    ∃ g : G, g • a = a' ∧ g • v = v' ∧ g • b = b' := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_of_valence_eq F (u := v) (w := v') (by rw [hv, hv'])
  have h1 : Γ.Adj v' (g₁ • a) := by
    have := (F.adj_smul g₁ _ _).2 hav.symm
    rwa [hg₁] at this
  obtain ⟨h, hh, hha⟩ := F.loc_trans v' _ _ h1 hav'.symm
  have hhv : h • v' = v' := MulAction.mem_stabilizer_iff.1 hh
  have hg₂b : Γ.Adj v' (h • g₁ • b) := by
    have h2 : Γ.Adj v' (g₁ • b) := by
      have := (F.adj_smul g₁ _ _).2 hvb
      rwa [hg₁] at this
    have := (F.adj_smul h _ _).2 h2
    rwa [hhv] at this
  have hne : h • g₁ • b ≠ a' := by
    intro e
    rw [← hha] at e
    exact hab (MulAction.injective g₁ (MulAction.injective h e)).symm
  obtain ⟨k, hk, hkb⟩ := F.exists_mem_nbrStab_smul_eq_of_valence_three h40 hav' hv' hg₂b
    hne hvb' hab'.symm
  have hka : k • a' = a' := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer a' hk)
  have hkv : k • v' = v' := mem_nbrStab.1 hk v' hav'
  refine ⟨k * h * g₁, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hha, hka]
  · rw [mul_smul, mul_smul, hg₁, hhv, hkv]
  · rw [mul_smul, mul_smul, hkb]

variable {L : ZLab Γ G} {ℓ : Line Γ} {j : ℤ}

theorem LineData.smul (D : LineData L ℓ j) (F : FanTree Γ G) (g : G) :
    LineData L (Line.smul F.adj_smul g ℓ) j := by
  refine ⟨?_, fun c i hc => ?_⟩
  · show valence Γ (g • ℓ.vert (j + 1)) = 3
    rw [F.valence_smul_eq]
    exact D.val
  · have hc' : valence Γ (ℓ.vert c) = 5 := by
      have : valence Γ (g • ℓ.vert c) = 5 := hc
      rwa [F.valence_smul_eq] at this
    show L.z (g • ℓ.vert c) • g • ℓ.vert i = g • ℓ.vert i ↔ _
    rw [z_smul hc' g, mul_smul, mul_smul, inv_smul_smul, (MulAction.injective g).eq_iff]
    exact D.fix c i hc'

variable (F : FanTree Γ G) (h40 : Fan40 F) (H : LabHyp L)
include F h40 H

theorem ballStab_four (D : LineData L ℓ j) {δ : V} (hδ : valence Γ δ = 5) :
    L.z δ ∈ ballStab Γ G 4 δ := by
  refine mem_ballStab.2 fun w hw => ?_
  by_cases h3 : Γ.dist δ w ≤ 3
  · exact mem_ballStab.1 (ballStab_three F H hδ) w h3
  have h4 : Γ.dist δ w = 4 := by omega
  obtain ⟨u₃, hu₃w, hd₃⟩ := exists_dist_pred F (n := 3) h4
  obtain ⟨u₂, hu₂u₃, hd₂⟩ := exists_dist_pred F (n := 2) hd₃
  obtain ⟨u₁, hu₁u₂, hd₁⟩ := exists_dist_pred F (n := 1) hd₂
  have hbr : Br Γ δ u₁ u₂ := ⟨dist_eq_one_iff_adj.1 hd₁, hu₁u₂, fun h => by
    rw [h, dist_self] at hd₂
    omega⟩
  have hv₂ : valence Γ u₂ = 5 := (Br.valence F hδ hbr).2
  have hv₃ : valence Γ u₃ = 3 := F.val3_of_adj_val5 hu₂u₃ hv₂
  have hne : u₂ ≠ w := fun h => by
    rw [← h, hd₂] at h4
    omega
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_arc_map F h40 D.val hv₃ (ℓ.adj j) (adj_j_j2 ℓ j) (ℓ.nb j)
    hu₂u₃ hu₃w hne
  have hbr' : Br Γ δ u₁ ((Line.smul F.adj_smul g ℓ).vert j) := by
    show Br Γ δ u₁ (g • ℓ.vert j)
    rw [hg1]
    exact hbr
  have := (D.smul F g).fix_four F h40 H hδ hbr'
    (by show Γ.dist δ (g • ℓ.vert (j + 1)) = 3; rw [hg2]; exact hd₃)
  show L.z δ • w = w
  have e : g • ℓ.vert (j + 2) = w := hg3
  rw [← e]
  exact this

end P63

end CFSG.Quasithin.Fan86
