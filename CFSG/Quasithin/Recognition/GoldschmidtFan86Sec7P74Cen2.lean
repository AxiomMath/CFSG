module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Cen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Fix
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Conj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3WChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Val

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem edge_isPGroup (F : FanTree Γ G) (h65 : Fan65 F) {α ν : V} (hα : valence Γ α = 5)
    (hαν : Γ.Adj α ν) :
    IsPGroup 2 ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν) ∧
      Finite ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν) := by
  have hle : nbrStab Γ G α ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν :=
    fun g hg => ⟨F.nbrStab_le_stabilizer α hg,
      MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg ν hαν)⟩
  have hfin : Finite ↥(nbrStab Γ G α) := P71.finite_nbrStab F α
  obtain ⟨a, ha⟩ := (F.nbrStab_isPGroup α).exists_card_eq
  have hidx := F.relIndex_edge_eq_four h65 hα hαν
  have hcard := Subgroup.card_mul_index ((nbrStab Γ G α).subgroupOf
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν))
  have hK : Nat.card ↥((nbrStab Γ G α).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν)) = Nat.card ↥(nbrStab Γ G α) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hE : Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν) = 2 ^ (a + 2) := by
    rw [← hcard, hK, ha]
    have : ((nbrStab Γ G α).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν)).index = 4 := hidx
    rw [this]; ring
  refine ⟨IsPGroup.of_card hE, ?_⟩
  exact Nat.finite_of_card_ne_zero (by rw [hE]; positivity)

theorem ballStab_five_eq_bot (F : FanTree Γ G) (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T)
    (h62 : Fan62 F) (h65 : Fan65 F) {α : V} (hα : valence Γ α = 5) :
    ballStab Γ G 5 α = ⊥ := by
  by_contra hne
  obtain ⟨ν, hαν⟩ := F.exists_adj α
  obtain ⟨hE2, hEfin⟩ := edge_isPGroup F h65 hα hαν
  have hMK : ballStab Γ G 5 α ≤ nbrStab Γ G α := fixSet_anti (fun w hw => by
    show Γ.dist α w ≤ 5
    rw [dist_eq_one_iff_adj.2 hw]; norm_num)
  have hKfin : Finite ↥(nbrStab Γ G α) := P71.finite_nbrStab F α
  have hMfin : Finite ↥(ballStab Γ G 5 α) :=
    Finite.of_injective (Subgroup.inclusion hMK) (Subgroup.inclusion_injective _)
  have hM2 : IsPGroup 2 ↥(ballStab Γ G 5 α) := (F.nbrStab_isPGroup α).to_le hMK
  have hnorm : ∀ g ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν,
      ∀ m ∈ ballStab Γ G 5 α, g * m * g⁻¹ ∈ ballStab Γ G 5 α := fun g hg m hm =>
    ballStab_conj_stab F (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hg).1) hm
  obtain ⟨h, hhM, hh1, hh2, hhc⟩ := exists_centralized_involution hE2 hM2 hnorm hne
  have hhα : h • α = α := mem_ballStab.1 hhM α (by simp)
  have hhν : h • ν = ν := mem_ballStab.1 hhM ν (by rw [dist_eq_one_iff_adj.2 hαν]; norm_num)
  obtain ⟨T, hT⟩ := hΞ
  obtain ⟨c, hc⟩ := exists_track_edge F T
  obtain ⟨g₀, hg₀⟩ := P62.exists_smul_of_valence_eq F (u := α) (w := T.line.vert c)
    (by rw [hc, hα])
  have hadj1 : Γ.Adj (T.line.vert c) (g₀ • ν) := by
    have := (F.adj_smul g₀ α ν).2 hαν
    rwa [hg₀] at this
  obtain ⟨k, hk, hkν⟩ := F.loc_trans (T.line.vert c) (g₀ • ν) (T.line.vert (c + 1)) hadj1
    (T.line.adj c)
  have hkc : k • T.line.vert c = T.line.vert c := MulAction.mem_stabilizer_iff.1 hk
  obtain ⟨g, hg⟩ : ∃ g : G, g = k * g₀ := ⟨_, rfl⟩
  have hgα : g • α = T.line.vert c := by rw [hg, mul_smul, hg₀, hkc]
  have hgν : g • ν = T.line.vert (c + 1) := by rw [hg, mul_smul, hkν]
  have hz1 : g * h * g⁻¹ ≠ 1 := fun e => hh1 (by
    have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [this, e]; group)
  have hz2 : g * h * g⁻¹ * (g * h * g⁻¹) = 1 := by
    calc g * h * g⁻¹ * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
      _ = 1 := by rw [hh2]; group
  have hz0 : (g * h * g⁻¹) • T.line.vert c = T.line.vert c := by
    rw [← hgα, mul_smul, mul_smul, inv_smul_smul, hhα]
  have hz0' : (g * h * g⁻¹) • T.line.vert (c + 1) = T.line.vert (c + 1) := by
    rw [← hgν, mul_smul, mul_smul, inv_smul_smul, hhν]
  have hcen : g * h * g⁻¹ ∈ Cen (T.line.edgeStab (G := G) c : Set G) := by
    refine ⟨⟨MulAction.mem_stabilizer_iff.2 hz0, MulAction.mem_stabilizer_iff.2 hz0'⟩,
      fun k' hk' => ?_⟩
    have hk'1 : k' • T.line.vert c = T.line.vert c := MulAction.mem_stabilizer_iff.1 hk'.1
    have hk'2 : k' • T.line.vert (c + 1) = T.line.vert (c + 1) :=
      MulAction.mem_stabilizer_iff.1 hk'.2
    have hmem : g⁻¹ * k' * g ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G ν := by
      refine Subgroup.mem_inf.2
        ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
      · rw [mul_smul, mul_smul, hgα, hk'1, inv_smul_eq_iff, hgα]
      · rw [mul_smul, mul_smul, hgν, hk'2, inv_smul_eq_iff, hgν]
    have hcomm := hhc _ hmem
    calc k' * (g * h * g⁻¹) = g * ((g⁻¹ * k' * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * k' * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * h * g⁻¹) * k' := by group
  obtain ⟨i, hi, hdi⟩ := track_moves F h40 h62 hT hz1 hz2 hcen
  have hball : g * h * g⁻¹ ∈ ballStab Γ G 5 (T.line.vert c) := by
    rw [← hgα]; exact ballStab_conj F g hhM
  exact hi (mem_ballStab.1 hball _ hdi)

end P74

end CFSG.Quasithin.Fan86
