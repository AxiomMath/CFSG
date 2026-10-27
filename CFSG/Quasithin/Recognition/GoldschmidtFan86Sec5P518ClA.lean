module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Z4

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

variable (F : FanTree Γ G) {L : ZLab Γ G} (H : Lab18 L)

include F H

theorem claimA_core {x0 x2 x4 : V} (hv0 : valence Γ x0 = 5) (hv2 : valence Γ x2 = 5)
    (hv4 : valence Γ x4 = 5) (h20 : Γ.dist x2 x0 = 2) (h24 : Γ.dist x2 x4 = 2)
    (hK : L.z x0 ∈ nbrStab Γ G x4) {δ : V} (hδ : Γ.dist x4 δ = 2) : L.z x0 • δ = δ := by
  by_contra hmove
  have hax4 : L.z x0 • x4 = x4 := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer x4 hK)
  obtain ⟨ν, hν⟩ := exists_br F hδ
  obtain ⟨hν3, hvδ⟩ := Br.valence F hv4 hν
  have haν : L.z x0 • ν = ν := mem_nbrStab.1 hK ν hν.1
  obtain ⟨δ', hδ', hne', hset⟩ := exists_sibling F hv4 hν
  have hadj : Γ.Adj ν (L.z x0 • δ) := by
    have := (F.adj_smul (L.z x0) ν δ).2 hν.2.1
    rwa [haν] at this
  have hswap : L.z x0 • δ = δ' := by
    have hmem : L.z x0 • δ ∈ Γ.neighborSet ν := hadj
    rw [hset] at hmem
    rcases hmem with h | h | h
    · exact absurd (MulAction.injective (L.z x0) (h.trans hax4.symm)) hν.2.2
    · exact absurd h hmove
    · exact h
  have e1 : L.z δ' = L.z δ * L.z x4 := sib_label F H.hyp hv4 hν hδ' hne'.symm
  have e2 : L.z δ' = L.z x0 * L.z δ * (L.z x0)⁻¹ := by
    rw [← hswap]
    exact L.equivariant (L.z x0) δ hvδ
  have e3 : L.z δ * L.z x4 = L.z x4 * L.z δ := z_comm_dist F H.hyp hv4 hδ
  have hz4 : L.z δ ∈ ballStab Γ G 2 x4 := H.z4 δ x4 hvδ (by rw [dist_comm]; exact hδ)
  have hzx2 : L.z δ • x2 = x2 := mem_ballStab.1 hz4 x2 (by rw [dist_comm, h24])
  have hdα : Γ.dist x2 (L.z δ • x0) = 2 := by
    have := dist_smul F (L.z δ) x2 x0
    rw [hzx2] at this
    rw [this]
    exact h20
  have e5 : L.z (L.z δ • x0) = L.z δ * L.z x0 * (L.z δ)⁻¹ := L.equivariant (L.z δ) x0 hv0
  have ia : (L.z x0)⁻¹ = L.z x0 := z_inv hv0
  have id' : (L.z δ)⁻¹ = L.z δ := z_inv hvδ
  have e4 : L.z x0 * L.z δ * L.z x0 = L.z δ * L.z x4 := by
    have := e2.symm.trans e1
    rwa [ia] at this
  have hprod : L.z x0 * L.z (L.z δ • x0) * L.z x4 = 1 := by
    rw [e5, id']
    calc L.z x0 * (L.z δ * L.z x0 * L.z δ) * L.z x4
        = (L.z x0 * L.z δ * L.z x0) * L.z δ * L.z x4 := by simp only [mul_assoc]
      _ = (L.z δ * L.z x4) * L.z δ * L.z x4 := by rw [e4]
      _ = L.z δ * (L.z x4 * L.z δ) * L.z x4 := by simp only [mul_assoc]
      _ = L.z δ * (L.z δ * L.z x4) * L.z x4 := by rw [← e3]
      _ = (L.z δ * L.z δ) * (L.z x4 * L.z x4) := by simp only [mul_assoc]
      _ = 1 := by rw [z_sq hvδ, z_sq hv4, one_mul]
  exact H.hyp.triple x2 x0 (L.z δ • x0) x4 hv2 h20 hdα h24 (by rw [hprod]; exact one_mem _)

theorem claimA' {x0 x1 x2 x3 x4 x5 : V} (a01 : Γ.Adj x0 x1) (a12 : Γ.Adj x1 x2)
    (a23 : Γ.Adj x2 x3) (a34 : Γ.Adj x3 x4) (a45 : Γ.Adj x4 x5) (n02 : x0 ≠ x2) (n24 : x2 ≠ x4)
    (n35 : x3 ≠ x5) (hv0 : valence Γ x0 = 5) (f3 : L.z x0 • x3 = x3) (f4 : L.z x0 • x4 = x4)
    (f5 : L.z x0 • x5 = x5) : L.z x0 ∈ ballStab Γ G 2 x4 := by
  have hv1 : valence Γ x1 = 3 := F.val3_of_adj_val5 a01 hv0
  have hv2 : valence Γ x2 = 5 := F.val5_of_adj_val3 a12 hv1
  have hv3 : valence Γ x3 = 3 := F.val3_of_adj_val5 a23 hv2
  have hv4 : valence Γ x4 = 5 := F.val5_of_adj_val3 a34 hv3
  have h20 : Γ.dist x2 x0 = 2 := Br.dist_two F ⟨a12.symm, a01.symm, n02⟩
  have h24 : Γ.dist x2 x4 = 2 := Br.dist_two F ⟨a23, a34, n24.symm⟩
  have hK : L.z x0 ∈ nbrStab Γ G x4 := F.fix_two_nbrs a34.symm a45 n35 f3 f5
  refine mem_ballStab.2 fun w hw => ?_
  rcases (by omega : Γ.dist x4 w = 0 ∨ Γ.dist x4 w = 1 ∨ Γ.dist x4 w = 2) with h0 | h1 | h2
  · rw [← F.isTree.connected.dist_eq_zero_iff.1 h0]
    exact f4
  · exact mem_nbrStab.1 hK w (dist_eq_one_iff_adj.1 h1)
  · exact claimA_core F H hv0 hv2 hv4 h20 h24 hK h2

end P518

end CFSG.Quasithin.Fan86
