module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P75C
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Sq2

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem relIndex_le_two (h40 : Fan40 F) (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (_h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) :
    (ballStab Γ G 3 (P.vert 4)).relIndex (L.calpha P) ≤ 2 := by
  obtain ⟨y, hy5, hy4, -, hall⟩ := exists_third_nbr_five F h5
  have hdy : Γ.dist (P.vert 4) y = 2 := by
    have h1 : Γ.Adj (P.vert 4) (P.vert 5) := P.adj 4 (by norm_num)
    have h0 : Γ.dist (P.vert 4) (P.vert 5) = 1 := dist_eq_one_iff_adj.mpr h1
    have := IsTree.dist_succ_of_ne F.isTree h1.symm hy5 (Ne.symm hy4)
      (by rw [SimpleGraph.dist_self, h0])
    omega
  have hCb : ∀ c ∈ L.calpha P, c ∈ ballStab Γ G 2 (P.vert 4) := fun c hc => by
    rw [(h73b P h5).1]
    exact Subgroup.mem_sup_right hc
  have hN : ∀ c ∈ L.calpha P, c ∈ nbrStab Γ G y → c ∈ ballStab Γ G 3 (P.vert 4) :=
    fun c hc hcy => mem_ballStab_three_of_nbrStab h73b h5 hc fun w hw =>
      mem_nbrStab_of_dist_two h65 h71a h71c h5 hall hc hcy hw
  have hyst : ∀ c ∈ L.calpha P,
      c ∈ MulAction.stabilizer G y ⊓ MulAction.stabilizer G (P.vert 5) := fun c hc => by
    have h56 := (calpha_mem_nbrStab_five_six h71a h71c h5 hc).1
    refine Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 h56 y hy5), ?_⟩
    have hcP := hc
    rw [calpha_eq_stab h71a h71c h5, Arc.mem_stab] at hcP
    exact MulAction.mem_stabilizer_iff.2 (hcP 5 (by norm_num))
  have hsq : ∀ c ∈ L.calpha P, c * c ∈ nbrStab Γ G y := fun c hc =>
    sq_mem_nbrStab h40 h64 h71a h71c h73b h5 hdy (hCb c hc)
  by_cases hle : L.calpha P ≤ ballStab Γ G 3 (P.vert 4)
  · rw [Subgroup.relIndex_eq_one.2 hle]
    norm_num
  · obtain ⟨c₀, hc₀, hc₀N⟩ := IsConcreteLE.not_le_iff_exists.1 hle
    have hc₀K : c₀ ∉ nbrStab Γ G y := fun h => hc₀N (hN _ hc₀ h)
    have h2 : (ballStab Γ G 3 (P.vert 4)).relIndex (L.calpha P) = 2 := by
      rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
      refine ⟨⟨c₀, hc₀⟩, fun b => ?_⟩
      have hbC : (b : G) ∈ L.calpha P := b.2
      show Xor ((b : G) * c₀ ∈ ballStab Γ G 3 (P.vert 4))
        ((b : G) ∈ ballStab Γ G 3 (P.vert 4))
      by_cases hbN : (b : G) ∈ ballStab Γ G 3 (P.vert 4)
      · have hn : (b : G) * c₀ ∉ ballStab Γ G 3 (P.vert 4) := fun h => hc₀N (by
          simpa using mul_mem (inv_mem hbN) h)
        exact Or.inr ⟨hbN, hn⟩
      · have hbK : (b : G) ∉ nbrStab Γ G y := fun h => hbN (hN _ hbC h)
        have hprod := P62.mul_mem_nbrStab_of_sq_mem F hy5.symm (hyst _ hbC) (hyst _ hc₀)
          (hsq _ hbC) (hsq _ hc₀) hbK hc₀K
        exact Or.inl ⟨hN _ (mul_mem hbC hc₀) hprod, hbN⟩
    rw [h2]

end P74

end CFSG.Quasithin.Fan86
