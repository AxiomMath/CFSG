module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExD10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Ex
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_not_mem_gcirc {F : FanTree Γ G} (h71b : Fan71b F) {a β : V}
    (hav : valence Γ a = 5) (haβ : Γ.Adj a β) :
    ∃ g ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G β, g ∉ Gcirc Γ G a β := by
  have hdeg : ∀ u v, Γ.Adj u v → ∃ w, Γ.Adj u w ∧ w ≠ v := fun u v _ => F.exists_adj_ne u v
  obtain ⟨Q, hQ0, hQ1⟩ := exists_arc_start hdeg haβ 2
  let P : Arc Γ 3 := Arc.rev Q
  have hP3 : P.vert 3 = a := by
    show (Arc.rev Q).vert 3 = a
    rw [Arc.rev_vert]
    exact hQ0
  have hP2 : P.vert 2 = β := by
    show (Arc.rev Q).vert 2 = β
    rw [Arc.rev_vert]
    exact hQ1
  set E : Subgroup G := MulAction.stabilizer G a ⊓ MulAction.stabilizer G β with hE
  have htr : ∀ u w, Γ.Adj a u → u ≠ β → Γ.Adj a w → w ≠ β → ∃ g ∈ E, g • u = w := by
    intro u w hu huβ hw hwβ
    obtain ⟨g, hg, hgu⟩ := (h71b.1 3 (by norm_num) (by norm_num) P).1 u w (by rw [hP3]; exact hu)
      (by rw [show 3 - 1 = 2 from rfl, hP2]; exact huβ) (by rw [hP3]; exact hw)
      (by rw [show 3 - 1 = 2 from rfl, hP2]; exact hwβ)
    refine ⟨g, ⟨?_, ?_⟩, hgu⟩
    · have := mem_stabRange.1 hg 3 (by norm_num) le_rfl
      rw [hP3] at this
      exact this
    · have := mem_stabRange.1 hg 2 (by norm_num) (by norm_num)
      rw [hP2] at this
      exact this
  obtain ⟨u, hu, huβ⟩ := F.exists_adj_ne a β
  have horb : MulAction.orbit ↥E u = Γ.neighborSet a \ {β} := by
    ext w
    constructor
    · rintro ⟨⟨g, hgE⟩, rfl⟩
      refine ⟨F.adj_smul_of_mem_stabilizer hgE.1 hu, fun h => huβ ?_⟩
      have hgβ : g • β = β := MulAction.mem_stabilizer_iff.1 hgE.2
      have h' : g • u = g • β := h.trans hgβ.symm
      exact MulAction.injective g h'
    · rintro ⟨hw, hwβ⟩
      obtain ⟨g, hgE, hgu⟩ := htr u w hu huβ hw hwβ
      exact ⟨⟨g, hgE⟩, hgu⟩
  have hstab : MulAction.stabilizer G u ⊓ E = nbrStab Γ G a := by
    ext g
    constructor
    · rintro ⟨hgu, hgE⟩
      exact F.fix_two_nbrs hu haβ huβ (MulAction.mem_stabilizer_iff.1 hgu)
        (MulAction.mem_stabilizer_iff.1 hgE.2)
    · intro hk
      refine ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk u hu), ⟨F.nbrStab_le_stabilizer a hk,
        MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk β haβ)⟩⟩
  have hidx : (nbrStab Γ G a).relIndex E = 4 := by
    have h1 := FanTree.relIndex_stabilizer_eq_ncard_orbit E u
    rw [horb, neighborSet_diff_ncard hav haβ] at h1
    rw [← hstab, Subgroup.inf_relIndex_right, h1]
  obtain ⟨H, hHeq, hHE, -, hHiff⟩ := F.exists_gcircSubgroup haβ
  have hne : H ≠ E := fun h => by
    have h2 := hHiff.1 h
    have h4 : (nbrStab Γ G a).relIndex (MulAction.stabilizer G a ⊓ MulAction.stabilizer G β) = 4 :=
      hidx
    omega
  obtain ⟨g, hgE, hgH⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hHE hne)
  refine ⟨g, hgE, fun hg => hgH ?_⟩
  rw [← SetLike.mem_coe, hHeq]
  exact hg

theorem exists_isYPair {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) {α : V}
    (D : D10Set L α) : ∃ δ' : V, D.IsYPair δ' := by
  obtain ⟨-, h71b, -, -⟩ := h7
  have hT := F.isTree
  have hav : valence Γ (D.alpha 0) = 5 := D.valence_alpha F 0
  have haβ : Γ.Adj (D.alpha 0) (D.beta 0) := (D.adj_beta_alpha 0).symm
  obtain ⟨g, hg, hgG⟩ := exists_not_mem_gcirc h71b hav haβ
  have hga : g • D.alpha 0 = D.alpha 0 := MulAction.mem_stabilizer_iff.1 hg.1
  have hgβ : g • D.beta 0 = D.beta 0 := MulAction.mem_stabilizer_iff.1 hg.2
  have hγ : Γ.Adj (D.alpha 0) (g • D.xi 0) := by
    have := (F.adj_smul g _ _).2 (D.adj_alpha_xi 0)
    rwa [hga] at this
  have hγβ : D.beta 0 ≠ g • D.xi 0 := fun h => D.xi_ne_beta 0 (MulAction.injective g (by
    show g • D.xi 0 = g • D.beta 0
    rw [hgβ]
    exact h.symm))
  obtain ⟨δ', hδ', hδ'a⟩ := F.exists_adj_ne (g • D.xi 0) (D.alpha 0)
  refine ⟨δ', ?_⟩
  refine ⟨D.dist_start_alpha F 0, haβ, by rw [D.dist_start_beta F 0, D.dist_start_alpha F 0],
    D.dist_alpha_delta F 0, IsTree.dist_eq_two_of_adj hT hγ hδ' hδ'a, D.dist_delta F 0, ?_, ?_⟩
  · exact IsTree.dist_eq_four_of_branches hT haβ (D.adj_start_beta 0).symm hγ hδ' hγβ
      (D.alpha_ne_start 0).symm hδ'a
  · rintro ⟨h, hh, hhδ⟩
    have hha : h • D.alpha 0 = D.alpha 0 := MulAction.mem_stabilizer_iff.1 hh.1.1
    have hhβ : h • D.beta 0 = D.beta 0 := MulAction.mem_stabilizer_iff.1 hh.1.2
    have h1 : Γ.Adj (D.alpha 0) (h • D.xi 0) := by
      have := (F.adj_smul h _ _).2 (D.adj_alpha_xi 0)
      rwa [hha] at this
    have h2 : Γ.Adj (h • D.xi 0) δ' := by
      have := (F.adj_smul h _ _).2 (D.adj_xi_delta 0)
      rwa [hhδ] at this
    have heq : h • D.xi 0 = g • D.xi 0 :=
      F.eq_of_adj_adj h1 h2 hγ hδ' (fun h' => hδ'a h'.symm)
    have hk : g⁻¹ * h ∈ nbrStab Γ G (D.alpha 0) := by
      refine F.fix_two_nbrs (D.adj_alpha_xi 0) haβ (D.xi_ne_beta 0) ?_ ?_
      · rw [mul_smul, heq, inv_smul_smul]
      · rw [mul_smul, hhβ, inv_smul_eq_iff]
        exact hgβ.symm
    have hk' : (g⁻¹ * h)⁻¹ ∈ Gcirc Γ G (D.alpha 0) (D.beta 0) :=
      F.nbrStab_le_gcirc haβ ((nbrStab Γ G (D.alpha 0)).inv_mem hk)
    apply hgG
    have := F.gcirc_mul_mem haβ hh hk'
    rwa [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at this

theorem fan_D10_exists {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) : D10YPairExists F L :=
  fun _ hα => by
    obtain ⟨D⟩ := exists_d10Set h7 hα
    obtain ⟨δ', h⟩ := exists_isYPair h7 D
    exact ⟨D, δ', h⟩

end CFSG.Quasithin.Fan86
