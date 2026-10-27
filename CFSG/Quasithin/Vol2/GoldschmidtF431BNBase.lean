module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNBaseCell
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer

public noncomputable section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.QuasithinUnique CFSG.Open
open scoped Pointwise

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem stabilizer_v_eq (i : Bool) : MulAction.stabilizer X (v D i) = P D i := by
  cases i
  · exact stabilizer_v_false D
  · exact stabilizer_v_true D

theorem smul_v_of_mem_B (i : Bool) {h : X} (hh : h ∈ D.B) : h • v D i = v D i := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_v_eq]
  exact B_le_P D i hh

theorem exists_nbr (i : Bool) {w : V D} (h : (Γ D).Adj (v D i) w) :
    ∃ z ∈ P D i, w = vt D (!i) z := by
  obtain ⟨-, z, hz1, hz2⟩ := id h
  have hty : vtype D.B D.N D.w₁ D.w₂ (v D i) = i := by rw [v_eq_vt, vtype_vt]
  have hz : z ∈ P D i := by
    rw [v_eq_vt] at hz1
    simpa [mem_vt_iff, P] using hz1
  refine ⟨z, hz, ?_⟩
  have e := D.rank2.eq_vtx_not_of_adj h hz2
  rw [hty] at e
  exact e

theorem vt_mem_adj (i : Bool) {z : X} (hz : z ∈ P D i) : (Γ D).Adj (v D i) (vt D (!i) z) := by
  refine ⟨?_, z, ?_, mem_self_vtx⟩
  · rw [v_eq_vt]
    exact vt_ne_of_ne i (!i) (by cases i <;> simp) 1 z
  · rw [v_eq_vt]
    simpa [mem_vt_iff, P] using hz

theorem qfix (hU : IsSylowTwoOf D.U ⊤) [Finite X] (i : Bool) {w : V D}
    (h : (Γ D).Adj (v D i) w) {q : X} (hq : q ∈ Q D i) : q • w = w := by
  obtain ⟨z, hz, rfl⟩ := exists_nbr D i h
  rw [smul_vt, vt_eq_vt_iff]
  have e : z * q⁻¹ * z⁻¹ = (z * q * z⁻¹)⁻¹ := by group
  rw [e]
  exact (P D (!i)).inv_mem
    (B_le_P D (!i) (Q_le_B D hU i (Q_normal_in_P D i z hz q hq)))

theorem two_trans (i : Bool) {z₁ z₂ z₁' z₂' : X} (h₁ : z₁ ∈ P D i) (h₂ : z₂ ∈ P D i)
    (h₁' : z₁' ∈ P D i) (h₂' : z₂' ∈ P D i) (hne : vt D (!i) z₁ ≠ vt D (!i) z₂)
    (hne' : vt D (!i) z₁' ≠ vt D (!i) z₂') :
    ∃ g ∈ P D i, g • vt D (!i) z₁ = vt D (!i) z₁' ∧ g • vt D (!i) z₂ = vt D (!i) z₂' := by
  have hdc : ∀ {z z' : X}, z ∈ P D i → z' ∈ P D i → vt D (!i) z ≠ vt D (!i) z' →
      ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, z' = b₁ * (D.lift (gen D.w₁ D.w₂ i) : X) * b₂ * z := by
    intro z z' hz hz' hne
    have hy : z' * z⁻¹ ∈ P D i := (P D i).mul_mem hz' ((P D i).inv_mem hz)
    rcases (mem_P_iff D).1 hy with hB | hd
    · exact absurd ((vt_eq_vt_iff (!i) z z').2 (D.rank2.B_le_pgen _ hB)).symm hne
    · obtain ⟨b₁, hb₁, b₂, hb₂, hy'⟩ := (mem_dc_of_lift (D.lift_mk (gen D.w₁ D.w₂ i))).1 hd
      exact ⟨b₁, hb₁, b₂, hb₂, by rw [← hy']; group⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hdc h₁ h₂ hne
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hdc h₁' h₂' hne'
  refine ⟨z₁'⁻¹ * (c₂⁻¹ * b₂) * z₁, ?_, ?_, ?_⟩
  · exact (P D i).mul_mem ((P D i).mul_mem ((P D i).inv_mem h₁')
      ((P D i).mul_mem ((P D i).inv_mem (B_le_P D i hc₂)) (B_le_P D i hb₂))) h₁
  · rw [smul_vt, vt_eq_vt_iff]
    have e : z₁ * (z₁'⁻¹ * (c₂⁻¹ * b₂) * z₁)⁻¹ * z₁'⁻¹ = b₂⁻¹ * c₂ := by group
    rw [e]
    exact D.rank2.B_le_pgen _ (D.B.mul_mem (D.B.inv_mem hb₂) hc₂)
  · rw [smul_vt, vt_eq_vt_iff]
    have e : b₁ * (D.lift (gen D.w₁ D.w₂ i) : X) * b₂ * z₁ * (z₁'⁻¹ * (c₂⁻¹ * b₂) * z₁)⁻¹ *
        (c₁ * (D.lift (gen D.w₁ D.w₂ i) : X) * c₂ * z₁')⁻¹ = b₁ * c₁⁻¹ := by group
    rw [e]
    exact D.rank2.B_le_pgen _ (D.B.mul_mem hb₁ (D.B.inv_mem hc₁))

theorem modelBase [Finite X] (hU : IsSylowTwoOf D.U ⊤) (i : Bool) :
    F45.ModelBase (Γ D) n (v D i) (pCoreOf 2 (MulAction.stabilizer X (v D i))) := by
  have hQ : pCoreOf 2 (MulAction.stabilizer X (v D i)) = Q D i := by rw [stabilizer_v_eq]; rfl
  rw [hQ]
  refine ⟨fun w hw q hq => qfix D hU i hw hq, fun b c hb hc => cell_trans D hU i hb hc,
    fun b hb q hq hqb => cell_free D hU i hb hq hqb, ?_⟩
  intro b c b' c' hb hc hbc hb' hc' hbc'
  obtain ⟨z₁, h₁, rfl⟩ := exists_nbr D i hb
  obtain ⟨z₂, h₂, rfl⟩ := exists_nbr D i hc
  obtain ⟨z₁', h₁', rfl⟩ := exists_nbr D i hb'
  obtain ⟨z₂', h₂', rfl⟩ := exists_nbr D i hc'
  obtain ⟨g, hg, hg1, hg2⟩ := two_trans D i h₁ h₂ h₁' h₂' hbc hbc'
  refine ⟨g, ?_, hg1, hg2⟩
  rw [← MulAction.mem_stabilizer_iff, stabilizer_v_eq]
  exact hg

theorem torus_fixes_vt {h c : X} (hh : h ∈ D.B ⊓ D.N) (hc : c ∈ D.N) (k : Bool) :
    h • vt D k c = vt D k c := by
  rw [smul_vt, vt_eq_vt_iff]
  have e : c * h⁻¹ * c⁻¹ = (c * h * c⁻¹)⁻¹ := by group
  rw [e]
  exact (pgen D.B D.N D.w₁ D.w₂ k).inv_mem
    (D.rank2.B_le_pgen k (D.conj_cartan_mem ⟨c, hc⟩ hh).1)

theorem mi_mem_N (i : Bool) : mi D i ∈ D.N :=
  SetLike.coe_mem (D.lift (gen D.w₁ D.w₂ i))

theorem chainElt_mem_N (m₁ m₂ : D.N) (first : Bool) :
    ∀ j : ℕ, chainElt (D.lifts m₁ m₂) first j ∈ D.N
  | 0 => D.N.one_mem
  | j + 1 => by
    rw [chainElt]
    refine D.N.mul_mem ?_ (chainElt_mem_N m₁ m₂ first j)
    have : ∀ s : Bool, D.lifts m₁ m₂ s ∈ D.N := fun s => by
      unfold RankTwoSystem.lifts
      split <;> exact SetLike.coe_mem _
    exact this _

theorem torus_fixes_apartment (i : Bool) : ∃ u₁ u₂ b₀ : V D, (Γ D).Adj (v D i) u₁ ∧
    (Γ D).Adj (v D i) u₂ ∧ u₁ ≠ u₂ ∧ (Γ D).dist (v D i) b₀ = n ∧
    ∀ h ∈ D.B ⊓ D.N, h • v D i = v D i ∧ h • u₁ = u₁ ∧ h • u₂ = u₂ ∧ h • b₀ = b₀ := by
  have hn := D.three_le
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  have hnn : n - 1 + 1 = n := by omega
  have hvn : D.vv m₁ m₂ (!i) n = vt D (stType (!i) (n - 1))
      (chainElt (D.lifts m₁ m₂) (!i) (n - 1)) := by
    have := D.vv_succ m₁ m₂ (!i) (n - 1)
    rw [hnn] at this
    exact this
  have hdist : (Γ D).dist (v D i) (D.vv m₁ m₂ (!i) n) = n := by
    have hlast : (D.basePath m₁ m₂ (!i)).getLast? = some (D.vv m₁ m₂ (!i) n) := by
      simp [RankTwoSystem.basePath, List.range_succ]
    have := D.polyHyp.dist_eq_of_path (D.basePath_isGLSPath m₁ m₂ hm₁ hm₂ (!i))
      (D.basePath_head m₁ m₂ (!i)) hlast (D.basePath_length m₁ m₂ (!i))
    rw [D.vv_zero, Bool.not_not] at this
    rw [v_eq_vt]
    exact this
  refine ⟨vt D (!i) 1, vt D (!i) (mi D i), D.vv m₁ m₂ (!i) n,
    vt_mem_adj D i (P D i).one_mem, vt_mem_adj D i (mi_mem_P D i), ?_, hdist, ?_⟩
  · intro h
    have h' := (vt_eq_vt_iff (!i) 1 (mi D i)).1 h.symm
    have hB := D.rank2.pgen_inter i (by simpa [P] using mi_mem_P D i)
      (by simpa using h')
    exact D.rank2.not_mem_B_of_mem_dc (D.rank2.gen_mem i) (mi_mem_dc D i) hB
  · intro h hh
    refine ⟨smul_v_of_mem_B D i hh.1, torus_fixes_vt D hh D.N.one_mem _,
      torus_fixes_vt D hh (mi_mem_N D i) _, ?_⟩
    rw [hvn]
    exact torus_fixes_vt D hh (chainElt_mem_N D m₁ m₂ (!i) (n - 1)) _

end CFSG.Quasithin.H13.F431.BN
