module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Far
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Sub

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Z2Cfg

variable {α a₀ β δ δ' γ γ' : V} {F : FanTree Γ G} {L : ZLab Γ G}

theorem false_of_fixed (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (h71c : Fan71c F L) (h72a : Fan72a F L)
    (h40 : Fan40 F) (hα : pval Γ α = 5) (hnot : ¬ ∃ g ∈ Gcirc Γ G a₀ β, g • δ = δ') {l : V}
    (hl5 : pval Γ l = 5) (hρl : (L.z δ * L.z δ') • l = l) (hlα : Γ.dist l α ≤ 4)
    (hlβ : Γ.dist l β ≤ 4) (hla : Γ.dist l a₀ ≤ 4) (hlγ : 4 < Γ.dist l γ)
    (hlγ' : 4 < Γ.dist l γ') : False := by
  have hT := F.isTree
  have ha5 := D.val_a F hα
  have hδ5 := D.val_δ F hα
  have hδ'5 := D.val_δ' F hα
  set s := L.z l with hs
  have hsα : s • α = α := (h71c.z_smul_eq_iff hl5 α).2 hlα
  have hsβ : s • β = β := (h71c.z_smul_eq_iff hl5 β).2 hlβ
  have hsa : s • a₀ = a₀ := (h71c.z_smul_eq_iff hl5 a₀).2 hla
  have hs2 : s * s = 1 := L.z_mul_self hl5
  have hss : ∀ x : V, s • (s • x) = x := fun x => by rw [← mul_smul, hs2, one_smul]
  have hsG : s ∈ Gcirc Γ G a₀ β := mem_gcirc_of_sq_eq_one
    ⟨MulAction.mem_stabilizer_iff.2 hsa, MulAction.mem_stabilizer_iff.2 hsβ⟩ hs2
  have hsγ : s • γ ≠ γ := fun h => by have := (h71c.z_smul_eq_iff hl5 γ).1 h; omega
  have hsγ' : s • γ' ≠ γ' := fun h => by have := (h71c.z_smul_eq_iff hl5 γ').1 h; omega
  obtain ⟨n01, n12⟩ := F.z2_branches h40 ha5 D.adj_βa.symm D.adj_aγ D.adj_aγ' D.adj_γδ D.ne_δa
    D.adj_γ'δ' D.ne_δ'a hsG hnot
  have n03 : γ ≠ s • γ' := fun h => n12 (by rw [h, hss])
  have n23 : s • γ ≠ s • γ' := fun h => n01 (MulAction.injective s h)
  have n24 : s • γ ≠ β := fun h => D.ne_γβ (MulAction.injective s (h.trans hsβ.symm))
  have n34 : s • γ' ≠ β := fun h => D.ne_γ'β (MulAction.injective s (h.trans hsβ.symm))
  have hAs : ∀ x y, Γ.Adj x y → Γ.Adj (s • x) (s • y) := fun x y h => (F.adj_smul s x y).2 h
  have a1 : Γ.Adj a₀ (s • γ) := by simpa [hsa] using hAs _ _ D.adj_aγ
  have a1' : Γ.Adj a₀ (s • γ') := by simpa [hsa] using hAs _ _ D.adj_aγ'
  have a2 : Γ.Adj (s • γ) (s • δ) := hAs _ _ D.adj_γδ
  have a2' : Γ.Adj (s • γ') (s • δ') := hAs _ _ D.adj_γ'δ'
  have nsδ : s • δ ≠ a₀ := fun h => D.ne_δa (MulAction.injective s (h.trans hsa.symm))
  have nsδ' : s • δ' ≠ a₀ := fun h => D.ne_δ'a (MulAction.injective s (h.trans hsa.symm))
  have b1 : Γ.Adj a₀ γ := D.adj_aγ
  have b1' : Γ.Adj a₀ γ' := D.adj_aγ'
  have b0 : Γ.Adj a₀ β := D.adj_βa.symm
  have bδ : Γ.Adj γ δ := D.adj_γδ
  have bδ' : Γ.Adj γ' δ' := D.adj_γ'δ'
  have bα : Γ.Adj β α := D.adj_αβ.symm
  have nδ : δ ≠ a₀ := D.ne_δa
  have nδ' : δ' ≠ a₀ := D.ne_δ'a
  have nα : α ≠ a₀ := D.ne_αa
  let c : Fin 5 → V := ![γ, γ', s • γ, s • γ', β]
  let l5 : Fin 5 → V := ![δ, δ', s • δ, s • δ', α]
  have hc1 : ∀ i, Γ.Adj a₀ (c i) := by
    intro i; fin_cases i <;> simp [c] <;> assumption
  have hc2 : ∀ i, Γ.Adj (c i) (l5 i) := by
    intro i; fin_cases i <;> simp [c, l5] <;> assumption
  have hne : ∀ i, l5 i ≠ a₀ := by
    intro i; fin_cases i <;> simp [l5] <;> assumption
  have hcinj : ∀ i j, i ≠ j → c i ≠ c j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [c, n01, n01.symm, n03, n03.symm, n12, n12.symm, n23, n23.symm, n24, n24.symm,
        n34, n34.symm, hsγ, hsγ.symm, hsγ', hsγ'.symm, D.ne_γβ, D.ne_γβ.symm, D.ne_γ'β,
        D.ne_γ'β.symm]
  have hdist4 : ∀ i j, i ≠ j → Γ.dist (l5 i) (l5 j) = 4 := fun i j hij =>
    IsTree.dist_eq_four_of_branches hT (hc1 i) (hc2 i) (hc1 j) (hc2 j) (hcinj i j hij) (hne i)
      (hne j)
  have hdist2 : ∀ i, Γ.dist a₀ (l5 i) = 2 := fun i =>
    IsTree.dist_eq_two_of_adj hT (hc1 i) (hc2 i) (hne i)
  have hval : ∀ i, pval Γ (l5 i) = 5 := by
    intro i
    fin_cases i <;> simp [l5]
    · exact hδ5
    · exact hδ'5
    · rw [valence_smul F]; exact hδ5
    · rw [valence_smul F]; exact hδ'5
    · exact hα
  have h5 := h72a a₀ l5 ha5 (fun i => ⟨hdist2 i, hval i⟩) hdist4
  have hprod : (List.ofFn fun i => L.z (l5 i)).prod =
      L.z δ * (L.z δ' * (L.z (s • δ) * (L.z (s • δ') * L.z α))) := by
    simp [List.ofFn_succ, l5]
  have hcomm : (L.z δ * L.z δ') * s = s * (L.z δ * L.z δ') := (h71c.comm_z_iff hl5 _).2 hρl
  have hsd : L.z (s • δ) = s * L.z δ * s⁻¹ := L.equivariant s δ hδ5
  have hsd' : L.z (s • δ') = s * L.z δ' * s⁻¹ := L.equivariant s δ' hδ'5
  have hρs : L.z (s • δ) * L.z (s • δ') = L.z δ * L.z δ' := by
    rw [hsd, hsd']
    have : s * (L.z δ * L.z δ') * s⁻¹ = L.z δ * L.z δ' :=
      mul_inv_eq_iff_eq_mul.2 hcomm.symm
    rw [← this]
    group
  have hcδ : L.z δ * L.z δ' = L.z δ' * L.z δ :=
    h71c.z_comm_of_dist_le hδ5 hδ'5 (le_of_eq (hdist4 0 1 (by decide)))
  have hρ2 : (L.z δ * L.z δ') * (L.z δ * L.z δ') = 1 := by
    calc (L.z δ * L.z δ') * (L.z δ * L.z δ') = L.z δ * (L.z δ' * L.z δ) * L.z δ' := by group
      _ = L.z δ * (L.z δ * L.z δ') * L.z δ' := by rw [hcδ]
      _ = (L.z δ * L.z δ) * (L.z δ' * L.z δ') := by group
      _ = 1 := by rw [L.z_mul_self hδ5, L.z_mul_self hδ'5, one_mul]
  have hfin : L.z δ * (L.z δ' * (L.z (s • δ) * (L.z (s • δ') * L.z α))) = L.z α := by
    calc L.z δ * (L.z δ' * (L.z (s • δ) * (L.z (s • δ') * L.z α)))
        = (L.z δ * L.z δ') * (L.z (s • δ) * L.z (s • δ')) * L.z α := by group
      _ = L.z α := by rw [hρs, hρ2, one_mul]
  rw [hprod, hfin] at h5
  rcases h5 with h | h
  · exact L.z_ne_one hα h
  · exact D.ne_αa (h71c.z_injective hα ha5 h)

theorem sup_target (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (h71c : Fan71c F L) (h72a : Fan72a F L)
    (h40 : Fan40 F) (hα : pval Γ α = 5) (hnot : ¬ ∃ g ∈ Gcirc Γ G a₀ β, g • δ = δ') {v : V}
    (hv : Γ.dist α v ≤ 4) (hρv : (L.z δ * L.z δ') • v = v) :
    Γ.dist a₀ v ≤ 2 ∨ Γ.dist β v ≤ 2 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  have hT := F.isTree
  have hβa : Γ.dist a₀ β = 1 := dist_eq_one_iff_adj.mpr D.adj_βa.symm
  have hρβ : (L.z δ * L.z δ') • β = β := D.rho_smul_of_dist_le h71c hα (by omega)
  obtain ⟨l, hl5, hρl, hβl, hal, hfar⟩ := D.exists_far F hα hρβ hρv hv hcon.1 hcon.2
  have hαβ : Γ.dist β α = 1 := dist_eq_one_iff_adj.mpr D.adj_αβ.symm
  have h1 := hT.connected.dist_triangle (u := l) (v := β) (w := α)
  have e1 : Γ.dist l β = Γ.dist β l := SimpleGraph.dist_comm
  have e2 : Γ.dist l a₀ = Γ.dist a₀ l := SimpleGraph.dist_comm
  exact D.false_of_fixed h71c h72a h40 hα hnot hl5 hρl (by omega) (by omega) (by omega)
    (by rw [hfar γ D.adj_aγ D.ne_γβ]; norm_num) (by rw [hfar γ' D.adj_aγ' D.ne_γ'β]; norm_num)

end Z2Cfg

end CFSG.Quasithin.Fan86
