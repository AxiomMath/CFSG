module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

@[expose] def InZ (L : ZLab Γ G) (α : V) (e : G) : Prop := e = 1 ∨ e = L.z α

theorem InZ.mul (hα : valence Γ α = 5) {a b : G} (ha : InZ L α a) (hb : InZ L α b) :
    InZ L α (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (one_mul 1)
  · exact Or.inr (one_mul _)
  · exact Or.inr (mul_one _)
  · exact Or.inl (L.z_mul_self hα)

theorem InZ.inv (hα : valence Γ α = 5) {a : G} (ha : InZ L α a) : InZ L α a⁻¹ := by
  rcases ha with rfl | rfl
  · exact Or.inl inv_one
  · exact Or.inr (L.z_inv hα)

theorem InZ.comm {a b : G} (ha : InZ L α a) (hb : InZ L α b) : a * b = b * a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem InZ.conj (hα : valence Γ α = 5) {y e : G} (hy : y ∈ MulAction.stabilizer G α)
    (he : InZ L α e) : y⁻¹ * e * y = e ∧ y * e * y⁻¹ = e := by
  rcases he with rfl | rfl
  · simp
  · have h := L.comm_z_of_mem_stabilizer hα hy
    exact ⟨by rw [mul_assoc, ← h]; group, by rw [h]; group⟩

theorem zGroup_le_stabilizer (h71c : Fan71c F L) : L.zGroup 2 α ≤ MulAction.stabilizer G α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨δ, hδ, hδ5, rfl⟩
  refine (h71c.z_mem_stabilizer_iff hδ5 α).2 ?_
  rw [SimpleGraph.dist_comm]
  omega

theorem sibling_mul (h7 : Fan7 F L) (h512 : Fan512 F L) (hα : valence Γ α = 5) {g : G}
    (hg : g ∈ nbrStab Γ G α) {δ : V} (hδ : Γ.dist α δ = 2) :
    InZ L α (L.z (g⁻¹ • δ) * L.z δ) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hδ5 : valence Γ δ = 5 := valence_of_dist_even F hα (by rw [hδ])
  obtain ⟨β, hβδ, hαβ⟩ := IsTree.exists_adj_dist_succ F.isTree (u := α) (v := δ) (n := 1) hδ
  have hαβ' : Γ.Adj α β := SimpleGraph.dist_eq_one_iff_adj.1 hαβ
  have hgi : g⁻¹ ∈ nbrStab Γ G α := inv_mem hg
  have hgβ : g⁻¹ • β = β := mem_nbrStab.1 hgi β hαβ'
  have hgα : g • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hg)
  have hadj : Γ.Adj β (g⁻¹ • δ) := by
    have := (F.adj_smul g⁻¹ β δ).2 hβδ
    rwa [hgβ] at this
  have hαδ : α ≠ δ := fun h => by
    rw [← h, SimpleGraph.dist_self] at hδ
    omega
  have hβ3 : valence Γ β = 3 := valence_adj_three F hα hαβ'
  obtain ⟨c, hc, hαc, hδc⟩ := exists_third_neighbor hβ3 hαβ'.symm hβδ hαδ
  by_cases heq : g⁻¹ • δ = δ
  · left
    rw [heq]
    exact L.z_mul_self hδ5
  · have hne : g⁻¹ • δ ≠ α := fun h => hαδ (by
      have := inv_smul_eq_iff.1 h
      rw [hgα] at this
      exact this.symm)
    have hmem : g⁻¹ • δ ∈ Γ.neighborSet β := hadj
    rw [hc] at hmem
    have hcc : g⁻¹ • δ = c := by
      rcases hmem with h | h | h
      · exact absurd h hne
      · exact absurd h heq
      · exact h
    have hβc : Γ.Adj β c := by
      have : c ∈ Γ.neighborSet β := by rw [hc]; simp
      exact this
    have hc5 : valence Γ c = 5 := valence_adj_five F hβ3 hβc
    have h3 := h512.2.2.1 β α δ c hβ3 hc hαδ hαc hδc
    have h4 : L.z δ * L.z c = L.z α := by
      rw [mul_assoc] at h3
      exact ((L.z_inv hα).symm.trans (inv_eq_of_mul_eq_one_right h3)).symm
    right
    rw [hcc, ← h4]
    refine (h71c.z_comm_of_dist_le hc5 hδ5 ?_)
    have := F.isTree.connected.dist_triangle (u := c) (v := β) (w := δ)
    have h5 : Γ.dist c β = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hβc.symm
    have h6 : Γ.dist β δ = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hβδ
    omega

theorem fcomm_z_mem (h7 : Fan7 F L) (h512 : Fan512 F L) (hα : valence Γ α = 5) {g : G}
    (hg : g ∈ nbrStab Γ G α) {δ : V} (hδ : Γ.dist α δ ≤ 2) (hδ5 : valence Γ δ = 5) :
    InZ L α (fcomm g (L.z δ)) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hgs : g ∈ MulAction.stabilizer G α := F.nbrStab_le_stabilizer α hg
  have hd : Γ.dist α δ = 0 ∨ Γ.dist α δ = 1 ∨ Γ.dist α δ = 2 := by omega
  rcases hd with h0 | h1 | h2
  · have := F.isTree.connected.dist_eq_zero_iff.1 h0
    subst this
    exact Or.inl (fcomm_eq_one_iff.2 (L.comm_z_of_mem_stabilizer hα hgs))
  · exfalso
    have := valence_of_dist_odd F hα (by rw [h1])
    omega
  · have : fcomm g (L.z δ) = L.z (g⁻¹ • δ) * L.z δ := by
      unfold fcomm
      rw [L.z_inv hδ5, L.z_inv_smul g hδ5]
    rw [this]
    exact sibling_mul h7 h512 hα hg h2

theorem fcomm_mem_Z (h7 : Fan7 F L) (h512 : Fan512 F L) (hα : valence Γ α = 5) {g v : G}
    (hg : g ∈ nbrStab Γ G α) (hv : v ∈ L.zGroup 2 α) : InZ L α (fcomm g v) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hle := zGroup_le_stabilizer (α := α) h71c
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, hδ5, rfl⟩ := hx
    exact fcomm_z_mem h7 h512 hα hg hδ hδ5
  | one => exact Or.inl (by simp [fcomm])
  | mul x y hx hy ihx ihy =>
    rw [fcomm_mul_right, (InZ.conj hα (hle hy) ihx).1]
    exact InZ.mul hα ihy ihx
  | inv x hx ih =>
    have : fcomm g x⁻¹ = x * (fcomm g x)⁻¹ * x⁻¹ := by
      unfold fcomm
      group
    rw [this, (InZ.conj hα (hle hx) (InZ.inv hα ih)).2]
    exact InZ.inv hα ih

theorem fcomm_mul_V (h7 : Fan7 F L) (h512 : Fan512 F L) (hα : valence Γ α = 5) {g a b : G}
    (hg : g ∈ nbrStab Γ G α) (ha : a ∈ L.zGroup 2 α) (hb : b ∈ L.zGroup 2 α) :
    fcomm g (a * b) = fcomm g a * fcomm g b := by
  have hle := zGroup_le_stabilizer (α := α) h7.2.2.1
  have h1 := fcomm_mem_Z h7 h512 hα hg ha
  have h2 := fcomm_mem_Z h7 h512 hα hg hb
  rw [fcomm_mul_right, (InZ.conj hα (hle hb) h1).1]
  exact InZ.comm h2 h1

end CFSG.Quasithin.Fan86.F87
