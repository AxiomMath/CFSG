module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2d1Frob
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Ind
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Y
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cBall

public section

namespace CFSG.Quasithin.Fan86.P2d1

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.F87
open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem smul_eq_of_move (F : FanTree Γ G) {ξ a δ : V} (hξ : valence Γ ξ = 3) (haξ : Γ.Adj ξ a)
    (hδξ : Γ.Adj ξ δ) (hne : a ≠ δ) {g g' : G} (hg1 : g • ξ = ξ) (hg2 : g • a = a)
    (hg3 : g • δ ≠ δ) (hg1' : g' • ξ = ξ) (hg2' : g' • a = a) (hg3' : g' • δ ≠ δ) :
    g • δ = g' • δ := by
  obtain ⟨c, hc, hac, hδc⟩ := exists_third_neighbor hξ haξ hδξ hne
  have key : ∀ k : G, k • ξ = ξ → k • a = a → k • δ ≠ δ → k • δ = c := by
    intro k hk1 hk2 hk3
    have hadj : Γ.Adj ξ (k • δ) := by
      have := (F.adj_smul k ξ δ).2 hδξ
      rwa [hk1] at this
    have hmem : k • δ ∈ Γ.neighborSet ξ := hadj
    rw [hc] at hmem
    rcases hmem with h | h | h
    · exact absurd (MulAction.injective k (h.trans hk2.symm)) (Ne.symm hne)
    · exact absurd h hk3
    · exact h
  rw [key g hg1 hg2 hg3, key g' hg1' hg2' hg3']

theorem exists_vc_plain (h7 : Fan7 F L) {h : G} (hh : h ∈ ballStab Γ G 2 α) :
    ∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, h = v * c := by
  have h71c : Fan71c F L := h7.2.2.1
  have hCN : D.calpha ≤ Subgroup.normalizer (L.zGroup 2 α : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    have hcH := calpha_le_ballStab h7 D hc
    have hcH' := inv_mem hcH
    intro g
    constructor
    · intro hv
      have : c * g * c⁻¹ = g := by rw [ballStab_comm h71c hcH hv, mul_inv_cancel_right]
      rw [this]
      exact hv
    · intro hv
      have h1 := ballStab_comm h71c hcH' hv
      have : g = c * g * c⁻¹ := by
        calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = (c * g * c⁻¹) * c⁻¹ * c := by rw [h1]
          _ = c * g * c⁻¹ := by group
      exact this.symm ▸ hv
  have hmul : (↑(D.calpha ⊔ L.zGroup 2 α) : Set G) =
      (D.calpha : Set G) * (L.zGroup 2 α : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN
  have hh' : h ∈ D.calpha ⊔ L.zGroup 2 α := by
    rw [sup_comm, ← (fan73b_dset h7 D).1]
    exact hh
  rw [← SetLike.mem_coe, hmul] at hh'
  obtain ⟨c, hc, v, hv, hcvh⟩ := hh'
  have hcvh' : c * v = h := hcvh
  subst hcvh'
  exact ⟨v, hv, c, hc, ballStab_comm h71c (calpha_le_ballStab h7 D hc) hv⟩

theorem z_mem_ballStab_two (h71c : Fan71c F L) (j : Fin 5) : L.z α ∈ ballStab Γ G 2 (D.beta j) := by
  refine mem_ballStab.2 fun w hw => ?_
  refine (h71c.z_smul_eq_iff D.val w).2 ?_
  have := F.isTree.connected.dist_triangle (u := α) (v := D.beta j) (w := w)
  have := D.dist_start_beta F j
  omega

theorem midlab_kstar : ∀ i j : Fin 5, midlab (kstar i j) (kstar j i) = midlab i j := by
  unfold kstar midlab
  decide

theorem classify_comm (h7 : Fan7 F L) (h512 : Fan512 F L) {i j : Fin 5} (hij : i ≠ j) {g : G}
    (hgH : g ∈ ballStab Γ G 2 α) (hgβ : g ∈ ballStab Γ G 2 (D.beta i))
    (hξi : g • D.xi i = D.xi i) (hξj : g • D.xi j = D.xi j)
    (hδi : g • D.delta i ≠ D.delta i) (hδj : g • D.delta j ≠ D.delta j) :
    ∃ e : Fin 2, g = L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) * L.z α ^ (e : ℕ) := by
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have h73b : Fan73b F L := h7.2.2.2.2.2.2.1
  obtain ⟨⟨hmi, hmj, hai, haj, ham, hbi, hbj, hbm, hab⟩, -, -⟩ := fin5_midlab_facts i j hij
  obtain ⟨k1, k2, -⟩ := fin5_kstar_facts i j hij
  have hmid := midlab_kstar i j
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hpV : L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) ∈ L.zGroup 2 α :=
    mul_mem (hzV _) (hzV _)
  have hfix := fun k n (hn : n ≤ 4) => D.fixed_iff F h7 h512 hab k hn
  have hpξi : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.xi i = D.xi i :=
    (hfix i 3 (by norm_num)).2 (Or.inr (Or.inr ⟨Or.inr (by rw [k2]), by norm_num⟩))
  have hpξj : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.xi j = D.xi j :=
    (hfix j 3 (by norm_num)).2 (Or.inr (Or.inr ⟨Or.inl (by rw [k1]), by norm_num⟩))
  have hpδ : ∀ k, k ≠ midlab i j → k ≠ kstar i j → k ≠ kstar j i →
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.delta k ≠ D.delta k := by
    intro k hk1 hk2 hk3 h
    rcases (hfix k 4 (by norm_num)).1 h with h1 | ⟨h2, h3⟩ | ⟨h4, h5⟩
    · exact hk1 (h1.trans hmid)
    · omega
    · omega
  have hpδi := hpδ i hmi.symm hai.symm hbi.symm
  have hpδj := hpδ j hmj.symm haj.symm hbj.symm
  have hpH : L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) ∈ ballStab Γ G 2 α :=
    zGroup_le_ballStab h7 D hpV
  have hpα : ∀ k, (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.alpha k =
      D.alpha k := fun k => mem_ballStab.1 hpH _ (by rw [D.dist_start_alpha F k])
  have hpβ : L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) ∈ ballStab Γ G 2 (D.beta i) :=
    labels_mem_ballStab_two D h7 hai hbi
  obtain ⟨w, hw, c, hc, rfl⟩ := exists_vc_plain D h7 hgH
  have hcfix : ∀ k : Fin 5, ∀ m : ℕ, m ≤ 4 → c • (D.P k).vert m = (D.P k).vert m :=
    fun k m hm => D.fix_of_mem_calpha F h71a h71c hc k hm
  have ecξi : c • D.xi i = D.xi i := hcfix i 3 (by norm_num)
  have ecξj : c • D.xi j = D.xi j := hcfix j 3 (by norm_num)
  have ecδi : c • D.delta i = D.delta i := hcfix i 4 (by norm_num)
  have ecδj : c • D.delta j = D.delta j := hcfix j 4 (by norm_num)
  have hwξi : w • D.xi i = D.xi i := by
    have h := hξi
    rwa [mul_smul, ecξi] at h
  have hwξj : w • D.xi j = D.xi j := by
    have h := hξj
    rwa [mul_smul, ecξj] at h
  have hwδi : w • D.delta i ≠ D.delta i := fun h => hδi (by rw [mul_smul, ecδi, h])
  have hwδj : w • D.delta j ≠ D.delta j := fun h => hδj (by rw [mul_smul, ecδj, h])
  have hwH : w ∈ ballStab Γ G 2 α := zGroup_le_ballStab h7 D hw
  have hwα : ∀ k, w • D.alpha k = D.alpha k :=
    fun k => mem_ballStab.1 hwH _ (by rw [D.dist_start_alpha F k])
  have hEi : w • D.delta i = (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.delta i :=
    smul_eq_of_move F (D.valence_xi F i) (D.adj_alpha_xi i).symm (D.adj_xi_delta i)
      (D.delta_ne_alpha i).symm hwξi (hwα i) hwδi hpξi (hpα i) hpδi
  have hEj : w • D.delta j = (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) • D.delta j :=
    smul_eq_of_move F (D.valence_xi F j) (D.adj_alpha_xi j).symm (D.adj_xi_delta j)
      (D.delta_ne_alpha j).symm hwξj (hwα j) hwδj hpξj (hpα j) hpδj
  have hui : ((L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w) • D.delta i =
      D.delta i := by rw [mul_smul, hEi, inv_smul_smul]
  have huj : ((L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w) • D.delta j =
      D.delta j := by rw [mul_smul, hEj, inv_smul_smul]
  have huV : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w ∈ L.zGroup 2 α :=
    mul_mem (inv_mem hpV) hw
  obtain ⟨P, hP0, hP4, hP8, -⟩ := D.exists_arc8 F h71c hij
  have huP : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w ∈ P.stab G :=
    (Arc.mem_stab G).2 fun k hk => Arc.fixes_of_ends F.isTree F.adj_smul P
      (by rw [hP0]; exact hui) (by rw [hP8]; exact huj) k hk
  have hv0 : valence Γ (P.vert 0) = 5 := by
    rw [hP0]
    exact D.valence_delta F i
  have hne : P.vert 0 ≠ P.vert 8 := by
    rw [hP0, hP8]
    exact fun h => hij (D.delta_injective h)
  have huC : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w ∈ L.calpha P := by
    rw [ZLab.calpha_eq_stab h71a h71c P hv0 hne]
    exact huP
  have hu : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w ∈
      Subgroup.zpowers (L.z α) := by
    have := (h73b P (by rw [hP4]; exact D.val)).2
    rw [hP4] at this
    rw [← this]
    exact Subgroup.mem_inf.2 ⟨huV, huC⟩
  have hwβ : w ∈ ballStab Γ G 2 (D.beta i) := by
    have h1 : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w ∈
        ballStab Γ G 2 (D.beta i) :=
      (Subgroup.zpowers_le.2 (z_mem_ballStab_two D h71c i)) hu
    have := mul_mem hpβ h1
    rwa [mul_inv_cancel_left] at this
  have hcβ : c ∈ ballStab Γ G 2 (D.beta i) := by
    have := mul_mem (inv_mem hwβ) hgβ
    rwa [inv_mul_cancel_left] at this
  have hcz := P2c.calpha_mem_zpowers D h7 hc hcβ
  have hq := mul_mem hu hcz
  have heq : w * c = (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) *
      ((L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))⁻¹ * w * c) := by group
  rcases mem_zpowers_involution (L.z_mul_self D.val) hq with h | h
  · exact ⟨0, by rw [heq, h]; simp⟩
  · exact ⟨1, by rw [heq, h]; simp⟩

end CFSG.Quasithin.Fan86.P2d1
