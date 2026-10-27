module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FRel
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Aff
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Key
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2F

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem eq_smul_or_inv_smul (F : FanTree Γ G) {a β ξ ν : V} {u : G}
    (ha : valence Γ a = 5) (hβ : Γ.Adj a β) (hξ : Γ.Adj a ξ) (hν : Γ.Adj a ν) (hξβ : ξ ≠ β)
    (hua : u • a = a) (huβ : u • β = β) (h4 : (u * u) * (u * u) = 1) (hs : (u * u) • ξ ≠ ξ)
    (hνβ : ν ≠ β) (hνξ : ν ≠ ξ) (hνs : ν ≠ (u * u) • ξ) : ν = u • ξ ∨ ν = u⁻¹ • ξ := by
  have hu4 : u * (u * u * u) = 1 := by
    calc u * (u * u * u) = (u * u) * (u * u) := by simp only [mul_assoc]
      _ = 1 := h4
  have hinv : u⁻¹ = u * u * u := inv_eq_of_mul_eq_one_right hu4
  have hadj : ∀ g : G, g • a = a → ∀ w, Γ.Adj a w → Γ.Adj a (g • w) := fun g hg w hw => by
    have := (F.adj_smul g a w).2 hw
    rwa [hg] at this
  have hsa : (u * u) • a = a := by rw [mul_smul, hua, hua]
  have hta : (u * u * u) • a = a := by rw [mul_smul, hua, hsa]
  have hsβ : (u * u) • β = β := by rw [mul_smul, huβ, huβ]
  have htβ : (u * u * u) • β = β := by rw [mul_smul, huβ, hsβ]
  have hsξ' : (u * u) • ξ = u • (u • ξ) := mul_smul u u ξ
  have htξ : (u * u * u) • ξ = (u * u) • (u • ξ) := mul_smul (u * u) u ξ
  have htξ' : (u * u * u) • ξ = u • ((u * u) • ξ) := by rw [mul_assoc, mul_smul]
  have hut : u • ((u * u * u) • ξ) = ξ := by
    rw [← mul_smul, hu4, one_smul]
  have inj : ∀ g : G, ∀ p q : V, g • p = g • q → p = q := fun g p q h => MulAction.injective g h
  have hβne : ∀ g : G, g • β = β → g • ξ ≠ β := fun g hg h => hξβ (inj g _ _ (h.trans hg.symm))
  have d1 : ξ ≠ u • ξ := fun h => hs (by
    calc (u * u) • ξ = u • (u • ξ) := mul_smul u u ξ
      _ = u • ξ := congrArg (fun t => u • t) h.symm
      _ = ξ := h.symm)
  have d3 : ξ ≠ (u * u * u) • ξ := fun h => d1 (by
    have := hut
    rw [← h] at this
    exact this.symm)
  have d4 : u • ξ ≠ (u * u) • ξ := fun h => d1 (inj u _ _ (h.trans hsξ'))
  have d5 : u • ξ ≠ (u * u * u) • ξ := fun h => hs (inj u _ _ (h.trans htξ')).symm
  have d6 : (u * u) • ξ ≠ (u * u * u) • ξ := fun h => d1 (inj (u * u) _ _ (h.trans htξ))
  let b : Fin 5 → V := ![β, ξ, u • ξ, (u * u) • ξ, (u * u * u) • ξ]
  have hbadj : ∀ i, Γ.Adj a (b i) := by
    intro i
    fin_cases i
    · exact hβ
    · exact hξ
    · exact hadj u hua ξ hξ
    · exact hadj (u * u) hsa ξ hξ
    · exact hadj (u * u * u) hta ξ hξ
  have hbinj : Function.Injective b := by
    intro i j hij
    have e0 : ∀ g : G, g • β = β → g • ξ ≠ β := hβne
    fin_cases i <;> fin_cases j <;> simp only [b, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
    all_goals first
      | rfl
      | exact absurd hij hξβ.symm
      | exact absurd hij.symm hξβ.symm
      | exact absurd hij hξβ
      | exact absurd hij.symm hξβ
      | exact absurd hij.symm (e0 u huβ)
      | exact absurd hij (e0 u huβ)
      | exact absurd hij.symm (e0 (u * u) hsβ)
      | exact absurd hij (e0 (u * u) hsβ)
      | exact absurd hij.symm (e0 (u * u * u) htβ)
      | exact absurd hij (e0 (u * u * u) htβ)
      | exact absurd hij d1
      | exact absurd hij.symm d1
      | exact absurd hij hs.symm
      | exact absurd hij.symm hs.symm
      | exact absurd hij d3
      | exact absurd hij.symm d3
      | exact absurd hij d4
      | exact absurd hij.symm d4
      | exact absurd hij d5
      | exact absurd hij.symm d5
      | exact absurd hij d6
      | exact absurd hij.symm d6
  obtain ⟨i, hi⟩ := F.exists_eq_of_adj_val5 ha hbadj hbinj hν
  fin_cases i
  · exact absurd hi.symm hνβ
  · exact absurd hi.symm hνξ
  · exact Or.inl hi.symm
  · exact absurd hi.symm hνs
  · exact Or.inr (by rw [hinv]; exact hi.symm)

variable {D}

theorem fcomm_eq_one_of_comm {a b : G} (h : a * b = b * a) : fcomm a b = 1 := by
  unfold fcomm
  calc a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

theorem y_move (F : FanTree Γ G) (h71c : Fan71c F L) (h83b : Fan83b F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) : D.y δ' i • D.alpha j ≠ D.alpha j := by
  intro hfix
  have hc := (h71c.comm_z_iff (D.valence_alpha F j) (D.y δ' i)).2 hfix
  have h1 : fcomm (D.y δ' i) (L.z (D.alpha j)) = 1 := fcomm_eq_one_of_comm hc
  have h2 : fcomm (D.y δ' i) (L.z (D.alpha j)) = L.z α := by
    simpa [hij] using h83b α D δ' hY i j
  exact L.z_ne_one D.val (h2.symm.trans h1)

theorem swap_eq_third (F : FanTree Γ G) {c : V}
    (hc : Γ.neighborSet (D.beta 0) = {α, D.alpha 0, c}) {g : G} (hg : g ∈ nbrStab Γ G α)
    (hmove : g • D.alpha 0 ≠ D.alpha 0) : g • D.alpha 0 = c := by
  have hgα : g • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hg)
  have hgβ : g • D.beta 0 = D.beta 0 := mem_nbrStab.1 hg _ (D.adj_start_beta 0)
  have hadj : Γ.Adj (D.beta 0) (g • D.alpha 0) := by
    have := (F.adj_smul g (D.beta 0) (D.alpha 0)).2 (D.adj_beta_alpha 0)
    rwa [hgβ] at this
  have hmem : g • D.alpha 0 ∈ Γ.neighborSet (D.beta 0) := hadj
  rw [hc] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact absurd (MulAction.injective g (h.trans hgα.symm)) (D.alpha_ne_start 0)
  · exact absurd h hmove
  · exact h

theorem u_fix_alpha (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) {δ' : V} (hY : D.IsYPair δ') :
    (D.y δ' 2 * D.y δ' 1) • D.alpha 0 = D.alpha 0 := by
  obtain ⟨c, hc, -⟩ := exists_third_neighbor (D.valence_beta F 0) (D.adj_start_beta 0).symm
    (D.adj_beta_alpha 0) (D.alpha_ne_start 0).symm
  have h1 := swap_eq_third F hc (Sec8P3.y_mem_nbrStab D h83a hY 1)
    (y_move F h71c h83b hY (by decide))
  have h2 := swap_eq_third F hc (Sec8P3.y_mem_nbrStab D h83a hY 2)
    (y_move F h71c h83b hY (by decide))
  rw [mul_smul, h1, ← h2, ← mul_smul, Sec8P3.y_mul_self D F h71c hY 2, one_smul]

theorem u_mem_nbrStab (h83a : Fan83a F L) {δ' : V} (hY : D.IsYPair δ') :
    D.y δ' 2 * D.y δ' 1 ∈ nbrStab Γ G α :=
  mul_mem (Sec8P3.y_mem_nbrStab D h83a hY 2) (Sec8P3.y_mem_nbrStab D h83a hY 1)

theorem u_sq (F : FanTree Γ G) (h71c : Fan71c F L) (h83d : Fan83d F L) {δ' : V}
    (hY : D.IsYPair δ') :
    (D.y δ' 2 * D.y δ' 1) * (D.y δ' 2 * D.y δ' 1) = L.z (D.alpha 0) * L.z (D.alpha 3) := by
  have h : fcomm (D.y δ' 2) (D.y δ' 1) = L.z (D.alpha 0) * L.z (D.alpha 3) := h83d.2 α D δ' hY 2 1
    (by decide)
  have hy2 := Sec8P3.y_mul_self D F h71c hY
  have hyinv : ∀ i, (D.y δ' i)⁻¹ = D.y δ' i := fun i => inv_eq_of_mul_eq_one_right (hy2 i)
  unfold fcomm at h
  rw [hyinv, hyinv] at h
  rw [← h]
  simp only [mul_assoc]

theorem u_four (F : FanTree Γ G) (h71c : Fan71c F L) (h83d : Fan83d F L) {δ' : V}
    (hY : D.IsYPair δ') :
    ((D.y δ' 2 * D.y δ' 1) * (D.y δ' 2 * D.y δ' 1)) *
      ((D.y δ' 2 * D.y δ' 1) * (D.y δ' 2 * D.y δ' 1)) = 1 := by
  rw [u_sq F h71c h83d hY]
  exact Sec8P3.zGroup_mul_self h71c _ (mul_mem (Sec8P3.z_alpha_mem_zGroup D F 0)
    (Sec8P3.z_alpha_mem_zGroup D F 3))

theorem u_sq_move (F : FanTree Γ G) (h71c : Fan71c F L) (h83d : Fan83d F L) {δ' : V}
    (hY : D.IsYPair δ') :
    ((D.y δ' 2 * D.y δ' 1) * (D.y δ' 2 * D.y δ' 1)) • D.xi 0 ≠ D.xi 0 := by
  rw [u_sq F h71c h83d hY, mul_smul]
  intro h
  have hd : Γ.dist (D.alpha 3) (D.xi 0) = 2 + 3 :=
    D.dist_vert_ne F h71c (i := 3) (j := 0) (by decide) (m := 2) (m' := 3) (by norm_num)
      (by norm_num)
  have h1 : L.z (D.alpha 3) • D.xi 0 ≠ D.xi 0 := fun h' => by
    have := (h71c.z_smul_eq_iff (D.valence_alpha F 3) _).1 h'
    omega
  have h2 : L.z (D.alpha 0) • D.xi 0 = D.xi 0 := by
    rw [h71c.z_smul_eq_iff (D.valence_alpha F 0), dist_eq_one_iff_adj.2 (D.adj_alpha_xi 0)]
    norm_num
  exact h1 (MulAction.injective (L.z (D.alpha 0)) (h.trans h2.symm))

theorem nu_cases (F : FanTree Γ G) (h7 : Fan7 F L) (h83a : Fan83a F L) (h83b : Fan83b F L)
    (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ') {ν : V} (hν : Γ.Adj (D.alpha 0) ν)
    (hνδ : Γ.Adj ν δ') :
    ν = (D.y δ' 2 * D.y δ' 1) • D.xi 0 ∨ ν = (D.y δ' 2 * D.y δ' 1)⁻¹ • D.xi 0 := by
  have h71c : Fan71c F L := h7.2.2.1
  have huα0 := u_fix_alpha F h71c h83a h83b hY
  have huβ0 : (D.y δ' 2 * D.y δ' 1) • D.beta 0 = D.beta 0 :=
    mem_nbrStab.1 (u_mem_nbrStab h83a hY) _ (D.adj_start_beta 0)
  have hu4 := u_four F h71c h83d hY
  have hs := u_sq_move F h71c h83d hY
  have hsG : (D.y δ' 2 * D.y δ' 1) * (D.y δ' 2 * D.y δ' 1) ∈
      Gcirc Γ G (D.alpha 0) (D.beta 0) := by
    refine mem_gcirc_of_sq_eq_one ⟨MulAction.mem_stabilizer_iff.2 ?_,
      MulAction.mem_stabilizer_iff.2 ?_⟩ hu4
    · rw [mul_smul, huα0, huα0]
    · rw [mul_smul, huβ0, huβ0]
  have hδ'a : δ' ≠ D.alpha 0 := fun h => by
    have := hY.2.2.2.2.1
    rw [← h, SimpleGraph.dist_self] at this
    omega
  obtain ⟨hne1, hne2⟩ := F.z2_branches (fan40_of_fan71b h7.2.1) (D.valence_alpha F 0)
    (D.adj_beta_alpha 0).symm (D.adj_alpha_xi 0) hν (D.adj_xi_delta 0) (D.delta_ne_alpha 0) hνδ
    hδ'a hsG hY.2.2.2.2.2.2.2
  have hνβ : ν ≠ D.beta 0 := by
    rintro rfl
    have h1 := F.isTree.connected.dist_triangle (u := α) (v := D.beta 0) (w := δ')
    rw [D.dist_start_beta F 0, dist_eq_one_iff_adj.2 hνδ] at h1
    have := hY.2.2.2.2.2.2.1
    omega
  exact eq_smul_or_inv_smul F (D.valence_alpha F 0) (D.adj_beta_alpha 0).symm
    (D.adj_alpha_xi 0) hν (D.xi_ne_beta 0) huα0 huβ0 hu4 hs hνβ hne1.symm hne2

end Sec8P2F

end CFSG.Quasithin.Fan86
