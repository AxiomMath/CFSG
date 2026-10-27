module

public import CFSG.Quasithin.MS93.S4A44Base

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Back

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem exists_isCritical_step (h : Hyp20 X) (hb : 0 < critDist X) {δ δ' : Vtx X}
    (hc : IsCritical X δ δ') (hV : ¬ Vv X δ ≤ Qv X (geo X δ' δ 2)) :
    ∃ ρ, X.treeGraph.dist δ ρ = 2 ∧ IsCritical X ρ (geo X δ' δ 2) := by
  have hd : X.treeGraph.dist δ δ' = critDist X := hc.2.1
  have hb2 := two_le_critDist X h hb
  set ε := geo X δ' δ 2
  have hδε : X.treeGraph.dist δ ε = critDist X - 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm, hd]
  obtain ⟨ρ, hρ, hρε⟩ : ∃ ρ, X.treeGraph.dist δ ρ ≤ 2 ∧ ¬ Zv X ρ ≤ Qv X ε := by
    by_contra hcon
    push Not at hcon
    exact hV (iSup₂_le fun ρ hρ => hcon ρ hρ)
  have htri := dist_triangle X ρ δ ε
  rw [tdist_comm X ρ δ] at htri
  by_cases hρM : IsMVtx X ρ
  · rw [zv_of_isMVtx X hρM] at hρε
    have hge : critDist X ≤ X.treeGraph.dist ρ ε := by
      by_contra hlt
      exact hρε (zm_le_qv_of_dist_lt X hρM (by omega))
    exact ⟨ρ, by omega, hρM, by omega, hρε⟩
  · exfalso
    rw [zv_of_not_isMVtx X hρM] at hρε
    have hδM := hc.1
    have hodd : ¬ Even (X.treeGraph.dist δ ρ) := by
      rw [even_dist_iff]
      tauto
    have h1 : X.treeGraph.dist δ ρ = 1 := by
      have h0 : X.treeGraph.dist δ ρ ≠ 0 := fun h0 => hodd (h0 ▸ ⟨0, rfl⟩)
      have h2 : X.treeGraph.dist δ ρ ≠ 2 := fun h2 => hodd (h2 ▸ ⟨1, rfl⟩)
      omega
    exact hρε ((zh_le_zm X (SimpleGraph.dist_eq_one_iff_adj.mp h1)).trans
      (zm_le_qv_of_dist_lt X hc.1 (by omega)))

theorem exists_isCritical_back (h : Hyp20 X) (hb : 0 < critDist X)
    (hV : ∀ δ δ' : Vtx X, IsCritical X δ δ' → ¬ Vv X δ ≤ Qv X (geo X δ' δ 2)) {α α' : Vtx X}
    (hc : IsCritical X α α') :
    ∀ i, 2 * i + 2 ≤ critDist X →
      ∃ ρ, IsCritical X ρ (geo X α α' (critDist X - 2 * i)) ∧
        X.treeGraph.dist ρ α = 2 * i := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨α, ?_, by simp⟩
    rw [Nat.mul_zero, Nat.sub_zero, ← hd, geo_dist]
    exact hc
  | succ i ih =>
    intro hi
    obtain ⟨ρ, hρc, hρα⟩ := ih (by omega)
    set v := geo X α α' (critDist X - 2 * i)
    set w := geo X α α' (critDist X - 2 * (i + 1))
    have hαw : X.treeGraph.dist α w = critDist X - 2 * (i + 1) := dist_geo X (by omega)
    have hwv : X.treeGraph.dist w v = 2 := by
      rw [dist_geo_geo X (by omega) (by omega)]
      omega
    have hρv : X.treeGraph.dist ρ v = critDist X := hρc.2.1
    have hw : w = geo X v ρ 2 := by
      have t1 := dist_triangle X ρ α w
      have t2 := dist_triangle X ρ w v
      rw [hαw, hρα] at t1
      rw [hwv, hρv] at t2
      have e1 : X.treeGraph.dist v w = 2 := by rw [SimpleGraph.dist_comm]; exact hwv
      apply eq_geo_of_dist X e1
      rw [e1, tdist_comm X w ρ, tdist_comm X v ρ, hρv]
      omega
    obtain ⟨ρ', hρρ', hρ'c⟩ := exists_isCritical_step X h hb hρc (hV ρ v hρc)
    rw [← hw] at hρ'c
    refine ⟨ρ', hρ'c, ?_⟩
    have hρ'w : X.treeGraph.dist ρ' w = critDist X := hρ'c.2.1
    have t1 := dist_triangle X ρ' ρ α
    have t2 := dist_triangle X ρ' α w
    rw [tdist_comm X ρ' ρ, hρρ', hρα] at t1
    rw [hαw, hρ'w] at t2
    omega


theorem dist_geo_back {α α' δ : Vtx X} {m : ℕ} (hm : m ≤ X.treeGraph.dist α α')
    (hcδ : X.treeGraph.dist δ (geo X α α' m) = critDist X)
    (hδα : X.treeGraph.dist δ α = critDist X - m) (hmb : m ≤ critDist X) {k : ℕ} (hk : k ≤ m) :
    X.treeGraph.dist δ (geo X α α' k) = critDist X - m + k := by
  have t1 := dist_triangle X δ α (geo X α α' k)
  have t2 := dist_triangle X δ (geo X α α' k) (geo X α α' m)
  rw [dist_geo X (hk.trans hm)] at t1
  rw [dist_geo_geo X hk hm, hcδ] at t2
  omega

theorem vv_le_centralizer_zm (h : Hyp20 X) {α δ : Vtx X} (hδ : IsMVtx X δ)
    (hd : X.treeGraph.dist δ α + 2 < critDist X) :
    Vv X α ≤ Subgroup.centralizer (ZM X δ : Set X.Universal) := by
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : X.treeGraph.dist α ρ ≤ 2 := hρ
  have hZQ : ZM X δ ≤ Qv X ρ := by
    refine zm_le_qv_of_dist_lt X hδ ?_
    have := dist_triangle X δ α ρ
    omega
  refine le_trans ?_ (Subgroup.centralizer_le hZQ)
  by_cases hρM : IsMVtx X ρ
  · rw [zv_of_isMVtx X hρM]
    exact zm_le_centralizer_qv X h hρM
  · rw [zv_of_not_isMVtx X hρM]
    exact zh_le_centralizer X ρ

end Back

section Mirror

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem eq_of_adj_adj_of_dist_eq_two {u x y w : Vtx (puAmalgam h.le)}
    (hux : (puAmalgam h.le).treeGraph.Adj u x) (hxw : (puAmalgam h.le).treeGraph.Adj x w)
    (huy : (puAmalgam h.le).treeGraph.Adj u y) (hyw : (puAmalgam h.le).treeGraph.Adj y w)
    (huw : (puAmalgam h.le).treeGraph.dist u w = 2) : x = y := by
  have h1 := eq_geo_one _ hux (by rw [dist_eq_one_of_adj _ hxw, huw])
  have h2 := eq_geo_one _ huy (by rw [dist_eq_one_of_adj _ hyw, huw])
  rw [h1, h2]

theorem exists_ltil_mirror (hfull : IsSL3Full M T L) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hs : IsStraight (puAmalgam h.le) α α') {j : ℕ}
    (hj0 : 0 < j) (hjb : 2 * j < critDist (puAmalgam h.le)) :
    ∃ s ∈ Ltil h.le L (geo (puAmalgam h.le) α α' (2 * j)),
      s • geo (puAmalgam h.le) α α' (2 * j + 2) = geo (puAmalgam h.le) α α' (2 * j - 2) ∧
        s • geo (puAmalgam h.le) α α' (2 * j + 1) = geo (puAmalgam h.le) α α' (2 * j - 1) := by
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  obtain ⟨g, hg, hge⟩ := hs j hj0 (by rw [hd]; exact hjb)
  have hM : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j)) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two_mul j, fun _ => hc.1⟩
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' (2 * j))
      (geo (puAmalgam h.le) α α' (2 * j + 1)) := adj_geo _ (by omega)
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' (2 * j + 1))
      (geo (puAmalgam h.le) α α' (2 * j + 2)) := adj_geo _ (by omega)
  obtain ⟨l, hl, hle⟩ := exists_ltil_smul_eq h hfull hM hadj1 hadj2 hg
  refine ⟨l, hl, hle.trans hge, ?_⟩
  have hls : l • geo (puAmalgam h.le) α α' (2 * j) = geo (puAmalgam h.le) α α' (2 * j) :=
    (mem_stab _).mp (ltil_le_stab h _ hl)
  have hadj3 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' (2 * j - 2))
      (geo (puAmalgam h.le) α α' (2 * j - 1)) := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := α') (i := 2 * j - 2) (by omega)
    rwa [show 2 * j - 2 + 1 = 2 * j - 1 by omega] at this
  have hadj4 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' (2 * j - 1))
      (geo (puAmalgam h.le) α α' (2 * j)) := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := α') (i := 2 * j - 1) (by omega)
    rwa [show 2 * j - 1 + 1 = 2 * j by omega] at this
  apply eq_of_adj_adj_of_dist_eq_two h (u := geo (puAmalgam h.le) α α' (2 * j))
    (w := geo (puAmalgam h.le) α α' (2 * j - 2))
  · rw [← hls]
    exact (adj_smul _ l _ _).mpr hadj1
  · rw [← hle.trans hge]
    exact (adj_smul _ l _ _).mpr hadj2
  · exact hadj4.symm
  · exact hadj3.symm
  · rw [SimpleGraph.dist_comm, dist_geo_geo _ (by omega) (by omega)]
    omega

theorem usup_le_dloc_transport (hfull : IsSL3Full M T L) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hs : IsStraight (puAmalgam h.le) α α') {j : ℕ}
    (hj : 2 ≤ j) (hjb : 2 * j < critDist (puAmalgam h.le))
    (hle : Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j + 2))
        (geo (puAmalgam h.le) α α' (2 * j + 1)) ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' (2 * j))) :
    Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j - 2))
        (geo (puAmalgam h.le) α α' (2 * j - 3)) ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' (2 * j - 4)) := by
  obtain ⟨s₁, hs₁, hs₁a, hs₁b⟩ := exists_ltil_mirror h hfull hc hs (j := j) (by omega) hjb
  obtain ⟨s₀, hs₀, hs₀a, hs₀b⟩ := exists_ltil_mirror h hfull hc hs (j := j - 1) (by omega)
    (by omega)
  have e₀ : 2 * (j - 1) = 2 * j - 2 := by omega
  have e₂ : 2 * (j - 1) + 2 = 2 * j := by omega
  have e₂' : 2 * (j - 1) - 2 = 2 * j - 4 := by omega
  have e₁ : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
  have e₁' : 2 * (j - 1) - 1 = 2 * j - 3 := by omega
  rw [e₂, e₂'] at hs₀a
  rw [e₁, e₁'] at hs₀b
  rw [e₀] at hs₀
  have hs₀s : s₀ • geo (puAmalgam h.le) α α' (2 * j - 2) = geo (puAmalgam h.le) α α' (2 * j - 2) :=
    (mem_stab _).mp (ltil_le_stab h _ hs₀)
  have e1 : (s₀ * s₁) • geo (puAmalgam h.le) α α' (2 * j + 2) =
      geo (puAmalgam h.le) α α' (2 * j - 2) := by rw [mul_smul, hs₁a, hs₀s]
  have e2 : (s₀ * s₁) • geo (puAmalgam h.le) α α' (2 * j + 1) =
      geo (puAmalgam h.le) α α' (2 * j - 3) := by rw [mul_smul, hs₁b, hs₀b]
  have e3 : (s₀ * s₁) • geo (puAmalgam h.le) α α' (2 * j) =
      geo (puAmalgam h.le) α α' (2 * j - 4) := by
    rw [mul_smul, (mem_stab _).mp (ltil_le_stab h _ hs₁), hs₀a]
  rw [← e1, ← e2, ← e3, usup_smul, dloc_smul h]
  exact Subgroup.map_mono hle

theorem usup_eq_of_le_dloc (hfull : IsSL3Full M T L) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') (hs : IsStraight (puAmalgam h.le) α α') {j : ℕ}
    (hj : 2 ≤ j) (hjb : 2 * j ≤ critDist (puAmalgam h.le))
    (hle : Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j))
        (geo (puAmalgam h.le) α α' (2 * j - 1)) ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' (2 * j - 2))) :
    Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j))
        (geo (puAmalgam h.le) α α' (2 * j - 1)) =
      Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j - 4))
        (geo (puAmalgam h.le) α α' (2 * j - 3)) := by
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨s, hsL, hsa, hsb⟩ := exists_ltil_mirror h hfull hc hs (j := j - 1) (by omega)
    (by omega)
  have e₀ : 2 * (j - 1) = 2 * j - 2 := by omega
  have e₂ : 2 * (j - 1) + 2 = 2 * j := by omega
  have e₂' : 2 * (j - 1) - 2 = 2 * j - 4 := by omega
  have e₁ : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
  have e₁' : 2 * (j - 1) - 1 = 2 * j - 3 := by omega
  rw [e₂, e₂'] at hsa
  rw [e₁, e₁'] at hsb
  rw [e₀] at hsL
  have hM : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α α' (2 * j - 2)) :=
    (isMVtx_geo _ (by omega)).mpr
      ⟨fun _ => ⟨j - 1, by omega⟩, fun _ => hc.1⟩
  have hcen := dloc_le_centralizer_ltil h hM
  rw [← hsa, ← hsb, usup_smul]
  symm
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp (hcen (hle hx)) s hsL
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxs, mul_inv_cancel_right]
    exact hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp (hcen (hle hx)) s hsL
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxs, mul_inv_cancel_right]

end Mirror

end CFSG.Quasithin.MS93.S4A
