module

public import CFSG.Quasithin.MS93.Sec2One

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def CentHyp : Prop :=
  ∀ α β : Vtx X, IsMVtx X α → X.treeGraph.Adj α β →
    Qv X β ⊓ Subgroup.centralizer (ZM X α : Set X.Universal) = Qv X α

theorem centHyp_of_edge {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    (hC : Qv X β ⊓ Subgroup.centralizer (ZM X α : Set X.Universal) = Qv X α) : CentHyp X := by
  intro α' β' hα' hαβ'
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx X hα hαβ hα' hαβ'
  rw [qv_smul, zm_smul, qv_smul, ← centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hC]

theorem two_le_critDist (h : Hyp20 X) (hb : 0 < critDist X) : 2 ≤ critDist X := by
  obtain ⟨k, hk⟩ := ms21_v X h
  rw [hk] at hb ⊢
  omega

theorem le_qv_of_le_centralizer (hC : CentHyp X) {α β : Vtx X} (hα : IsMVtx X α)
    (hαβ : X.treeGraph.Adj α β) {K : Subgroup X.Universal} (hK : K ≤ Qv X β)
    (hKc : K ≤ Subgroup.centralizer (ZM X α : Set X.Universal)) : K ≤ Qv X α :=
  (hC α β hα hαβ) ▸ le_inf hK hKc

theorem ms22_i (h : Hyp20 X) (hC : CentHyp X) {α μ : Vtx X}
    (hα : IsMVtx X α) (hμ : IsMVtx X μ) (hd : X.treeGraph.dist α μ < critDist X) :
    XM X α ≤ Qv X μ := by
  suffices key : ∀ n, ∀ μ, IsMVtx X μ → X.treeGraph.dist α μ = n → n < critDist X →
      XM X α ≤ Qv X μ from key _ μ hμ rfl hd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro μ hμ hn hnb
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [(dist_eq_zero_iff X).mp hn]
      exact xm_le_qv X μ
    · set ρ := geo X μ α 1
      have hμρ : X.treeGraph.Adj μ ρ := adj_geo_one X (by rw [SimpleGraph.dist_comm]; omega)
      have hρ : ¬ IsMVtx X ρ := (isMVtx_iff_of_adj X hμρ).mp hμ
      have hρα : X.treeGraph.dist ρ α = n - 1 := by
        rw [dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega), SimpleGraph.dist_comm, hn]
      have hρα0 : 0 < X.treeGraph.dist ρ α := by
        rcases Nat.eq_zero_or_pos (X.treeGraph.dist ρ α) with h0 | h0
        · rw [(dist_eq_zero_iff X).mp h0] at hρ
          exact absurd hα hρ
        · exact h0
      set ν := geo X ρ α 1
      have hρν : X.treeGraph.Adj ρ ν := adj_geo_one X hρα0
      have hν : IsMVtx X ν := by
        have := isMVtx_iff_of_adj X hρν
        tauto
      have hνα : X.treeGraph.dist α ν = n - 2 := by
        rw [SimpleGraph.dist_comm, dist_geo_right X (show 1 ≤ X.treeGraph.dist ρ α by omega), hρα]
        omega
      have hXρ : XM X α ≤ Qv X ρ :=
        (ih (n - 2) (by omega) ν hν hνα (by omega)).trans (qv_le_qv X h hν hρν.symm)
      by_contra hle
      have hnc : ¬ XM X α ≤ Subgroup.centralizer (ZM X μ : Set X.Universal) := fun hc =>
        hle (le_qv_of_le_centralizer X hC hμ hμρ hXρ hc)
      have hZμ : ¬ ZM X μ ≤ Qv X α := fun hZ => hnc (Subgroup.le_centralizer_iff.mp
        (hZ.trans (qv_le_centralizer_xm X α)))
      exact hZμ (zm_le_qv_of_dist_lt X hμ (by rw [SimpleGraph.dist_comm]; omega))

theorem ms22_ii (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X) {α α' : Vtx X}
    (hc : IsCritical X α α') : ⁅ZM X α, ZM X α'⁆ ≠ ⊥ := by
  intro hbot
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hα' := hc.isMVtx_right X h
  set γ := geo X α' α 1
  have hα'γ : X.treeGraph.Adj α' γ := adj_geo_one X (by rw [SimpleGraph.dist_comm]; omega)
  have hZγ : ZM X α ≤ Qv X γ := by
    refine zm_le_qv_of_dist_lt X hc.1 ?_
    rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm]
    omega
  exact hc.2.2 (le_qv_of_le_centralizer X hC hα' hα'γ hZγ
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot))

theorem ms22_iii (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X) {α α' : Vtx X}
    (hc : IsCritical X α α') : IsCritical X α' α := by
  refine ⟨hc.isMVtx_right X h, by rw [SimpleGraph.dist_comm]; exact hc.2.1, fun hle => ?_⟩
  apply ms22_ii X h hb hC hc
  rw [← le_bot_iff, ← commutator_zm_qv X h hc.1]
  exact Subgroup.commutator_mono_right hle

theorem isMVtx_geo_two (h : Hyp20 X) (hb : 0 < critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') : IsMVtx X (geo X α α' 2) := by
  have := two_le_critDist X h hb
  rw [isMVtx_geo X (by rw [hc.2.1]; omega)]
  exact ⟨fun _ => even_two, fun _ => hc.1⟩

theorem ms22_iv (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X) {α α' : Vtx X}
    (hc : IsCritical X α α') :
    ¬ stab X (geo X α α' 2) ≤ Subgroup.normalizer
      ((ZM X α ⊔ XM X (geo X α α' 2) : Subgroup X.Universal) : Set X.Universal) := by
  intro hN
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hb2 := two_le_critDist X h hb
  have hα := hc.1
  have hα' := hc.isMVtx_right X h
  set β := geo X α α' 1
  set γ := geo X α α' 2
  have hαβ : X.treeGraph.Adj α β := adj_geo_one X (by omega)
  have hβγ : X.treeGraph.Adj β γ := adj_geo X (i := 1) (by omega)
  have hγ : IsMVtx X γ := isMVtx_geo_two X h hb hc
  have hNβ : ZM X α ⊔ XM X γ ≤ Qv X β :=
    sup_le ((zm_le_qv_self X hα hb).trans (qv_le_qv X h hα hαβ))
      ((xm_le_qv X γ).trans (qv_le_qv X h hγ hβγ.symm))
  have hNγ : ZM X α ⊔ XM X γ ≤ Qv X γ := le_qv_of_normalizer X h hγ hβγ.symm hNβ hN
  have hγα' : X.treeGraph.dist γ α' = critDist X - 2 := by
    rw [dist_geo_right X (by omega), hd]
  have hb4 : 4 ≤ critDist X := by
    obtain ⟨k, hk⟩ := ms21_v X h
    by_contra hlt
    have hb2' : critDist X = 2 := by omega
    have hγeq : γ = α' := (dist_eq_zero_iff X).mp (by rw [hγα', hb2'])
    exact hc.2.2 (hγeq ▸ le_sup_left.trans hNγ)
  set δ := geo X α α' 3
  have hγδ : X.treeGraph.Adj γ δ := adj_geo X (i := 2) (by omega)
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul X hβγ.symm hγδ
  have hgN := map_conj_eq_of_mem_normalizer (hN hg)
  rw [Subgroup.map_sup, ← zm_smul, ← xm_smul, (mem_stab X).mp hg] at hgN
  have hZ : ZM X α ≤ ZM X (g • α) ⊔ XM X γ := by
    rw [hgN]
    exact le_sup_left
  refine hc.2.2 (hZ.trans (sup_le ?_ (ms22_i X h hC hγ hα' (by omega))))
  refine zm_le_qv_of_dist_lt X ((isMVtx_smul X g α).mpr hα) ?_
  have h1 : X.treeGraph.dist (g • α) δ = 1 := by
    rw [← hgβ, dist_smul, dist_eq_one_of_adj X hαβ]
  have h2 : X.treeGraph.dist δ α' = critDist X - 3 := by
    rw [dist_geo_right X (by omega), hd]
  have := dist_triangle X (g • α) δ α'
  omega

private theorem step_v (h : Hyp20 X) (hb : 0 < critDist X) {δ δ' : Vtx X}
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
    exact hρε ((zh_le_zm X (dist_eq_one_iff_adj.mp h1)).trans
      (zm_le_qv_of_dist_lt X hc.1 (by omega)))

private theorem iter_v (h : Hyp20 X) (hb : 0 < critDist X)
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
    obtain ⟨ρ', hρρ', hρ'c⟩ := step_v X h hb hρc (hV ρ v hρc)
    rw [← hw] at hρ'c
    refine ⟨ρ', hρ'c, ?_⟩
    have hρ'w : X.treeGraph.dist ρ' w = critDist X := hρ'c.2.1
    have t1 := dist_triangle X ρ' ρ α
    have t2 := dist_triangle X ρ' α w
    rw [tdist_comm X ρ' ρ, hρρ', hρα] at t1
    rw [hαw, hρ'w] at t2
    omega

theorem ms22_v (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    (hV : ∀ δ δ' : Vtx X, IsCritical X δ δ' → ¬ Vv X δ ≤ Qv X (geo X δ' δ 2)) {α α' : Vtx X}
    (hc : IsCritical X α α') :
    ¬ stab X α ≤ Subgroup.normalizer
      ((ZM X (geo X α α' 2) ⊔ XM X α : Subgroup X.Universal) : Set X.Universal) := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hb2 := two_le_critDist X h hb
  obtain ⟨k, hk⟩ := ms21_v X h
  obtain ⟨ρ, hρc, hρα⟩ := iter_v X h hb hV hc (k - 1) (by omega)
  rw [show critDist X - 2 * (k - 1) = 2 by omega] at hρc
  set γ := geo X α α' 2
  have hγc := ms22_iii X h hb hC hρc
  have hγα : X.treeGraph.dist γ α = 2 := by
    rw [SimpleGraph.dist_comm, dist_geo X (by omega)]
  have hgeo : geo X γ ρ 2 = α := by
    symm
    apply eq_geo_of_dist X hγα
    rw [hγα, tdist_comm X α ρ, hρα, hγc.2.1]
    omega
  have := ms22_iv X h hb hC hγc
  rwa [hgeo] at this

private def IsFFAt (V : Subgroup X.Universal) (α β : Vtx X) : Prop :=
  ∃ E : Subgroup X.Universal, E ≤ Qv X β ∧ CFSG.Open.IsElemAbelian 2 E ∧ ¬ E ≤ Qv X α ∧
    (Subgroup.centralizer (E : Set X.Universal)).relIndex V ≤ (Qv X α).relIndex E

private theorem isFFAt_smul {V : Subgroup X.Universal} {α β : Vtx X} (g : X.Universal)
    (hV : IsFFAt X V α β) :
    IsFFAt X (V.map (MulAut.conj g).toMonoidHom) (g • α) (g • β) := by
  obtain ⟨E, hEβ, hE, hEα, hineq⟩ := hV
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, (isElemAbelian_map_mulEquiv _).mpr hE, ?_, ?_⟩
  · rw [qv_smul]
    exact Subgroup.map_mono hEβ
  · rwa [qv_smul, map_conj_le_map_conj_iff]
  · rw [← centralizer_map_mulEquiv, qv_smul,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hineq

private theorem relIndex_ne_zero_of_le {H K L : Subgroup X.Universal} (hKL : K ≤ L) [Finite L] :
    H.relIndex K ≠ 0 := by
  have : Finite K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  exact Subgroup.index_ne_zero_of_finite

private theorem relIndex_centralizer_le {Q V E P : Subgroup X.Universal} (hEP : E ≤ P) [Finite P]
    (hQV : Q ≤ Subgroup.centralizer (V : Set X.Universal)) :
    (Subgroup.centralizer (V : Set X.Universal)).relIndex E ≤ Q.relIndex E := by
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (H := Q)]
  exact Subgroup.relIndex_le_of_le_left (inf_le_inf_right _ hQV)
    (relIndex_ne_zero_of_le X hEP)

private theorem isFFAt_or {α α' β γ : Vtx X} {V V' : Subgroup X.Universal}
    [Finite (Qv X β)] [Finite (Qv X γ)] (hV'β : V' ≤ Qv X β) (hVγ : V ≤ Qv X γ)
    (hQV : Qv X α ≤ Subgroup.centralizer (V : Set X.Universal))
    (hQV' : Qv X α' ≤ Subgroup.centralizer (V' : Set X.Universal))
    (hV : CFSG.Open.IsElemAbelian 2 V) (hV' : CFSG.Open.IsElemAbelian 2 V')
    (hn : ¬ V' ≤ Qv X α) (hn' : ¬ V ≤ Qv X α') :
    IsFFAt X V α β ∨ IsFFAt X V' α' γ := by
  rcases le_total ((Subgroup.centralizer (V' : Set X.Universal)).relIndex V)
      ((Subgroup.centralizer (V : Set X.Universal)).relIndex V') with hle | hle
  · exact Or.inl ⟨V', hV'β, hV', hn, hle.trans (relIndex_centralizer_le X hV'β hQV)⟩
  · exact Or.inr ⟨V, hVγ, hV, hn', hle.trans (relIndex_centralizer_le X hVγ hQV')⟩

theorem ms22_vi (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X) {α β : Vtx X}
    (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β) :
    (∃ E : Subgroup X.Universal, E ≤ Qv X β ∧ CFSG.Open.IsElemAbelian 2 E ∧ ¬ E ≤ Qv X α ∧
      (Subgroup.centralizer (E : Set X.Universal)).relIndex (ZM X α) ≤ (Qv X α).relIndex E) ∧
    (∃ E : Subgroup X.Universal, E ≤ Qv X β ∧ CFSG.Open.IsElemAbelian 2 E ∧ ¬ E ≤ Qv X α ∧
      (Subgroup.centralizer (E : Set X.Universal)).relIndex (XM X α) ≤ (Qv X α).relIndex E) := by
  obtain ⟨α', hc, hβ⟩ := exists_isCritical_geo X h hb hα hαβ
  have hc' := ms22_iii X h hb hC hc
  have hα' := hc.isMVtx_right X h
  have hb2 := two_le_critDist X h hb
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  set γ := geo X α' α 1
  have hα'γ : X.treeGraph.Adj α' γ := adj_geo_one_of_isCritical X hb hc'
  have : Finite (Qv X β) := finite_qv X h ((isMVtx_iff_of_adj X hαβ).mp hα)
  have : Finite (Qv X γ) := finite_qv X h ((isMVtx_iff_of_adj X hα'γ).mp hα')
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx X hα' hα'γ hα hαβ
  have hZβ : ZM X α' ≤ Qv X β := hβ ▸ zm_le_qv_geo_one X h hb hc
  have hZγ : ZM X α ≤ Qv X γ := zm_le_qv_geo_one X h hb hc'
  have hXβ : XM X α' ≤ Qv X β := by
    have h1 : X.treeGraph.Adj (geo X α α' 1) (geo X α α' 2) := adj_geo X (i := 1) (by omega)
    rw [← hβ]
    refine (ms22_i X h hC hα' (isMVtx_geo_two X h hb hc) ?_).trans
      (qv_le_qv X h (isMVtx_geo_two X h hb hc) h1.symm)
    rw [SimpleGraph.dist_comm, dist_geo_right X (by omega), hd]
    omega
  have hXγ : XM X α ≤ Qv X γ := by
    have h1 : X.treeGraph.Adj (geo X α' α 1) (geo X α' α 2) :=
      adj_geo X (i := 1) (by rw [SimpleGraph.dist_comm]; omega)
    refine (ms22_i X h hC hα (isMVtx_geo_two X h hb hc') ?_).trans
      (qv_le_qv X h (isMVtx_geo_two X h hb hc') h1.symm)
    rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm, hd]
    omega
  refine ⟨?_, ?_⟩
  · rcases isFFAt_or X hZβ hZγ (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv X h hα))
      (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv X h hα')) (isElemAbelian_zm X h hb hα)
      (isElemAbelian_zm X h hb hα') hc'.2.2 hc.2.2 with h1 | h1
    · exact h1
    · have := isFFAt_smul X g h1
      rwa [← zm_smul, hg1, hg2] at this
  · rcases isFFAt_or X hXβ hXγ (qv_le_centralizer_xm X α) (qv_le_centralizer_xm X α')
      (isElemAbelian_xm X α) (isElemAbelian_xm X α')
      (fun hle => hc'.2.2 ((zm_le_xm X h hb hα').trans hle))
      (fun hle => hc.2.2 ((zm_le_xm X h hb hα).trans hle)) with h1 | h1
    · exact h1
    · have := isFFAt_smul X g h1
      rwa [← xm_smul, hg1, hg2] at this

end CFSG.Quasithin.MS93
