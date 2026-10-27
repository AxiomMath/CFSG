module

public import CFSG.Quasithin.MS93.S38Crit

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 SimpleGraph
open scoped commutatorElement

section GroupTheory

variable {G : Type*} [Group G]

theorem commutator_closure_le {s t : Set G} {N : Subgroup G}
    (hs : Subgroup.closure s ≤ Subgroup.normalizer (N : Set G))
    (ht : Subgroup.closure t ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ x ∈ s, ∀ y ∈ t, ⁅x, y⁆ ∈ N) :
    ⁅Subgroup.closure s, Subgroup.closure t⁆ ≤ N := by
  have conj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  have step1 : ∀ x ∈ s, ∀ y ∈ Subgroup.closure t, ⁅x, y⁆ ∈ N := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => rw [commutatorElement_one_right]; exact N.one_mem
    | mul y₁ y₂ hy₁ _ ih₁ ih₂ =>
      have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem ih₁ (conj _ (ht hy₁) _ ih₂)
    | inv y hy ih =>
      have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact conj _ (inv_mem (ht hy)) _ (inv_mem ih)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  induction hx using Subgroup.closure_induction generalizing y with
  | mem x hx => exact step1 x hx y hy
  | one => rw [commutatorElement_one_left]; exact N.one_mem
  | mul x₁ x₂ hx₁ _ ih₁ ih₂ =>
    have e : ⁅x₁ * x₂, y⁆ = (x₁ * ⁅x₂, y⁆ * x₁⁻¹) * ⁅x₁, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem (conj _ (hs hx₁) _ (ih₂ y hy)) (ih₁ y hy)
  | inv x hx ih =>
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj _ (inv_mem (hs hx)) _ (inv_mem (ih y hy))

theorem commutator_iSup_le {ι : Type*} (K : ι → Subgroup G) {N : Subgroup G}
    (hN : ∀ i, K i ≤ Subgroup.normalizer (N : Set G)) (hK : ∀ i j, ⁅K i, K j⁆ ≤ N) :
    ⁅⨆ i, K i, ⨆ i, K i⁆ ≤ N := by
  have hle : Subgroup.closure (⋃ i, (K i : Set G)) ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.closure_le]
    rintro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hN i hi
  rw [Subgroup.iSup_eq_closure]
  refine commutator_closure_le hle hle fun x hx y hy => ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  exact hK i j (Subgroup.commutator_mem_commutator hi hj)

theorem le_normalizer_commutator' {Z A B : Subgroup G}
    (hA : Z ≤ Subgroup.normalizer (A : Set G)) (hB : Z ≤ Subgroup.normalizer (B : Set G)) :
    Z ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hA hz),
    map_conj_eq_of_mem_normalizer (hB hz)]

theorem le_normalizer_iSup {ι : Sort*} {Z : Subgroup G} {K : ι → Subgroup G}
    (h : ∀ i, Z ≤ Subgroup.normalizer (K i : Set G)) :
    Z ≤ Subgroup.normalizer ((⨆ i, K i : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_iSup]
  exact iSup_mono fun i => (map_conj_eq_of_mem_normalizer (h i hz)).le

end GroupTheory

section Amalgam

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def StarNorm : Prop :=
  ∀ δ δ' : Vtx X, IsCritical X δ δ' →
    stab X (geo X δ δ' 2) ≤ Subgroup.normalizer
      ((⁅XM X δ, XM X δ'⁆ : Subgroup X.Universal) : Set X.Universal)

@[expose] noncomputable def nA (α : Vtx X) : Subgroup X.Universal :=
  ⨆ (δ : Vtx X) (δ' : Vtx X) (_ : IsCritical X δ δ' ∧ geo X δ δ' 2 = α), ⁅XM X δ, XM X δ'⁆

theorem commutator_xm_le_nA {δ δ' : Vtx X} (hc : IsCritical X δ δ') :
    ⁅XM X δ, XM X δ'⁆ ≤ nA X (geo X δ δ' 2) :=
  le_iSup_of_le δ (le_iSup_of_le δ' (le_iSup_of_le (f := fun _ => ⁅XM X δ, XM X δ'⁆)
    ⟨hc, rfl⟩ le_rfl))

theorem stab_le_normalizer_nA (hN : StarNorm X) (α : Vtx X) :
    stab X α ≤ Subgroup.normalizer (nA X α : Set X.Universal) := by
  refine le_normalizer_iSup fun δ => le_normalizer_iSup fun δ' => le_normalizer_iSup fun hδ => ?_
  rw [← hδ.2]
  exact hN δ δ' hδ.1

theorem commutator_zm_eq_bot (h : Hyp20 X) (hb : 2 < critDist X) {γ γ' : Vtx X}
    (hγ : IsMVtx X γ) (hγ' : IsMVtx X γ') (hd : X.treeGraph.dist γ γ' ≤ 2) :
    ⁅ZM X γ, ZM X γ'⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (zm_le_qv_of_dist_lt X (γ := γ') hγ (by omega)).trans ?_
  rw [Subgroup.le_centralizer_iff]
  exact zm_le_centralizer_qv X h hγ'

theorem exists_zv_le_zm {α ρ : Vtx X} (hα : IsMVtx X α) (hd : X.treeGraph.dist α ρ ≤ 2) :
    ∃ γ, IsMVtx X γ ∧ X.treeGraph.dist α γ ≤ 2 ∧ Zv X ρ ≤ ZM X γ := by
  by_cases hρ : IsMVtx X ρ
  · exact ⟨ρ, hρ, hd, (zv_of_isMVtx X hρ).le⟩
  · refine ⟨α, hα, by simp, ?_⟩
    rw [zv_of_not_isMVtx X hρ]
    have hodd : ¬ Even (X.treeGraph.dist α ρ) := by
      rw [even_dist_iff]
      tauto
    have h1 : X.treeGraph.dist α ρ = 1 := by
      have h0 : X.treeGraph.dist α ρ ≠ 0 := fun h0 => hodd (h0 ▸ Even.zero)
      have h2 : X.treeGraph.dist α ρ ≠ 2 := fun h2 => hodd (h2 ▸ even_two)
      omega
    exact zh_le_zm X (dist_eq_one_iff_adj.mp h1)

theorem commutator_zm_le_nA (h : Hyp20 X) (hb : critDist X = 4) {α γ γ' : Vtx X}
    (hγ : IsMVtx X γ) (hγ' : IsMVtx X γ') (hd : X.treeGraph.dist α γ ≤ 2)
    (hd' : X.treeGraph.dist α γ' ≤ 2) : ⁅ZM X γ, ZM X γ'⁆ ≤ nA X α := by
  have htri : X.treeGraph.dist γ γ' ≤ X.treeGraph.dist γ α + X.treeGraph.dist α γ' :=
    dist_triangle X γ α γ'
  rw [tdist_comm X γ α] at htri
  by_cases h2 : X.treeGraph.dist γ γ' ≤ 2
  · rw [commutator_zm_eq_bot X h (by omega) hγ hγ' h2]
    exact bot_le
  have hev : Even (X.treeGraph.dist γ γ') := (even_dist_iff X γ γ').mpr ⟨fun _ => hγ', fun _ => hγ⟩
  have h4 : X.treeGraph.dist γ γ' = 4 := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hgeo : geo X γ γ' 2 = α := by
    refine (eq_geo_of_dist X (x := α) (i := 2) ?_ ?_).symm
    · rw [tdist_comm]
      omega
    · rw [h4, tdist_comm X γ α]
      omega
  by_cases hZ : ZM X γ ≤ Qv X γ'
  · have : ⁅ZM X γ, ZM X γ'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      refine hZ.trans ?_
      rw [Subgroup.le_centralizer_iff]
      exact zm_le_centralizer_qv X h hγ'
    rw [this]
    exact bot_le
  · have hc : IsCritical X γ γ' := ⟨hγ, by rw [h4, hb], hZ⟩
    have hb0 : 0 < critDist X := by omega
    rw [← hgeo]
    exact (Subgroup.commutator_mono (zm_le_xm X h hb0 hγ) (zm_le_xm X h hb0 hγ')).trans
      (commutator_xm_le_nA X hc)

theorem commutator_xm_le_left (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {δ δ' : Vtx X} (hc : IsCritical X δ δ') : ⁅XM X δ, XM X δ'⁆ ≤ XM X δ := by
  rw [Subgroup.commutator_comm]
  exact commutator_xm_le_right X h hb hC (ms22_iii X h hb hC hc)

theorem commutator_xm_le_xm_smul (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    (hN : StarNorm X) {δ δ' : Vtx X} (hc : IsCritical X δ δ') {g : X.Universal}
    (hg : g ∈ stab X (geo X δ δ' 2)) : ⁅XM X δ, XM X δ'⁆ ≤ XM X (g • δ) := by
  rw [← map_conj_eq_of_mem_normalizer (hN δ δ' hc hg), xm_smul]
  exact Subgroup.map_mono (commutator_xm_le_left X h hb hC hc)

theorem exists_stab_dist_le_two (hb : critDist X = 4) {δ δ' γ : Vtx X} (hc : IsCritical X δ δ')
    (hγ : X.treeGraph.dist (geo X δ δ' 2) γ ≤ 2) (hγM : IsMVtx X γ) :
    ∃ g ∈ stab X (geo X δ δ' 2), X.treeGraph.dist (g • δ) γ ≤ 2 := by
  set α := geo X δ δ' 2
  have hd : X.treeGraph.dist δ δ' = 4 := hc.2.1.trans hb
  have hδα : X.treeGraph.dist α δ = 2 := by
    rw [tdist_comm]
    exact dist_geo X (by omega)
  by_cases hγα : γ = α
  · refine ⟨1, (stab X α).one_mem, ?_⟩
    rw [one_smul, hγα, tdist_comm, hδα]
  have hαM : IsMVtx X α := by
    have := (even_dist_iff X α δ).mp (by rw [hδα]; exact even_two)
    exact this.mpr hc.1
  have hγ2 : X.treeGraph.dist α γ = 2 := by
    have hev : Even (X.treeGraph.dist α γ) :=
      (even_dist_iff X α γ).mpr ⟨fun _ => hγM, fun _ => hαM⟩
    have h0 : X.treeGraph.dist α γ ≠ 0 := fun h0 => hγα ((dist_eq_zero_iff X).mp h0).symm
    obtain ⟨k, hk⟩ := hev
    omega
  set σ := geo X α δ 1
  set σ' := geo X α γ 1
  have hσ : X.treeGraph.Adj α σ := adj_geo_one X (by omega)
  have hσ' : X.treeGraph.Adj α σ' := adj_geo_one X (by omega)
  have hσδ : X.treeGraph.dist σ δ = 1 := by
    rw [dist_geo_right X (by omega), hδα]
  have hσ'γ : X.treeGraph.dist σ' γ = 1 := by
    rw [dist_geo_right X (by omega), hγ2]
  obtain ⟨g, hg, hgσ⟩ := exists_mem_stab_smul X hσ hσ'
  refine ⟨g, hg, ?_⟩
  have htri := dist_triangle X (g • δ) σ' γ
  have h1 : X.treeGraph.dist (g • δ) σ' = 1 := by
    rw [← hgσ, dist_smul, tdist_comm, hσδ]
  omega

theorem zm_le_centralizer_nA (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hN : StarNorm X) {α γ : Vtx X} (hγ : IsMVtx X γ) (hd : X.treeGraph.dist α γ ≤ 2) :
    ZM X γ ≤ Subgroup.centralizer (nA X α : Set X.Universal) := by
  rw [Subgroup.le_centralizer_iff]
  refine iSup_le fun δ => iSup_le fun δ' => iSup_le fun hδ => ?_
  obtain ⟨hc, hαδ⟩ := hδ
  rw [← hαδ] at hd
  obtain ⟨g, hg, hgd⟩ := exists_stab_dist_le_two X hb hc hd hγ
  refine (commutator_xm_le_xm_smul X h (by omega) hC hN hc hg).trans ?_
  rw [Subgroup.le_centralizer_iff]
  refine (zm_le_qv_of_dist_lt X (γ := g • δ) hγ (by rw [tdist_comm]; omega)).trans ?_
  exact qv_le_centralizer_xm X _

theorem vv_eq_iSup (α : Vtx X) :
    Vv X α = ⨆ ρ : {ρ : Vtx X // X.treeGraph.dist α ρ ≤ 2}, Zv X ρ.1 := by
  rw [Vv, Vi, iSup_subtype']
  rfl

theorem vv_le_qv (hb : 2 < critDist X) {α : Vtx X} (hα : IsMVtx X α) : Vv X α ≤ Qv X α := by
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hα hρ
  exact hle.trans (zm_le_qv_of_dist_lt X hγ (by rw [tdist_comm]; omega))

theorem commutator_vv_le_nA (h : Hyp20 X) (hb : critDist X = 4) (hN : StarNorm X) {α : Vtx X}
    (hα : IsMVtx X α) : ⁅Vv X α, Vv X α⁆ ≤ nA X α := by
  rw [vv_eq_iSup]
  refine commutator_iSup_le _ (fun ρ => ?_) (fun ρ ρ' => ?_)
  · obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hα ρ.2
    exact hle.trans ((zm_le_qv_of_dist_lt X hγ (by rw [tdist_comm]; omega)).trans
      ((qv_le_stab X α).trans (stab_le_normalizer_nA X hN α)))
  · obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hα ρ.2
    obtain ⟨γ', hγ', hdγ', hle'⟩ := exists_zv_le_zm X hα ρ'.2
    exact (Subgroup.commutator_mono hle hle').trans (commutator_zm_le_nA X h hb hγ hγ' hdγ hdγ')

theorem nA_le_centralizer_vv (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hN : StarNorm X) {α : Vtx X} (hα : IsMVtx X α) :
    nA X α ≤ Subgroup.centralizer (Vv X α : Set X.Universal) := by
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hα hρ
  exact hle.trans (zm_le_centralizer_nA X h hb hC hN hγ hdγ)

theorem commutator_vv_le_centralizer (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hN : StarNorm X) {α : Vtx X} (hα : IsMVtx X α) :
    ⁅Vv X α, Vv X α⁆ ≤ Subgroup.centralizer (Vv X α : Set X.Universal) :=
  (commutator_vv_le_nA X h hb hN hα).trans (nA_le_centralizer_vv X h hb hC hN hα)

theorem commutator_vi_one_eq_bot (h : Hyp20 X) (hb : 2 < critDist X) (β : Vtx X) :
    ⁅Vi X β 1, Vi X β 1⁆ = ⊥ := by
  have key : ∀ ρ, X.treeGraph.dist β ρ ≤ 1 →
      ∃ γ, IsMVtx X γ ∧ X.treeGraph.dist β γ ≤ 1 ∧ Zv X ρ ≤ ZM X γ := by
    intro ρ hρ
    by_cases hρM : IsMVtx X ρ
    · exact ⟨ρ, hρM, hρ, (zv_of_isMVtx X hρM).le⟩
    · rw [zv_of_not_isMVtx X hρM]
      obtain ⟨σ, hσ⟩ := exists_adj X ρ
      have hσM : IsMVtx X σ := by
        have := isMVtx_iff_of_adj X hσ
        tauto
      rcases (dist_le_one_iff X).mp hρ with rfl | hβρ
      · exact ⟨σ, hσM, by rw [dist_eq_one_of_adj X hσ], zh_le_zm X hσ.symm⟩
      · have hβM : IsMVtx X β := by
          have := isMVtx_iff_of_adj X hβρ
          tauto
        exact ⟨β, hβM, by simp, zh_le_zm X hβρ⟩
  rw [eq_bot_iff, Vi, iSup_subtype']
  refine commutator_iSup_le _ (fun _ => ?_) (fun ρ ρ' => ?_)
  · rw [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_bot)]
    exact le_top
  · obtain ⟨γ, hγ, hdγ, hle⟩ := key ρ.1 ρ.2
    obtain ⟨γ', hγ', hdγ', hle'⟩ := key ρ'.1 ρ'.2
    have hd : X.treeGraph.dist γ γ' ≤ 2 := by
      have := dist_triangle X γ β γ'
      rw [tdist_comm X γ β] at this
      omega
    rw [← commutator_zm_eq_bot X h hb hγ hγ' hd]
    exact Subgroup.commutator_mono hle hle'

theorem zm_le_vv {α γ : Vtx X} (hγ : IsMVtx X γ) (hd : X.treeGraph.dist α γ ≤ 2) :
    ZM X γ ≤ Vv X α :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}) => Zv X ρ) γ hd
    (zv_of_isMVtx X hγ).ge

theorem vi_one_le_vv {α β : Vtx X} (hαβ : X.treeGraph.Adj α β) : Vi X β 1 ≤ Vv X α := by
  refine iSup₂_le fun ρ hρ => ?_
  refine le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}) => Zv X ρ)
    ρ ?_ le_rfl
  have := dist_triangle X α β ρ
  rw [dist_eq_one_of_adj X hαβ] at this
  exact this.trans (by simp only [Set.mem_ofPred_eq] at hρ; omega)

theorem commutator_vv_ne_bot (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    {α α' : Vtx X} (hc : IsCritical X α α') (hV : ¬ Vv X α ≤ Qv X (geo X α α' 2)) :
    ⁅Vv X α, Vv X α⁆ ≠ ⊥ := by
  set μ := geo X α α' 2
  have hd : X.treeGraph.dist α α' = 4 := hc.2.1.trans hb
  have hαμ : X.treeGraph.dist α μ = 2 := dist_geo X (by omega)
  have hμ : IsMVtx X μ := isMVtx_geo_two X h (by omega) hc
  have hex : ∃ ρ, X.treeGraph.dist α ρ ≤ 2 ∧ ¬ Zv X ρ ≤ Qv X μ := by
    by_contra hcon
    push Not at hcon
    exact hV (iSup₂_le fun ρ hρ => hcon ρ hρ)
  obtain ⟨ρ, hρ, hρμ⟩ := hex
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hc.1 hρ
  have hγμ : ¬ ZM X γ ≤ Qv X μ := fun h' => hρμ (hle.trans h')
  have hdγμ : X.treeGraph.dist γ μ = 4 := by
    have h1 : 4 ≤ X.treeGraph.dist γ μ := by
      by_contra hlt
      exact hγμ (zm_le_qv_of_dist_lt X hγ (by omega))
    have h2 := dist_triangle X γ α μ
    rw [tdist_comm X γ α] at h2
    omega
  have hcγ : IsCritical X γ μ := ⟨hγ, by rw [hdγμ, hb], hγμ⟩
  have hne := ms22_ii X h (by omega) hC hcγ
  intro hbot
  apply hne
  rw [eq_bot_iff, ← hbot]
  exact Subgroup.commutator_mono (zm_le_vv X hγ hdγ) (zm_le_vv X hμ (by omega))

theorem vv_le_of_vi_le {α β : Vtx X} (hαβ : X.treeGraph.Adj α β) {K : Subgroup X.Universal}
    (hK : stab X α ≤ Subgroup.normalizer (K : Set X.Universal)) (hβ : Vi X β 1 ≤ K) :
    Vv X α ≤ K := by
  have hσ : ∀ σ, X.treeGraph.Adj α σ → Vi X σ 1 ≤ K := by
    intro σ hσ
    obtain ⟨g, hg, rfl⟩ := exists_mem_stab_smul X hαβ hσ
    rw [vi_smul, ← map_conj_eq_of_mem_normalizer (hK hg)]
    exact Subgroup.map_mono hβ
  refine iSup₂_le fun ρ hρ => ?_
  have hex : ∃ σ, X.treeGraph.Adj α σ ∧ X.treeGraph.dist σ ρ ≤ 1 := by
    simp only [Set.mem_ofPred_eq] at hρ
    rcases Nat.lt_or_ge (X.treeGraph.dist α ρ) 1 with h0 | h1
    · have : ρ = α := ((dist_eq_zero_iff X).mp (by omega)).symm
      exact ⟨β, hαβ, by rw [this, tdist_comm, dist_eq_one_of_adj X hαβ]⟩
    · refine ⟨geo X α ρ 1, adj_geo_one X (by omega), ?_⟩
      rw [dist_geo_right X (by omega)]
      omega
  obtain ⟨σ, hσα, hσρ⟩ := hex
  exact (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist σ ρ ≤ 1}) => Zv X ρ)
    ρ hσρ le_rfl).trans (hσ σ hσα)

@[expose] def StarCent (Lt : Vtx X → Subgroup X.Universal) : Prop :=
  ∀ δ δ' : Vtx X, IsCritical X δ δ' →
    Lt (geo X δ δ' 2) ≤ Subgroup.centralizer
      ((⁅XM X δ, XM X δ'⁆ : Subgroup X.Universal) : Set X.Universal)

theorem nA_le_centralizer_lt {Lt : Vtx X → Subgroup X.Universal} (hL : StarCent X Lt)
    (α : Vtx X) : nA X α ≤ Subgroup.centralizer (Lt α : Set X.Universal) := by
  refine iSup_le fun δ => iSup_le fun δ' => iSup_le fun hδ => ?_
  rw [Subgroup.le_centralizer_iff, ← hδ.2]
  exact hL δ δ' hδ.1

theorem commutator_vv_eq_bot_of_le (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hN : StarNorm X) {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    {Lt : Subgroup X.Universal} (hLt : stab X α = Lt ⊔ Qv X β)
    (hLC : Lt ≤ Subgroup.centralizer ((⁅Vv X α, Vv X α⁆ : Subgroup X.Universal) :
      Set X.Universal))
    (hcomm : ⁅⁅Vv X α, Lt⁆, Vv X α⁆ ≤ ⁅⁅Vv X α, Vv X α⁆, Qv X β⁆) :
    ⁅Vv X α, Vv X α⁆ = ⊥ := by
  set V := Vv X α with hVdef
  set C := ⁅V, V⁆ with hCdef
  set C₁ := ⁅C, Qv X β⁆ with hC₁def
  have hβ : ¬ IsMVtx X β := (isMVtx_iff_of_adj X hαβ).mp hα
  have hVα : V ≤ Qv X α := vv_le_qv X (by omega) hα
  have hVs : stab X α ≤ Subgroup.normalizer (V : Set X.Universal) :=
    stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ 2) (fun g ρ => vi_smul X g ρ 2) α
  have hCs : stab X α ≤ Subgroup.normalizer (C : Set X.Universal) :=
    le_normalizer_commutator' hVs hVs
  have hTα : Qv X β ≤ stab X α := qv_le_stab_of_adj X hαβ.symm
  have hCZ : C ≤ Subgroup.centralizer (V : Set X.Universal) :=
    commutator_vv_le_centralizer X h hb hC hN hα
  have hC₁C : C₁ ≤ C := Subgroup.le_normalizer_iff_commutator_le_left.mp (hTα.trans hCs)
  have hC₁eq : C₁ = ⁅C, stab X α⁆ := by
    rw [hLt, sup_comm, commutator_sup_eq_of_le_centralizer (hTα.trans hCs)]
    rw [← Subgroup.le_centralizer_iff] at hLC
    exact fun x hx => Subgroup.le_centralizer_iff.mp hLC hx
  have hC₁s : stab X α ≤ Subgroup.normalizer (C₁ : Set X.Universal) := by
    rw [hC₁eq]
    exact le_normalizer_commutator' hCs Subgroup.le_normalizer
  have hcen : ∀ c ∈ C₁, ∀ v ∈ V, v * c * v⁻¹ = c := by
    intro c hc v hv
    have := Subgroup.mem_centralizer_iff.mp (hCZ (hC₁C hc)) v hv
    rw [this, mul_inv_cancel_right]
  let Zh : Subgroup X.Universal :=
    { carrier := {v | v ∈ V ∧ ∀ w ∈ V, ⁅v, w⁆ ∈ C₁}
      one_mem' := ⟨V.one_mem, fun w _ => by simp [C₁.one_mem]⟩
      mul_mem' := by
        rintro v₁ v₂ ⟨hv₁, h₁⟩ ⟨hv₂, h₂⟩
        refine ⟨V.mul_mem hv₁ hv₂, fun w hw => ?_⟩
        have e : ⁅v₁ * v₂, w⁆ = (v₁ * ⁅v₂, w⁆ * v₁⁻¹) * ⁅v₁, w⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcen _ (h₂ w hw) v₁ hv₁]
        exact C₁.mul_mem (h₂ w hw) (h₁ w hw)
      inv_mem' := by
        rintro v ⟨hv, h₁⟩
        refine ⟨V.inv_mem hv, fun w hw => ?_⟩
        have e : ⁅v⁻¹, w⁆ = v⁻¹ * ⁅v, w⁆⁻¹ * v⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcen _ (C₁.inv_mem (h₁ w hw)) v⁻¹ (V.inv_mem hv)]
        exact C₁.inv_mem (h₁ w hw) }
  have hZhV : Zh ≤ V := fun v hv => hv.1
  have hZhs : stab X α ≤ Subgroup.normalizer (Zh : Set X.Universal) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rintro _ ⟨v, ⟨hv, hv'⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hVs hg) v).mp hv, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVs (inv_mem hg)) w).mp hw
    have e : ⁅g * v * g⁻¹, w⁆ = g * ⁅v, g⁻¹ * w * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    show ⁅g * v * g⁻¹, w⁆ ∈ C₁
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hC₁s hg) _).mp (hv' _ hw')
  set K := Vi X β 1 ⊔ Zh with hKdef
  have hVβV : Vi X β 1 ≤ V := vi_one_le_vv X hαβ
  have hKV : K ≤ V := sup_le hVβV hZhV
  have hLs : Lt ≤ stab X α := le_sup_left.trans hLt.ge
  have hKs : stab X α ≤ Subgroup.normalizer (K : Set X.Universal) := by
    rw [hLt]
    refine sup_le ?_ ?_
    · refine le_normalizer_of_map_conj_le fun l hl => ?_
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hZhs (hLs hl))]
      refine sup_le ?_ le_sup_right
      rintro _ ⟨v, hv, rfl⟩
      have hlv : ⁅l, v⁆ ∈ Zh := by
        have hvV := hVβV hv
        have h1 : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hVs (hLs hl)) v).mp hvV
        refine ⟨?_, fun w hw => ?_⟩
        · rw [commutatorElement_def]
          exact V.mul_mem h1 (V.inv_mem hvV)
        · have h2 : ⁅l, v⁆ ∈ ⁅V, Lt⁆ := by
            rw [← commutatorElement_inv]
            exact inv_mem (Subgroup.commutator_mem_commutator hvV hl)
          exact hcomm (Subgroup.commutator_mem_commutator h2 hw)
      have e : (MulAut.conj l).toMonoidHom v = ⁅l, v⁆ * v := by
        simp [commutatorElement_def]
      rw [e]
      exact K.mul_mem (Subgroup.mem_sup_right hlv) (Subgroup.mem_sup_left hv)
    · refine le_normalizer_sup ?_ (hTα.trans hZhs)
      exact (qv_le_stab X β).trans (stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ 1)
        (fun g ρ => vi_smul X g ρ 1) β)
  have hVK : V ≤ K := vv_le_of_vi_le X hαβ hKs le_sup_left
  have hKK : ⁅K, K⁆ ≤ C₁ := by
    have hcl : K = Subgroup.closure ((Vi X β 1 : Set X.Universal) ∪ Zh) := by
      rw [hKdef, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hKn : Subgroup.closure ((Vi X β 1 : Set X.Universal) ∪ Zh) ≤
        Subgroup.normalizer (C₁ : Set X.Universal) := by
      rw [← hcl]
      exact (hKV.trans (hVα.trans (qv_le_stab X α))).trans hC₁s
    have hVβ := commutator_vi_one_eq_bot X h (by omega) β
    rw [hcl]
    refine commutator_closure_le hKn hKn fun x hx y hy => ?_
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · have : ⁅x, y⁆ ∈ ⁅Vi X β 1, Vi X β 1⁆ := Subgroup.commutator_mem_commutator hx hy
        rw [hVβ, Subgroup.mem_bot] at this
        rw [this]
        exact C₁.one_mem
      · rw [← commutatorElement_inv]
        exact inv_mem (hy.2 x (hVβV hx))
    · have hyK : y ∈ K := by
        rcases hy with hy | hy
        · exact Subgroup.mem_sup_left hy
        · exact Subgroup.mem_sup_right hy
      exact hx.2 y (hKV hyK)
  have hCC₁ : C ≤ ⊥ ⊔ ⁅C, Qv X β⁆ := by
    rw [bot_sup_eq]
    exact (Subgroup.commutator_mono hVK hVK).trans hKK
  have hCβ : C ≤ Qv X β :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer).trans
      (hVα.trans (qv_le_qv X h hα hαβ))
  have hbotN : Qv X β ≤ Subgroup.normalizer ((⊥ : Subgroup X.Universal) : Set X.Universal) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
    exact le_top
  exact eq_of_le_sup_commutator (isNilpotent_qv X h hβ) bot_le hCβ le_rfl hbotN bot_le hCC₁

end Amalgam

end CFSG.Quasithin.MS93.S38E
