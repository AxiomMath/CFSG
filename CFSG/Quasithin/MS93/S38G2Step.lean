module

public import CFSG.Quasithin.MS93.S38G2Hyp
public import CFSG.Quasithin.MS93.S38EBase
public import CFSG.Quasithin.MS93.S38G2Codim

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 SimpleGraph
open scoped commutatorElement

section GroupTheory

variable {Γ : Type*} [Group Γ]

theorem relIndex_sup_of_le_normalizer' {H K : Subgroup Γ}
    (hH : H ≤ Subgroup.normalizer (K : Set Γ)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  set P := Subgroup.normalizer (K : Set Γ)
  have hK : K ≤ P := Subgroup.le_normalizer
  have : (K.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  rw [← Subgroup.relIndex_subgroupOf (sup_le hH hK), ← Subgroup.relIndex_subgroupOf hH,
    Subgroup.subgroupOf_sup hH hK, Subgroup.relIndex_sup_right]

theorem le_normalizer_cRel {S A N : Subgroup Γ} (hA : S ≤ Subgroup.normalizer (A : Set Γ))
    (hN : S ≤ Subgroup.normalizer (N : Set Γ)) :
    S ≤ Subgroup.normalizer (cRel A N : Set Γ) := by
  refine le_normalizer_of_conj fun g hg x hx => ?_
  obtain ⟨hxN, hx'⟩ := hx
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hN hg) hxN) (Subgroup.inv_mem _ (hN hg)),
    fun a ha => ?_⟩
  have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hA (S.inv_mem hg)) a).mp ha
  have e : ⁅g * x * g⁻¹, a⁆ = g * ⁅x, g⁻¹ * a * g⁻¹⁻¹⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hN hg) _).mp (hx' _ ha')

theorem cRel_map_conj {A N : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (N : Set Γ)) :
    cRel (A.map (MulAut.conj g).toMonoidHom) N = (cRel A N).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj, mem_cRel, mem_cRel]
  have hg' : g⁻¹ ∈ Subgroup.normalizer (N : Set Γ) := Subgroup.inv_mem _ hg
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg' hxN) hg, fun a ha => ?_⟩
    have h1 := hx _ ⟨a, ha, rfl⟩
    have e : ⁅g⁻¹ * x * g, a⁆ =
        g⁻¹ * ⁅x, (MulAut.conj g).toMonoidHom a⁆ * g⁻¹⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hg' _).mp h1
  · rintro ⟨hxN, hx⟩
    have hxN' : x ∈ Subgroup.normalizer (N : Set Γ) := by
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxN) hg'
      simpa [mul_assoc] using this
    refine ⟨hxN', fun a' ha' => ?_⟩
    obtain ⟨a, ha, rfl⟩ := ha'
    have h1 := hx a ha
    have e : ⁅x, (MulAut.conj g).toMonoidHom a⁆ = g * ⁅g⁻¹ * x * g, a⁆ * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp h1

theorem relIndex_cRel_map_conj {A N H : Subgroup Γ} {g : Γ}
    (hgN : g ∈ Subgroup.normalizer (N : Set Γ)) (hgH : g ∈ Subgroup.normalizer (H : Set Γ)) :
    (cRel (A.map (MulAut.conj g).toMonoidHom) N).relIndex H = (cRel A N).relIndex H := by
  rw [cRel_map_conj hgN]
  conv_lhs => rw [← map_conj_eq_of_mem_normalizer hgH]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem relIndex_inf_of_le {X V H : Subgroup Γ} (hHV : H ≤ V) :
    (X ⊓ V).relIndex H = X.relIndex H := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hHV x.2⟩⟩

theorem relIndex_cRel_mul_le {A N H V : Subgroup Γ} [Finite ↥V] (hNH : N ≤ H) (hHV : H ≤ V)
    (hVH : V ≤ Subgroup.normalizer (H : Set Γ)) (hAH : A ≤ Subgroup.normalizer (H : Set Γ)) :
    (cRel A H).relIndex V * (cRel A N).relIndex H ≤ (cRel A N).relIndex V := by
  set C₀ := cRel A N ⊓ V
  set C₁ := cRel A H ⊓ V
  have hC₀₁ : C₀ ≤ C₁ := by
    rintro g ⟨⟨_, hg⟩, hgV⟩
    exact ⟨⟨hVH hgV, fun a ha => hNH (hg a ha)⟩, hgV⟩
  have hHC₁ : H ≤ C₁ := by
    intro h hh
    refine ⟨⟨hVH (hHV hh), fun a ha => ?_⟩, hHV hh⟩
    have e : ⁅h, a⁆ = h * (a * h⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem hh ((Subgroup.mem_normalizer_iff.mp (hAH ha) _).mp (H.inv_mem hh))
  have hC₁V : C₁ ≤ V := inf_le_right
  have hfin : Finite ↥C₁ := Finite.of_injective _ (Subgroup.inclusion_injective hC₁V)
  have h0 : C₀.relIndex C₁ ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_mul_relIndex C₀ C₁ V hC₀₁ hC₁V
  have h2 : C₀.relIndex H ≤ C₀.relIndex C₁ := Subgroup.relIndex_le_of_le_right hHC₁ h0
  rw [relIndex_inf_of_le hHV] at h2
  have h3 : C₁.relIndex V = (cRel A H).relIndex V := Subgroup.inf_relIndex_right _ _
  have h4 : C₀.relIndex V = (cRel A N).relIndex V := Subgroup.inf_relIndex_right _ _
  rw [← h3, ← h4, ← h1, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem exists_relIndex_eq_two_pow {V : Subgroup Γ} [Finite ↥V] (hV : IsPGroup 2 ↥V)
    (X : Subgroup Γ) : ∃ k : ℕ, X.relIndex V = 2 ^ k := by
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have h := Subgroup.index_dvd_card (X.subgroupOf V)
  rw [hn] at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨k, hk⟩

theorem le_two_or_le_two {a b : ℕ} (ha : ∃ k, a = 2 ^ k) (hb : ∃ k, b = 2 ^ k)
    (hab : a * b ≤ 8) : a ≤ 2 ∨ b ≤ 2 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [← pow_add] at hab
  have : i + j ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ≤ 2 ^ (i + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.lt_or_ge i 2 with hi | hi
  · left
    calc 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := rfl
  · right
    calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := rfl

theorem exists_mul_of_mem_sup {H N : Subgroup Γ} (hHN : H ≤ Subgroup.normalizer (N : Set Γ))
    {x : Γ} (hx : x ∈ H ⊔ N) : ∃ a ∈ H, ∃ b ∈ N, a * b = x := by
  have hx' : x ∈ ((H ⊔ N : Subgroup Γ) : Set Γ) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H N hHN] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab⟩

theorem le_normalizer_inf' {S A B : Subgroup Γ} (hA : S ≤ Subgroup.normalizer (A : Set Γ))
    (hB : S ≤ Subgroup.normalizer (B : Set Γ)) :
    S ≤ Subgroup.normalizer ((A ⊓ B : Subgroup Γ) : Set Γ) :=
  le_normalizer_of_conj fun _ hg x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hA hg) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hB hg) x).mp hx.2⟩

theorem le_normalizer_centralizer' {S C : Subgroup Γ} (hC : S ≤ Subgroup.normalizer (C : Set Γ)) :
    S ≤ Subgroup.normalizer (Subgroup.centralizer (C : Set Γ) : Set Γ) := by
  refine le_normalizer_of_conj fun g hg x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hc' : g⁻¹ * c * g⁻¹⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hC (S.inv_mem hg)) c).mp hc
  have h1 := Subgroup.mem_centralizer_iff.mp hx _ hc'
  calc c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * c * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * c := by group

theorem conj_mem_of_commutator_mem {K : Subgroup Γ} {x l : Γ} (hx : x ∈ K) (hxl : ⁅x, l⁆ ∈ K) :
    l * x * l⁻¹ ∈ K := by
  have e : l * x * l⁻¹ = ⁅x, l⁆⁻¹ * x := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact K.mul_mem (K.inv_mem hxl) hx

end GroupTheory

section Amalgam

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}
  {Lt Ut Wt : Vtx X → Subgroup X.Universal}

theorem zv_le_vi' {δ ρ : Vtx X} {i : ℕ} (hd : X.treeGraph.dist δ ρ ≤ i) : Zv X ρ ≤ Vi X δ i :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist δ ρ ≤ i}) => Zv X ρ) ρ hd
    le_rfl

theorem stab_le_normalizer_vi (δ : Vtx X) (i : ℕ) :
    stab X δ ≤ Subgroup.normalizer (Vi X δ i : Set X.Universal) :=
  stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ i) (fun g ρ => vi_smul X g ρ i) δ

namespace G2Hyp

variable (hG : G2Hyp X Lt Ut Wt)
include hG

theorem critDist_pos : 0 < critDist X := by rw [hG.b4]; norm_num

theorem dist_crit {α α' : Vtx X} (hc : IsCritical X α α') : X.treeGraph.dist α α' = 4 :=
  hc.2.1.trans hG.b4

theorem adj_one {α α' : Vtx X} (hc : IsCritical X α α') :
    X.treeGraph.Adj α (geo X α α' 1) :=
  adj_geo_one_of_isCritical X hG.critDist_pos hc

theorem adj_one_two {α α' : Vtx X} (hc : IsCritical X α α') :
    X.treeGraph.Adj (geo X α α' 1) (geo X α α' 2) :=
  adj_geo X (by rw [hG.dist_crit hc]; norm_num)

theorem adj_two_three {α α' : Vtx X} (hc : IsCritical X α α') :
    X.treeGraph.Adj (geo X α α' 2) (geo X α α' 3) :=
  adj_geo X (by rw [hG.dist_crit hc]; norm_num)

theorem dist_two {α α' : Vtx X} (hc : IsCritical X α α') :
    X.treeGraph.dist α (geo X α α' 2) = 2 :=
  dist_geo X (by rw [hG.dist_crit hc]; norm_num)

theorem dist_two_right {α α' : Vtx X} (hc : IsCritical X α α') :
    X.treeGraph.dist (geo X α α' 2) α' = 2 := by
  rw [dist_geo_right X (by rw [hG.dist_crit hc]; norm_num), hG.dist_crit hc]

theorem isMVtx_two {α α' : Vtx X} (hc : IsCritical X α α') : IsMVtx X (geo X α α' 2) :=
  isMVtx_geo_two X hG.h20 hG.critDist_pos hc

theorem not_isMVtx_one {α α' : Vtx X} (hc : IsCritical X α α') : ¬ IsMVtx X (geo X α α' 1) :=
  (isMVtx_iff_of_adj X (hG.adj_one hc)).mp hc.1

theorem geo_rev {α α' : Vtx X} (hc : IsCritical X α α') {i : ℕ} (hi : i ≤ 4) :
    geo X α' α i = geo X α α' (4 - i) := by
  have h := geo_symm X (u := α) (w := α') (i := 4 - i) (by rw [hG.dist_crit hc]; omega)
  rwa [hG.dist_crit hc, show 4 - (4 - i) = i by omega] at h

theorem critical_symm {α α' : Vtx X} (hc : IsCritical X α α') : IsCritical X α' α :=
  ms22_iii X hG.h20 hG.critDist_pos hG.cent hc

theorem zm_le_qv {γ δ : Vtx X} (hγ : IsMVtx X γ) (hd : X.treeGraph.dist γ δ ≤ 3) :
    ZM X γ ≤ Qv X δ :=
  zm_le_qv_of_dist_lt X hγ (by rw [hG.b4]; omega)

theorem qv_finite {γ : Vtx X} (hγ : IsMVtx X γ) : Finite ↥(Qv X γ) := by
  have := hG.fin γ hγ
  exact Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab X γ))

theorem isPGroup_qv_m {γ ρ : Vtx X} (hγ : IsMVtx X γ) (hγρ : X.treeGraph.Adj γ ρ) :
    IsPGroup 2 ↥(Qv X γ) :=
  (isPGroup_qv X hG.h20 ((isMVtx_iff_of_adj X hγρ).mp hγ)).to_le (qv_le_qv X hG.h20 hγ hγρ)

theorem qv_finite_h {ρ : Vtx X} (hρ : ¬ IsMVtx X ρ) : Finite ↥(Qv X ρ) :=
  finite_qv X hG.h20 hρ

theorem commutator_zm_le_left {α α' : Vtx X} (hc : IsCritical X α α') :
    ⁅ZM X α, ZM X α'⁆ ≤ ZM X α :=
  commutator_le_self_of ((zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos hc).trans
    (stab_le_normalizer_zm X α))

theorem commutator_zm_le_right {α α' : Vtx X} (hc : IsCritical X α α') :
    ⁅ZM X α, ZM X α'⁆ ≤ ZM X α' := by
  rw [Subgroup.commutator_comm]
  exact commutator_le_self_of ((zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos
    (hG.critical_symm hc)).trans (stab_le_normalizer_zm X α'))

theorem commutator_qv_inf_le {α α' : Vtx X} (hc : IsCritical X α α') {y : X.Universal}
    (hy : y ∈ Qv X α ⊓ Qv X (geo X α α' 2)) {z : X.Universal} (hz : z ∈ ZM X α') :
    ⁅y, z⁆ ∈ ⁅ZM X α, ZM X α'⁆ := by
  have hc' := hG.critical_symm hc
  have hα' : IsMVtx X α' := hc.isMVtx_right X hG.h20
  have hlam : geo X α' α 1 = geo X α α' 3 := hG.geo_rev hc (by norm_num)
  have hylam : y ∈ Qv X (geo X α' α 1) := by
    rw [hlam]
    exact qv_le_qv X hG.h20 (hG.isMVtx_two hc) (hG.adj_two_three hc) hy.2
  have hcomm : ∀ a ∈ ZM X α, ⁅y, a⁆ ∈ Qv X α' := by
    intro a ha
    have : ⁅y, a⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv X hG.h20 hc.1 ha) y hy.1)
    rw [this]
    exact Subgroup.one_mem _
  have hy' := hG.off_cent α' α hc' y hylam hcomm
  have hd3 : X.treeGraph.dist α (geo X α' α 1) ≤ 3 := by
    rw [hlam, dist_geo X (by rw [hG.dist_crit hc]; norm_num)]
  have hZn : ZM X α ≤ Subgroup.normalizer (Qv X α' : Set X.Universal) :=
    (hG.zm_le_qv hc.1 hd3).trans ((qv_le_stab_of_isMVtx X hG.h20 hα'
      (hG.adj_one hc')).trans (stab_le_normalizer_qv X α'))
  obtain ⟨a, ha, q, hq, rfl⟩ := exists_mul_of_mem_sup hZn hy'
  have hqz : ⁅q, z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv X hG.h20 hα' hz) q hq)
  have e : ⁅a * q, z⁆ = (a * ⁅q, z⁆ * a⁻¹) * ⁅a, z⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, hqz, mul_one, mul_inv_cancel, one_mul]
  exact Subgroup.commutator_mem_commutator ha hz

theorem commutator_le_of_codim_at {α α' : Vtx X} (hc : IsCritical X α α')
    {H N : Subgroup X.Universal} (hHQ : H ≤ Qv X α) (hNH : N ≤ H)
    (hHn : stab X α ≤ Subgroup.normalizer (H : Set X.Universal))
    (hNn : stab X α ≤ Subgroup.normalizer (N : Set X.Universal))
    (hcod : (cRel (ZM X α') N).relIndex H ≤ 2) : ⁅H, Lt α⁆ ≤ N := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hgen⟩ := hG.two_gen α α' hc
  have : Finite ↥(Qv X α) := hG.qv_finite hc.1
  have hQ2 := hG.isPGroup_qv_m hc.1 (hG.adj_one hc)
  have hZs : ZM X α' ≤ stab X α := zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos hc
  have hAs : ∀ g ∈ stab X α, (ZM X α').map (MulAut.conj g).toMonoidHom ≤ stab X α := by
    rintro g hg _ ⟨z, hz, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hZs hz)) (Subgroup.inv_mem _ hg)
  have hQs := qv_le_stab X α
  have hQn := stab_le_normalizer_qv X α
  have hLs := hG.lt_le α hc.1
  refine commutator_le_of_codim hQ2 hHQ (hQs.trans hHn) (hLs.trans hHn) (hLs.trans hQn)
    ((hAs g₁ hg₁).trans hHn) ((hAs g₁ hg₁).trans hQn) ((hAs g₂ hg₂).trans hHn)
    ((hAs g₂ hg₂).trans hQn) (hG.lt_perf α hc.1) hgen N hNH (hQs.trans hNn) (hLs.trans hNn)
    ((hAs g₁ hg₁).trans hNn) ((hAs g₂ hg₂).trans hNn) ?_ ?_
  · rw [relIndex_cRel_map_conj (hNn hg₁) (hHn hg₁)]
    exact hcod
  · rw [relIndex_cRel_map_conj (hNn hg₂) (hHn hg₂)]
    exact hcod

theorem crit_of_not_le {α α' γ : Vtx X} (hc : IsCritical X α α') (hγ : IsMVtx X γ)
    (hdγ : X.treeGraph.dist α γ ≤ 2) (hγμ : ¬ ZM X γ ≤ Qv X (geo X α α' 2)) :
    IsCritical X (geo X α α' 2) γ ∧ geo X (geo X α α' 2) γ 1 = geo X α α' 1 ∧
      geo X (geo X α α' 2) γ 2 = α ∧ X.treeGraph.dist α γ = 2 := by
  set β := geo X α α' 1
  set μ := geo X α α' 2
  have hαμ : X.treeGraph.dist α μ = 2 := hG.dist_two hc
  have h1 : 4 ≤ X.treeGraph.dist γ μ := by
    by_contra hlt
    exact hγμ (hG.zm_le_qv hγ (by omega))
  have h2 := dist_triangle X γ α μ
  rw [tdist_comm X γ α] at h2
  have hdγμ : X.treeGraph.dist γ μ = 4 := by omega
  have hdαγ : X.treeGraph.dist α γ = 2 := by omega
  have hcγ : IsCritical X γ μ := ⟨hγ, by rw [hdγμ, hG.b4], hγμ⟩
  have hcμ := hG.critical_symm hcγ
  have hμα : X.treeGraph.dist μ α = 2 := by rw [tdist_comm X μ α]; exact hαμ
  have hμγ : X.treeGraph.dist μ γ = 4 := by rw [tdist_comm X μ γ]; exact hdγμ
  have hsum : X.treeGraph.dist μ α + X.treeGraph.dist α γ = X.treeGraph.dist μ γ := by
    rw [hμα, hdαγ, hμγ]
  have hα2 : α = geo X μ γ 2 := eq_geo_of_dist X hμα hsum
  have hβα : X.treeGraph.dist β α = 1 := by
    rw [tdist_comm X β α]
    exact dist_eq_one_of_adj X (hG.adj_one hc)
  have hβ1 : geo X μ γ 1 = β := by
    rw [← geo_geo X (i := 1) (j := 2) (by norm_num) (by rw [hμγ]; norm_num), ← hα2]
    symm
    apply eq_geo_one X (hG.adj_one_two hc).symm
    rw [hβα, hμα]
  exact ⟨hcμ, hβ1, hα2.symm, hdαγ⟩

theorem exists_crit_back {α α' : Vtx X} (hc : IsCritical X α α') :
    ∃ δ, IsCritical X (geo X α α' 2) δ ∧ geo X (geo X α α' 2) δ 1 = geo X α α' 1 ∧
      geo X (geo X α α' 2) δ 2 = α ∧ X.treeGraph.dist α δ = 2 := by
  have hVμ := hG.hV α α' hc
  rw [hG.geo_rev hc (by norm_num), show 4 - 2 = 2 from rfl] at hVμ
  obtain ⟨ρ, hρ, hρμ⟩ : ∃ ρ, X.treeGraph.dist α ρ ≤ 2 ∧ ¬ Zv X ρ ≤ Qv X (geo X α α' 2) := by
    by_contra hcon
    push Not at hcon
    exact hVμ (iSup₂_le fun ρ hρ => hcon ρ hρ)
  obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm X hc.1 hρ
  obtain ⟨h1, h2, h3, h4⟩ := hG.crit_of_not_le hc hγ hdγ fun h => hρμ (hle.trans h)
  exact ⟨γ, h1, h2, h3, h4⟩

theorem vi_one_le_qv {α α' : Vtx X} (hc : IsCritical X α α') :
    Vi X (geo X α α' 1) 1 ≤ Qv X (geo X α α' 2) := by
  refine iSup₂_le fun ρ hρ => ?_
  rcases (dist_le_one_iff X).mp hρ with rfl | hβρ
  · rw [zv_of_not_isMVtx X (hG.not_isMVtx_one hc)]
    exact (zh_le_zm X (hG.adj_one_two hc).symm).trans
      (zm_le_qv_self X (hG.isMVtx_two hc) hG.critDist_pos)
  · have hρM : IsMVtx X ρ := by
      have := isMVtx_iff_of_adj X hβρ
      have h1 := hG.not_isMVtx_one hc
      tauto
    rw [zv_of_isMVtx X hρM]
    refine hG.zm_le_qv hρM ?_
    have h := dist_triangle X ρ (geo X α α' 1) (geo X α α' 2)
    have h1 : X.treeGraph.dist ρ (geo X α α' 1) = 1 := by
      rw [tdist_comm X ρ]
      exact dist_eq_one_of_adj X hβρ
    have h2 := dist_eq_one_of_adj X (hG.adj_one_two hc)
    omega

theorem vv_le_offJoin {α α' : Vtx X} (hc : IsCritical X α α') :
    Vv X α ≤ offJoin X (geo X α α' 2) (geo X α α' 1) := by
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm X hc.1 hρ
  refine hle.trans ?_
  by_cases hγμ : ZM X γ ≤ Qv X (geo X α α' 2)
  · exact hγμ.trans le_sup_right
  · obtain ⟨h1, h2, -, -⟩ := hG.crit_of_not_le hc hγ hdγ hγμ
    exact le_sup_of_le_left (le_iSup₂_of_le (f := fun ε (_ : IsCritical X (geo X α α' 2) ε ∧
      geo X (geo X α α' 2) ε 1 = geo X α α' 1) => ZM X ε) γ ⟨h1, h2⟩ le_rfl)

theorem commutator_vv_le_qv {α α' : Vtx X} (hc : IsCritical X α α') :
    ⁅Vv X α, Vv X α⁆ ≤ Qv X (geo X α α' 2) := by
  set β := geo X α α' 1 with hβdef
  set μ := geo X α α' 2 with hμdef
  set V := Vv X α with hVdef
  have hμ := hG.isMVtx_two hc
  have hαβ : X.treeGraph.Adj α β := hG.adj_one hc
  have hμβ : X.treeGraph.Adj μ β := (hG.adj_one_two hc).symm
  have hVs : stab X α ≤ Subgroup.normalizer (V : Set X.Universal) := stab_le_normalizer_vi α 2
  have hVQ : V ≤ Qv X α := S38E.vv_le_qv X (by rw [hG.b4]; norm_num) hc.1
  have hV'n : stab X α ≤ Subgroup.normalizer ((⁅V, V⁆ : Subgroup X.Universal) : Set X.Universal) :=
    S38E.le_normalizer_commutator' hVs hVs
  have hZn : stab X α ≤ Subgroup.normalizer (ZM X α : Set X.Universal) := stab_le_normalizer_zm X α
  have hV'V : ⁅V, V⁆ ≤ V := commutator_le_self_of Subgroup.le_normalizer
  have hV'Q : ⁅V, V⁆ ≤ Qv X α := hV'V.trans hVQ
  have hZs : ZM X α' ≤ stab X α := zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos hc
  obtain ⟨D, -, hDβ, hDi, hDc⟩ := hG.comm_off μ β hμ hμβ
  have hVJ := hG.vv_le_offJoin hc
  have hV'D : ⁅V, V⁆ ≤ D :=
    Subgroup.commutator_le.mpr fun x hx y hy => hDc x (hVJ hx) y (hVJ hy)
  have : Finite ↥(Qv X β) := hG.qv_finite_h (hG.not_isMVtx_one hc)
  have hD0 : (Qv X μ).relIndex D ≠ 0 := by
    have : Finite ↥D := Finite.of_injective _ (Subgroup.inclusion_injective hDβ)
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hidx : (Qv X μ).relIndex ⁅V, V⁆ ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hV'D hD0).trans hDi
  set N := ⁅V, V⁆ ⊓ ZM X α with hNdef
  have hNn : stab X α ≤ Subgroup.normalizer (N : Set X.Universal) := le_normalizer_inf' hV'n hZn
  have hcod : (cRel (ZM X α') N).relIndex ⁅V, V⁆ ≤ 2 := by
    have hle : ⁅V, V⁆ ⊓ Qv X μ ≤ cRel (ZM X α') N := by
      rintro g ⟨hg, hgμ⟩
      have hgs : g ∈ stab X α := qv_le_stab X α (hV'Q hg)
      refine ⟨hNn hgs, fun z hz => ⟨?_, ?_⟩⟩
      · have e : ⁅g, z⁆ = g * (z * g⁻¹ * z⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ hg
          ((Subgroup.mem_normalizer_iff.mp (hV'n (hZs hz)) _).mp (Subgroup.inv_mem _ hg))
      · exact hG.commutator_zm_le_left hc (hG.commutator_qv_inf_le hc ⟨hV'Q hg, hgμ⟩ hz)
    have hfV : Finite ↥(⁅V, V⁆ : Subgroup X.Universal) := by
      have := hG.qv_finite hc.1
      exact Finite.of_injective _ (Subgroup.inclusion_injective hV'Q)
    have h0 : (⁅V, V⁆ ⊓ Qv X μ).relIndex ⁅V, V⁆ ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    calc (cRel (ZM X α') N).relIndex ⁅V, V⁆ ≤ (⁅V, V⁆ ⊓ Qv X μ).relIndex ⁅V, V⁆ :=
          Subgroup.relIndex_le_of_le_left hle h0
      _ = (Qv X μ).relIndex ⁅V, V⁆ := Subgroup.inf_relIndex_left _ _
      _ ≤ 2 := hidx
  have hcL : ⁅⁅V, V⁆, Lt α⁆ ≤ N :=
    hG.commutator_le_of_codim_at hc hV'Q inf_le_left hV'n hNn hcod
  set Vβ := Vi X β 1 with hVβdef
  set N₁ := ⁅V, Vβ⁆ ⊔ ZM X α with hN₁def
  have hVβV : Vβ ≤ V := S38E.vi_one_le_vv X hαβ
  have hZVβ : ZM X α ≤ Vβ := by
    rw [← zv_of_isMVtx X hc.1]
    refine zv_le_vi' ?_
    rw [tdist_comm X β α, dist_eq_one_of_adj X hαβ]
  have hTs : Qv X β ≤ stab X α := qv_le_stab_of_isMVtx X hG.h20 hc.1 hαβ
  have hTVβ : Qv X β ≤ Subgroup.normalizer (Vβ : Set X.Universal) :=
    (qv_le_stab X β).trans (stab_le_normalizer_vi β 1)
  have hLs := hG.lt_le α hc.1
  have hLcRel : ⁅V, V⁆ ⊔ ZM X α ≤ cRel (Lt α) (ZM X α) := by
    refine sup_le (fun g hg => ⟨hZn (qv_le_stab X α (hV'Q hg)), fun l hl =>
      (hcL (Subgroup.commutator_mem_commutator hg hl)).2⟩) (fun z hz => ⟨hZn (qv_le_stab X α
      ((zm_le_qv_self X hc.1 hG.critDist_pos) hz)), fun l hl => ?_⟩)
    have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ hz
      ((Subgroup.mem_normalizer_iff.mp (hZn (hLs hl)) _).mp (Subgroup.inv_mem _ hz))
  have hN₁le : N₁ ≤ ⁅V, V⁆ ⊔ ZM X α :=
    sup_le_sup_right (Subgroup.commutator_mono le_rfl hVβV) _
  have hN₁n : stab X α ≤ Subgroup.normalizer (N₁ : Set X.Universal) := by
    rw [hG.lt_sup α β hc.1 hαβ]
    refine sup_le ?_ ?_
    · exact le_normalizer_of_conj fun l hl x hx => conj_mem_of_commutator_mem hx
        (Subgroup.mem_sup_right ((hLcRel (hN₁le hx)).2 l hl))
    · exact le_normalizer_sup (S38E.le_normalizer_commutator' (hTs.trans hVs) hTVβ)
        (hTs.trans hZn)
  have hK : V ≤ cRel V N₁ ⊓ V := by
    refine S38E.vv_le_of_vi_le X hαβ (le_normalizer_inf' (le_normalizer_cRel hVs hN₁n) hVs) ?_
    intro b hb
    refine ⟨⟨hN₁n (qv_le_stab X α (hVQ (hVβV hb))), fun w hw => ?_⟩, hVβV hb⟩
    have h1 := Subgroup.commutator_mem_commutator hb hw
    rw [Subgroup.commutator_comm] at h1
    exact Subgroup.mem_sup_left h1
  have hV'N₁ : ⁅V, V⁆ ≤ N₁ := Subgroup.commutator_le.mpr fun v hv w hw => (hK hv).1.2 w hw
  have hVnVβ : V ≤ Subgroup.normalizer (Vβ : Set X.Universal) :=
    (hVQ.trans (qv_le_qv X hG.h20 hc.1 hαβ)).trans hTVβ
  have hN₁Vβ : N₁ ≤ Vβ := by
    refine sup_le ?_ hZVβ
    rw [Subgroup.commutator_comm]
    exact commutator_le_self_of hVnVβ
  exact hV'N₁.trans (hN₁Vβ.trans (hG.vi_one_le_qv hc))

theorem vv_le_zm_sup {α α' δ : Vtx X} (hc : IsCritical X α α')
    (hcδ : IsCritical X (geo X α α' 2) δ) (hδ1 : geo X (geo X α α' 2) δ 1 = geo X α α' 1)
    (hdδ : X.treeGraph.dist α δ = 2) : Vv X α ≤ ZM X δ ⊔ Qv X (geo X α α' 2) := by
  have hVQ : Vv X α ≤ Qv X α := S38E.vv_le_qv X (by rw [hG.b4]; norm_num) hc.1
  have hδM : IsMVtx X δ := hcδ.isMVtx_right X hG.h20
  have hZV : ZM X δ ≤ Vv X α := S38E.zm_le_vv X hδM (by omega)
  have h4 := hG.commutator_vv_le_qv hc
  intro y hy
  refine hG.off_cent _ δ hcδ y ?_ fun z hz => h4 (Subgroup.commutator_mem_commutator hy (hZV hz))
  rw [hδ1]
  exact qv_le_qv X hG.h20 hc.1 (hG.adj_one hc) (hVQ hy)

theorem relIndex_cRel_vv_le {α α' : Vtx X} (hc : IsCritical X α α') :
    (cRel (ZM X α') (ZM X α)).relIndex (Vv X α) ≤ 8 := by
  obtain ⟨δ, hcδ, hδ1, -, hdδ⟩ := hG.exists_crit_back hc
  set μ := geo X α α' 2 with hμdef
  set β := geo X α α' 1 with hβdef
  have hVle := hG.vv_le_zm_sup hc hcδ hδ1 hdδ
  have hVQ : Vv X α ≤ Qv X α := S38E.vv_le_qv X (by rw [hG.b4]; norm_num) hc.1
  have hμ := hG.isMVtx_two hc
  have hZδβ : ZM X δ ≤ Qv X β := by
    have := zm_le_qv_geo_one X hG.h20 hG.critDist_pos hcδ
    rwa [hδ1] at this
  have hQμβ : Qv X μ ≤ Qv X β := qv_le_qv X hG.h20 hμ (hG.adj_one_two hc).symm
  have : Finite ↥(Qv X β) := hG.qv_finite_h (hG.not_isMVtx_one hc)
  have hfin : Finite ↥(ZM X δ ⊔ Qv X μ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hZδβ hQμβ))
  have hle : Vv X α ⊓ Qv X μ ≤ cRel (ZM X α') (ZM X α) := by
    rintro g ⟨hg, hgμ⟩
    exact ⟨stab_le_normalizer_zm X α (qv_le_stab X α (hVQ hg)), fun z hz =>
      hG.commutator_zm_le_left hc (hG.commutator_qv_inf_le hc ⟨hVQ hg, hgμ⟩ hz)⟩
  have hfV : Finite ↥(Vv X α) := by
    have := hG.qv_finite hc.1
    exact Finite.of_injective _ (Subgroup.inclusion_injective hVQ)
  have h0 : (Vv X α ⊓ Qv X μ).relIndex (Vv X α) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h0' : (Qv X μ).relIndex (ZM X δ ⊔ Qv X μ) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hZn : ZM X δ ≤ Subgroup.normalizer (Qv X μ : Set X.Universal) :=
    hZδβ.trans ((qv_le_stab_of_isMVtx X hG.h20 hμ (hG.adj_one_two hc).symm).trans
      (stab_le_normalizer_qv X μ))
  calc (cRel (ZM X α') (ZM X α)).relIndex (Vv X α) ≤ (Vv X α ⊓ Qv X μ).relIndex (Vv X α) :=
        Subgroup.relIndex_le_of_le_left hle h0
    _ = (Qv X μ).relIndex (Vv X α) := Subgroup.inf_relIndex_left _ _
    _ ≤ (Qv X μ).relIndex (ZM X δ ⊔ Qv X μ) := Subgroup.relIndex_le_of_le_right hVle h0'
    _ = (Qv X μ).relIndex (ZM X δ) := relIndex_sup_of_le_normalizer' hZn
    _ ≤ 8 := hG.off_idx _ δ hcδ

theorem commutator_vv_qv {α α' : Vtx X} (hc : IsCritical X α α') :
    ⁅⁅Vv X α, Qv X α⁆, Vv X α⁆ = ⊥ ∧ ⁅⁅Vv X α, Vv X α⁆, Qv X α⁆ = ⊥ := by
  set β := geo X α α' 1 with hβdef
  set V := Vv X α with hVdef
  set Q := Qv X α with hQdef
  have hαβ : X.treeGraph.Adj α β := hG.adj_one hc
  have hβ : ¬ IsMVtx X β := hG.not_isMVtx_one hc
  have hVs : stab X α ≤ Subgroup.normalizer (V : Set X.Universal) := stab_le_normalizer_vi α 2
  have hQs : stab X α ≤ Subgroup.normalizer (Q : Set X.Universal) := stab_le_normalizer_qv X α
  have hZs : stab X α ≤ Subgroup.normalizer (ZM X α : Set X.Universal) :=
    stab_le_normalizer_zm X α
  have hVQ : V ≤ Q := S38E.vv_le_qv X (by rw [hG.b4]; norm_num) hc.1
  have hQst : Q ≤ stab X α := qv_le_stab X α
  have hVst : V ≤ stab X α := hVQ.trans hQst
  have hfV : Finite ↥V := by
    have := hG.qv_finite hc.1
    exact Finite.of_injective _ (Subgroup.inclusion_injective hVQ)
  have hV2 : IsPGroup 2 ↥V := (hG.isPGroup_qv_m hc.1 hαβ).to_le hVQ
  have hZV : ZM X α ≤ V := S38E.zm_le_vv X hc.1 (by simp)
  have hA : ZM X α' ≤ stab X α := zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos hc
  set H := ⁅V, Q⁆ ⊔ ZM X α with hHdef
  have hVQV : ⁅V, Q⁆ ≤ V := commutator_le_self_of (hQst.trans hVs)
  have hHV : H ≤ V := sup_le hVQV hZV
  have hZH : ZM X α ≤ H := le_sup_right
  have hHs : stab X α ≤ Subgroup.normalizer (H : Set X.Universal) :=
    le_normalizer_sup (S38E.le_normalizer_commutator' hVs hQs) hZs
  have hprod := relIndex_cRel_mul_le (A := ZM X α') hZH hHV (hVst.trans hHs) (hA.trans hHs)
  have h8 := hG.relIndex_cRel_vv_le hc
  have hfH : Finite ↥H := Finite.of_injective _ (Subgroup.inclusion_injective hHV)
  have hH2 : IsPGroup 2 ↥H := hV2.to_le hHV
  have hTs : Qv X β ≤ stab X α := qv_le_stab_of_isMVtx X hG.h20 hc.1 hαβ
  have hQβ : Q ≤ Qv X β := qv_le_qv X hG.h20 hc.1 hαβ
  set Vβ := Vi X β 1 with hVβdef
  have hTVβ : Qv X β ≤ Subgroup.normalizer (Vβ : Set X.Universal) :=
    (qv_le_stab X β).trans (stab_le_normalizer_vi β 1)
  have hVβV : Vβ ≤ V := S38E.vi_one_le_vv X hαβ
  have hZVβ : ZM X α ≤ Vβ := by
    rw [← zv_of_isMVtx X hc.1]
    refine zv_le_vi' ?_
    rw [tdist_comm X β α, dist_eq_one_of_adj X hαβ]
  have hLs := hG.lt_le α hc.1
  have hVβab := S38E.commutator_vi_one_eq_bot X hG.h20 (by rw [hG.b4]; norm_num) β
  rcases le_two_or_le_two (exists_relIndex_eq_two_pow hV2 _) (exists_relIndex_eq_two_pow hH2 _)
    (hprod.trans h8) with h1 | h2
  ·
    exfalso
    have hVL : ⁅V, Lt α⁆ ≤ H := hG.commutator_le_of_codim_at hc hVQ hHV hVs hHs h1
    have hKn : stab X α ≤ Subgroup.normalizer ((Vβ ⊔ H : Subgroup X.Universal) :
        Set X.Universal) := by
      rw [hG.lt_sup α β hc.1 hαβ]
      refine sup_le ?_ (le_normalizer_sup hTVβ (hTs.trans hHs))
      exact le_normalizer_of_conj fun l hl x hx => conj_mem_of_commutator_mem hx
        (Subgroup.mem_sup_right (hVL (Subgroup.commutator_mem_commutator
          (sup_le hVβV hHV hx) hl)))
    have hVK : V ≤ Vβ ⊔ H := S38E.vv_le_of_vi_le X hαβ hKn le_sup_left
    have hVK' : V ≤ Vβ ⊔ ⁅V, Q⁆ := hVK.trans (sup_le le_sup_left (sup_le le_sup_right
      (hZVβ.trans le_sup_left)))
    have hVeq : V = Vβ :=
      eq_of_le_sup_commutator (isNilpotent_qv X hG.h20 hβ) (hVβV.trans (hVQ.trans hQβ))
        (hVQ.trans hQβ) hQβ (hQβ.trans hTVβ) hVβV hVK'
    have hne := S38E.commutator_vv_ne_bot X hG.h20 hG.b4 hG.cent hc (by
      have := hG.hV α α' hc
      rwa [hG.geo_rev hc (by norm_num)] at this)
    apply hne
    rw [← hVdef, hVeq]
    exact hVβab
  ·
    have hHL : ⁅H, Lt α⁆ ≤ ZM X α :=
      hG.commutator_le_of_codim_at hc (hHV.trans hVQ) hZH hHs hZs h2
    set N₂ := ⁅Vβ, Q⁆ ⊔ ZM X α with hN₂def
    have hN₂H : N₂ ≤ H := sup_le_sup_right (Subgroup.commutator_mono hVβV le_rfl) _
    have hN₂n : stab X α ≤ Subgroup.normalizer (N₂ : Set X.Universal) := by
      rw [hG.lt_sup α β hc.1 hαβ]
      refine sup_le ?_ (le_normalizer_sup (S38E.le_normalizer_commutator' hTVβ (hTs.trans hQs))
        (hTs.trans hZs))
      exact le_normalizer_of_conj fun l hl x hx => conj_mem_of_commutator_mem hx
        (Subgroup.mem_sup_right (hHL (Subgroup.commutator_mem_commutator (hN₂H hx) hl)))
    have hK : V ≤ cRel Q N₂ ⊓ V := by
      refine S38E.vv_le_of_vi_le X hαβ (le_normalizer_inf' (le_normalizer_cRel hQs hN₂n) hVs) ?_
      intro b hb
      exact ⟨⟨hN₂n (hVst (hVβV hb)), fun q hq =>
        Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb hq)⟩, hVβV hb⟩
    have hVQN₂ : ⁅V, Q⁆ ≤ N₂ := Subgroup.commutator_le.mpr fun v hv q hq => (hK hv).1.2 q hq
    have hN₂Vβ : N₂ ≤ Vβ := sup_le (commutator_le_self_of (hQβ.trans hTVβ)) hZVβ
    have hCVβ : ⁅V, Q⁆ ≤ Vβ := hVQN₂.trans hN₂Vβ
    have hVC : V ≤ Subgroup.centralizer ((⁅V, Q⁆ : Subgroup X.Universal) : Set X.Universal) := by
      have hK3 : V ≤ V ⊓ Subgroup.centralizer ((⁅V, Q⁆ : Subgroup X.Universal) :
          Set X.Universal) := by
        refine S38E.vv_le_of_vi_le X hαβ (le_normalizer_inf' hVs
          (le_normalizer_centralizer' (S38E.le_normalizer_commutator' hVs hQs))) ?_
        refine le_inf hVβV ?_
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        have := Subgroup.commutator_mem_commutator hb (hCVβ hc)
        rw [hVβab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this.symm
      exact hK3.trans inf_le_right
    have h1 : ⁅⁅V, Q⁆, V⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hVC
    refine ⟨h1, Subgroup.commutator_commutator_eq_bot_of_rotate h1 ?_⟩
    rw [Subgroup.commutator_comm Q V]
    exact h1

end G2Hyp

end Amalgam

end CFSG.Quasithin.MS93.S38G
