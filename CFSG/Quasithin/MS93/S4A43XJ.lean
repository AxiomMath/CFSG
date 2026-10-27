module

public import CFSG.Quasithin.MS93.S4A43XI

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Geo

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem geo_eq_geo_of_dist_add {u w x : Vtx X}
    (h : X.treeGraph.dist u x + X.treeGraph.dist x w = X.treeGraph.dist u w) {i : ℕ}
    (hi : i ≤ X.treeGraph.dist u x) : geo X u w i = geo X u x i := by
  have hx : x = geo X u w (X.treeGraph.dist u x) := eq_geo X h
  have := geo_geo X hi (show X.treeGraph.dist u x ≤ X.treeGraph.dist u w by omega)
  rw [← hx] at this
  exact this.symm

theorem geo_tail {u w : Vtx X} {j i : ℕ} (h : j + i ≤ X.treeGraph.dist u w) :
    geo X (geo X u w j) w i = geo X u w (j + i) := by
  symm
  apply eq_geo_of_dist X
  · rw [dist_geo_geo X (by omega) h]
    omega
  · rw [dist_geo_geo X (by omega) h, dist_geo_right X h, dist_geo_right X (by omega)]
    omega

theorem vi_le_vi_of_dist {x y : Vtx X} {i j : ℕ} (h : X.treeGraph.dist x y + i ≤ j) :
    Vi X y i ≤ Vi X x j :=
  iSup₂_le fun t ht => le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X |
    X.treeGraph.dist x ρ ≤ j}) => Zv X ρ) t (by
      have := dist_triangle X x y t
      have ht' : X.treeGraph.dist y t ≤ i := ht
      change X.treeGraph.dist x t ≤ j
      omega) le_rfl

theorem zv_le_vi_of_dist {x t : Vtx X} {i : ℕ} (h : X.treeGraph.dist x t ≤ i) : Zv X t ≤ Vi X x i :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist x ρ ≤ i}) => Zv X ρ) t h
    le_rfl

theorem vi_le_of_forall_zm {x : Vtx X} (hx : IsMVtx X x) {i : ℕ} {S : Subgroup X.Universal}
    (hS : ∀ t, IsMVtx X t → X.treeGraph.dist x t ≤ i → ZM X t ≤ S) : Vi X x i ≤ S := by
  refine iSup₂_le fun t ht => ?_
  have ht' : X.treeGraph.dist x t ≤ i := ht
  by_cases htM : IsMVtx X t
  · rw [zv_of_isMVtx X htM]
    exact hS t htM ht'
  · have hpos : 0 < X.treeGraph.dist t x := by
      rcases Nat.eq_zero_or_pos (X.treeGraph.dist t x) with h0 | h0
      · rw [(dist_eq_zero_iff X).mp h0] at htM
        exact absurd hx htM
      · exact h0
    have hadj : X.treeGraph.Adj t (geo X t x 1) := adj_geo_one X hpos
    have hd1 : X.treeGraph.dist (geo X t x 1) x = X.treeGraph.dist t x - 1 :=
      dist_geo_right X hpos
    have hM : IsMVtx X (geo X t x 1) := by
      have := isMVtx_iff_of_adj X hadj
      tauto
    rw [zv_of_not_isMVtx X htM]
    refine (zh_le_zm X hadj.symm).trans (hS _ hM ?_)
    rw [tdist_comm, hd1, tdist_comm]
    omega

theorem zv_le_qv_of_dist_lt' {t y : Vtx X}
    (hd : X.treeGraph.dist t y < critDist X) : Zv X t ≤ Qv X y := by
  by_cases htM : IsMVtx X t
  · rw [zv_of_isMVtx X htM]
    exact zm_le_qv_of_dist_lt X htM hd
  · rw [zv_of_not_isMVtx X htM]
    rcases Nat.eq_zero_or_pos (X.treeGraph.dist t y) with h0 | h0
    · rw [(dist_eq_zero_iff X).mp h0]
      exact zh_le_qv X y
    · have hadj : X.treeGraph.Adj t (geo X t y 1) := adj_geo_one X h0
      have hM : IsMVtx X (geo X t y 1) := by
        have := isMVtx_iff_of_adj X hadj
        tauto
      refine (zh_le_zm X hadj.symm).trans (zm_le_qv_of_dist_lt X hM ?_)
      rw [dist_geo_right X h0]
      omega

theorem vi_le_qv' {x y : Vtx X} {i : ℕ}
    (hd : i + X.treeGraph.dist x y < critDist X) : Vi X x i ≤ Qv X y :=
  iSup₂_le fun t ht => zv_le_qv_of_dist_lt' X (by
    have := dist_triangle X t x y
    have ht' : X.treeGraph.dist x t ≤ i := ht
    rw [tdist_comm X t x] at this
    omega)

theorem stab_le_normalizer_vi' (x : Vtx X) (i : ℕ) :
    stab X x ≤ Subgroup.normalizer (Vi X x i : Set X.Universal) :=
  stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ i) (fun g ρ => vi_smul X g ρ i) x

theorem zm_le_zm_smul_sup {x ν : Vtx X}
    (hN : stab X x ≤ Subgroup.normalizer ((ZM X ν ⊔ ZM X x : Subgroup X.Universal) :
      Set X.Universal))
    {k : X.Universal} (hk : k ∈ stab X x) : ZM X ν ≤ ZM X (k • ν) ⊔ ZM X x := by
  have heq : (ZM X ν ⊔ ZM X x).map (MulAut.conj k).toMonoidHom = ZM X ν ⊔ ZM X x :=
    map_conj_eq_of_mem_normalizer (hN hk)
  have hkx : k • x = x := (mem_stab _).mp hk
  rw [Subgroup.map_sup, ← zm_smul, ← zm_smul, hkx] at heq
  rw [heq]
  exact le_sup_left

theorem le_centralizer_stab {m : Vtx X} {R : Subgroup X.Universal} (hR : R ≤ stabCenter X m) :
    R ≤ Subgroup.centralizer (stab X m : Set X.Universal) := fun _ hr =>
  Subgroup.mem_centralizer_iff.mpr fun g hg => ((mem_stabCenter_iff_comm _).mp (hR hr)).2 g hg

theorem le_qv_or_crit {t w a : Vtx X} (ht : IsMVtx X t)
    {k : ℕ} (hk : k ≤ critDist X) (hta : X.treeGraph.dist t a ≤ k)
    (haw : X.treeGraph.dist a w ≤ critDist X - k) :
    ZM X t ≤ Qv X w ∨
      (IsCritical X t w ∧ X.treeGraph.dist t a = k ∧ X.treeGraph.dist a w = critDist X - k) := by
  by_cases hQ : ZM X t ≤ Qv X w
  · exact Or.inl hQ
  · right
    have h1 : critDist X ≤ X.treeGraph.dist t w := by
      by_contra hlt
      exact hQ (zm_le_qv_of_dist_lt X ht (by omega))
    have h2 := dist_triangle X t a w
    exact ⟨⟨ht, by omega, hQ⟩, by omega, by omega⟩

theorem eq_usup_smul {m p w : Vtx X} {R : Subgroup X.Universal} (hR : R ≤ stabCenter X m)
    (hU : R = Usup X w p) {k : X.Universal} (hk : k ∈ stab X m) : R = Usup X (k • w) (k • p) := by
  rw [usup_smul, ← hU]
  exact (map_conj_eq_of_le_centralizer (le_centralizer_stab X hR) hk).symm

end Geo

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem zm_ne_bot {x : Vtx 𝔛} (hx : IsMVtx 𝔛 x) : ZM 𝔛 x ≠ ⊥ := by
  obtain ⟨x', hs⟩ := c.star_at hx
  intro hbot
  apply ms22_ii _ h.hyp20 h.critDist_pos c.cent hs.1
  rw [eq_bot_iff, ← hbot]
  exact critR_le_zm h hs

theorem stab_le_normalizer_zm_sup {x ν : Vtx 𝔛} (hx : IsMVtx 𝔛 x)
    (hZB : ZM 𝔛 ν ≤ Bloc h.le L x) (hZV : ZM 𝔛 ν ≤ Vv 𝔛 x) :
    stab 𝔛 x ≤ Subgroup.normalizer ((ZM 𝔛 ν ⊔ ZM 𝔛 x : Subgroup 𝔘) : Set 𝔘) := by
  rw [stab_eq_ltil_sup_qv h c.full hx]
  refine sup_le ?_ ?_
  · exact le_normalizer_sup_of_comm_le ((ltil_le_stab h _).trans (stab_le_normalizer_zm _ _))
      (((Subgroup.commutator_mono hZB le_rfl).trans (commutator_bloc_le h c.hb hx)).trans
        le_sup_right)
  · exact le_normalizer_sup_of_comm_le ((qv_le_stab _ _).trans (stab_le_normalizer_zm _ _))
      (((Subgroup.commutator_mono hZV le_rfl).trans (c.commutator_vv_qv_le_zm hx)).trans
        le_sup_right)

theorem zm_le_zm_smul_sup_of_not_mem {x ν : Vtx 𝔛} (hx : IsMVtx 𝔛 x)
    (hd : (puAmalgam h.le).treeGraph.dist x ν = 2) (hn : ν ∉ nablaSet h.le L x) {k : 𝔘}
    (hk : k ∈ stab 𝔛 x) : ZM 𝔛 ν ≤ ZM 𝔛 (k • ν) ⊔ ZM 𝔛 x := by
  have hνM : IsMVtx 𝔛 ν := by
    have := (even_dist_iff (puAmalgam h.le) x ν).mp (by rw [hd]; decide)
    tauto
  have hZB : ZM 𝔛 ν ≤ Bloc h.le L x := by
    by_contra hc
    exact hn ⟨hd, by rwa [zv_of_isMVtx _ hνM]⟩
  have hZV : ZM 𝔛 ν ≤ Vv 𝔛 x := by
    rw [← zv_of_isMVtx _ hνM]
    exact zv_le_vv h hd.le
  exact zm_le_zm_smul_sup _ (c.stab_le_normalizer_zm_sup hx hZB hZV) hk

theorem critR0_le_stabCenter_four {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
  by_contra hn
  have hb8 := c.eight_le_critDist
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hγM := c.isMVtx_geo_rev hs (i := 2) (by omega) (by decide)
  have hd : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) (geo 𝔛 α' α 4) = 2 := by
    rw [dist_geo_geo _ (by omega) (by omega)]
  exact c.not_mem_nablaSet_geo_four hs ((c.nabla_symm hγM hd).mp (c.concl436 hs hn).1)

theorem commute_zm_of_shift {k : ℕ} (hk : 2 * k + 2 ≤ critDist 𝔛)
    (hE : ∀ x x' : Vtx 𝔛, Star 𝔛 x x' → critR0 𝔛 x x' ≤ stabCenter 𝔛 (geo 𝔛 x' x (2 * k)))
    {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {w : Vtx 𝔛} (hwM : IsMVtx 𝔛 w)
    (hw : 𝔄 (geo 𝔛 α' α (2 * k + 1)) w)
    (hU : critR0 𝔛 α α' = Usup 𝔛 w (geo 𝔛 α' α (2 * k + 1))) {t : Vtx 𝔛} (ht : IsMVtx 𝔛 t)
    (hdt : (puAmalgam h.le).treeGraph.dist α t ≤ 2 * k) :
    ZM 𝔛 t ≤ Subgroup.centralizer (ZM 𝔛 w : Set 𝔘) := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  set p := geo 𝔛 α' α (2 * k + 1) with hp
  have hdp : (puAmalgam h.le).treeGraph.dist α p = critDist 𝔛 - (2 * k + 1) :=
    c.dist_geo_rev hs (by omega)
  have hpH : ¬ IsMVtx 𝔛 p := c.not_isMVtx_geo_rev hs (by omega) (by
    rw [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩)
  have hαw : (puAmalgam h.le).treeGraph.dist α w ≤ critDist 𝔛 - 2 * k := by
    have := dist_triangle (puAmalgam h.le) α p w
    rw [dist_eq_one_of_adj _ hw] at this
    omega
  rcases le_qv_or_crit _ ht (a := α) (k := 2 * k) (by omega)
      (by rw [tdist_comm]; exact hdt) hαw with hQ | ⟨hcrit, hta, haw⟩
  · exact hQ.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hwM))
  · exfalso
    have hsw : Star 𝔛 w t := c.star_of_crit hcrit
    have hdtw : (puAmalgam h.le).treeGraph.dist t w = critDist 𝔛 := hcrit.2.1
    have hgeo : geo 𝔛 t w (2 * k) = α :=
      (eq_geo_of_dist _ hta (by rw [hta, haw, hdtw]; omega)).symm
    have hE' := hE w t hsw
    rw [hgeo] at hE'
    have h1 : ⁅ZM 𝔛 t, ZM 𝔛 w⁆ ≤ stabCenter 𝔛 α := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono (zm_le_vv h hwM) le_rfl).trans hE'
    have hZtp : ZM 𝔛 t ≤ Qv 𝔛 p := zm_le_qv_of_not_isMVtx _ h.hyp20 ht hpH (by
      have := dist_triangle (puAmalgam h.le) t α p
      rw [tdist_comm _ t α] at this
      omega)
    have h2 : ⁅ZM 𝔛 t, ZM 𝔛 w⁆ ≤ critR0 𝔛 α α' := by
      rw [hU, Usup, zv_of_isMVtx _ hwM, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl hZtp
    have h3 : ⁅ZM 𝔛 t, ZM 𝔛 w⁆ = ⊥ := by
      rw [eq_bot_iff, ← c.critR0_inf_stabCenter hs]
      exact le_inf h2 h1
    exact ms22_ii _ h.hyp20 h.critDist_pos c.cent hcrit h3

theorem dist_rev_rev {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ critDist 𝔛) :
    (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α i) (geo 𝔛 α' α j) = j - i := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  exact dist_geo_geo _ hij (by omega)

theorem geo_one_eq_rev {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    geo 𝔛 α α' 1 = geo 𝔛 α' α (critDist 𝔛 - 1) := by
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hs.1.2.1
  rw [← geo_symm _ (show 1 ≤ (puAmalgam h.le).treeGraph.dist α α' by
    have := c.b6; omega), hd]

theorem dist_rev_geo_one {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {i : ℕ} (hi : i ≤ critDist 𝔛 - 1) :
    (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α i) (geo 𝔛 α α' 1) = critDist 𝔛 - 1 - i := by
  rw [c.geo_one_eq_rev hs, c.dist_rev_rev hs hi (by omega)]

theorem false_of_commutator_vi_ltil_le {α β : Vtx 𝔛} (hα : IsMVtx 𝔛 α) (hαβ : 𝔄 α β) {i : ℕ}
    (hi : i < critDist 𝔛) (hi1 : 1 ≤ i)
    (hL : ⁅Vi 𝔛 α (i + 1), Ltil h.le L α⁆ ≤ Vi 𝔛 α (i - 1)) : False := by
  have hKT : Vi 𝔛 β i ≤ Qv 𝔛 β := vi_le_qv' _ (by rw [SimpleGraph.dist_self]; omega)
  have hKβ := stab_le_normalizer_vi' (puAmalgam h.le) β i
  have hlow : Vi 𝔛 α (i - 1) ≤ Vi 𝔛 β i :=
    vi_le_vi_of_dist _ (by rw [dist_eq_one_of_adj _ hαβ.symm]; omega)
  have hup : Vi 𝔛 β i ≤ Vi 𝔛 α (i + 1) :=
    vi_le_vi_of_dist _ (by rw [dist_eq_one_of_adj _ hαβ]; omega)
  have hKα : stab 𝔛 α ≤ Subgroup.normalizer (Vi 𝔛 β i : Set 𝔘) := by
    rw [stab_eq_ltil_sup_qv h c.full hα]
    refine sup_le ?_ ?_
    · have := le_normalizer_sup_of_comm_le (Y := Vi 𝔛 β i) (W := Vi 𝔛 α (i - 1))
        ((ltil_le_stab h α).trans (stab_le_normalizer_vi' _ α (i - 1)))
        (((Subgroup.commutator_mono hup le_rfl).trans hL).trans le_sup_right)
      rwa [sup_eq_left.mpr hlow] at this
    · exact (qv_le_qv _ h.hyp20 hα hαβ).trans ((qv_le_stab _ β).trans hKβ)
  have hbot := ms21_iii _ h.hyp20 hα hαβ hKT hKα hKβ
  apply c.zm_ne_bot hα
  rw [eq_bot_iff, ← hbot, ← zv_of_isMVtx _ hα]
  exact zv_le_vi_of_dist _ (by rw [dist_eq_one_of_adj _ hαβ.symm]; omega)

theorem mu_facts {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) (hg1 : g • geo 𝔛 α' α 1 = geo 𝔛 α' α 3) :
    𝔄 (geo 𝔛 α' α 3) (g • α') ∧ IsMVtx 𝔛 (g • α') ∧
      critR0 𝔛 α α' = Usup 𝔛 (g • α') (geo 𝔛 α' α 3) ∧
      geo 𝔛 α' α 2 ∈ nablaSet h.le L (g • α') := by
  have hb8 := c.eight_le_critDist
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hα'M : IsMVtx 𝔛 α' := (c.crit_symm hs).1
  have hγM := c.isMVtx_geo_two' hs
  have hα'1 : 𝔄 α' (geo 𝔛 α' α 1) := adj_geo_one _ (by omega)
  have hadj : 𝔄 (geo 𝔛 α' α 3) (g • α') := by
    have := (adj_smul _ g _ _).mpr hα'1.symm
    rwa [hg1] at this
  have hU : critR0 𝔛 α α' = Usup 𝔛 (g • α') (geo 𝔛 α' α 3) := by
    rw [← hg1]
    exact eq_usup_smul _ (c.critR0_le_stabCenter hs) (c.critR0_eq hs) hg
  have hdγ : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) α' = 2 := by
    rw [tdist_comm, dist_geo _ (by omega)]
  have hγα' : geo 𝔛 α' α 2 ∈ nablaSet h.le L α' :=
    (c.nabla_symm hγM hdγ).mp (c.mem_nablaSet_geo_two' hs.1)
  refine ⟨hadj, (isMVtx_smul _ g _).mpr hα'M, hU, ?_⟩
  have hgγ : g • geo 𝔛 α' α 2 = geo 𝔛 α' α 2 := (mem_stab _).mp hg
  rw [← hgγ]
  exact (mem_nablaSet_smul h g α' _).mpr hγα'

theorem mu_ne_four {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) (hg1 : g • geo 𝔛 α' α 1 = geo 𝔛 α' α 3) :
    g • α' ≠ geo 𝔛 α' α 4 := by
  intro he
  have hb8 := c.eight_le_critDist
  obtain ⟨-, -, hU, -⟩ := c.mu_facts hs hg hg1
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have h43 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := (c.adj_geo_rev hs (i := 3) (by omega)).symm
  rw [he] at hU
  have hle : critR0 𝔛 α α' ≤ Uloc h.le L (geo 𝔛 α' α 4) ⊓ stabCenter 𝔛 (geo 𝔛 α' α 4) :=
    le_inf (hU ▸ c.usup_le_uloc hηM h43) (c.critR0_le_stabCenter_four hs)
  rw [c.uloc_inf_stabCenter hηM, le_bot_iff] at hle
  have hcard := c.card_critR0 hs
  rw [hle, Subgroup.card_bot] at hcard
  have : 1 < Fintype.card F := Fintype.one_lt_card
  nlinarith

theorem not_vcirc_le_qv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) : ¬ Vcirc h.le L (g • α') ≤ Qv 𝔛 α := by
  intro hle
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hα'M : IsMVtx 𝔛 α' := (c.crit_symm hs).1
  have hγM := c.isMVtx_geo_two' hs
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hβH : ¬ IsMVtx 𝔛 (geo 𝔛 α α' 1) := by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα
  have hs' : Star 𝔛 α' α := c.star_of_crit hs.1
  have hT : Vv 𝔛 α' ⊔ Qv 𝔛 α = Qv 𝔛 (geo 𝔛 α α' 1) :=
    vv_sup_qv_eq_of_star h c.full c.cent c.via c.hb hs' (c.isC1 hα'M)
      (le_of_eq (c.relIndex_qv hα hαβ))
  obtain ⟨-, hBne, hBsup⟩ := isC1_bloc h c.full c.hb hα'M (c.isC1 hα'M)
  have hVcB : ¬ Vcirc h.le L α' ≤ Bloc h.le L α' := by
    intro hVB
    apply hBne
    refine le_antisymm (bloc_le_vv h α') fun v hv => ?_
    have h1 : ⁅⁅Vv 𝔛 α', Ltil h.le L α'⁆, Ltil h.le L α'⁆ ≤ ZM 𝔛 α' :=
      (Subgroup.commutator_mono hVB le_rfl).trans (commutator_bloc_le h c.hb hα'M)
    have hLs := ltil_le_stab h α'
    have hZn := stab_le_normalizer_zm (puAmalgam h.le) α'
    have hVs : Vv 𝔛 α' ≤ stab 𝔛 α' := (vv_le_qv h c.hb hα'M).trans (qv_le_stab _ α')
    have h3 := three_subgroups_le (N := ZM 𝔛 α') (H₁ := Ltil h.le L α')
      (H₂ := Ltil h.le L α') (H₃ := Vv 𝔛 α') (hLs.trans hZn) (hLs.trans hZn) (hVs.trans hZn)
      (by rw [Subgroup.commutator_comm (Ltil h.le L α') (Vv 𝔛 α')]; exact h1) h1
    rw [ltil_perfect h hα'M, Subgroup.commutator_comm] at h3
    exact (mem_bloc_iff h c.hb hα'M).mpr ⟨hv, fun l hl =>
      h3 (Subgroup.commutator_mem_commutator hv hl)⟩
  have hVcn : stab 𝔛 α' ≤ Subgroup.normalizer (Vcirc h.le L α' : Set 𝔘) :=
    le_normalizer_commutator (stab_le_normalizer_vv h α') (stab_le_normalizer_ltil h α')
  have hVcV : Vcirc h.le L α' ≤ Vv 𝔛 α' := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((ltil_le_stab h α').trans (stab_le_normalizer_vv h α'))
  have hVVB : Vv 𝔛 α' ≤ Vcirc h.le L α' ⊔ Bloc h.le L α' :=
    (hBsup _ hVcn hVcV hVcB).ge
  have hdγ : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) α' = 2 := by
    rw [tdist_comm, dist_geo _ (by omega)]
  have hγα' : geo 𝔛 α' α 2 ∈ nablaSet h.le L α' :=
    (c.nabla_symm hγM hdγ).mp (c.mem_nablaSet_geo_two' hs.1)
  obtain ⟨γ', hsγ⟩ := c.star_at hγM
  have hiγ := (c.concl437_i hsγ hdγ hγα').2
  have hVcγn : stab 𝔛 (geo 𝔛 α' α 2) ≤
      Subgroup.normalizer (Vcirc h.le L (geo 𝔛 α' α 2) : Set 𝔘) :=
    le_normalizer_commutator (stab_le_normalizer_vv h _) (stab_le_normalizer_ltil h _)
  have hα'1 : 𝔄 α' (geo 𝔛 α' α 1) := adj_geo_one _ (by omega)
  have h1γ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  have hQγα' : Qv 𝔛 (geo 𝔛 α' α 2) ≤ stab 𝔛 α' :=
    (qv_le_qv _ h.hyp20 hγM h1γ.symm).trans (qv_le_stab_of_adj _ hα'1.symm)
  have hWn : stab 𝔛 (geo 𝔛 α' α 2) ≤ Subgroup.normalizer
      ((Vcirc h.le L α' ⊔ Vcirc h.le L (geo 𝔛 α' α 2) : Subgroup 𝔘) : Set 𝔘) := by
    rw [stab_eq_ltil_sup_qv h c.full hγM]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_comm_le ((ltil_le_stab h _).trans hVcγn)
        ((Subgroup.commutator_mono hVcV le_rfl).trans (hiγ.trans le_sup_right))
    · exact (le_inf (hQγα'.trans hVcn) ((qv_le_stab _ _).trans hVcγn)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hVcμ : Vcirc h.le L α' ≤ Vcirc h.le L (g • α') ⊔ Vcirc h.le L (geo 𝔛 α' α 2) := by
    have heq := map_conj_eq_of_mem_normalizer (hWn hg)
    have hgγ : g • geo 𝔛 α' α 2 = geo 𝔛 α' α 2 := (mem_stab _).mp hg
    rw [Subgroup.map_sup, ← vcirc_smul h, ← vcirc_smul h, hgγ] at heq
    rw [heq]
    exact le_sup_left
  have hZsα' : ZM 𝔛 α ≤ stab 𝔛 α' := zm_le_stab_of_star h hs'
  obtain ⟨F', _, _, ψ', -, -, -, -, -, hBG, -⟩ := isC1_normal h c.full c.hb hα'M (c.isC1 hα'M)
  have hZB : ⁅ZM 𝔛 α, Bloc h.le L α'⁆ ≤ critR 𝔛 α α' := by
    have h1 : ⁅ZM 𝔛 α, Bloc h.le L α'⁆ ≤ ZM 𝔛 α' := by
      rw [Subgroup.commutator_comm]
      refine (Subgroup.commutator_mono le_rfl hZsα').trans (hBG.trans ?_)
      exact sup_le (c.commutator_vv_qv_le_zm hα'M) le_rfl
    have h2 : ⁅ZM 𝔛 α, Bloc h.le L α'⁆ ≤ critR0 𝔛 α' α := by
      rw [critR0, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono (bloc_le_vv h α') le_rfl
    have h3 := le_inf h2 h1
    rw [c.critR0_inf_zm hs'] at h3
    calc ⁅ZM 𝔛 α, Bloc h.le L α'⁆ ≤ critR 𝔛 α' α := h3
      _ = critR 𝔛 α α' := by rw [critR, critR, Subgroup.commutator_comm]
  have hHγ := (c.concl432 hγM).2 α' (c.mem_nablaSet_geo_two' hs.1)
  have hgeo1 : geo 𝔛 (geo 𝔛 α' α 2) α' 1 = geo 𝔛 α' α 1 :=
    (eq_geo_one _ h1γ.symm (by rw [dist_eq_one_of_adj _ hα'1.symm, hdγ])).symm
  rw [hgeo1, ← c.critR0_eq hs] at hHγ
  have hZγ : ZM 𝔛 α ≤ Qv 𝔛 (geo 𝔛 α' α 2) :=
    zm_le_qv_of_dist_lt _ hα (by rw [c.dist_geo_rev hs (by omega)]; omega)
  have hVγβ : Vv 𝔛 (geo 𝔛 α' α 2) ≤ Qv 𝔛 (geo 𝔛 α α' 1) :=
    vv_le_qv_of_dist h hγM (by rw [c.dist_rev_geo_one hs (by omega)]; omega)
  have hVcγV : Vcirc h.le L (geo 𝔛 α' α 2) ≤ Vv 𝔛 (geo 𝔛 α' α 2) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h _).trans (stab_le_normalizer_vv h _))
  have hZVc : ⁅ZM 𝔛 α, Vcirc h.le L (geo 𝔛 α' α 2)⁆ ≤ critR 𝔛 α α' := by
    have h1 : ⁅ZM 𝔛 α, Vcirc h.le L (geo 𝔛 α' α 2)⁆ ≤ critR0 𝔛 α α' := by
      rw [← hHγ.2, ← hHγ.1, Hloc, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl hZγ
    have h2 : ⁅ZM 𝔛 α, Vcirc h.le L (geo 𝔛 α' α 2)⁆ ≤ ZM 𝔛 α :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        (((hVcγV.trans hVγβ).trans (qv_le_stab_of_adj _ hαβ.symm)).trans
          (stab_le_normalizer_zm _ α))
    rw [← c.critR0_inf_zm hs]
    exact le_inf h1 h2
  obtain ⟨u, hu, hun⟩ : ∃ u ∈ Uloc h.le L α, u ∉ Usup 𝔛 α (geo 𝔛 α α' 1) := by
    by_contra hall
    push Not at hall
    have hfin : Finite ↥(Usup 𝔛 α (geo 𝔛 α α' 1)) := by
      have := finite_qv _ h.hyp20 hβH
      exact Finite.of_injective _ (Subgroup.inclusion_injective
        ((c.usup_le_zh hα hαβ).trans (zh_le_qv _ _)))
    have h1 := Subgroup.card_le_of_le (fun x hx => hall x hx)
    rw [c.card_uloc hα, c.card_usup hα hαβ] at h1
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  have hmem : ∀ s ∈ Qv 𝔛 (geo 𝔛 α α' 1), ⁅u, s⁆ ∈ Usup 𝔛 α (geo 𝔛 α α' 1) := fun s hs0 => by
    rw [usup_eq_commutator_uloc h c.full hα hαβ]
    exact Subgroup.commutator_mem_commutator hu hs0
  have hcomm : Usup 𝔛 α (geo 𝔛 α α' 1) ≤ Subgroup.centralizer (Qv 𝔛 (geo 𝔛 α α' 1) : Set 𝔘) :=
    (c.usup_le_zh hα hαβ).trans (zh_le_centralizer _ _)
  set f := subCommHom (Qv 𝔛 (geo 𝔛 α α' 1)) (Usup 𝔛 α (geo 𝔛 α α' 1)) u hmem hcomm with hf
  have hker : f.ker ≤ (Qv 𝔛 α).subgroupOf (Qv 𝔛 (geo 𝔛 α α' 1)) := by
    intro s hs
    rw [MonoidHom.mem_ker, hf, subCommHom_apply, commutatorElement_eq_one_iff_mul_comm] at hs
    rw [Subgroup.mem_subgroupOf]
    by_contra hsμ
    exact hun (c.mem_usup_of_commute hα hαβ s.2 hsμ hu hs.symm)
  have huZ : u ∈ ZM 𝔛 α := uloc_le_zm h c.full hα hu
  have hK : ∀ s ∈ Qv 𝔛 (geo 𝔛 α α' 1), ⁅u, s⁆ ∈ critR 𝔛 α α' := by
    intro s hs0
    let K : Subgroup 𝔘 := ((critR 𝔛 α α').comap f).map (Qv 𝔛 (geo 𝔛 α α' 1)).subtype
    have hKmem : ∀ x, x ∈ K ↔ ∃ hx : x ∈ Qv 𝔛 (geo 𝔛 α α' 1), ⁅u, x⁆ ∈ critR 𝔛 α α' := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hx, hux⟩
        exact ⟨⟨x, hx⟩, hux, rfl⟩
    have hQK : Qv 𝔛 α ≤ K := fun x hx => (hKmem x).mpr ⟨qv_le_qv _ h.hyp20 hα hαβ hx, by
      have : ⁅u, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hα huZ) x hx).symm
      rw [this]
      exact Subgroup.one_mem _⟩
    have hVcK : Vcirc h.le L (geo 𝔛 α' α 2) ≤ K := fun x hx =>
      (hKmem x).mpr ⟨hVγβ (hVcγV hx), hZVc (Subgroup.commutator_mem_commutator huZ hx)⟩
    have hVα'β : Vv 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 α α' 1) := by
      have h2 : 𝔄 (geo 𝔛 α α' 1) (geo 𝔛 α α' 2) := adj_geo _ (i := 1) (by
        rw [hs.1.2.1]; omega)
      exact hs'.2.trans (qv_le_qv _ h.hyp20 (isMVtx_geo_two _ h.hyp20 h.critDist_pos hs.1)
        h2.symm)
    have hBK : Bloc h.le L α' ≤ K := fun x hx =>
      (hKmem x).mpr ⟨hVα'β (bloc_le_vv h α' hx), hZB (Subgroup.commutator_mem_commutator huZ hx)⟩
    have hTK : Qv 𝔛 (geo 𝔛 α α' 1) ≤ K := by
      rw [← hT]
      refine sup_le ?_ hQK
      refine hVVB.trans (sup_le (hVcμ.trans (sup_le (hle.trans hQK) hVcK)) hBK)
    obtain ⟨-, hx⟩ := (hKmem s).mp (hTK hs0)
    exact hx
  have hrange : f.range ≤ critR 𝔛 α α' := by
    rintro _ ⟨s, rfl⟩
    rw [hf, subCommHom_apply]
    exact hK s s.2
  have hfinβ := finite_qv _ h.hyp20 hβH
  have hfinR : Finite ↥(critR 𝔛 α α') :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((c.critR_le_usup hs).trans
      ((c.usup_le_zh hα hαβ).trans (zh_le_qv _ _))))
  have h1 : (Qv 𝔛 α).relIndex (Qv 𝔛 (geo 𝔛 α α' 1)) ≤ Nat.card ↥f.range := by
    rw [← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have h2 := h1.trans (Subgroup.card_le_of_le hrange)
  rw [c.relIndex_qv hα hαβ, c.card_critR hs] at h2
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  nlinarith

theorem not_mem_nablaSet_mu {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) (hg1 : g • geo 𝔛 α' α 1 = geo 𝔛 α' α 3) :
    g • α' ∉ nablaSet h.le L (geo 𝔛 α' α 4) := by
  intro hmem
  have hb8 := c.eight_le_critDist
  obtain ⟨hμ3, hμM, -, -⟩ := c.mu_facts hs hg hg1
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hdη : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) (g • α') = 2 := hmem.1
  have hημ := (c.nabla_symm hηM hdη).mp hmem
  obtain ⟨η', hsη⟩ := c.star_at hηM
  have hN := (c.concl437_i hsη hdη hημ).1
  have h43 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := (c.adj_geo_rev hs (i := 3) (by omega)).symm
  have h45 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  obtain ⟨k, hk, hk3⟩ := exists_mem_stab_smul _ h43 h45
  have hV := vv_le_vv_smul_sup _ hN hk
  have hlam : 𝔄 (geo 𝔛 α' α 5) (k • g • α') := by
    have := (adj_smul _ k _ _).mpr hμ3
    rwa [hk3] at this
  have hlamM : IsMVtx 𝔛 (k • g • α') := (isMVtx_smul _ k _).mpr hμM
  have hd5 := c.dist_geo_rev hs (i := 5) (by omega)
  have hd4 := c.dist_geo_rev hs (i := 4) (by omega)
  have hVlam : Vv 𝔛 (k • g • α') ≤ Qv 𝔛 α := by
    refine vv_le_qv_of_dist h hlamM ?_
    have := dist_triangle (puAmalgam h.le) (k • g • α') (geo 𝔛 α' α 5) α
    have h5 : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 5) α = critDist 𝔛 - 5 := by
      rw [tdist_comm]; exact hd5
    rw [dist_eq_one_of_adj _ hlam.symm, h5] at this
    omega
  have hVη : Vv 𝔛 (geo 𝔛 α' α 4) ≤ Qv 𝔛 α :=
    vv_le_qv_of_dist h hηM (by rw [tdist_comm, hd4]; omega)
  apply c.not_vcirc_le_qv hs hg
  refine le_trans ?_ (hV.trans (sup_le hVlam hVη))
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((ltil_le_stab h _).trans (stab_le_normalizer_vv h _))

theorem dist_four_mu {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) (hg1 : g • geo 𝔛 α' α 1 = geo 𝔛 α' α 3) :
    (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) (g • α') = 2 := by
  have hb8 := c.eight_le_critDist
  obtain ⟨hμ3, -, -, -⟩ := c.mu_facts hs hg hg1
  exact dist_eq_two_of_adj_adj _ (c.adj_geo_rev hs (i := 3) (by omega)).symm hμ3
    (c.mu_ne_four hs hg hg1).symm

theorem vi_four_le_centralizer_lambda {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g k : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) (hg1 : g • geo 𝔛 α' α 1 = geo 𝔛 α' α 3)
    (hk : k ∈ stab 𝔛 (geo 𝔛 α' α 4)) (hk3 : k • geo 𝔛 α' α 3 = geo 𝔛 α' α 5) :
    Vi 𝔛 α 4 ≤ Subgroup.centralizer (ZM 𝔛 (k • g • α') : Set 𝔘) ∧
      ZM 𝔛 (g • α') ≤ ZM 𝔛 (k • g • α') ⊔ ZM 𝔛 (geo 𝔛 α' α 4) ∧
      critR0 𝔛 α α' = Usup 𝔛 (k • g • α') (geo 𝔛 α' α 5) := by
  have hb8 := c.eight_le_critDist
  obtain ⟨hμ3, hμM, hUμ, -⟩ := c.mu_facts hs hg hg1
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hUlam : critR0 𝔛 α α' = Usup 𝔛 (k • g • α') (geo 𝔛 α' α 5) := by
    rw [← hk3]
    exact eq_usup_smul _ (c.critR0_le_stabCenter_four hs) hUμ hk
  have hlam : 𝔄 (geo 𝔛 α' α 5) (k • g • α') := by
    have := (adj_smul _ k _ _).mpr hμ3
    rwa [hk3] at this
  have hlamM : IsMVtx 𝔛 (k • g • α') := (isMVtx_smul _ k _).mpr hμM
  refine ⟨vi_le_of_forall_zm _ hs.1.1 fun t ht hdt =>
    c.commute_zm_of_shift (k := 2) (by omega) (fun x x' hsx => c.critR0_le_stabCenter_four hsx)
      hs hlamM hlam hUlam ht hdt,
    c.zm_le_zm_smul_sup_of_not_mem hηM (c.dist_four_mu hs hg hg1)
      (c.not_mem_nablaSet_mu hs hg hg1) hk, hUlam⟩

theorem not_vi_four_le_qv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ¬ Vi 𝔛 α 4 ≤ Qv 𝔛 (geo 𝔛 α' α 4) := by
  intro hV4
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hγM := c.isMVtx_geo_two' hs
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hγ1 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) := (c.adj_geo_rev hs (i := 1) (by omega)).symm
  have hγ3 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := c.adj_geo_rev hs (i := 2) (by omega)
  have hη3 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := (c.adj_geo_rev hs (i := 3) (by omega)).symm
  have hη5 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  obtain ⟨g, hg, hg1⟩ := exists_mem_stab_smul _ hγ1 hγ3
  obtain ⟨k, hk, hk3⟩ := exists_mem_stab_smul _ hη3 hη5
  obtain ⟨hμ3, hμM, -, hγμ⟩ := c.mu_facts hs hg hg1
  obtain ⟨hcen, hZμ, -⟩ := c.vi_four_le_centralizer_lambda hs hg hg1 hk hk3
  have hC : Vi 𝔛 α 4 ≤ Subgroup.centralizer (ZM 𝔛 (g • α') : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff]
    refine hZμ.trans (sup_le (Subgroup.le_centralizer_iff.mp hcen) ?_)
    exact (zm_le_centralizer_qv _ h.hyp20 hηM).trans (Subgroup.centralizer_le hV4)
  have hVμ : Vi 𝔛 α 4 ≤ Qv 𝔛 (g • α') := by
    rw [← c.cent (g • α') _ hμM hμ3.symm]
    exact le_inf (hV4.trans (qv_le_qv _ h.hyp20 hηM hη3)) hC
  have hHμ := (c.concl432 hμM).2 _ hγμ
  have hdμγ : (puAmalgam h.le).treeGraph.dist (g • α') (geo 𝔛 α' α 2) = 2 := hγμ.1
  have hadj : 𝔄 (geo 𝔛 (g • α') (geo 𝔛 α' α 2) 1) (geo 𝔛 α' α 2) := by
    have := adj_geo (puAmalgam h.le) (u := g • α') (w := geo 𝔛 α' α 2) (i := 1) (by omega)
    rwa [show geo 𝔛 (g • α') (geo 𝔛 α' α 2) (1 + 1) = geo 𝔛 α' α 2 from
      geo_of_le _ (by omega)] at this
  have hfinH : Finite ↥(Hloc h.le L (g • α')) := by
    rw [hHμ.1, hHμ.2]
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hadj.symm]; exact hγM)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((c.usup_le_zh hγM hadj.symm).trans (zh_le_qv _ _)))
  have hcardH : Nat.card ↥(Hloc h.le L (g • α')) = Fintype.card F ^ 2 := by
    rw [hHμ.1, hHμ.2, c.card_usup hγM hadj.symm]
  have hVcμV : Vcirc h.le L (g • α') ≤ Vv 𝔛 (g • α') :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h _).trans (stab_le_normalizer_vv h _))
  have hVcβ : Vcirc h.le L (g • α') ≤ Qv 𝔛 (geo 𝔛 α α' 1) := by
    refine hVcμV.trans (vv_le_qv_of_dist h hμM ?_)
    have := dist_triangle (puAmalgam h.le) (g • α') (geo 𝔛 α' α 3) (geo 𝔛 α α' 1)
    rw [dist_eq_one_of_adj _ hμ3.symm, c.dist_rev_geo_one hs (by omega)] at this
    omega
  have hXα := c.not_vcirc_le_qv hs hg
  have h4H : ⁅Vi 𝔛 α 4, Vcirc h.le L (g • α')⁆ ≤ Hloc h.le L (g • α') := by
    rw [Hloc, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hVμ
  have hVV4 : Vv 𝔛 α ≤ Vi 𝔛 α 4 := vi_le_vi_of_dist _ (by simp)
  have hsq := sq_le_card_commutator_vv h c.full c.cent c.hb hα hαβ c.via (c.isC1 hα) hVcβ hXα
  have hEq : ⁅Vv 𝔛 α, Vcirc h.le L (g • α')⁆ = Hloc h.le L (g • α') := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.commutator_mono hVV4 le_rfl).trans h4H) ?_
    rw [hcardH]
    exact hsq
  have hXW : ⁅Vi 𝔛 α 4, Vcirc h.le L (g • α')⁆ ≤ Vv 𝔛 α := by
    refine h4H.trans (hEq.symm ▸ ?_)
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hVcβ.trans (qv_le_stab_of_adj _ hαβ.symm)).trans (stab_le_normalizer_vv h α))
  have hker := commutator_ltil_le_of_comm_le h c.full hα hαβ (stab_le_normalizer_vi' _ α 4)
    hVcβ hXα (stab_le_normalizer_vv h α) hXW
  exact c.false_of_commutator_vi_ltil_le hα hαβ (i := 3) (by omega) (by omega) hker

theorem exists_crit_four {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ∃ z, IsCritical 𝔛 z (geo 𝔛 α' α 4) ∧ (puAmalgam h.le).treeGraph.dist z α = 4 ∧
      (puAmalgam h.le).treeGraph.dist α (geo 𝔛 α' α 4) = critDist 𝔛 - 4 := by
  have hb8 := c.eight_le_critDist
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hd4 := c.dist_geo_rev hs (i := 4) (by omega)
  by_contra hall
  push Not at hall
  apply c.not_vi_four_le_qv hs
  refine vi_le_of_forall_zm _ hs.1.1 fun t ht hdt => ?_
  rcases le_qv_or_crit _ ht (a := α) (k := 4) (by omega)
      (by rw [tdist_comm]; exact hdt) (by rw [hd4]) with hQ | ⟨hcrit, hta, -⟩
  · exact hQ
  · exact absurd hd4 (hall t hcrit hta)

theorem mem_nablaSet_geo_six {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    geo 𝔛 α' α 4 ∈ nablaSet h.le L (geo 𝔛 α' α 6) := by
  have hb8 := c.eight_le_critDist
  obtain ⟨z, hcrit, hdz, hdη⟩ := c.exists_crit_four hs
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hmem := c.mem_nablaSet_geo_two' hcrit
  have hdηz : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) z = critDist 𝔛 := by
    rw [tdist_comm]; exact hcrit.2.1
  have hsum : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) α +
      (puAmalgam h.le).treeGraph.dist α z = (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) z := by
    rw [tdist_comm _ (geo 𝔛 α' α 4) α, hdη, tdist_comm _ α z, hdz, hdηz]
    omega
  have h1 : geo 𝔛 (geo 𝔛 α' α 4) z 2 = geo 𝔛 (geo 𝔛 α' α 4) α 2 :=
    geo_eq_geo_of_dist_add _ hsum (by rw [tdist_comm, hdη]; omega)
  have h2 : geo 𝔛 (geo 𝔛 α' α 4) α 2 = geo 𝔛 α' α 6 := by
    rw [geo_tail _ (by rw [hd']; omega)]
  rw [h1, h2] at hmem
  exact hmem

theorem concl438_c {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    Vi 𝔛 (geo 𝔛 α' α 4) 4 ⊔ Qv 𝔛 α = Qv 𝔛 (geo 𝔛 α α' 1) := by
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hα'M : IsMVtx 𝔛 α' := (c.crit_symm hs).1
  have hγM := c.isMVtx_geo_two' hs
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hs' : Star 𝔛 α' α := c.star_of_crit hs.1
  have hT : Vv 𝔛 α' ⊔ Qv 𝔛 α = Qv 𝔛 (geo 𝔛 α α' 1) :=
    vv_sup_qv_eq_of_star h c.full c.cent c.via c.hb hs' (c.isC1 hα'M)
      (le_of_eq (c.relIndex_qv hα hαβ))
  have hγ1 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) := (c.adj_geo_rev hs (i := 1) (by omega)).symm
  have hγ3 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := c.adj_geo_rev hs (i := 2) (by omega)
  obtain ⟨g, hg, hg1⟩ := exists_mem_stab_smul _ hγ1 hγ3
  have hdγ : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 2) α' = 2 := by
    rw [tdist_comm, dist_geo _ (by omega)]
  have hγα' : geo 𝔛 α' α 2 ∈ nablaSet h.le L α' :=
    (c.nabla_symm hγM hdγ).mp (c.mem_nablaSet_geo_two' hs.1)
  obtain ⟨γ', hsγ⟩ := c.star_at hγM
  have hV := vv_le_vv_smul_sup _ (c.concl437_i hsγ hdγ hγα').1 hg
  have hVμ : Vv 𝔛 (g • α') ≤ Vi 𝔛 (geo 𝔛 α' α 4) 4 :=
    vi_le_vi_of_dist _ (by rw [c.dist_four_mu hs hg hg1])
  have hVγ : Vv 𝔛 (geo 𝔛 α' α 2) ≤ Vi 𝔛 (geo 𝔛 α' α 4) 4 :=
    vi_le_vi_of_dist _ (by rw [tdist_comm, c.dist_rev_rev hs (by omega) (by omega)])
  have hVi : Vi 𝔛 (geo 𝔛 α' α 4) 4 ≤ Qv 𝔛 (geo 𝔛 α α' 1) :=
    vi_le_qv' _ (by rw [c.dist_rev_geo_one hs (by omega)]; omega)
  refine le_antisymm (sup_le hVi (qv_le_qv _ h.hyp20 hα hαβ)) ?_
  rw [← hT]
  exact sup_le_sup_right (hV.trans (sup_le hVμ hVγ)) _

end Ctx43

end CFSG.Quasithin.MS93.S4A
