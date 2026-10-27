module

public import CFSG.Quasithin.MS93.S46I466bP1

public section

namespace CFSG.Quasithin.MS93.S46.I466b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I464
open scoped commutatorElement

theorem commutator_iSup₂_le_of {𝔾 : Type*} [Group 𝔾] {ι : Type*} {p : ι → Prop}
    {A : ι → Subgroup 𝔾} {H N : Subgroup 𝔾} (hA : ∀ i, p i → ⁅A i, H⁆ ≤ N)
    (hN : ∀ i, p i → A i ≤ Subgroup.normalizer (N : Set 𝔾)) :
    ⁅⨆ i, ⨆ (_ : p i), A i, H⁆ ≤ N := by
  rw [iSup_subtype']
  exact commutator_iSup_le_of (fun i => hA i.1 i.2) (iSup_le fun i => hN i.1 i.2)

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)
  (h466 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    (Qv (puAmalgam h.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2)
  (h461 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → centerOf (Vv _ x) ≤ Bloc h.le L x)
  (h465 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
    ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
include h hφ

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

omit [Fintype F] hφ in
theorem commutator_vv_le_centralizer_stab {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hle : ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≤ stabCenter _ α) {x : Vtx (puAmalgam h.le)}
    (hx : IsMVtx _ x) :
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Subgroup.centralizer (stab (puAmalgam h.le) x : Set 𝔘) := by
  obtain ⟨k, rfl⟩ := exists_smul_eq_of_isMVtx _ hα hx
  have hV : Vv 𝔛 (k • α) = (Vv 𝔛 α).map (MulAut.conj k).toMonoidHom := vi_smul _ k α 2
  rw [hV, ← Subgroup.map_commutator]
  rintro _ ⟨w₀, hw₀, rfl⟩
  obtain ⟨c, hc, rfl⟩ := hle hw₀
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : k⁻¹ * y * k ∈ stab 𝔛 α := (mem_stab_smul _).mp hy
  have e : k⁻¹ * y * k * (c : 𝔘) = c * (k⁻¹ * y * k) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k⁻¹ * y * k, hy'⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
  calc y * (k * (c : 𝔘) * k⁻¹) = k * (k⁻¹ * y * k * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * y * k)) * k⁻¹ := by rw [e]
    _ = k * c * k⁻¹ * y := by group

theorem zm_inf_centralizer_le_zloc {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    ZM (puAmalgam h.le) x ⊓ Subgroup.centralizer (stab (puAmalgam h.le) x : Set 𝔘) ≤
      Zloc h.le L x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rintro z ⟨hz, hzc⟩
  obtain ⟨u, hu, ζ, hζ, rfl⟩ := exists_uloc_mul_zloc h hfull hx hz
  have huc : u ∈ Subgroup.centralizer (stab 𝔛 x : Set 𝔘) := by
    have := Subgroup.mul_mem _ hzc (Subgroup.inv_mem _ (zloc_le_centralizer_stab h hfull hx hζ))
    rwa [mul_inv_cancel_right] at this
  have hu1 : u ∈ Uloc h.le L x ⊓ Subgroup.centralizer (stab 𝔛 x : Set 𝔘) := ⟨hu, huc⟩
  rw [uloc_inf_centralizer_stab h hφ hx, Subgroup.mem_bot] at hu1
  rw [hu1, one_mul]
  exact hζ

theorem eq_bot_or_eq_uloc_of_le {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) {N : Subgroup 𝔘}
    (hN : N ≤ Uloc h.le L x) (hn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (N : Set 𝔘)) :
    N = ⊥ ∨ N = Uloc h.le L x := by
  obtain ⟨ψ, hsurj, hψ⟩ := exists_natural_Uloc h hφ hx
  exact eq_or_eq_of_natural hsurj (fun v w hv hw => statedSL3_transitive v w hv hw) hψ bot_le hN hn

include h464 h461 h465 in
theorem commutator_mem_zloc_of_mem_centerOf (hb4 : critDist (puAmalgam h.le) = 4)
    {g ρ y : Vtx (puAmalgam h.le)} (hg : IsMVtx _ g) (hgρ : (puAmalgam h.le).treeGraph.Adj g ρ)
    (hρy : (puAmalgam h.le).treeGraph.Adj ρ y) (hy : IsMVtx _ y) {z : 𝔘}
    (hzc : z ∈ centerOf (Vv (puAmalgam h.le) g)) (hzy : z ∈ ZM (puAmalgam h.le) y) {t : 𝔘}
    (ht : t ∈ Qv (puAmalgam h.le) g) : ⁅z, t⁆ ∈ Zloc h.le L g := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have hQg : Qv 𝔛 g ≤ Qv _ ρ := qv_le_qv _ h20 hg hgρ
  have hVQ : Vv 𝔛 g ≤ Qv _ g := vv_le_qv h hb hg
  have hQn := stab_le_normalizer_qv 𝔛 g
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) g
  set Y : Subgroup 𝔘 := Subgroup.closure {w | ∃ s ∈ Qv 𝔛 g, w = ⁅z, s⁆} with hYdef
  have hYZ : Y ≤ ZM 𝔛 g := by
    rw [hYdef, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact h465 g hg (Subgroup.commutator_mem_commutator hzc.1 hs)
  have hYρ : Y ≤ ZH 𝔛 ρ := by
    rw [hYdef, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    have := h464 y ρ hy hρy.symm
    rw [Usup, zv_of_isMVtx _ hy] at this
    exact this (Subgroup.commutator_mem_commutator hzy (hQg hs))
  have hYn : stab 𝔛 g ≤ Subgroup.normalizer (Y : Set 𝔘) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    rw [hYdef, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hc : k * z * k⁻¹ * z⁻¹ ∈ ZM 𝔛 g :=
      commutator_centerOf_stab_le h h461 h465 hfull hb hg hzc hk
    have hks : k * s * k⁻¹ ∈ Qv 𝔛 g := (Subgroup.mem_normalizer_iff.mp (hQn hk) s).mp hs
    have hzs : z * (k * s * k⁻¹) * z⁻¹ ∈ Qv 𝔛 g :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hVQ hzc.1) hks) (Subgroup.inv_mem _ (hVQ hzc.1))
    have e1 : z * (k * s * k⁻¹) * z⁻¹ * (k * z * k⁻¹ * z⁻¹) =
        k * z * k⁻¹ * z⁻¹ * (z * (k * s * k⁻¹) * z⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hg hc) _ hzs
    refine Subgroup.subset_closure ⟨k * s * k⁻¹, hks, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
    calc k * (z * s * z⁻¹ * s⁻¹) * k⁻¹
        = k * z * k⁻¹ * z⁻¹ * (z * (k * s * k⁻¹) * z⁻¹) * (k * z * k⁻¹ * z⁻¹)⁻¹ *
          (k * s * k⁻¹)⁻¹ := by group
      _ = z * (k * s * k⁻¹) * z⁻¹ * (k * z * k⁻¹ * z⁻¹) * (k * z * k⁻¹ * z⁻¹)⁻¹ *
          (k * s * k⁻¹)⁻¹ := by rw [← e1]
      _ = z * (k * s * k⁻¹) * z⁻¹ * (k * s * k⁻¹)⁻¹ := by group
  have hn : stab 𝔛 g ≤ Subgroup.normalizer ((Y ⊓ Uloc h.le L g : Subgroup 𝔘) : Set 𝔘) :=
    le_normalizer_of_map_conj_le fun k hk => (Subgroup.map_inf_le _ _ _).trans (le_of_eq (by
      rw [map_conj_eq_of_mem_normalizer (hYn hk), map_conj_eq_of_mem_normalizer (hUn hk)]))
  have hY : Y ⊓ Uloc h.le L g = ⊥ := by
    rcases eq_bot_or_eq_uloc_of_le h hφ hg inf_le_right hn with h0 | h1
    · exact h0
    · exfalso
      apply not_qv_le_qv_of_adj h hg hgρ
      obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hg
      intro s hs
      have hss : s ∈ stab 𝔛 g := qv_le_stab_of_adj _ hgρ.symm hs
      have h1' : toSL3 ψ ⟨s, hss⟩ = 1 := (toSL3_eq_one_iff hψ _).mpr fun u hu => by
        have huY : u ∈ Y ⊓ Uloc h.le L g := by rw [h1]; exact hu
        have e := Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ ρ (hYρ huY.1)) s hs
        change s * u * s⁻¹ = u
        rw [e, mul_inv_cancel_right]
      exact (toSL3_eq_one_iff_mem_qv h hφ hg hψ _).mp h1'
  have hYc : Y ≤ Subgroup.centralizer (stab 𝔛 g : Set 𝔘) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨u, hu, ζ, hζ, hwu⟩ := exists_uloc_mul_zloc h hfull hg (hYZ hw)
    have hζc : ζ * k⁻¹ = k⁻¹ * ζ := (Subgroup.mem_centralizer_iff.mp
      (zloc_le_centralizer_stab h hfull hg hζ) _ (Subgroup.inv_mem _ hk)).symm
    have e : k * w * k⁻¹ * w⁻¹ = k * u * k⁻¹ * u⁻¹ := by
      rw [hwu]
      calc k * (u * ζ) * k⁻¹ * (u * ζ)⁻¹ = k * u * (ζ * k⁻¹) * ζ⁻¹ * u⁻¹ := by group
        _ = k * u * k⁻¹ * u⁻¹ := by rw [hζc]; group
    have hmem : k * w * k⁻¹ * w⁻¹ ∈ Y ⊓ Uloc h.le L g := by
      refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hYn hk) w).mp hw)
        (Subgroup.inv_mem _ hw), ?_⟩
      rw [e]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hUn hk) u).mp hu)
        (Subgroup.inv_mem _ hu)
    rw [hY, Subgroup.mem_bot] at hmem
    have hkw : k * w * k⁻¹ = w := mul_inv_eq_one.mp hmem
    calc k * w = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [hkw]
  have hgen : ⁅z, t⁆ ∈ Y := Subgroup.subset_closure ⟨t, ht, rfl⟩
  exact zm_inf_centralizer_le_zloc h hφ hg ⟨hYZ hgen, hYc hgen⟩

include h464 hsq h466 h461 h465 in
theorem commutator_zm_qv_le_zloc (hb4 : critDist (puAmalgam h.le) = 4)
    (hW : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Zloc h.le L x)
    {y g : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y) (hg : IsMVtx _ g)
    (hd : (puAmalgam h.le).treeGraph.dist y g = 2) :
    ⁅ZM (puAmalgam h.le) y, Qv _ g⁆ ≤ Zloc h.le L g := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have h20 := h.hyp20
  by_cases hcr : ∃ δ, IsCritical 𝔛 y δ ∧ geo 𝔛 y δ 2 = g
  · obtain ⟨δ, hc, hgeo⟩ := hcr
    have h1 := usup_le_zloc_of_isCritical h hφ h464 hsq h466 h461 h465 hb4 hW hc
    have hadj : (puAmalgam h.le).treeGraph.Adj (geo 𝔛 y δ 1) g := by
      have := adj_geo_crit hb4 hc (i := 1) (by omega)
      rwa [hgeo] at this
    rw [hgeo, Usup, zv_of_isMVtx _ hy] at h1
    exact (Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hg hadj.symm)).trans h1
  · have hgen : critGen 𝔛 y g = ⊥ := le_bot_iff.mp (iSup₂_le fun δ hδ => (hcr ⟨δ, hδ⟩).elim)
    have hVQ : Vv 𝔛 g ≤ Qv _ y := by
      have := vv_le_critGen_sup h20 hC hb4 hg hd
      rwa [hgen, bot_sup_eq] at this
    have hZc : ZM 𝔛 y ≤ centerOf (Vv _ g) :=
      le_inf (zm_le_vv_of_dist_le_two hy (by rw [tdist_comm]; omega))
        ((zm_le_centralizer_qv _ h20 hy).trans (Subgroup.centralizer_le hVQ))
    have hρ : (puAmalgam h.le).treeGraph.Adj y (geo 𝔛 y g 1) := adj_geo_one _ (by omega)
    have hρg : (puAmalgam h.le).treeGraph.Adj (geo 𝔛 y g 1) g := by
      have := adj_geo (puAmalgam h.le) (u := y) (w := g) (i := 1) (by omega)
      rwa [geo_of_le (puAmalgam h.le) (by omega : (puAmalgam h.le).treeGraph.dist y g ≤ 1 + 1)]
        at this
    rw [Subgroup.commutator_le]
    intro z hz t ht
    exact commutator_mem_zloc_of_mem_centerOf h hφ h464 h461 h465 hb4 hg hρg.symm hρ.symm hy
      (hZc hz) hz ht

include h464 hsq h466 h461 h465 in
theorem commutator_vv_qv_le_zloc_of (hb4 : critDist (puAmalgam h.le) = 4)
    (hW : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Zloc h.le L x)
    {g : Vtx (puAmalgam h.le)} (hg : IsMVtx _ g) :
    ⁅Vv (puAmalgam h.le) g, Qv _ g⁆ ≤ Zloc h.le L g := by
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have hN : stab 𝔛 g ≤ Subgroup.normalizer (Zloc h.le L g : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) g
  have hVs : Vv 𝔛 g ≤ stab _ g := (vv_le_qv h hb hg).trans (qv_le_stab _ g)
  rw [vv_eq_iSup_vv hg]
  refine commutator_iSup₂_le_of (fun ρ hρ => ?_) fun ρ hρ =>
    ((vv_le_vv_of_adj h hg hρ).trans hVs).trans hN
  have hρH : ¬ IsMVtx 𝔛 ρ := (isMVtx_iff_of_adj _ hρ).mp hg
  have hVρ : Vv 𝔛 ρ ≤ Vv 𝔛 g := vv_le_vv_of_adj h hg hρ
  have hyM : ∀ y, (puAmalgam h.le).treeGraph.Adj ρ y → IsMVtx 𝔛 y := fun y hy => by
    have := isMVtx_iff_of_adj _ hy
    tauto
  rw [vv_eq_iSup_of_not_isMVtx hρH]
  refine commutator_iSup₂_le_of (fun y hy => ?_) fun y hy =>
    (((zm_le_vv_of_adj hy (hyM y hy)).trans hVρ).trans hVs).trans hN
  by_cases hyg : y = g
  · subst hyg
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (zm_le_centralizer_qv _ h20 hg)]
    exact bot_le
  · have hd : (puAmalgam h.le).treeGraph.dist y g = 2 := by
      have htri := dist_triangle (puAmalgam h.le) y ρ g
      rw [dist_eq_one_of_adj _ (show (puAmalgam h.le).treeGraph.Adj y ρ from hy.symm),
        dist_eq_one_of_adj _ (show (puAmalgam h.le).treeGraph.Adj ρ g from hρ.symm)] at htri
      have h0 : (puAmalgam h.le).treeGraph.dist y g ≠ 0 := fun h0 =>
        hyg ((dist_eq_zero_iff _).mp h0)
      have h1 : (puAmalgam h.le).treeGraph.dist y g ≠ 1 := fun h1 => by
        have := isMVtx_iff_of_adj _ (SimpleGraph.dist_eq_one_iff_adj.mp h1)
        have := hyM y hy
        tauto
      omega
    exact commutator_zm_qv_le_zloc h hφ h464 hsq h466 h461 h465 hb4 hW (hyM y hy) hg hd

include h464 hsq h466 h461 h465 in
theorem false_of_commutator_vv_le_zloc (h43 : S43) (hmin : PUMin M T L)
    (h462 : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As →
        ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Uloc h.le L x)
    (hb4 : critDist (puAmalgam h.le) = 4)
    (hW : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Zloc h.le L x) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have h20 := h.hyp20
  have hb : 2 < critDist 𝔛 := by omega
  have h463 : ∀ x : Vtx 𝔛, IsMVtx _ x → ⁅Vv 𝔛 x, Vv _ x⁆ ≤ ZM _ x := fun x hx =>
    (hW x hx).trans (zloc_le_zm h hfull hx)
  have hcomm : ∀ x y : Vtx 𝔛, IsMVtx _ x → IsMVtx _ y → (puAmalgam h.le).treeGraph.dist x y = 2 →
      ⁅Vv 𝔛 x ⊓ Qv _ y, critGen _ x y⁆ ≤ Bloc h.le L x := by
    intro x y hx hy hd
    have hxρ : (puAmalgam h.le).treeGraph.Adj x (geo 𝔛 x y 1) := adj_geo_one _ (by omega)
    have hρy : (puAmalgam h.le).treeGraph.Adj (geo 𝔛 x y 1) y := by
      have := adj_geo (puAmalgam h.le) (u := x) (w := y) (i := 1) (by omega)
      rwa [geo_of_le (puAmalgam h.le) (by omega : (puAmalgam h.le).treeGraph.dist x y ≤ 1 + 1)]
        at this
    calc ⁅Vv 𝔛 x ⊓ Qv _ y, critGen _ x y⁆ ≤ ⁅Qv 𝔛 y, Vv _ y⁆ :=
          Subgroup.commutator_mono inf_le_right (critGen_le_vv hb4 x y)
      _ = ⁅Vv 𝔛 y, Qv _ y⁆ := Subgroup.commutator_comm _ _
      _ ≤ Zloc h.le L y := commutator_vv_qv_le_zloc_of h hφ h464 hsq h466 h461 h465 hb4 hW hy
      _ ≤ ZH 𝔛 (geo 𝔛 x y 1) := zloc_le_zh h hfull hy hρy.symm
      _ ≤ ZM 𝔛 x := zh_le_zm _ hxρ
      _ ≤ Bloc h.le L x := zm_le_bloc h hb hx
  have key : ∀ z : Vtx 𝔛, IsMVtx _ z → (∃ As, IsOffenderOn 𝔛 z (Bloc h.le L z) As) → False := by
    rintro z hz ⟨As, hA⟩
    apply commutator_vv_ne_bot h hC h43 hmin hfull hb4 hz
    rw [eq_bot_iff, ← uloc_inf_zloc h hfull z]
    exact le_inf (h462 z As hz hA) (hW z hz)
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h20 (isMVtx_baseA 𝔛)
  rcases exists_offender_bloc h hC h43 hmin hfull hb4 h463 hcomm hc with hoff | hoff
  · exact key _ hc.1 hoff
  · exact key _ (isMVtx_geo_two' hb4 hc) hoff

end Main

end CFSG.Quasithin.MS93.S46.I466b

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem i466b_of (h43 : S43) (h461 : I461) (h462 : I462) (h463 : I463) (h464 : I464)
    (h465 : I465) (h466a : I466a) : I466b := by
  intro G _ _ M T L F _ _ φ c α hα hle
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  refine I466b.false_of_commutator_vv_le_zloc c.pu c.via
    (fun δ ρ hδ hδρ => h464 G M T L F φ c δ ρ hδ hδρ)
    (fun δ ρ hδ hδρ => (h465 G M T L F φ c δ ρ hδ hδρ).1)
    (fun δ ρ hδ hδρ => h466a G M T L F φ c δ ρ hδ hδρ)
    (fun x hx => h461 G M T L F φ c x hx) (fun x hx => ?_) h43 c.min
    (fun x As hx hA => h462 G M T L F φ c x As hx hA) c.b4 (fun x hx => ?_)
  · obtain ⟨β, hβ⟩ := exists_adj _ x
    exact (h465 G M T L F φ c x β hx hβ).2.2
  · exact (le_inf (h463 G M T L F φ c x hx).2
      (I466b.commutator_vv_le_centralizer_stab c.pu hα hle hx)).trans
      (I466b.zm_inf_centralizer_le_zloc c.pu c.via hx)

end CFSG.Quasithin.MS93.S46
