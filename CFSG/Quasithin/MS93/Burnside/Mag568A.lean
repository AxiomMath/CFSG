module

public import CFSG.Quasithin.MS93.Burnside.SL3GZ461B
public import CFSG.Quasithin.MS93.S4A44Base

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem mag568_not_normal_sup (h : PUHyp M T L) {α γ δ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hδ : IsMVtx _ δ) (hαγ : (puAmalgam h.le).treeGraph.Adj α γ)
    (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ) {Y : Subgroup (puAmalgam h.le).Universal}
    (hY : Y ≤ ZM _ δ)
    (hn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer ((Y ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) : Set _)) :
    ⁅Y, Ltil h.le L α⁆ ≤ ZM _ α ∨ ⁅Y, Qv (puAmalgam h.le) α⁆ = ⊥ := by
  have h20 := h.hyp20
  have hKγ : Qv (puAmalgam h.le) δ ≤ Qv _ γ := qv_le_qv _ h20 hδ hγδ.symm
  have hKs : Qv (puAmalgam h.le) δ ≤ stab _ α := hKγ.trans (qv_le_stab_of_adj _ hαγ.symm)
  by_cases hQ : Qv (puAmalgam h.le) δ ≤ Qv _ α
  · right
    have hcard : Nat.card (Qv (puAmalgam h.le) δ) = Nat.card (Qv (puAmalgam h.le) α) := by
      obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
      obtain ⟨k, rfl⟩ := exists_eq_smul_baseA _ hα
      rw [qv_smul, qv_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (MulAut.conj k).injective]
    have hγH := (isMVtx_iff_of_adj _ hαγ).mp hα
    have : Finite (Qv (puAmalgam h.le) γ) := finite_qv _ h20 hγH
    have hαγQ : Qv (puAmalgam h.le) α ≤ Qv _ γ := qv_le_qv _ h20 hα hαγ
    have : Finite (Qv (puAmalgam h.le) α) :=
      Finite.of_injective (Subgroup.inclusion hαγQ) (Subgroup.inclusion_injective hαγQ)
    have heq : Qv (puAmalgam h.le) δ = Qv _ α := Subgroup.eq_of_le_of_card_ge hQ hcard.ge
    rw [← heq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hY.trans (zm_le_centralizer_qv _ h20 hδ)
  · left
    let D : Subgroup (puAmalgam h.le).Universal :=
      { carrier := {a | a ∈ stab (puAmalgam h.le) α ∧
          ∀ k ∈ Qv (puAmalgam h.le) δ, ⁅k, a⁆ ∈ ZM (puAmalgam h.le) α}
        mul_mem' := by
          rintro a c ⟨ha, haK⟩ ⟨hc, hcK⟩
          refine ⟨Subgroup.mul_mem _ ha hc, fun k hk => ?_⟩
          have e : ⁅k, a * c⁆ = ⁅k, a⁆ * (a * ⁅k, c⁆ * a⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact Subgroup.mul_mem _ (haK k hk)
            ((stab_le_normalizer_zm _ α ha _).mp (hcK k hk))
        one_mem' := ⟨Subgroup.one_mem _, fun k _ => by
          simp only [commutatorElement_def, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _⟩
        inv_mem' := by
          rintro a ⟨ha, haK⟩
          refine ⟨Subgroup.inv_mem _ ha, fun k hk => ?_⟩
          have e : ⁅k, a⁻¹⁆ = a⁻¹ * ⁅k, a⁆⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [e]
          have := (stab_le_normalizer_zm _ α (Subgroup.inv_mem _ ha) ⁅k, a⁆⁻¹).mp
            (Subgroup.inv_mem _ (haK k hk))
          simpa using this }
    have hZδs : ZM (puAmalgam h.le) δ ≤ stab _ α :=
      (zm_le_qv_self _ hδ h.critDist_pos).trans hKs
    have hYD : Y ≤ D := fun y hy => ⟨hZδs (hY hy), fun k hk => by
      have hc : k * y = y * k := (zm_le_centralizer_qv _ h20 hδ (hY hy)) k hk
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
      exact Subgroup.one_mem _⟩
    have hZD : ZM (puAmalgam h.le) α ≤ D := fun z hz =>
      ⟨((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α)) hz, fun k hk => by
        have h1 : k * z * k⁻¹ ∈ ZM (puAmalgam h.le) α :=
          (stab_le_normalizer_zm _ α (hKs hk) z).mp hz
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)⟩
    have hAK : ⁅Y ⊔ ZM (puAmalgam h.le) α, Qv (puAmalgam h.le) δ⁆ ≤ ZM _ α := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_le]
      intro k hk a ha
      exact (sup_le hYD hZD ha).2 k hk
    have hL := S34F.commutator_ltil_le_of_commutator_le_gen h hα hαγ hn
      (stab_le_normalizer_zm _ α) hAK hKγ hQ
    exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hL

@[expose] def mag568_Bad (h : PUHyp M T L) : Prop :=
  ∀ α : Vtx (puAmalgam h.le), IsMVtx _ α →
    ¬ ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α

@[expose] def mag568_IsLine (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le))
    (Z : Subgroup (puAmalgam h.le).Universal) : Prop :=
  Z ≤ Uloc h.le L δ ∧ ∀ x ∈ S34F.flat h δ, x ∈ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal) →
    IsPGroup 2 (Subgroup.zpowers x) → x ∈ Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal)

noncomputable def mag568_zE (h : PUHyp M T L) (E : Subgroup (puAmalgam h.le).Universal)
    (g : (puAmalgam h.le).Universal) : Subgroup (puAmalgam h.le).Universal :=
  (Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).map (MulAut.conj g).toMonoidHom

theorem burnsideMag568_zE_def (h : PUHyp M T L) (E : Subgroup (puAmalgam h.le).Universal)
    (g : (puAmalgam h.le).Universal) :
    mag568_zE h E g = (Uloc h.le L (baseA _) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).map (MulAut.conj g).toMonoidHom := by
  rw [mag568_zE]

@[expose] def mag568_RG (h : PUHyp M T L) (Z : Subgroup (puAmalgam h.le).Universal) : Prop :=
  ∃ μ, IsCritical (puAmalgam h.le) (baseA _) μ ∧ ZM _ μ ≤ Qv _ (baseB _) ∧
    (⁅Uloc h.le L (baseA _), ZM _ μ⁆ = Z ∨
      ∃ μ', IsCritical (puAmalgam h.le) (baseA _) μ' ∧ ZM _ μ' ≤ Qv _ (baseB _) ∧
        Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (ZM _ μ : Set (puAmalgam h.le).Universal) =
          Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (ZM _ μ' : Set (puAmalgam h.le).Universal) ∧
        Z ≤ Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (ZM _ μ : Set (puAmalgam h.le).Universal) ∧
        ⁅Uloc h.le L (baseA _), ZM _ μ⁆ ≠ ⁅Uloc h.le L (baseA _), ZM _ μ'⁆)

theorem mag568_mem_normalizer_centralizer {K : Type*} [Group K] {E : Subgroup K} {y : K}
    (hy : y ∈ Subgroup.normalizer (E : Set K)) :
    y ∈ Subgroup.normalizer (Subgroup.centralizer (E : Set K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro z
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hz e he
    have he' : y⁻¹ * e * y ∈ E := (hy _).mpr (by simpa [mul_assoc] using he)
    have := hz _ he'
    calc e * (y * z * y⁻¹) = y * ((y⁻¹ * e * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * e * y)) * y⁻¹ := by rw [this]
      _ = y * z * y⁻¹ * e := by group
  · intro hz e he
    have h' : y * (e * z) * y⁻¹ = y * (z * e) * y⁻¹ :=
      calc y * (e * z) * y⁻¹ = (y * e * y⁻¹) * (y * z * y⁻¹) := by group
        _ = (y * z * y⁻¹) * (y * e * y⁻¹) := hz _ ((hy e).mp he)
        _ = y * (z * e) * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')

theorem mag568_conj_mem_normalizer_map {K : Type*} [Group K] {H : Subgroup K} {y : K} (g : K)
    (hy : y ∈ Subgroup.normalizer (H : Set K)) :
    g * y * g⁻¹ ∈ Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup K) : Set K) := by
  have key : ∀ w, w ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ H := by
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [mul_assoc] using hu
    · intro hw
      exact ⟨_, hw, by simp [mul_assoc]⟩
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro w
  rw [key, key, hy (g⁻¹ * w * g)]
  rw [show g⁻¹ * (g * y * g⁻¹ * w * (g * y * g⁻¹)⁻¹) * g = y * (g⁻¹ * w * g) * y⁻¹ by group]

theorem mag568_gamma_ne_geo_one (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {E : Subgroup (puAmalgam h.le).Universal}
    (hEf : E ≤ S34F.flat h (baseA _)) (hET : Qv _ (baseB _) ≤ Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    (hline : mag568_IsLine h (baseA _)
      (Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {g : (puAmalgam h.le).Universal} (hg : g • baseB (puAmalgam h.le) = geo _ α α' 1)
    (hgα : g • baseA (puAmalgam h.le) ≠ α) :
    ZM _ α' ≤ Subgroup.normalizer ((mag568_zE h E g ⊔ ZM _ α : Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := h.critDist_pos
  have hα'M : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hd1 : (puAmalgam h.le).treeGraph.dist α' (geo _ α α' 1) < critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by rw [hc.2.1]; omega), hc.2.1]; omega
  have hZq : ZM _ α' ≤ Qv _ (geo _ α α' 1) := zm_le_qv_of_dist_lt _ hα'M hd1
  have hadj : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 1) α :=
    (adj_geo_one _ (by rw [hc.2.1]; omega)).symm
  intro x hx
  refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, ?_⟩
  ·
    have hxq := hZq hx
    rw [← hg, qv_smul] at hxq
    obtain ⟨y, hy, rfl⟩ := hxq
    have hyU : y ∈ Subgroup.normalizer (Uloc h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
      S4A.stab_le_normalizer_uloc h _ (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm hy)
    have hyZ : y ∈ Subgroup.normalizer ((Uloc h.le L (baseA _) ⊓
        Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) : Subgroup _) : Set _) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hyU, mag568_mem_normalizer_centralizer (hET hy)⟩
    simpa [mag568_zE] using mag568_conj_mem_normalizer_map g hyZ
  · exact stab_le_normalizer_zm _ α (qv_le_stab_of_adj _ hadj (hZq hx))

theorem mag568_le_qv_alpha'_sub_two (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    {α α' δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hδ : (puAmalgam h.le).treeGraph.dist α δ = 2)
    (hδ' : (puAmalgam h.le).treeGraph.dist δ α' = critDist (puAmalgam h.le) + 2)
    {Z : Subgroup (puAmalgam h.le).Universal} (hZ : mag568_IsLine h δ Z)
    (hZn : Qv (puAmalgam h.le) (geo _ δ α 1) ≤ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal)) :
    Z ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := by
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := h.critDist_pos
  have hαα' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm]; exact hc.2.1
  have hα'M : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hδM : IsMVtx _ δ := ((even_dist_iff _ α δ).mp (by rw [hδ]; exact even_two)).mp hc.1
  have hν1 : (puAmalgam h.le).treeGraph.dist α' (geo _ α' α 2) = 2 := dist_geo _ (by omega)
  have hν2 : (puAmalgam h.le).treeGraph.dist (geo _ α' α 2) α = critDist (puAmalgam h.le) - 2 :=
    by rw [dist_geo_right _ (by omega), hαα']
  have hε2 : (puAmalgam h.le).treeGraph.dist (geo _ α' α 3) α = critDist (puAmalgam h.le) - 3 :=
    by rw [dist_geo_right _ (by omega), hαα']
  have hνM : IsMVtx _ (geo _ α' α 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'M⟩
  have hadj : (puAmalgam h.le).treeGraph.Adj (geo _ α' α 2) (geo _ α' α 3) :=
    adj_geo _ (i := 2) (by omega)
  have hδα : (puAmalgam h.le).treeGraph.dist δ α = 2 := by rw [SimpleGraph.dist_comm]; exact hδ
  have hZδ : Z ≤ ZM _ δ := hZ.1.trans (S34F.uloc_le_zm' h hδM)
  have hZε : Z ≤ Qv _ (geo _ α' α 3) := by
    refine hZδ.trans (zm_le_qv_of_dist_lt _ hδM ?_)
    have := dist_triangle _ δ α (geo _ α' α 3)
    rw [SimpleGraph.dist_comm (u := α), hε2, hδα] at this
    omega
  by_cases hle : ZM _ δ ≤ Qv _ (geo _ α' α 2)
  · exact hZδ.trans hle
  have hδν : (puAmalgam h.le).treeGraph.dist δ (geo _ α' α 2) = critDist (puAmalgam h.le) := by
    have h1 := dist_triangle _ δ α (geo _ α' α 2)
    have h2 := dist_triangle _ δ (geo _ α' α 2) α'
    rw [SimpleGraph.dist_comm (u := α), hν2, hδα] at h1
    rw [SimpleGraph.dist_comm (u := geo _ α' α 2), hν1, hδ'] at h2
    omega
  have hcν : IsCritical _ (geo _ α' α 2) δ := ms22_iii _ h20 hb0 hC ⟨hδM, hδν, hle⟩
  have hflat := S34F.zm_le_flat h hU hcν
  have hγα : (puAmalgam h.le).treeGraph.dist (geo _ δ α 1) α = 1 := by
    rw [dist_geo_right _ (by omega), hδα]
  have hνγ : ZM _ (geo _ α' α 2) ≤ Qv _ (geo _ δ α 1) := by
    refine zm_le_qv_of_dist_lt _ hνM ?_
    have := dist_triangle _ (geo _ α' α 2) α (geo _ δ α 1)
    rw [SimpleGraph.dist_comm (u := α), hν2, hγα] at this
    omega
  have hγ : ¬ IsMVtx _ (geo _ δ α 1) := by
    rw [isMVtx_geo _ (by omega)]
    exact fun hi => Nat.not_even_one (hi.mp hδM)
  have hp := isPGroup_qv _ h20 hγ
  have hcent : ZM _ (geo _ α' α 2) ≤ Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal) :=
    fun x hx => hZ.2 x (hflat hx) (hZn (hνγ hx))
      (hp.to_le ((Subgroup.zpowers_le).mpr (hνγ hx)))
  rw [← hC _ _ hνM hadj]
  exact le_inf hZε (Subgroup.le_centralizer_iff.mpr hcent)

theorem mag568_false_of_crit_delta (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le)) (hbad : mag568_Bad h)
    {α α' δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hδ : (puAmalgam h.le).treeGraph.dist α δ = 2)
    (hδ' : (puAmalgam h.le).treeGraph.dist δ α' = critDist (puAmalgam h.le) + 2)
    (hcδ : IsCritical (puAmalgam h.le) δ (geo _ α' α 2))
    {Z : Subgroup (puAmalgam h.le).Universal}
    (hZ : Z ≤ Uloc h.le L δ ⊓ Qv (puAmalgam h.le) (geo _ α' α 2)) :
    ⁅Z, ZM _ α'⁆ = ⊥ := by
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := h.critDist_pos
  have hc' : IsCritical (puAmalgam h.le) (geo _ α' α 2) δ := ms22_iii _ h20 hb0 hC hcδ
  have hF := burnsideSL3G_uloc_inf_qv_le_centerOf h hU (by omega) hc' (hbad _ hc'.1)
  have hd : (puAmalgam h.le).treeGraph.dist α' (geo _ α' α 2) = 2 :=
    dist_geo _ (by rw [SimpleGraph.dist_comm, hc.2.1]; omega)
  have hZv : ZM (puAmalgam h.le) α' ≤ burnsideSL3G_vb (puAmalgam h.le) (geo _ α' α 2) := by
    have := le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.dist (geo _ α' α 2) ρ ≤ critDist (puAmalgam h.le) - 2}) =>
        Zv (puAmalgam h.le) ρ) α'
      (show (puAmalgam h.le).treeGraph.dist (geo _ α' α 2) α' ≤ critDist (puAmalgam h.le) - 2 by
        rw [SimpleGraph.dist_comm, hd]; omega) le_rfl
    rwa [zv_of_isMVtx _ (hc.isMVtx_right _ h20)] at this
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact ((hZ.trans hF).trans inf_le_right).trans (Subgroup.centralizer_le hZv)

end CFSG.Quasithin.MS93.S4L
