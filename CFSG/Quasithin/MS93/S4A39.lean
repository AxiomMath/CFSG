module

public import CFSG.Quasithin.MS93.S4A35

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Joins

variable {G : Type*} [Group G]

theorem commutator_iSup_le_of {ι : Type*} {A : ι → Subgroup G} {H N : Subgroup G}
    (hA : ∀ i, ⁅A i, H⁆ ≤ N) (hN : (⨆ i, A i) ≤ Subgroup.normalizer (N : Set G)) :
    ⁅⨆ i, A i, H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.iSup_eq_closure] at hx
  have hN' : Subgroup.closure (⋃ i, (A i : Set G)) ≤ Subgroup.normalizer (N : Set G) := by
    rw [← Subgroup.iSup_eq_closure]
    exact hN
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact hA i (Subgroup.commutator_mem_commutator hi hy)
  | one => simp
  | mul a b ha hb iha ihb =>
    have hrw : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN' ha) _).mp ihb) iha
  | inv a ha iha =>
    have hrw : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN' ha)) _).mp (N.inv_mem iha)

theorem le_centerOf_of_triple {ι : Type*} {A : ι → Subgroup G}
    (h3 : ∀ i j k, ⁅⁅A i, A j⁆, A k⁆ = ⊥) :
    ⁅⨆ i, A i, ⨆ i, A i⁆ ≤ centerOf (⨆ i, A i) := by
  set V := ⨆ i, A i with hV
  have hcen : ∀ i j, ⁅A i, A j⁆ ≤ centerOf V := by
    intro i j
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      have hx' : x ∈ V := le_iSup A i hx
      have hy' : y ∈ V := le_iSup A j hy
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem hx' hy') (V.inv_mem hx')) (V.inv_mem hy')
    rw [hV, Subgroup.le_centralizer_iff]
    refine iSup_le fun k => ?_
    rw [← Subgroup.le_centralizer_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h3 i j k
  have hnorm : V ≤ Subgroup.normalizer (centerOf V : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hzV, hzc⟩
      have hc := Subgroup.mem_centralizer_iff.mp hzc v hv
      refine ⟨?_, ?_⟩
      · rw [hc, mul_inv_cancel_right]
        exact hzV
      · rw [hc, mul_inv_cancel_right]
        exact hzc
    · rintro ⟨hzV, hzc⟩
      have hzV' : z ∈ V := by
        have := V.mul_mem (V.mul_mem (V.inv_mem hv) hzV) hv
        simpa [mul_assoc] using this
      have hc := Subgroup.mem_centralizer_iff.mp hzc v hv
      refine ⟨hzV', Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hzc w hw
      have h2 : v * z = z * v := by
        have e : v * (v * z * v⁻¹) = v * z * v⁻¹ * v := hc
        calc v * z = v⁻¹ * (v * (v * z * v⁻¹)) * v := by group
          _ = v⁻¹ * (v * z * v⁻¹ * v) * v := by rw [e]
          _ = z * v := by group
      have h3 : v * z * v⁻¹ = z := by rw [h2, mul_inv_cancel_right]
      rw [h3] at h1
      exact h1
  refine commutator_iSup_le_of (fun i => ?_) hnorm
  rw [Subgroup.commutator_comm]
  exact commutator_iSup_le_of (fun j => hcen j i) hnorm

end Joins

section S39

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem natImage_mono {K : Subgroup G} {F : Type} [Field F] {φ : ↥K →* ↥(StatedSL 3 F)}
    {A B : Subgroup G} (hAB : A ≤ B) : natImage φ A ≤ natImage φ B :=
  Subgroup.map_mono fun _ hx => hAB hx

theorem triple_commutator_zm_eq_bot (h : PUHyp M T L) (hC : CentHyp (puAmalgam h.le))
    (hb4 : critDist (puAmalgam h.le) = 4) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α δ₁ δ₂ δ₃ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hδ₁ : IsMVtx _ δ₁) (hδ₂ : IsMVtx _ δ₂) (hδ₃ : IsMVtx _ δ₃)
    (hd₁ : (puAmalgam h.le).treeGraph.dist α δ₁ = 2)
    (hd₂ : (puAmalgam h.le).treeGraph.dist α δ₂ = 2)
    (hd₃ : (puAmalgam h.le).treeGraph.dist α δ₃ = 2) :
    ⁅⁅ZM (puAmalgam h.le) δ₁, ZM _ δ₂⁆, ZM _ δ₃⁆ = ⊥ := by
  have h20 := h.hyp20
  have hb : 0 < critDist (puAmalgam h.le) := h.critDist_pos
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hZQ : ∀ {δ}, IsMVtx (puAmalgam h.le) δ → (puAmalgam h.le).treeGraph.dist α δ = 2 →
      ZM (puAmalgam h.le) δ ≤ Qv (puAmalgam h.le) α := fun hδ hd =>
    zm_le_qv_of_dist_lt (puAmalgam h.le) hδ (by rw [tdist_comm]; omega)
  have hQs : ∀ {ε}, (puAmalgam h.le).treeGraph.dist α ε = 2 →
      Qv (puAmalgam h.le) α ≤ stab (puAmalgam h.le) ε := fun hd =>
    qv_le_stab_of_dist_le_two (puAmalgam h.le) h20 hα hd.le
  have hX1 : ⁅ZM (puAmalgam h.le) δ₁, ZM (puAmalgam h.le) δ₂⁆ ≤ ZM (puAmalgam h.le) δ₁ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((hZQ hδ₂ hd₂).trans (hQs hd₁)).trans (stab_le_normalizer_zm (puAmalgam h.le) δ₁))
  have hX2 : ⁅ZM (puAmalgam h.le) δ₁, ZM (puAmalgam h.le) δ₂⁆ ≤ ZM (puAmalgam h.le) δ₂ :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (((hZQ hδ₁ hd₁).trans (hQs hd₂)).trans (stab_le_normalizer_zm (puAmalgam h.le) δ₂))
  by_contra hne
  have hXQ : ¬ ⁅ZM (puAmalgam h.le) δ₁, ZM (puAmalgam h.le) δ₂⁆ ≤ Qv (puAmalgam h.le) δ₃ := by
    intro hle
    apply hne
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono hle le_rfl).trans ?_
    rw [Subgroup.commutator_comm, commutator_zm_qv (puAmalgam h.le) h20 hδ₃]
  obtain ⟨x, hxX, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hXQ
  have hcrit : ∀ {δ}, IsMVtx (puAmalgam h.le) δ → (puAmalgam h.le).treeGraph.dist α δ = 2 →
      ¬ ZM (puAmalgam h.le) δ ≤ Qv (puAmalgam h.le) δ₃ →
      IsCritical (puAmalgam h.le) δ δ₃ := by
    intro δ hδ hd hZ
    refine ⟨hδ, ?_, hZ⟩
    have hle : (puAmalgam h.le).treeGraph.dist δ δ₃ ≤ 4 := by
      have := dist_triangle (puAmalgam h.le) δ α δ₃
      rw [tdist_comm (puAmalgam h.le) δ α] at this
      omega
    by_contra hneq
    exact hZ (zm_le_qv_of_dist_lt (puAmalgam h.le) hδ (by omega))
  have hc₁ := hcrit hδ₁ hd₁ fun hle => hXQ (hX1.trans hle)
  have hc₂ := hcrit hδ₂ hd₂ fun hle => hXQ (hX2.trans hle)
  obtain ⟨ψ₃, -, hψ₃⟩ := exists_natural_Uloc h hφ hδ₃
  obtain ⟨ψ₁, -, hψ₁⟩ := exists_natural_Uloc h hφ hδ₁
  obtain ⟨ψ₂, -, hψ₂⟩ := exists_natural_Uloc h hφ hδ₂
  obtain ⟨hf₁, hcard₁, ha₁, -⟩ := s35_core h hC hφ hc₁ hψ₁ hψ₃
  obtain ⟨hf₂, hcard₂, ha₂, -⟩ := s35_core h hC hφ hc₂ hψ₂ hψ₃
  set E₁ := natImage ψ₃ (ZM (puAmalgam h.le) δ₁) with hE₁
  set E₂ := natImage ψ₃ (ZM (puAmalgam h.le) δ₂) with hE₂
  have hE₁card : Nat.card ↥E₁ = Nat.card F ^ (3 - Module.finrank F (fixN E₁)) := by
    rw [hcard₁, ha₁, hf₁]
  have hE₂card : Nat.card ↥E₂ = Nat.card F ^ (3 - Module.finrank F (fixN E₂)) := by
    rw [hcard₂, ha₂, hf₂]
  have hβ₃ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α δ₃ 1) :=
    adj_geo_one (puAmalgam h.le) (by omega)
  have hβδ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α δ₃ 1) δ₃ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := δ₃) (i := 1) (by omega)
    rwa [show geo (puAmalgam h.le) α δ₃ (1 + 1) = δ₃ from geo_of_le (puAmalgam h.le) (by omega)]
      at this
  have hQαβ : Qv (puAmalgam h.le) α ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α δ₃ 1) :=
    qv_le_qv (puAmalgam h.le) h20 hα hβ₃
  have hβs : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α δ₃ 1) ≤ stab (puAmalgam h.le) δ₃ :=
    qv_le_stab_of_adj (puAmalgam h.le) hβδ
  have hβH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α δ₃ 1) := by
    rw [← isMVtx_iff_of_adj (puAmalgam h.le) hβ₃]
    exact hα
  set S := natImage ψ₃ (Qv (puAmalgam h.le) (geo (puAmalgam h.le) α δ₃ 1)) with hS
  have hS2 : IsPGroup 2 ↥S := by
    have hT : IsPGroup 2 ↥((Qv (puAmalgam h.le) (geo (puAmalgam h.le) α δ₃ 1)).subgroupOf
        (stab (puAmalgam h.le) δ₃)) :=
      (isPGroup_qv (puAmalgam h.le) h20 hβH).of_equiv (Subgroup.subgroupOfEquivOfLe hβs).symm
    exact hT.map _
  have hE₁S : E₁ ≤ S := natImage_mono ((hZQ hδ₁ hd₁).trans hQαβ)
  have hE₂S : E₂ ≤ S := natImage_mono ((hZQ hδ₂ hd₂).trans hQαβ)
  have hZ₁s : ZM (puAmalgam h.le) δ₁ ≤ stab (puAmalgam h.le) δ₃ := (hZQ hδ₁ hd₁).trans (hQs hd₃)
  have hZ₂s : ZM (puAmalgam h.le) δ₂ ≤ stab (puAmalgam h.le) δ₃ := (hZQ hδ₂ hd₂).trans (hQs hd₃)
  have hnc : ∃ g₁ ∈ E₁, ∃ g₂ ∈ E₂, g₁ * g₂ ≠ g₂ * g₁ := by
    by_contra hall
    push Not at hall
    set K := (toSL3 ψ₃).ker.map (stab (puAmalgam h.le) δ₃).subtype with hK
    have hXK : ⁅ZM (puAmalgam h.le) δ₁, ZM (puAmalgam h.le) δ₂⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro z₁ hz₁ z₂ hz₂
      have hcm := hall _ (mem_natImage.mpr ⟨⟨z₁, hZ₁s hz₁⟩, hz₁, rfl⟩) _
        (mem_natImage.mpr ⟨⟨z₂, hZ₂s hz₂⟩, hz₂, rfl⟩)
      refine ⟨⁅(⟨z₁, hZ₁s hz₁⟩ : ↥(stab (puAmalgam h.le) δ₃)), ⟨z₂, hZ₂s hz₂⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcm
    obtain ⟨y, hy, hyx⟩ := hXK hxX
    apply hxQ
    have hyc := (toSL3_eq_one_iff hψ₃ y).mp hy
    have hxs : x ∈ stab (puAmalgam h.le) δ₃ := hyx ▸ y.2
    have hxc : x ∈ Subgroup.centralizer (ZM (puAmalgam h.le) δ₃ : Set (puAmalgam h.le).Universal) :=
        by
      refine (mem_centralizer_zm_iff h hfull hδ₃ hxs).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hyc u hu
      have hyx' : ((y : ↥(stab (puAmalgam h.le) δ₃)) : (puAmalgam h.le).Universal) = x := hyx
      rw [hyx'] at this
      calc u * x = x * u * x⁻¹ * x := by rw [this]
        _ = x * u := by group
    rw [← hC δ₃ _ hδ₃ hβδ.symm]
    exact ⟨hQαβ ((hZQ hδ₁ hd₁) (hX1 hxX)), hxc⟩
  have hcomm : ⁅E₁, E₂⁆ ≤ E₁ ⊓ E₂ := by
    rw [hE₁, hE₂, natImage, natImage, ← Subgroup.map_commutator,
      ← commutator_subgroupOf hZ₁s hZ₂s]
    exact le_inf (Subgroup.map_mono fun _ hz => hX1 hz) (Subgroup.map_mono fun _ hz => hX2 hz)
  obtain ⟨x₀, hx₀⟩ := exists_conj_le_sStar hS2
  set c := (MulAut.conj x₀).toMonoidHom with hc
  have hsq : ∀ {E : Subgroup (SL3 F)}, (∀ g ∈ E, g * g = 1) → ∀ g ∈ E.map c, g * g = 1 := by
    rintro E hE _ ⟨g, hg, rfl⟩
    rw [← map_mul, hE g hg, map_one]
  have hcm : ∀ {E : Subgroup (SL3 F)}, (∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) →
      ∀ g ∈ E.map c, ∀ g' ∈ E.map c, g * g' = g' * g := by
    rintro E hE _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [← map_mul, hE g hg g' hg', map_mul]
  have hcardc : ∀ E : Subgroup (SL3 F), Nat.card ↥(E.map c) = Nat.card ↥E := fun E =>
    Subgroup.card_map_of_injective (MulAut.conj x₀).injective
  refine false_of_noncommuting_elemAb (E₁ := E₁.map c) (E₂ := E₂.map c)
    ((Subgroup.map_mono hE₁S).trans hx₀) ((Subgroup.map_mono hE₂S).trans hx₀)
    (hsq (natImage_zm_sq h hδ₁)) (hcm (natImage_zm_comm h hδ₁))
    (hsq (natImage_zm_sq h hδ₂)) (hcm (natImage_zm_comm h hδ₂)) ?_ ?_ ?_ ?_
  · obtain ⟨g₁, hg₁, g₂, hg₂, hne'⟩ := hnc
    refine ⟨c g₁, ⟨g₁, hg₁, rfl⟩, c g₂, ⟨g₂, hg₂, rfl⟩, fun he => hne' ?_⟩
    rw [← map_mul, ← map_mul] at he
    exact (MulAut.conj x₀).injective he
  · rw [← Subgroup.map_commutator]
    exact (Subgroup.map_mono hcomm).trans (Subgroup.map_inf_le _ _ _)
  · rw [hcardc, finrank_fixN_map_conj]
    exact hE₁card
  · rw [hcardc, finrank_fixN_map_conj]
    exact hE₂card

theorem s39_of (h32 : S32) : S39 := by
  intro G _ _ M T L h hb4 hfull α hα
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have hC := centHyp_of_S32 h32 h
  have h20 := h.hyp20
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hVQ := vv_le_qv h hb2 hα
  have hZc : ZM (puAmalgam h.le) α ≤
      Subgroup.centralizer (Vv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    (zm_le_centralizer_qv (puAmalgam h.le) h20 hα).trans (Subgroup.centralizer_le hVQ)
  have hV : Vv (puAmalgam h.le) α =
      ⨆ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
        Zv (puAmalgam h.le) ρ := by
    rw [show Vv (puAmalgam h.le) α = Vi (puAmalgam h.le) α 2 from rfl]
    unfold Vi
    exact iSup_subtype'
  have hgen : ∀ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
      Zv (puAmalgam h.le) ρ ≤ ZM (puAmalgam h.le) α ∨
        (IsMVtx (puAmalgam h.le) ρ ∧ (puAmalgam h.le).treeGraph.dist α ρ = 2) := by
    rintro ⟨ρ, hρ⟩
    rcases isMVtx_of_dist_le_two h hα hρ with hρM | hadj
    · have hev : Even ((puAmalgam h.le).treeGraph.dist α ρ) :=
        (even_dist_iff (puAmalgam h.le) α ρ).mpr ⟨fun _ => hρM, fun _ => hα⟩
      rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist α ρ) 1 with h0 | h1
      · left
        have : ρ = α := ((dist_eq_zero_iff (puAmalgam h.le)).mp (Nat.lt_one_iff.mp h0)).symm
        subst this
        rw [zv_of_isMVtx (puAmalgam h.le) hρM]
      · right
        refine ⟨hρM, ?_⟩
        obtain ⟨k, hk⟩ := hev
        show (puAmalgam h.le).treeGraph.dist α ρ = 2
        omega
    · left
      have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by
        rw [← isMVtx_iff_of_adj (puAmalgam h.le) hadj]
        exact hα
      rw [zv_of_not_isMVtx (puAmalgam h.le) hρH]
      exact zh_le_zm (puAmalgam h.le) hadj
  have hmemV : ∀ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
      Zv (puAmalgam h.le) ρ ≤ Vv (puAmalgam h.le) α := fun ρ =>
    hV ▸ le_iSup (fun ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2} =>
      Zv (puAmalgam h.le) ρ) ρ
  rw [hV]
  refine le_centerOf_of_triple fun ρ₁ ρ₂ ρ₃ => ?_
  rcases hgen ρ₁ with h1 | ⟨hM1, hd1⟩
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((h1.trans hZc).trans (Subgroup.centralizer_le (hmemV ρ₂))), Subgroup.commutator_bot_left]
  rcases hgen ρ₂ with h2 | ⟨hM2, hd2⟩
  · rw [Subgroup.commutator_comm (Zv (puAmalgam h.le) (ρ₁ : Vtx (puAmalgam h.le))),
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((h2.trans hZc).trans (Subgroup.centralizer_le (hmemV ρ₁))), Subgroup.commutator_bot_left]
  rcases hgen ρ₃ with h3 | ⟨hM3, hd3⟩
  · have hXV : ⁅Zv (puAmalgam h.le) ρ₁, Zv (puAmalgam h.le) ρ₂⁆ ≤ Vv (puAmalgam h.le) α := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have ha' := hmemV ρ₁ ha
      have hb' := hmemV ρ₂ hb
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' hb')
        (Subgroup.inv_mem _ ha')) (Subgroup.inv_mem _ hb')
    rw [Subgroup.commutator_comm, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr]
    exact (h3.trans hZc).trans (Subgroup.centralizer_le hXV)
  rw [zv_of_isMVtx (puAmalgam h.le) hM1, zv_of_isMVtx (puAmalgam h.le) hM2,
    zv_of_isMVtx (puAmalgam h.le) hM3]
  exact triple_commutator_zm_eq_bot h hC hb4 hφ hα hM1 hM2 hM3 hd1 hd2 hd3

end S39

end CFSG.Quasithin.MS93
