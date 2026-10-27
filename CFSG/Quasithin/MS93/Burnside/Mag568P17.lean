module

public import CFSG.Quasithin.MS93.Burnside.Mag568Coord
public import CFSG.Quasithin.MS93.S46TypeLin

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideMag568_natImage_mono {Γ : Type} [Group Γ] {K : Subgroup Γ} {F : Type} [Field F]
    (ψ : ↥K →* ↥(StatedSL 3 F)) {A B : Subgroup Γ} (hAB : A ≤ B) :
    natImage ψ A ≤ natImage ψ B :=
  Subgroup.map_mono fun _ hx => hAB hx

theorem burnsideMag568_commutator_le_of_flat_plane (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hbad : mag568_Bad h)
    {α α' δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hδ : (puAmalgam h.le).treeGraph.dist α δ = 2)
    (hZδ : ZM _ δ ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2))
    (hB : ¬ ⁅⁅ZM _ δ, Qv (puAmalgam h.le) α⁆, ZM _ α'⁆ ≤ ZM _ α) :
    ⁅ZM _ δ, ZM _ α'⁆ ≤ ⁅⁅ZM _ δ, Qv (puAmalgam h.le) α⁆, ZM _ α'⁆ ⊔ ZM _ α := by
  have h20 := h.hyp20
  have hC := h.centHyp
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα'M : IsMVtx _ α' := hc'.1
  have hdα'α : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
  set ε := geo (puAmalgam h.le) α' α 1 with hεdef
  set ν := geo (puAmalgam h.le) α' α 2 with hνdef
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' ε := adj_geo_one_of_isCritical _ hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) ε := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hα'M
  have hνε : (puAmalgam h.le).treeGraph.Adj ν ε := (adj_geo _ (i := 1) (by omega)).symm
  have hνM : IsMVtx (puAmalgam h.le) ν := by
    rw [hνdef, isMVtx_geo _ (by omega)]
    exact ⟨fun _ => even_two, fun _ => hα'M⟩
  have hδM : IsMVtx (puAmalgam h.le) δ :=
    ((even_dist_iff _ α δ).mp (by rw [hδ]; exact even_two)).mp hα
  have hZδε : ZM (puAmalgam h.le) δ ≤ Qv _ ε := hZδ.trans (qv_le_qv _ h20 hνM hνε)
  have hZδα : ZM (puAmalgam h.le) δ ≤ Qv _ α :=
    zm_le_qv_of_dist_lt _ hδM (by rw [tdist_comm, hδ]; omega)
  obtain ⟨hReq, hRle⟩ := critR_eq_commutator_uloc_right h hC hc
  have hRZ : critR (puAmalgam h.le) α α' ≤ ZM _ α := hRle.trans inf_le_right
  have hZδC : ZM (puAmalgam h.le) δ ≤
      Subgroup.centralizer (critR (puAmalgam h.le) α α' : Set _) :=
    (hZδα.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα))).trans
      (Subgroup.centralizer_le hRZ)
  have hZδf : ZM (puAmalgam h.le) δ ≤ flat h α' :=
    (le_inf hZδε hZδC).trans (qv_inf_centralizer_critR_le_flat h hU hc)
  set B := ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ with hBdef
  have hBZ : B ≤ ZM (puAmalgam h.le) δ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_dist_le_two _ h20 hα hδ.le).trans (stab_le_normalizer_zm _ δ))
  have hBε : B ≤ Qv _ ε := hBZ.trans hZδε
  have hBf : B ≤ flat h α' := hBZ.trans hZδf
  have hZαε : ZM (puAmalgam h.le) α ≤ Qv _ ε := zm_le_qv_geo_one_left _ h20 hb0 hC hc
  have hZαf : ZM (puAmalgam h.le) α ≤ flat h α' := zm_le_flat h hU hc
  have hcomδ : ⁅ZM (puAmalgam h.le) δ, ZM _ α'⁆ = ⁅Uloc h.le L α', ZM (puAmalgam h.le) δ⁆ := by
    rw [Subgroup.commutator_comm, commutator_zm_eq_commutator_uloc_of_le_qv h hα'M hα'ε hZδε]
  have hcomB : ⁅B, ZM (puAmalgam h.le) α'⁆ = ⁅Uloc h.le L α', B⁆ := by
    rw [Subgroup.commutator_comm, commutator_zm_eq_commutator_uloc_of_le_qv h hα'M hα'ε hBε]
  obtain ⟨n, F, _, _, φ, hcardF, hφs, hnat⟩ := exists_natural_flat h hU
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcardF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  obtain ⟨ψ, -, hψ⟩ := exists_natural_flat_at h hφs hnat hα'M
  obtain ⟨-, hRw, -⟩ := burnsideMag568_rootGroup h hU (by omega) hcardF hφs hnat hc' (hbad α hα) hψ
  set Y := Qv (puAmalgam h.le) ε ⊓ flat h α' with hYdef
  have hY2 : IsPGroup 2 ↥(natImage ψ Y) := by
    have hP : IsPGroup 2 ↥Y := (isPGroup_qv _ h20 hεH).to_le inf_le_left
    exact (hP.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
  have hdY := S46.finrank_commN_le_two_of_pGroup hY2
  set A₁ := commN (natImage ψ (ZM (puAmalgam h.le) α)) with hA₁
  set A₂ := commN (natImage ψ B) with hA₂
  have hA₁Y : A₁ ≤ commN (natImage ψ Y) :=
    commN_mono (burnsideMag568_natImage_mono ψ (le_inf hZαε hZαf))
  have hA₂Y : A₂ ≤ commN (natImage ψ Y) :=
    commN_mono (burnsideMag568_natImage_mono ψ (le_inf hBε hBf))
  have hA₂A₁ : ¬ A₂ ≤ A₁ := by
    intro hle
    apply hB
    rw [hcomB]
    have hUB : ⁅Uloc h.le L α', B⁆ ≤ Uloc h.le L α' :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hBf.trans hψ.1)
    intro v hv
    have hv' := (burnsideMag568_mem_commutator_iff hψ hBf ⟨v, hUB hv⟩).mp hv
    have := (burnsideMag568_mem_commutator_iff hψ hZαf ⟨v, hUB hv⟩).mpr (hle hv')
    rw [← hReq] at this
    exact hRZ this
  have hlt : A₁ < A₁ ⊔ A₂ := lt_of_le_of_ne le_sup_left fun he => hA₂A₁ (he ▸ le_sup_right)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have hsup : A₁ ⊔ A₂ = commN (natImage ψ Y) :=
    Submodule.eq_of_le_of_finrank_le (sup_le hA₁Y hA₂Y) (by rw [hRw] at h1; omega)
  rw [hcomδ]
  have hUδ : ⁅Uloc h.le L α', ZM (puAmalgam h.le) δ⁆ ≤ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZδf.trans hψ.1)
  intro v hv
  have hv' := (burnsideMag568_mem_commutator_iff hψ hZδf ⟨v, hUδ hv⟩).mp hv
  have hv'' : natVec hψ ⟨v, hUδ hv⟩ ∈ A₁ ⊔ A₂ := by
    rw [hsup]
    exact commN_mono (burnsideMag568_natImage_mono ψ (le_inf hZδε hZδf)) hv'
  have hmem := burnsideMag568_mem_sup_of_natVec hψ hZαf hBf ⟨v, hUδ hv⟩ hv''
  rw [← hReq, ← hcomB] at hmem
  exact (sup_le (hRZ.trans le_sup_right) le_sup_left) hmem

end CFSG.Quasithin.MS93.S4L
