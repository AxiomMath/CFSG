module

public import CFSG.Quasithin.MS93.S4A431F
public import CFSG.Quasithin.MS93.S46Gen

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem sub_mem_of_finrank_eq_succ [CharP F 2] {W₁ W₂ : Submodule F (Fin 3 → F)}
    (h12 : W₁ ≤ W₂) (hdim : Module.finrank F W₂ = Module.finrank F W₁ + 1)
    {g : Matrix (Fin 3) (Fin 3) F} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (hg1 : ∀ x ∈ W₁, g *ᵥ x ∈ W₁) (hg2 : ∀ x ∈ W₂, g *ᵥ x ∈ W₂) :
    ∀ x ∈ W₂, g *ᵥ x - x ∈ W₁ := by
  obtain ⟨r, hr2, hr1⟩ : ∃ r ∈ W₂, r ∉ W₁ := by
    by_contra hcon
    push Not at hcon
    have : W₂ = W₁ := le_antisymm hcon h12
    rw [this] at hdim
    omega
  have hr0 : r ≠ 0 := fun h0 => hr1 (h0 ▸ W₁.zero_mem)
  have hspan : W₂ = W₁ ⊔ Submodule.span F {r} := by
    have hle : W₁ ⊔ Submodule.span F {r} ≤ W₂ :=
      sup_le h12 ((Submodule.span_singleton_le_iff_mem _ _).mpr hr2)
    have hinf : W₁ ⊓ Submodule.span F {r} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd (by simpa [hc] using W₁.smul_mem c⁻¹ hx1) hr1
    have hd := Submodule.finrank_sup_add_finrank_inf_eq W₁ (Submodule.span F {r})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hr0] at hd
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hdec : ∀ x ∈ W₂, ∃ w ∈ W₁, ∃ c : F, x = w + c • r := by
    intro x hx
    rw [hspan] at hx
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨w, hw, c, rfl⟩
  obtain ⟨w₀, hw₀, c, hc⟩ := hdec _ (hg2 r hr2)
  have hpow : ∀ n : ℕ, ∃ w ∈ W₁, (g ^ n) *ᵥ r = w + c ^ n • r := by
    intro n
    induction n with
    | zero => exact ⟨0, W₁.zero_mem, by simp⟩
    | succ n ih =>
      obtain ⟨w, hw, hn⟩ := ih
      refine ⟨g *ᵥ w + c ^ n • w₀, W₁.add_mem (hg1 w hw) (W₁.smul_mem _ hw₀), ?_⟩
      rw [pow_succ', ← Matrix.mulVec_mulVec, hn, Matrix.mulVec_add, Matrix.mulVec_smul, hc,
        smul_add, smul_smul, ← pow_succ, add_assoc]
  have hc1 : c = 1 := by
    obtain ⟨w, hw, hn⟩ := hpow (2 ^ k)
    rw [hg, Matrix.one_mulVec] at hn
    have hck : c ^ 2 ^ k = 1 := by
      by_contra hne
      apply hr1
      have hsub : (1 - c ^ 2 ^ k) • r ∈ W₁ := by
        have : (1 - c ^ 2 ^ k) • r = w := by
          rw [sub_smul, one_smul, sub_eq_iff_eq_add]
          exact hn
        rw [this]
        exact hw
      have hu : (1 - c ^ 2 ^ k) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have := W₁.smul_mem (1 - c ^ 2 ^ k)⁻¹ hsub
      rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    have h2 : (c - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, hck, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2 ^ k) (by positivity) |>.mp h2)
  intro x hx
  obtain ⟨w, hw, d, rfl⟩ := hdec x hx
  have hgr : g *ᵥ r - r = w₀ := by rw [hc, hc1, one_smul, add_sub_cancel_right]
  have : g *ᵥ (w + d • r) - (w + d • r) = (g *ᵥ w - w) + d • (g *ᵥ r - r) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
    abel
  rw [this, hgr]
  exact W₁.add_mem (W₁.sub_mem (hg1 w hw) hw) (W₁.smul_mem _ hw₀)

end Lin

section Perp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem stab_le_normalizer_vvPerp (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : stab _ α ≤ Subgroup.normalizer (K : Set _)) :
    stab (puAmalgam h.le) α ≤ Subgroup.normalizer (S46.vvPerp α K : Set _) := by
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α :=
    (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hKV : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (K : Set _) := hVs.trans hK
  have hVn := stab_le_normalizer_vv h α
  have key : ∀ y ∈ stab (puAmalgam h.le) α, ∀ v ∈ S46.vvPerp α K, y * v * y⁻¹ ∈ S46.vvPerp α K := by
    intro y hy v hv
    rw [S46.mem_vvPerp_iff hKV] at hv ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn hy) v).mp hv.1, fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ Vv (puAmalgam h.le) α :=
      (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hy)) w).mp hw
    have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hK hy) _).mp (hv.2 _ hw')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact key g hg v
  · intro hv
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
    simpa [mul_assoc] using this

end Perp

section B4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_critR0_qv_le (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb4 : critDist (puAmalgam h.le) = 4) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    ⁅critR0 (puAmalgam h.le) α α', Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)⁆ ≤
      critR (puAmalgam h.le) α α' := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc := hs.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hα' := hc'.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 4 := hc'.2.1.trans hb4
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hεγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by omega)
  have hγρ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 2)
      (geo (puAmalgam h.le) α' α 3) := adj_geo _ (i := 2) (by omega)
  have hρα : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 3) α := by
    have := adj_geo (puAmalgam h.le) (u := α') (w := α) (i := 3) (by omega)
    rwa [show geo (puAmalgam h.le) α' α (3 + 1) = α from geo_of_le _ (by omega)] at this
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hα'
  have hQε : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤
      Qv _ (geo (puAmalgam h.le) α' α 1) := qv_le_qv _ h20 hγ hεγ.symm
  have hQs' : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤ stab _ α' :=
    hQε.trans (qv_le_stab_of_adj _ hα'ε.symm)
  have hQs : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤ stab _ α :=
    (qv_le_qv _ h20 hγ hγρ).trans (qv_le_stab_of_adj _ hρα)
  have hVs' : Vv (puAmalgam h.le) α ≤ stab _ α' := hs.2.trans hQs'
  have hZs' : ZM (puAmalgam h.le) α ≤ stab _ α' := (zm_le_vv h hα).trans hVs'
  have hT2 : IsPGroup 2 ↥(Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)) :=
    (isPGroup_qv _ h20 hεH).to_le hQε
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hα'
  have hUn : stab (puAmalgam h.le) α' ≤
      Subgroup.normalizer (Uloc h.le L α' : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α'
  have hR0 : critR0 (puAmalgam h.le) α α' = ⁅Uloc h.le L α', Vv (puAmalgam h.le) α⁆ := by
    rw [critR0, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hα' hVs']
  have hR : critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ := by
    rw [critR, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hα' hZs']
  obtain ⟨-, hR0q, hRq⟩ := concl431_i_ii h hC hφ (by omega) hs
  have hdim2 : Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) = 2 := by
    have := hR0q
    rw [hR0, card_commutator_eq hψ' hVs', Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  have hdim1 : Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) = 1 := by
    have := hRq
    rw [hR, card_commutator_eq hψ' hZs', Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq
      (show Nat.card F ^ _ = Nat.card F ^ 1 by rw [pow_one]; exact this)
  have h12 : commN (natImage ψ' (ZM (puAmalgam h.le) α)) ≤
      commN (natImage ψ' (Vv (puAmalgam h.le) α)) :=
    commN_mono (natImage_mono (zm_le_vv h hα))
  have hQnV : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    hQs.trans (stab_le_normalizer_vv h α)
  have hQnZ : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    hQs.trans (stab_le_normalizer_zm _ α)
  have hinv : ∀ {A : Subgroup (puAmalgam h.le).Universal}, A ≤ stab _ α' →
      Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤
        Subgroup.normalizer (A : Set (puAmalgam h.le).Universal) →
      ∀ t (ht : t ∈ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)),
        ∀ x ∈ commN (natImage ψ' A),
          ((toSL3 ψ' ⟨t, hQs' ht⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈
            commN (natImage ψ' A) := by
    intro A hA hQA t ht x hx
    obtain ⟨u, rfl⟩ := natVec_surjective hψ' x
    have hu : (u : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L α', A⁆ :=
      (mem_commutator_iff_natVec hψ' hA u).mpr hx
    have hn : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) ≤
        Subgroup.normalizer ((⁅Uloc h.le L α', A⁆ : Subgroup (puAmalgam h.le).Universal) :
          Set (puAmalgam h.le).Universal) :=
      le_normalizer_commutator (hQs'.trans hUn) hQA
    have hmemU : t * (u : (puAmalgam h.le).Universal) * t⁻¹ ∈ Uloc h.le L α' :=
      (Subgroup.mem_normalizer_iff.mp (hUn (hQs' ht)) _).mp u.2
    have hmem : t * (u : (puAmalgam h.le).Universal) * t⁻¹ ∈ ⁅Uloc h.le L α', A⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hn ht) _).mp hu
    rw [← natVec_conj hψ' ⟨t, hQs' ht⟩ u ⟨_, hmemU⟩ rfl]
    exact (mem_commutator_iff_natVec hψ' hA ⟨_, hmemU⟩).mp hmem
  rw [hR0, hR, Subgroup.commutator_le]
  intro r hr t ht
  have hrU : r ∈ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hVs'.trans hUn) hr
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hg : ((toSL3 ψ' ⟨t, hQs' ht⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← map_pow]
    have : (⟨t, hQs' ht⟩ : ↥(stab (puAmalgam h.le) α')) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
    rfl
  have hlin := sub_mem_of_finrank_eq_succ h12 (by rw [hdim1, hdim2]) hg
    (hinv hZs' hQnZ t ht) (hinv hVs' hQnV t ht) (natVec hψ' ⟨r, hrU⟩)
    ((mem_commutator_iff_natVec hψ' hVs' ⟨r, hrU⟩).mp hr)
  have hcU : ⁅r, t⁆ ∈ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs'.trans hUn)
      (Subgroup.commutator_mem_commutator hrU ht)
  have hw := natVec_commutator hψ' ⟨t, hQs' ht⟩ ⟨r, hrU⟩ ⟨_, hcU⟩ rfl
  refine (mem_commutator_iff_natVec hψ' hZs' ⟨_, hcU⟩).mpr ?_
  rw [hw, ← neg_sub]
  exact Submodule.neg_mem _ hlin

theorem vv_comm_le_zm_of_star_four (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb4 : critDist (puAmalgam h.le) = 4) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) α := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hc := hs.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hKn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_zm _ α
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hRZ : critR (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hKn)
  have hR0V : critR0 (puAmalgam h.le) α α' ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_vv h α))
  have hR0U : ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤ S46.vvPerp α (ZM _ α) := by
    intro r hr
    rw [S46.mem_vvPerp_iff (hVs.trans hKn)]
    refine ⟨hR0V hr, fun w hw => hRZ ?_⟩
    exact commutator_critR0_qv_le h hfull hC hφ hb4 hs
      (Subgroup.commutator_mem_commutator hr (hs.2 hw))
  have hVL := commutator_vv_ltil_le_of h hfull hα (adj_geo_one_of_isCritical _ hb0 hc)
    (zm_le_qv_geo_one _ h20 hb0 hc) hc'.2.2 (stab_le_normalizer_vvPerp h hb hα hKn) hR0U
  exact S46.commutator_vv_le_of_ltil h hfull hb hα hKn hVL

end B4

section Props

theorem s43b4Ab (h32 : S32) : S43b4Ab := by
  intro G _ _ M T L h F _ _ φ hH hb4 α α' hs
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  exact vv_comm_le_zm_of_star_four h hfull (centHyp_of_S32 h32 h) hH.2.2 hb4 hs

theorem s43b4_of_cff (hF : S4CFF) (h32 : S32) : S43b4 :=
  s43b4_of hF h32 (s43b4Ab h32)

end Props

end CFSG.Quasithin.MS93.S4A
