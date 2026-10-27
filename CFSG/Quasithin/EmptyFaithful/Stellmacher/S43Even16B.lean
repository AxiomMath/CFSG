module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even16A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C16

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Cfg (α α' δ ρ : Geo H M) : Prop where
  crit : IsCritPair₁ α α'
  hδ : δ ∈ nbrs α'
  dδ : dist α δ = bMin H M - 1
  hρ : ρ ∈ nbrs δ
  dρ : dist α ρ = bMin H M - 2

theorem exists_cfg (hA : F53Amalgam H M S) {α α' : Geo H M} (hb : 2 ≤ bMin H M)
    (hc : IsCritPair₁ α α') : ∃ δ ρ : Geo H M, Cfg α α' δ ρ := by
  obtain ⟨δ, hδ, hdδ⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := α')
    (d := bMin H M - 1) (by rw [hc.2]; omega)
  obtain ⟨ρ, hρ, hdρ⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α) (δ := δ)
    (d := bMin H M - 2) (by rw [hdδ]; omega)
  exact ⟨δ, ρ, hc, hδ, hdδ, hρ, hdρ⟩

variable {α α' δ ρ : Geo H M}

theorem Cfg.vα' (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hc : Cfg α α' δ ρ) : vtype α' = false :=
  hs.vtype_crit hA he hc.crit

theorem Cfg.vδ (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hc : Cfg α α' δ ρ) : vtype δ = true :=
  Sit43.vtype_true_of_adj (hc.vα' hA hs he) hc.hδ

theorem Cfg.vρ (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hc : Cfg α α' δ ρ) : vtype ρ = false :=
  Sit43.vtype_false_of_adj (hc.vδ hA hs he) hc.hρ

omit [Finite G] in
theorem Cfg.hα'δ (hc : Cfg α α' δ ρ) : α' ∈ nbrs δ := nbrs_symm hc.hδ

omit [Finite G] in
theorem Cfg.hδρ (hc : Cfg α α' δ ρ) : δ ∈ nbrs ρ := nbrs_symm hc.hρ

omit [Finite G] in
theorem Cfg.ρ_ne (hs : Sit43 α) (hc : Cfg α α' δ ρ) : ρ ≠ α' := by
  intro h
  have h1 := hc.dρ
  rw [h, hc.crit.2] at h1
  have := hs.b1
  omega

omit [Finite G] in
theorem Cfg.dδ_lt (hs : Sit43 α) (hc : Cfg α α' δ ρ) : dist α δ < bMin H M := by
  have := hs.b1
  rw [hc.dδ]
  omega

theorem Cfg.Zv_le_stab (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hc : Cfg α α' δ ρ) : Zv α' ≤ stab α :=
  hs.Zv_le_stab_crit' hA he hc.crit

theorem Cfg.Vn_le_stab (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hc : Cfg α α' δ ρ) : Vn δ ≤ stab α := by
  refine iSup₂_le fun l hl => ?_
  have hlv : vtype l = false := Sit43.vtype_false_of_adj (hc.vδ hA hs he) hl
  refine hs.Zv_le_stab_of_dist_le_false hA hlv ?_
  have h1 := dist_triangle hA.amalgam.gen l δ α
  have h2 : dist l δ = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hl)
  have h3 : dist δ α = bMin H M - 1 := by rw [CosetGeom.dist_comm]; exact hc.dδ
  have := hs.b1
  omega

omit [Finite G] in
theorem Cfg.Zv_le_Qv (hs : Sit43 α) (hc : Cfg α α' δ ρ) : Zv α ≤ Qv δ :=
  hs.Zv_le_Qv_of_dist_lt_false hs.vα (hc.dδ_lt hs)

theorem claim17_of_relIndex (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) (h15 : Claim15 α) (hc : IsCritPair₁ α α')
    (hK : (Wn α ⊓ stab α').relIndex (Wn α) ≤ 2) : Claim17 α := by
  obtain ⟨x, hxZ, hxQ, hx⟩ := h15 hc
  refine ⟨x, hs.Zv_le_stab_crit' hA he hc hxZ, hxQ,
    isTransvec_of_le hA h26 hs (by omega) inf_le_left hK (hs.Zv_le_stab_crit' hA he hc hxZ) hxQ
      fun k hk => ?_⟩
  have h1 := (Zv α).inv_mem (hx k hk)
  have e : (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
  rwa [e] at h1

theorem not_Wn_le_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : ¬ Wn α ≤ stab δ := by
  intro hW
  have hρW := (h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ).1
  exact hno (claim17_of_relIndex hA h26 hs he hb h15 hc.crit
    (relIndex_inf_stab_le_two hA (hc.vρ hA hs he) hc.hδρ hc.hα'δ (le_inf hρW hW)))

theorem not_Wn_inf_le_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : ¬ Wn α ⊓ stab δ ≤ stab α' := by
  intro hD
  have h2 := (h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ).2.1
  refine hno (claim17_of_relIndex hA h26 hs he hb h15 hc.crit ?_)
  exact (Subgroup.relIndex_le_of_le_left (le_inf inf_le_left hD) (relIndex_ne_zero' _ _)).trans h2

theorem Wn_sup_edge (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : Wn α ⊔ (stab ρ ⊓ stab δ) = stab ρ := by
  have h := h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ
  have hle : Wn α ⊔ (stab ρ ⊓ stab δ) ≤ stab ρ := sup_le h.1 inf_le_left
  by_contra hne
  have hM := le_Mab hle le_sup_right hne
  exact not_Wn_le_stab hA h26 hs he hb h14 h15 hno hc
    ((le_inf le_rfl (le_sup_left.trans hM)).trans h.2.2.2.2)

theorem R0_le_Wn (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hc : Cfg α α' δ ρ) : ⁅Wn α ⊓ stab δ, Vn δ⁆ ≤ Wn α := by
  rw [Subgroup.commutator_le]
  intro d hd v hv
  have h1 : v * d⁻¹ * v⁻¹ ∈ Wn α := (Subgroup.mem_normalizer_iff.mp
    (stab_le_normalizer_Wn α (hc.Vn_le_stab hA hs he hv)) _).mp ((Wn α).inv_mem hd.1)
  have e : ⁅d, v⁆ = d * (v * d⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Wn α).mul_mem hd.1 h1

omit [Finite G] in
theorem R0_le_Vn : ⁅Wn α ⊓ stab δ, Vn δ⁆ ≤ Vn δ := by
  rw [Subgroup.commutator_le]
  intro d hd v hv
  have h1 : d * v * d⁻¹ ∈ Vn δ :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hd.2) v).mp hv
  have e : ⁅d, v⁆ = (d * v * d⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact (Vn δ).mul_mem h1 ((Vn δ).inv_mem hv)

theorem Wn_le_centralizer_R0 (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    (hb : 6 ≤ bMin H M) (hc : Cfg α α' δ ρ) :
    Wn α ≤ Subgroup.centralizer ((⁅Wn α ⊓ stab δ, Vn δ⁆ : Subgroup G) : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact isElemAbelian_comm (hs.isElemAbelian_Wn hA hb) (R0_le_Wn hA hs he hc hr) hw

theorem comm_Zv_le_R0 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hc : Cfg α α' δ ρ) : ⁅Zv α, Zv α'⁆ ≤ ⁅Wn α ⊓ stab δ, Vn δ⁆ :=
  Subgroup.commutator_mono (le_inf (hs.Zv_le_Wn hA h26) ((hc.Zv_le_Qv hs).trans (pCoreOf_le 2 _)))
    (Sit43.Zv_le_Vn_nbrs hc.hα'δ)

theorem eight_le_card_R0 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) (h14 : Claim14 α) (h15 : Claim15 α)
    (hno : ¬ Claim17 α) (hc : Cfg α α' δ ρ) : 8 ≤ Nat.card ↥⁅Wn α ⊓ stab δ, Vn δ⁆ := by
  have hδv := hc.vδ hA hs he
  obtain ⟨w, hw, hwα'⟩ :=
    IsConcreteLE.not_le_iff_exists.mp (not_Wn_inf_le_stab hA h26 hs he hb h14 h15 hno hc)
  have hwQ : w ∉ Qv δ := fun h => hwα' (Qv_le_stab_of_mem_nbrs hA hc.hα'δ h)
  have h2b := hs.claim2b hA h26 (by omega) hδv hw.2 hwQ
  have hle : ⁅Vn δ, Subgroup.zpowers w⁆ ≤ ⁅Wn α ⊓ stab δ, Vn δ⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hw) le_rfl
  have hRN : ⁅Wn α ⊓ stab δ, Vn δ⁆ ≤ Subgroup.normalizer (Yv δ : Set G) :=
    ((R0_le_Vn.trans (hs.Vn_le_Qv_of_true hδv)).trans (pCoreOf_le 2 _)).trans
      (hs.stab_le_normalizer_Yv hA h26 hδv)
  have h3 : (Yv δ).relIndex (⁅Vn δ, Subgroup.zpowers w⁆ ⊔ Yv δ) ≤
      (Yv δ).relIndex (⁅Wn α ⊓ stab δ, Vn δ⁆ ⊔ Yv δ) :=
    Subgroup.relIndex_le_of_le_right (sup_le_sup_right hle _) (relIndex_ne_zero' _ _)
  rw [Sit43.relIndex_sup_of_le_normalizer hRN] at h3
  have h5 := Subgroup.relIndex_mul_card (Yv δ) ⁅Wn α ⊓ stab δ, Vn δ⁆
  have h6 : 1 < Nat.card ↥(Yv δ ⊓ ⁅Wn α ⊓ stab δ, Vn δ⁆) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    apply hs.comm_ne_bot_crit hA he hc.crit
    rw [eq_bot_iff, ← hbot]
    exact le_inf (hs.comm_le_Yv hA h26 he hc.crit hc.hδ (hc.dδ_lt hs)) (comm_Zv_le_R0 hA h26 hs hc)
  nlinarith

omit [Finite G] in
theorem comm_mul_mem_sup {R Z V : Subgroup G} {c d v : G} (hv : v ∈ V) (hr : ⁅d, v⁆ ∈ R)
    (hrV : ⁅d, v⁆ ∈ V) (hcV : ∀ u ∈ V, c * u * c⁻¹ * u⁻¹ ∈ Z) : ⁅c * d, v⁆ ∈ R ⊔ Z := by
  have e : ⁅c * d, v⁆ = (c * ⁅d, v⁆ * c⁻¹ * ⁅d, v⁆⁻¹) * ⁅d, v⁆ * (c * v * c⁻¹ * v⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcV _ hrV))
    (Subgroup.mem_sup_left hr)) (Subgroup.mem_sup_right (hcV v hv))

theorem edge_le_normalizer_R0 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (h14 : Claim14 α) (hc : Cfg α α' δ ρ) :
    stab ρ ⊓ stab δ ≤
      Subgroup.normalizer ((⁅Wn α ⊓ stab δ, Vn δ⁆ ⊔ Zv ρ : Subgroup G) : Set G) := by
  have hρv := hc.vρ hA hs he
  have hδv := hc.vδ hA hs he
  have hWρ : Wn α ≤ stab ρ := (h14 hc.crit hc.hδ hc.dδ hc.hρ hc.dρ).1
  have hcomm : ∀ c ∈ Qst δ, ∀ v ∈ Vn δ, c * v * c⁻¹ * v⁻¹ ∈ Zv ρ := by
    intro c hcq v hv
    have h1 : ⁅v, c⁆ ∈ Yv δ :=
      hs.comm_Vn_Qst hA h26 hδv hc.hρ ▸ Subgroup.commutator_mem_commutator hv hcq
    have e : c * v * c⁻¹ * v⁻¹ = ⁅v, c⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Yv_le_Zv hc.hρ ((Yv δ).inv_mem h1)
  refine Sit43.le_normalizer_of_conj_mem fun g hg n hn => ?_
  have hsub : ⁅Wn α ⊓ stab δ, Vn δ⁆ ⊔ Zv ρ ≤ conjSub g⁻¹ (⁅Wn α ⊓ stab δ, Vn δ⁆ ⊔ Zv ρ) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro d hd v hv
      rw [mem_conjSub, inv_inv]
      have hc1 := comm_mem_Qst hA h26 hs hρv hc.hδρ hg ⟨hWρ hd.1, hd.2⟩
      have hv' : g * v * g⁻¹ ∈ Vn δ :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg.2) v).mp hv
      have hr := Subgroup.commutator_mem_commutator hd hv'
      have e : g * ⁅d, v⁆ * g⁻¹ = ⁅(g * d * g⁻¹ * d⁻¹) * d, g * v * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact comm_mul_mem_sup hv' hr (R0_le_Vn hr) (hcomm _ hc1)
    · intro z hz
      rw [mem_conjSub, inv_inv]
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA ρ hg.1) z).mp hz)
  have h1 := hsub hn
  rwa [mem_conjSub, inv_inv] at h1

end C16

end CFSG.Quasithin.F53.Stellmacher.S43.Even
