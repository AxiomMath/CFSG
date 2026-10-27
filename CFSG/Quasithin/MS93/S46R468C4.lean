module

public import CFSG.Quasithin.MS93.S46R468B3
public import CFSG.Quasithin.MS93.S46R468C4A
public import CFSG.Quasithin.MS93.S46R468C4T

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

@[expose] def FarNonDeg (c : Hyp46 M T L φ) (α α' : Vtx (puAmalgam c.pu.le)) : Prop :=
  Usup (puAmalgam c.pu.le) α' (geo _ α α' 3) ⊓ Zloc c.pu.le L (geo _ α α' 2) = ⊥

theorem usup_geo_three_ne (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) α α') :
    Usup (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 3) ≠
      Usup (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  have hb4 := c.b4
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  have hα := hc.1
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγβ' : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 2) (geo _ α α' 3) :=
    adj_geo_crit hb4 hc (i := 2) (by omega)
  have hβ'α' : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 3) α' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [show (3 : ℕ) + 1 = 4 from rfl, geo_four hb4 hc] at this
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) (geo _ α α' 3) := not_isMVtx_geo_three hb4 hc
  intro heq
  have hQ : Qv (puAmalgam c.pu.le) (geo _ α α' 1) = Qv _ (geo _ α α' 3) :=
    qv_eq_of_usup_eq h464 h465 h466a c hγ hβγ.symm hγβ' heq.symm
  have hV : Vv (puAmalgam c.pu.le) (geo _ α α' 1) = Vv _ (geo _ α α' 3) :=
    vv_eq_of_usup_eq h464 h465 h466a c hγ hβγ.symm hγβ' heq.symm
  have hidx := (h465 G M T L F φ c α' _ hα' hβ'α'.symm).2.1
  obtain ⟨y, hy, hyβ'⟩ : ∃ y ∈ ZM (puAmalgam c.pu.le) α',
      y ∉ ZH (puAmalgam c.pu.le) (geo _ α α' 3) := by
    by_contra hno
    have h1 : (ZH (puAmalgam c.pu.le) (geo _ α α' 3)).relIndex (ZM _ α') = 1 :=
      Subgroup.relIndex_eq_one.mpr fun y hy => by_contra fun hn => hno ⟨y, hy, hn⟩
    rw [h1] at hidx
    have : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  apply hc.2.2
  intro t ht
  have htT : t ∈ Qv (puAmalgam c.pu.le) (geo _ α α' 3) :=
    hQ ▸ (zm_le_qv_self _ hα hb0).trans (qv_le_qv _ c.pu.hyp20 hα hαβ) ht
  have hcomm : t * y = y * t := by
    have htV : t ∈ Vv (puAmalgam c.pu.le) (geo _ α α' 3) := hV ▸ zm_le_vv_of_adj hαβ.symm hα ht
    exact vv_comm c.pu (by omega) hβ' htV (zm_le_vv_of_adj hβ'α' hα' hy)
  exact mem_qv_of_commute c.pu c.via h464' hsq h466 hα' hβ'α'.symm hy hyβ' htT hcomm

theorem qv_inf_ptQ_le_ptSub_sup (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {α β γ : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {δ q₀ : Subgroup (puAmalgam c.pu.le).Universal}
    (hq₀ : IsPtOn (puAmalgam c.pu.le) γ β q₀)
    (hY : pencil (puAmalgam c.pu.le) α δ ≤ Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ q₀)
    (hI : Fintype.card F ≤ (Qv (puAmalgam c.pu.le) γ).relIndex (ptSub _ α δ)) :
    Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ q₀ ≤ ptSub (puAmalgam c.pu.le) α δ ⊔ Qv _ γ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  set A := Qv (puAmalgam c.pu.le) β ⊓ ptQ _ γ q₀ with hAdef
  set U := ptSub (puAmalgam c.pu.le) α δ with hUdef
  have hUA : U ≤ A := (ptSub_le_pencil α δ).trans hY
  have hq₀Z : q₀ ≤ ZM (puAmalgam c.pu.le) γ :=
    (le_uloc_of_isPtOn c hγ hq₀).trans (uloc_le_zm c.pu hfull hγ)
  have hQA : Qv (puAmalgam c.pu.le) γ ≤ A :=
    le_inf (qv_le_qv _ c.pu.hyp20 hγ hγβ) (qv_le_ptQ c hγ hq₀Z)
  have hAs : A ≤ stab (puAmalgam c.pu.le) γ := inf_le_left.trans (qv_le_stab_of_adj _ hγβ.symm)
  have hUn : U ≤ Subgroup.normalizer (Qv (puAmalgam c.pu.le) γ : Set _) :=
    (hUA.trans hAs).trans (stab_le_normalizer_qv _ γ)
  have h1 : (Qv (puAmalgam c.pu.le) γ).relIndex (U ⊔ Qv _ γ) =
      (Qv (puAmalgam c.pu.le) γ).relIndex U := S46.relIndex_sup_of_le_normalizer hUn
  have hmul := Subgroup.relIndex_mul_relIndex (Qv (puAmalgam c.pu.le) γ) (U ⊔ Qv _ γ) A
    le_sup_right (sup_le hUA hQA)
  rw [relIndex_qv_inf_ptQ h464 h465 h466a c hγ hγβ hq₀, h1] at hmul
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hr0 : (U ⊔ Qv (puAmalgam c.pu.le) γ).relIndex A ≠ 0 :=
    relIndex_ne_zero_of_le_stab c hγ hAs _
  have hr1 : (U ⊔ Qv (puAmalgam c.pu.le) γ).relIndex A ≤ 1 := by
    by_contra h
    have h2 : Fintype.card F * 2 ≤ (Qv (puAmalgam c.pu.le) γ).relIndex U *
        (U ⊔ Qv (puAmalgam c.pu.le) γ).relIndex A := Nat.mul_le_mul hI (by omega)
    omega
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem zm_le_usup_sup_zh (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {γ β β' α' : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) (hγβ' : (puAmalgam c.pu.le).treeGraph.Adj γ β')
    (hne : Usup (puAmalgam c.pu.le) γ β ≠ Usup _ γ β') (hα' : IsMVtx (puAmalgam c.pu.le) α')
    (hα'β' : (puAmalgam c.pu.le).treeGraph.Adj α' β')
    (hfar : Usup (puAmalgam c.pu.le) α' β' ⊓ Zloc c.pu.le L γ = ⊥) :
    ZM (puAmalgam c.pu.le) γ ≤ Usup (puAmalgam c.pu.le) α' β' ⊔ ZH _ β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  set Y := Usup (puAmalgam c.pu.le) α' β' with hYdef
  set Zβ := ZH (puAmalgam c.pu.le) β with hZβdef
  set Zγ := ZM (puAmalgam c.pu.le) γ with hZγdef
  set Zt := Zloc c.pu.le L γ with hZtdef
  set P := Usup (puAmalgam c.pu.le) γ β ⊓ Usup _ γ β' with hPdef
  have hYZβ' : Y ≤ ZH (puAmalgam c.pu.le) β' := h464' α' β' hα' hα'β'
  have hYZγ : Y ≤ Zγ := hYZβ'.trans (zh_le_zm _ hγβ')
  have hZβZγ : Zβ ≤ Zγ := zh_le_zm _ hγβ
  have hZγs : Zγ ≤ stab (puAmalgam c.pu.le) γ := (zm_le_qv_self _ hγ hb0).trans (qv_le_stab _ γ)
  have : Finite ↥Zγ := I466b.finite_of_le_stab c.pu hγ hZγs
  have : Finite ↥Y := Finite.of_injective _ (Subgroup.inclusion_injective hYZγ)
  have hYZ : Y ⊓ Zβ ≤ P ⊔ Zt := by
    rw [hPdef, hZtdef, ← zh_inf_zh_eq h464 h465 c hγ hγβ hγβ']
    exact le_inf inf_le_right (inf_le_left.trans hYZβ')
  have hZtc : Zt ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) γ : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hγ
  have hPU : P ≤ Uloc c.pu.le L γ := inf_le_left.trans (usup_le_uloc' c.pu hfull hγ hγβ)
  have hUs : Uloc c.pu.le L γ ≤ stab (puAmalgam c.pu.le) γ := puTrans_le_stab c.pu.le _ γ
  have e1 : Nat.card ↥((Y ⊓ Zβ) ⊔ Zt) = Nat.card ↥(Y ⊓ Zβ) * Nat.card ↥Zt :=
    card_sup_of_commute (hZtc.trans (Subgroup.centralizer_le
      (inf_le_left.trans (hYZγ.trans hZγs))))
      (le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hfar.le))
  have e2 : Nat.card ↥(P ⊔ Zt) = Nat.card ↥P * Nat.card ↥Zt :=
    card_sup_of_commute (hZtc.trans (Subgroup.centralizer_le (hPU.trans hUs)))
      (le_bot_iff.mp ((inf_le_inf_right _ hPU).trans (uloc_inf_zloc c.pu hfull γ).le))
  have hPZs : P ⊔ Zt ≤ stab (puAmalgam c.pu.le) γ :=
    sup_le (hPU.trans hUs) ((zloc_le_zm c.pu hfull hγ).trans hZγs)
  have : Finite ↥(P ⊔ Zt) := I466b.finite_of_le_stab c.pu hγ hPZs
  have hle : Nat.card ↥((Y ⊓ Zβ) ⊔ Zt) ≤ Nat.card ↥(P ⊔ Zt) :=
    Subgroup.card_le_of_le (sup_le hYZ le_sup_right)
  rw [e1, e2, card_usup_inf_usup h464 h465 c hγ hγβ hγβ' hne] at hle
  have : Finite ↥Zt := I466b.finite_of_le_stab c.pu hγ ((zloc_le_zm c.pu hfull hγ).trans hZγs)
  have hZtpos : 0 < Nat.card ↥Zt := Nat.card_pos
  have hcard : Nat.card ↥(Y ⊓ Zβ) ≤ Fintype.card F := Nat.le_of_mul_le_mul_right hle hZtpos
  have hYc : Nat.card ↥Y = Fintype.card F ^ 2 := (h465 G M T L F φ c α' β' hα' hα'β').1
  have hYn : Y ≤ Subgroup.normalizer (Zβ : Set (puAmalgam c.pu.le).Universal) :=
    (hYZγ.trans ((zm_le_qv_self _ hγ hb0).trans ((qv_le_qv _ c.pu.hyp20 hγ hγβ).trans
      (qv_le_stab _ β)))).trans (stab_le_normalizer_of_smul _ (fun g y => zh_smul _ g y) β)
  have h1 : Zβ.relIndex (Y ⊔ Zβ) = Zβ.relIndex Y := S46.relIndex_sup_of_le_normalizer hYn
  have h2 := QjAux.relIndex_mul_card_inf' Zβ Y
  rw [hYc, inf_comm] at h2
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have h3 : Fintype.card F ≤ Zβ.relIndex Y := by
    by_contra hlt
    have h4 : Zβ.relIndex Y * Nat.card ↥(Y ⊓ Zβ) < Fintype.card F * Fintype.card F :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) hcard hq
    rw [h2, ← sq] at h4
    exact lt_irrefl _ h4
  have hidx : Zβ.relIndex Zγ = Fintype.card F := (h465 G M T L F φ c γ β hγ hγβ).2.1
  have hmul := Subgroup.relIndex_mul_relIndex Zβ (Y ⊔ Zβ) Zγ le_sup_right (sup_le hYZγ hZβZγ)
  rw [h1, hidx] at hmul
  have hr0 : (Y ⊔ Zβ).relIndex Zγ ≠ 0 := relIndex_ne_zero_of_le_stab c hγ hZγs _
  have hr1 : (Y ⊔ Zβ).relIndex Zγ ≤ 1 := by
    by_contra h
    have h5 : Fintype.card F * 2 ≤ Zβ.relIndex Y * (Y ⊔ Zβ).relIndex Zγ :=
      Nat.mul_le_mul h3 (by omega)
    omega
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem BadConf.false_of_zm_le_ptSub (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α')
    {δ₁ δ₂ : Subgroup (puAmalgam c.pu.le).Universal}
    (h₁ : IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ₁)
    (h₂ : IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ₂) (hne : δ₁ ≠ δ₂)
    (hZ₁ : ZM (puAmalgam c.pu.le) (geo _ α α' 2) ≤ ptSub _ α δ₁)
    (hZ₂ : ZM (puAmalgam c.pu.le) (geo _ α α' 2) ≤ ptSub _ α δ₂) : False := by
  have hc := hB.crit
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hα := hc.1
  have h464' := h464 G M T L F φ c
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) (geo _ α α' 1) := not_isMVtx_geo_one hb4 hc
  set Zγ := ZM (puAmalgam c.pu.le) (geo _ α α' 2) with hZγdef
  have hZγV : Zγ ≤ Vv (puAmalgam c.pu.le) (geo _ α α' 1) := zm_le_vv_of_adj hβγ hγ
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {k | k ∈ stab (puAmalgam c.pu.le) α ∧ ∀ z ∈ Zγ, ⁅z, k⁆ ∈ ZM (puAmalgam c.pu.le) α}
      one_mem' := ⟨Subgroup.one_mem _, fun z _ => by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', fun z hz => ?_⟩
        have e : ⁅z, a * b⁆ = ⁅z, a⁆ * (a * ⁅z, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ (ha' z hz) ((Subgroup.mem_normalizer_iff.mp
          (stab_le_normalizer_zm _ α ha) _).mp (hb'' z hz))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun z hz => ?_⟩
        have e : ⁅z, a⁻¹⁆ = a⁻¹ * ⁅z, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α
          (Subgroup.inv_mem _ ha)) _).mp (Subgroup.inv_mem _ (ha' z hz)) }
  have hTS : Qv (puAmalgam c.pu.le) (geo _ α α' 1) ≤ S := fun t ht =>
    ⟨qv_le_stab_of_adj _ hαβ.symm ht, fun z hz => zh_le_zm _ hαβ
      (commutator_vv_qv_le_zh c.pu h464' hβ (Subgroup.commutator_mem_commutator (hZγV hz) ht))⟩
  have hQS : ∀ {δ}, Zγ ≤ ptSub (puAmalgam c.pu.le) α δ → ptQ (puAmalgam c.pu.le) α δ ≤ S :=
    fun {δ} hZ t ht => ⟨(mem_ptQ.mp ht).1, fun z hz =>
      commutator_ptSub_ptQ_le c hα δ (Subgroup.commutator_mem_commutator (hZ hz) ht)⟩
  apply hB.bad
  intro g hg z hz v hv
  have hgS := isOddL1_mem_of_ptQ_le h464 h465 h466a c hα hαβ h₁ h₂ hne hTS (hQS hZ₁) (hQS hZ₂) hg
  have h1 : ⁅z, g⁆ ∈ ZM (puAmalgam c.pu.le) α := hgS.2 z hz
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (commute_zm_vv c.pu hb hα h1 hv)]
  exact Subgroup.one_mem _

theorem mul_self_mem_zm_of_mem_ptSub (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) (P : Subgroup (puAmalgam c.pu.le).Universal)
    {v : (puAmalgam c.pu.le).Universal} (hv : v ∈ ptSub (puAmalgam c.pu.le) x P) :
    v * v ∈ ZM (puAmalgam c.pu.le) x := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hVV : ∀ a ∈ Vv (puAmalgam c.pu.le) x, ∀ b ∈ Vv (puAmalgam c.pu.le) x,
      ⁅a, b⁆ ∈ ZM (puAmalgam c.pu.le) x := fun a ha b hb' =>
    (h465 G M T L F φ c x β hx hxβ).2.2
      (Subgroup.commutator_mem_commutator ha (vv_le_qv c.pu hb hx hb'))
  induction hv using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨ρ, hxρ, -, hwV, -⟩ := hw
    have hρ : ¬ IsMVtx (puAmalgam c.pu.le) ρ := (isMVtx_iff_of_adj _ hxρ).mp hx
    rw [vv_mul_self_eq_one c.pu hb hρ hwV]
    exact Subgroup.one_mem _
  | one => rw [mul_one]; exact Subgroup.one_mem _
  | mul a b ha hb' iha ihb =>
    have haV := ptSub_le_vv c hx P ha
    have hbV := ptSub_le_vv c hx P hb'
    have e : a * b * (a * b) = a * a * ⁅a⁻¹, b⁆ * (b * b) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ iha (hVV _ (Subgroup.inv_mem _ haV) _ hbV)) ihb
  | inv a _ iha =>
    have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ iha

theorem BadConf.usup_le_ptSub (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α')
    {p₀ δ : Subgroup (puAmalgam c.pu.le).Universal}
    (hp₀ : IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) p₀)
    (hZp : ZM (puAmalgam c.pu.le) α' ≤ Qv _ (geo _ α α' 1) ⊓ ptQ (puAmalgam c.pu.le) α p₀)
    (hδ : IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ) (hne : δ ≠ p₀)
    (hI : (Qv (puAmalgam c.pu.le) (geo _ α α' 2)).relIndex (ptSub _ α δ) < Fintype.card F) :
    Usup (puAmalgam c.pu.le) α' (geo _ α α' 3) ≤ ptSub (puAmalgam c.pu.le) α δ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  have hc := hB.crit
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  have hα := hc.1
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγβ' : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 2) (geo _ α α' 3) :=
    adj_geo_crit hb4 hc (i := 2) (by omega)
  have hβ'α' : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 3) α' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [show (3 : ℕ) + 1 = 4 from rfl, geo_four hb4 hc] at this
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  set β := geo (puAmalgam c.pu.le) α α' 1 with hβdef
  set γ := geo (puAmalgam c.pu.le) α α' 2 with hγdef
  set β' := geo (puAmalgam c.pu.le) α α' 3 with hβ'def
  set U := ptSub (puAmalgam c.pu.le) α δ with hUdef
  set W := U ⊓ Qv (puAmalgam c.pu.le) γ with hWdef
  have hδH : δ ≤ Usup (puAmalgam c.pu.le) α β := by
    obtain ⟨_, _, _, he⟩ := hδ
    rw [he]
    exact inf_le_left
  have hZαU : ZM (puAmalgam c.pu.le) α ≤ U := zm_le_ptSub c hα hδ
  have hZαγ : ZM (puAmalgam c.pu.le) α ≤ Qv _ γ := zm_le_qv_geo hb4 hc (by norm_num)
  have hZαW : ZM (puAmalgam c.pu.le) α ≤ W := le_inf hZαU hZαγ
  have hWU : W ≤ U := inf_le_left
  have hWT' : W ≤ Qv (puAmalgam c.pu.le) β' := inf_le_right.trans (qv_le_qv _ c.pu.hyp20 hγ hγβ')
  have hWs' : W ≤ stab (puAmalgam c.pu.le) α' := hWT'.trans (qv_le_stab_of_adj _ hβ'α')
  have hZ'T : ZM (puAmalgam c.pu.le) α' ≤ Qv _ β := hZp.trans inf_le_left
  have hZ's : ZM (puAmalgam c.pu.le) α' ≤ stab _ α := hZ'T.trans (qv_le_stab_of_adj _ hαβ.symm)
  have hZ'nδ : ZM (puAmalgam c.pu.le) α' ≤ Subgroup.normalizer (δ : Set _) := fun t ht =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (h464' α β hα hαβ (hδH ha)))
        t (hZ'T ht)).symm)
  have hZ'nU : ZM (puAmalgam c.pu.le) α' ≤ Subgroup.normalizer (U : Set _) :=
    le_normalizer_ptSub hZ's hZ'nδ
  have hcomm : ⁅ZM (puAmalgam c.pu.le) α', W⁆ = ⁅Uloc c.pu.le L α', W⁆ :=
    commutator_zm_eq_uloc c.pu hfull hα' hWs'
  have hcR : IsCritical (puAmalgam c.pu.le) α' α := ms22_iii _ c.pu.hyp20 hb0 c.pu.centHyp hc
  have hRle : critR (puAmalgam c.pu.le) α' α ≤ ⁅Uloc c.pu.le L α', W⁆ := by
    rw [← hcomm, critR]
    exact Subgroup.commutator_mono le_rfl hZαW
  have hYle : ⁅Uloc c.pu.le L α', W⁆ ≤ Usup (puAmalgam c.pu.le) α' β' := by
    rw [← hcomm, Usup, zv_of_isMVtx _ hα']
    exact Subgroup.commutator_mono le_rfl hWT'
  have hconcl : ⁅Uloc c.pu.le L α', W⁆ ≤ U := by
    rw [← hcomm, Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hWU le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hZ'nU)
  have hYc : Nat.card ↥(Usup (puAmalgam c.pu.le) α' β') = Fintype.card F ^ 2 :=
    hsq α' β' hα' hβ'α'.symm
  have hfinY : Finite ↥(Usup (puAmalgam c.pu.le) α' β') := Nat.finite_of_card_ne_zero (by
    rw [hYc]; exact pow_ne_zero 2 Fintype.card_ne_zero)
  rcases crit_type c.pu c.via c.pu.centHyp hcR with ⟨-, hR⟩ | ⟨-, hR⟩ | ⟨-, hR, -⟩
  rotate_right
  · have hReq : critR (puAmalgam c.pu.le) α' α = Usup _ α' β' :=
      Subgroup.eq_of_le_of_card_ge (hRle.trans hYle) (by rw [hR, hYc])
    exact (hReq ▸ hRle).trans hconcl
  all_goals
  have hRZ : critR (puAmalgam c.pu.le) α' α ≤ ZM _ α := by
    rw [critR, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_zm _ α))
  suffices hkey : ¬ ⁅W, ZM (puAmalgam c.pu.le) α'⁆ ≤ ZM _ α by
    rcases commutator_uloc_eq_of_le c.pu c.via hα' hβ'α'.symm hWT' hR hYc hRle hYle with h | h
    · exact absurd (by rw [Subgroup.commutator_comm, hcomm, h]; exact hRZ) hkey
    · rw [← h]; exact hconcl
  intro hWZ
  obtain ⟨ψ, hψs, hψU, hδc, hψT⟩ := exists_coord_pt h464 h465 h466a c hα hαβ hδ
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have : Finite ↥(stab (puAmalgam c.pu.le) α) := finite_stab c.pu hα
  have : Finite ↥(ptL (puAmalgam c.pu.le) α ψ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (ptL_le_stab ψ))
  have hUs : U ≤ stab (puAmalgam c.pu.le) α := (ptSub_le_vv c hα δ).trans (vv_le_stab_self c α)
  have : Finite ↥U := I466b.finite_of_le_stab c.pu hα hUs
  have hδU : δ ≤ Uloc c.pu.le L α := le_uloc_of_isPtOn c hα hδ
  have hδZ : δ ≤ ZM (puAmalgam c.pu.le) α := hδU.trans (uloc_le_zm c.pu hfull hα)
  have hconjδ : ∀ k ∈ ptL (puAmalgam c.pu.le) α ψ, δ.map (MulAut.conj k).toMonoidHom = δ :=
    fun k hk => map_conj_eq_of_coord hψU hδU hδU hδc hδc ⟨k, ptL_le_stab ψ hk⟩
      (map_pt0_of_mem_stabE0 (mem_ptL_iff.mp hk).snd)
  have hKδ : ptL (puAmalgam c.pu.le) α ψ ≤ Subgroup.normalizer (δ : Set _) := fun k hk =>
    mem_normalizer_of_map_conj_le (hconjδ k hk).le (hconjδ k⁻¹ (Subgroup.inv_mem _ hk)).le
  have hKV : ptL (puAmalgam c.pu.le) α ψ ≤ Subgroup.normalizer (U : Set _) :=
    le_normalizer_ptSub (ptL_le_stab ψ) hKδ
  have hKZ : ptL (puAmalgam c.pu.le) α ψ ≤ Subgroup.normalizer (ZM (puAmalgam c.pu.le) α : Set _) :=
    (ptL_le_stab ψ).trans (stab_le_normalizer_zm _ α)
  have hVc : ∀ v ∈ U, ∀ w ∈ U, ⁅v, w⁆ ∈ ZM (puAmalgam c.pu.le) α := fun v hv w hw =>
    (h465 G M T L F φ c α β hα hαβ).2.2 (Subgroup.commutator_mem_commutator
      (ptSub_le_vv c hα δ hv) (vv_le_qv c.pu hb hα (ptSub_le_vv c hα δ hw)))
  have hV2 : ∀ v ∈ U, v * v ∈ ZM (puAmalgam c.pu.le) α := fun v hv =>
    mul_self_mem_zm_of_mem_ptSub h465 c hα hαβ δ hv
  have hker : ∀ k : ↥(ptL (puAmalgam c.pu.le) α ψ), ptTheta ψ k = 1 →
      ∀ v ∈ U, ⁅(k : (puAmalgam c.pu.le).Universal), v⁆ ∈ ZM (puAmalgam c.pu.le) α := by
    intro k hk v hv
    have hkQ := (ptTheta_eq_one_iff c hα hψU hδU hδc k).mp hk
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (commutator_ptSub_ptQ_le c hα δ
      (Subgroup.commutator_mem_commutator hv hkQ))
  have hTK : Qv (puAmalgam c.pu.le) β ≤ ptL _ α ψ := qv_le_ptL hαβ hψT
  have hXK : ZM (puAmalgam c.pu.le) α' ≤ ptL _ α ψ := hZ'T.trans hTK
  have hX2 : IsPGroup 2 ↥(ZM (puAmalgam c.pu.le) α') :=
    (isPGroup_qv_of_isMVtx c.pu hα').to_le (zm_le_qv_self _ hα' hb0)
  have hp₀δ := qv_inf_ptQ_inf_ptQ_le h464 h465 h466a c hα hαβ hp₀ hδ (Ne.symm hne)
  have hXc : Nat.card ↥(((ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)).map (ptTheta ψ)) =
      Nat.card F := by
    rw [← Subgroup.relIndex_ker]
    have hkerX : (ptTheta ψ).ker ⊓ (ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ) =
        (Qv (puAmalgam c.pu.le) α).subgroupOf (ptL _ α ψ) ⊓
          (ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ) := by
      ext k
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨hk, hkX⟩
        exact ⟨hp₀δ ⟨hZp hkX, (ptTheta_eq_one_iff c hα hψU hδU hδc k).mp hk⟩, hkX⟩
      · rintro ⟨hkQ, hkX⟩
        exact ⟨(ptTheta_eq_one_iff c hα hψU hδU hδc k).mpr (qv_le_ptQ c hα hδZ hkQ), hkX⟩
    calc (ptTheta ψ).ker.relIndex ((ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ))
        = ((ptTheta ψ).ker ⊓ (ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)).relIndex
            ((ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)) :=
          (Subgroup.inf_relIndex_right _ _).symm
      _ = ((Qv (puAmalgam c.pu.le) α).subgroupOf (ptL _ α ψ) ⊓
            (ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)).relIndex
            ((ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)) := by rw [hkerX]
      _ = ((Qv (puAmalgam c.pu.le) α).subgroupOf (ptL _ α ψ)).relIndex
            ((ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)) :=
          Subgroup.inf_relIndex_right _ _
      _ = (Qv (puAmalgam c.pu.le) α).relIndex (ZM _ α') := Subgroup.relIndex_subgroupOf hXK
      _ = Nat.card F := by rw [hB.relIndex_qv_zm h464 h465 h466a, Nat.card_eq_fintype_card]
  have hCX : ∀ x ∈ ZM (puAmalgam c.pu.le) α', ∀ y ∈ W, ⁅x, y⁆ ∈ ZM (puAmalgam c.pu.le) α :=
    fun x hx y hy => by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hWZ (Subgroup.commutator_mem_commutator hy hx))
  have hCi : W.relIndex U ≤ Fintype.card F := by
    rw [hWdef, Subgroup.inf_relIndex_left]
    exact hI.le
  rcases natural_sec_of_ff hn (ptTheta ψ) (ptTheta_surjective hψs) hKV hKZ hZαU hVc hV2 hker
      (X := ZM (puAmalgam c.pu.le) α')
      ((hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm).map _) hXc (C := W) hCX hCi with
    htriv | ⟨βv, hβs, hβk, hβe⟩
  ·
    apply not_commutator_vv_ptQ_le h464 h465 h466a c hB.not_s468At hα hαβ hα hαβ hδ
    rw [Subgroup.commutator_le]
    intro v hv t ht
    have hyU : ⁅v, t⁆ ∈ U := hB.commutator_vv_ptQ_le_ptSub h464 h465 h466a hα hαβ hδ
      (Subgroup.commutator_mem_commutator hv ht)
    have hyV : ⁅v, t⁆ ∈ Vv (puAmalgam c.pu.le) β := by
      have e : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hv ((Subgroup.mem_normalizer_iff.mp
        (ptQ_le_normalizer_vv h464 h465 h466a c hα hαβ hδH ht) _).mp (Subgroup.inv_mem _ hv))
    have hcl : ∀ k ∈ Subgroup.closure {g | g ∈ ptL (puAmalgam c.pu.le) α ψ ∧ Odd (orderOf g)},
        k ∈ stab (puAmalgam c.pu.le) α ∧ ⁅k, ⁅v, t⁆⁆ ∈ ZM (puAmalgam c.pu.le) α := by
      intro k hk
      induction hk using Subgroup.closure_induction with
      | mem k hk => exact ⟨ptL_le_stab ψ hk.1, htriv k hk.1 hk.2 _ hyU⟩
      | one => exact ⟨Subgroup.one_mem _, by
          rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      | mul a b _ _ iha ihb =>
        refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, ?_⟩
        have e : ⁅a * b, ⁅v, t⁆⁆ = a * ⁅b, ⁅v, t⁆⁆ * a⁻¹ * ⁅a, ⁅v, t⁆⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
          (stab_le_normalizer_zm _ α iha.1) _).mp ihb.2) iha.2
      | inv a _ iha =>
        refine ⟨Subgroup.inv_mem _ iha.1, ?_⟩
        have e : ⁅a⁻¹, ⁅v, t⁆⁆ = a⁻¹ * ⁅a, ⁅v, t⁆⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α
          (Subgroup.inv_mem _ iha.1)) _).mp (Subgroup.inv_mem _ iha.2)
    refine mem_bzero_of_forall_vv h464 h465 c hα hαβ hδ fun ℓ hαℓ hδℓ => ?_
    obtain ⟨k, hk, hkℓ⟩ := exists_closure_odd_smul h464 h465 c hα hψs hψU hδc hαβ hαℓ hδH hδℓ
    obtain ⟨hks, hky⟩ := hcl k hk
    have hkα : k • α = α := MulAction.mem_stabilizer_iff.mp hks
    have hαkβ : (puAmalgam c.pu.le).treeGraph.Adj α (k • β) := by
      have := (adj_smul _ k α β).mpr hαβ
      rwa [hkα] at this
    have hVkβ : Vv (puAmalgam c.pu.le) (k • β) = Vv _ ℓ :=
      vv_eq_of_usup_eq h464 h465 h466a c hα hαkβ hαℓ hkℓ
    have hconj : k * ⁅v, t⁆ * k⁻¹ ∈ Vv (puAmalgam c.pu.le) ℓ := by
      rw [← hVkβ, show Vv (puAmalgam c.pu.le) (k • β) = (Vv _ β).map (MulAut.conj k).toMonoidHom
        from vi_smul _ k β 2]
      exact conj_mem_map_conj hyV
    have e : ⁅v, t⁆ = ⁅k, ⁅v, t⁆⁆⁻¹ * (k * ⁅v, t⁆ * k⁻¹) := by
      conv_rhs => rw [commutatorElement_def k]
      group
    rw [e]
    exact Subgroup.mul_mem _ (zm_le_vv_of_adj hαℓ.symm hα (Subgroup.inv_mem _ hky)) hconj
  ·
    obtain ⟨z, hzX, b, hb0', hzb⟩ : ∃ z : ↥(ptL (puAmalgam c.pu.le) α ψ),
        (z : (puAmalgam c.pu.le).Universal) ∈ ZM (puAmalgam c.pu.le) α' ∧
          ∃ b : F, b ≠ 0 ∧ ptTheta ψ z = SL2Model.e12 b := by
      have hne1 : ((ZM (puAmalgam c.pu.le) α').subgroupOf (ptL _ α ψ)).map (ptTheta ψ) ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hXc
        have : 1 < Nat.card F := Finite.one_lt_card
        omega
      obtain ⟨B, hB1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne1
      obtain ⟨z, hz, hzB⟩ := Subgroup.mem_map.mp B.2
      have hzT : ptTheta ψ z ∈ SL2Model.Rg F := by
        rw [← map_ptTheta_qv hψT]
        exact Subgroup.mem_map.mpr ⟨z, Subgroup.mem_subgroupOf.mpr
          (hZ'T (Subgroup.mem_subgroupOf.mp hz)), rfl⟩
      obtain ⟨b, hb⟩ := SL2Model.mem_Rg.mp hzT
      refine ⟨z, Subgroup.mem_subgroupOf.mp hz, b, fun h0 => hB1 (Subtype.ext ?_), hb.symm⟩
      rw [← hzB, ← hb, h0, SL2Model.e12_zero]
      rfl
    have hWline : ∀ w : ↥U, (w : (puAmalgam c.pu.le).Universal) ∈ W →
        (Multiplicative.toAdd (βv w)) 1 = 0 := by
      intro w hw
      have hw'U : (z : (puAmalgam c.pu.le).Universal) * (w : (puAmalgam c.pu.le).Universal) *
          (z : (puAmalgam c.pu.le).Universal)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hKV z.2) _).mp w.2
      have h1 := hβe z w ⟨_, hw'U⟩ rfl
      have hcz : ⁅(z : (puAmalgam c.pu.le).Universal), (w : (puAmalgam c.pu.le).Universal)⁆ ∈
          ZM (puAmalgam c.pu.le) α :=
        hCX _ hzX _ hw
      have e : (⟨_, hw'U⟩ : ↥U) = ⟨_, hZαU hcz⟩ * w := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, commutatorElement_def]
        group
      have h2 : βv ⟨_, hZαU hcz⟩ = 1 := (hβk _).mpr fun k hk _ => by
        have hkn := (Subgroup.mem_normalizer_iff.mp (hKZ hk) _).mp hcz
        have e' : ⁅k, ⁅(z : (puAmalgam c.pu.le).Universal), (w : (puAmalgam c.pu.le).Universal)⁆⁆ =
            (k * ⁅(z : (puAmalgam c.pu.le).Universal), (w : (puAmalgam c.pu.le).Universal)⁆ * k⁻¹) *
              ⁅(z : (puAmalgam c.pu.le).Universal), (w : (puAmalgam c.pu.le).Universal)⁆⁻¹ := by
          rw [commutatorElement_def k]
        rw [e']
        exact Subgroup.mul_mem _ hkn (Subgroup.inv_mem _ hcz)
      rw [e, map_mul, h2, one_mul, hzb, SL2Model.e12_coe] at h1
      have h3 := congrFun h1 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h3
      rcases h3 with h3 | h3
      · exact absurd h3 hb0'
      · exact h3
    let f : ↥U →* Multiplicative F :=
      { toFun := fun u => Multiplicative.ofAdd ((Multiplicative.toAdd (βv u)) 1)
        map_one' := by simp
        map_mul' := fun a b => by simp [map_mul] }
    have hfs : Function.Surjective f := by
      intro a
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single 1 (Multiplicative.toAdd a)))
      refine ⟨u, ?_⟩
      show Multiplicative.ofAdd ((Multiplicative.toAdd (βv u)) 1) = a
      rw [hu]
      simp
    have hWker : W.subgroupOf U ≤ f.ker := fun w hw => by
      rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd ((Multiplicative.toAdd (βv w)) 1) = 1
      rw [hWline w (Subgroup.mem_subgroupOf.mp hw)]
      rfl
    have hidx : Fintype.card F ≤ W.relIndex U := by
      calc Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
        _ = Nat.card (Multiplicative F) := Nat.card_congr Multiplicative.ofAdd
        _ = Nat.card ↥f.range := by rw [MonoidHom.range_eq_top.mpr hfs, Subgroup.card_top]
        _ = f.ker.index := (Subgroup.index_ker f).symm
        _ ≤ (W.subgroupOf U).index := Subgroup.index_antitone hWker
    rw [hWdef, Subgroup.inf_relIndex_left] at hidx
    omega

theorem BadConf.exists_ptSub (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α')
    (hfar : FarNonDeg c α α') :
    ∃ δ₀ q₀, IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ₀ ∧
      IsPtOn (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) q₀ ∧
      Qv (puAmalgam c.pu.le) (geo _ α α' 1) ⊓ ptQ _ (geo _ α α' 2) q₀ ≤
        ptSub (puAmalgam c.pu.le) α δ₀ ⊔ Qv _ (geo _ α α' 2) := by
  have hc := hB.crit
  have hb4 := c.b4
  have hα := hc.1
  have hα' : IsMVtx (puAmalgam c.pu.le) α' := hc.isMVtx_right _ c.pu.hyp20
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγβ' : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 2) (geo _ α α' 3) :=
    adj_geo_crit hb4 hc (i := 2) (by omega)
  have hβ'α' : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 3) α' := by
    have := adj_geo_crit hb4 hc (i := 3) (by omega)
    rwa [show (3 : ℕ) + 1 = 4 from rfl, geo_four hb4 hc] at this
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  obtain ⟨p₀, hp₀, hZp⟩ := hB.exists_center h464 h465 h466a
  obtain ⟨δ₁, δ₂, h₁, h₂, h12, h1p, h2p⟩ := exists_two_isPtOn_ne h464 h465 h466a c hα hαβ p₀
  have hgood : ∀ {δ}, IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ →
      Fintype.card F ≤ (Qv (puAmalgam c.pu.le) (geo _ α α' 2)).relIndex (ptSub _ α δ) →
      ∃ δ₀ q₀, IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ₀ ∧
        IsPtOn (puAmalgam c.pu.le) (geo _ α α' 2) (geo _ α α' 1) q₀ ∧
        Qv (puAmalgam c.pu.le) (geo _ α α' 1) ⊓ ptQ _ (geo _ α α' 2) q₀ ≤
          ptSub (puAmalgam c.pu.le) α δ₀ ⊔ Qv _ (geo _ α α' 2) := fun {δ} hδ hI => by
    obtain ⟨q₀, hq₀, hY⟩ := exists_pencil_le_ptQ h464 h465 h466a c hγ hβγ.symm hα hαβ hδ
      (hB.nondeg.2 δ hδ)
    exact ⟨δ, q₀, hδ, hq₀, qv_inf_ptQ_le_ptSub_sup h464 h465 h466a c hγ hβγ.symm hq₀ hY hI⟩
  have hbad : ∀ {δ}, IsPtOn (puAmalgam c.pu.le) α (geo _ α α' 1) δ → δ ≠ p₀ →
      (Qv (puAmalgam c.pu.le) (geo _ α α' 2)).relIndex (ptSub _ α δ) < Fintype.card F →
      ZM (puAmalgam c.pu.le) (geo _ α α' 2) ≤ ptSub _ α δ := fun {δ} hδ hne hI =>
    (zm_le_usup_sup_zh h464 h465 c hγ hβγ.symm hγβ'
      (usup_geo_three_ne h464 h465 h466a c hc).symm hα' hβ'α'.symm hfar).trans
      (sup_le (hB.usup_le_ptSub h464 h465 h466a hp₀ hZp hδ hne hI)
        ((zh_le_zm _ hαβ).trans (zm_le_ptSub c hα hδ)))
  by_cases hI₁ : Fintype.card F ≤ (Qv (puAmalgam c.pu.le) (geo _ α α' 2)).relIndex
      (ptSub _ α δ₁)
  · exact hgood h₁ hI₁
  by_cases hI₂ : Fintype.card F ≤ (Qv (puAmalgam c.pu.le) (geo _ α α' 2)).relIndex
      (ptSub _ α δ₂)
  · exact hgood h₂ hI₂
  exact (hB.false_of_zm_le_ptSub h464 h465 h466a h₁ h₂ h12 (hbad h₁ h1p (by omega))
    (hbad h₂ h2p (by omega))).elim

end CFSG.Quasithin.MS93.S46R
