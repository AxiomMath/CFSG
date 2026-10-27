module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20AAlg

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Vst_le_Vn (δ : Geo H M) : Vst δ ≤ Vn δ :=
  commutator_le_left_of_le_normalizer ((pCoreOf_le 2 _).trans (stab_le_normalizer_Vn δ))

omit [Finite G] in
theorem stab_le_normalizer_Vst (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Vst δ : Set G) :=
  le_normalizer_commutator (stab_le_normalizer_Vn δ) (le_normalizer_pCoreOf 2 _)

theorem Vst_comm (hA : F53Amalgam H M S) (hb : 3 ≤ bMin H M) (δ : Geo H M) {x y : G}
    (hx : x ∈ Vst δ) (hy : y ∈ Vst δ) : x * y = y * x :=
  isElemAbelian_comm (isElemAbelian_Vn hA hb δ) (Vst_le_Vn δ hx) (Vst_le_Vn δ hy)

theorem Vst_sq (hA : F53Amalgam H M S) (hb : 3 ≤ bMin H M) (δ : Geo H M) {x : G}
    (hx : x ∈ Vst δ) : x * x = 1 := by
  rw [← pow_two]
  exact isElemAbelian_pow_eq_one (isElemAbelian_Vn hA hb δ) (Vst_le_Vn δ hx)

omit [Finite G] in
theorem A_le_Vst {δ l : Geo H M} (hl : l ∈ nbrs δ) : ⁅Zv l, Qv δ⁆ ≤ Vst δ :=
  Subgroup.commutator_mono (Sit43.Zv_le_Vn_nbrs hl) le_rfl

variable {α δ : Geo H M}

theorem Zv_le_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) : Zv δ ≤ Yv δ :=
  le_iInf₂ fun _ hl => hs.Zv_le_Zv_nbr hA h26 hδ hl

theorem relIndex_Zv_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) : (Zv δ).relIndex (Yv δ) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (Zv δ) (Yv δ)
  rw [inf_eq_left.mpr (Zv_le_Yv hA h26 hs hδ), hs.card_Zv_true hA h26 hδ,
    hs.card_Yv hA h26 hδ] at h1
  omega

theorem relIndex_A_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) {l : Geo H M} (hl : l ∈ nbrs δ)
    (h4 : Nat.card (Vn δ) = 2 ^ 6) : (⁅Zv l, Qv δ⁆).relIndex (Vst δ) = 2 := by
  have h1 := Subgroup.relIndex_mul_card ⁅Zv l, Qv δ⁆ (Vst δ)
  rw [inf_eq_left.mpr (A_le_Vst hl), hs.card_comm_Qv hA h26 hδ hl,
    hs.card_Vst hA h26 hb hδ h4] at h1
  norm_num at h1
  omega

theorem A_inf_A_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) {l l' : Geo H M} (hl : l ∈ nbrs δ) (hl' : l' ∈ nbrs δ) (hne : l ≠ l') :
    ⁅Zv l, Qv δ⁆ ⊓ ⁅Zv l', Qv δ⁆ ≤ Yv δ := by
  rw [← hs.inf_Zv_eq_Yv hA h26 hδ hl hl' hne]
  exact inf_le_inf (hs.comm_le_Zv hA h26 hδ hl) (hs.comm_le_Zv hA h26 hδ hl')

theorem comm_A_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) {l : Geo H M} (hl : l ∈ nbrs δ) : ⁅⁅Zv l, Qv δ⁆, Qv δ⁆ = Yv δ := by
  have hlv : vtype l = false := Sit43.vtype_false_of_adj hδ hl
  have hQδl : Qv δ ≤ stab l := Qv_le_stab_of_mem_nbrs hA hl
  have h1 := commutator_sup_eq_of_centralizes (Z := ⁅Zv l, Qv δ⁆) (C := Qv l) (T := Qv δ)
    (fun c hc z hz => (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l hc) z
      (hs.comm_le_Zv hA h26 hδ hl hz)).symm)
    (hQδl.trans (le_normalizer_pCoreOf 2 (stab l)))
    (le_normalizer_commutator (hQδl.trans (stab_le_normalizer_Zv hA l)) Subgroup.le_normalizer)
  rw [← h1, hs.sup_Qv_edge hA h26 hlv (nbrs_symm hl), hs.Yv_eq_comm_comm hA h26 hδ hl,
    hs.comm_Qv_eq hA h26 hδ hl]

theorem comm_Qv_Yv_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) {q y : G} (hq : q ∈ Qv δ) (hy : y ∈ Yv δ) : ⁅q, y⁆ ∈ Zv δ := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  rw [← hs.comm_Yv_Qv hA h26 hδ hl, ← commutatorElement_inv]
  exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy hq)

theorem comm_Qv_A_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) {l : Geo H M} (hl : l ∈ nbrs δ) {q x : G} (hq : q ∈ Qv δ)
    (hx : x ∈ ⁅Zv l, Qv δ⁆) : ⁅q, x⁆ ∈ Yv δ := by
  rw [← comm_A_Qv hA h26 hs hδ hl, ← commutatorElement_inv]
  exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hx hq)

theorem comm_Zv_of_mem_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) {g z : G} (hg : g ∈ stab δ) (hz : z ∈ Zv δ) : g * z = z * g :=
  Subgroup.mem_centralizer_iff.mp (hs.Zv_le_centerOf hA h26 hδ hz).2 g hg

theorem exists_comm_not_mem_of_A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) {l : Geo H M} (hl : l ∈ nbrs δ) {v : G}
    (hv : v ∈ ⁅Zv l, Qv δ⁆) (hvY : v ∉ Yv δ) : ∃ q ∈ Qv δ, ⁅q, v⁆ ∉ Zv δ := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅⁅Zv l, Qv δ⁆, Qv δ⁆ ≤ Zv δ := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    rw [← commutatorElement_inv]
    refine Subgroup.inv_mem _ ?_
    by_cases hxY : x ∈ Yv δ
    · exact comm_Qv_Yv_mem hA h26 hs hδ hq hxY
    · have h1 : v⁻¹ * x ∈ Yv δ :=
        inv_mul_mem_of_relIndex_two (hs.relIndex_Yv_comm hA h26 hδ hl) hv hx hvY hxY
      have hz := comm_Qv_Yv_mem hA h26 hs hδ hq h1
      have hcomm : Commute ⁅q, v⁻¹ * x⁆ v :=
        Vst_comm hA hb δ (hs.Yv_le_Vst hA h26 hδ (Zv_le_Yv hA h26 hs hδ hz)) (A_le_Vst hl hv)
      have e : ⁅q, x⁆ = ⁅q, v * (v⁻¹ * x)⁆ := by rw [mul_inv_cancel_left]
      rw [e, comm_mul_right hcomm]
      exact (Zv δ).mul_mem (hcon q hq) hz
  rw [comm_A_Qv hA h26 hs hδ hl] at hle
  have := Subgroup.card_le_of_le hle
  rw [hs.card_Yv hA h26 hδ, hs.card_Zv_true hA h26 hδ] at this
  omega

theorem exists_mem_A_not_mem_Yv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) {l : Geo H M} (hl : l ∈ nbrs δ) :
    ∃ b ∈ ⁅Zv l, Qv δ⁆, b ∉ Yv δ := by
  by_contra hcon
  push Not at hcon
  have := Subgroup.card_le_of_le (show ⁅Zv l, Qv δ⁆ ≤ Yv δ from hcon)
  rw [hs.card_comm_Qv hA h26 hδ hl, hs.card_Yv hA h26 hδ] at this
  omega

theorem mem_A_of_mem_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (h4 : Nat.card (Vn δ) = 2 ^ 6) {v : G}
    (hv : v ∈ Vst δ) : ∃ l ∈ nbrs δ, v ∈ ⁅Zv l, Qv δ⁆ := by
  obtain ⟨l₁, hl₁⟩ := exists_adj_of_vtype_true hA hδ
  obtain ⟨l₂, l₃, h29⟩ := hs.exists_sit29 hA h26 hδ hl₁
  have hl₂ : l₂ ∈ nbrs δ := h29.n₂
  have hl₃ : l₃ ∈ nbrs δ := h29.n₃
  by_cases h1 : v ∈ ⁅Zv l₁, Qv δ⁆
  · exact ⟨l₁, hl₁, h1⟩
  by_cases h2 : v ∈ ⁅Zv l₂, Qv δ⁆
  · exact ⟨l₂, hl₂, h2⟩
  refine ⟨l₃, hl₃, ?_⟩
  obtain ⟨b, hb2, hbY⟩ := exists_mem_A_not_mem_Yv hA h26 hs hδ hl₂
  have hbV := A_le_Vst hl₂ hb2
  have hb1 : b ∉ ⁅Zv l₁, Qv δ⁆ := fun h =>
    hbY (A_inf_A_le hA h26 hs hδ hl₁ hl₂ h29.ne₁₂ ⟨h, hb2⟩)
  have hb3 : b ∉ ⁅Zv l₃, Qv δ⁆ := fun h =>
    hbY (A_inf_A_le hA h26 hs hδ hl₂ hl₃ h29.ne₂₃ ⟨hb2, h⟩)
  have hc1 : b⁻¹ * v ∈ ⁅Zv l₁, Qv δ⁆ :=
    inv_mul_mem_of_relIndex_two (relIndex_A_Vst hA h26 hs hb hδ hl₁ h4) hbV hv hb1 h1
  have hcY : b⁻¹ * v ∉ Yv δ := fun h =>
    h2 (by simpa using (⁅Zv l₂, Qv δ⁆).mul_mem hb2 (hs.Yv_le_comm hA h26 hδ hl₂ h))
  have hc3 : b⁻¹ * v ∉ ⁅Zv l₃, Qv δ⁆ := fun h =>
    hcY (A_inf_A_le hA h26 hs hδ hl₁ hl₃ h29.ne₁₃ ⟨hc1, h⟩)
  have := mul_mem_of_relIndex_two (relIndex_A_Vst hA h26 hs hb hδ hl₃ h4) hbV
    ((Vst δ).mul_mem ((Vst δ).inv_mem hbV) hv) hb3 hc3
  simpa using this

theorem exists_comm_not_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (h4 : Nat.card (Vn δ) = 2 ^ 6) {v : G}
    (hv : v ∈ Vst δ) (hvY : v ∉ Yv δ) : ∃ q ∈ Qv δ, ⁅q, v⁆ ∉ Zv δ := by
  obtain ⟨l, hl, hvl⟩ := mem_A_of_mem_Vst hA h26 hs hb hδ h4 hv
  exact exists_comm_not_mem_of_A hA h26 hs hb hδ hl hvl hvY

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A
