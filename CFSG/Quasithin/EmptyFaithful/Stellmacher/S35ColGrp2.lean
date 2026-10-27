module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColGrp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Col

open S35.Std
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Uc_inf_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Uc δ ⊓ Cb δ = Zv δ := by
  apply le_antisymm
  · rintro x ⟨hxU, hxC⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := S34.exists_mul_of_mem_sup
      (fun a ha b hb => Vn_comm hS δ (comm_Lr_le_Vn hS δ ha) (Std.Zv_le_Vn_S5 hS hδ hb)) hxU
    have hzC : z ∈ Cb δ := S34.Zv_le_Cb hS.glob hδ hz
    have huC : u ∈ Cb δ := by
      have := (Cb δ).mul_mem hxC ((Cb δ).inv_mem hzC)
      rwa [mul_inv_cancel_right] at this
    exact (Zv δ).mul_mem (Cb_inf_comm_le hS hδ ⟨huC, hu⟩) hz
  · exact le_inf (Zv_le_Uc δ) (S34.Zv_le_Cb hS.glob hδ)

theorem Uc_sup_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Uc δ ⊔ Cb δ = Vn δ := by
  apply le_antisymm (sup_le (Uc_le_Vn hS hδ) (S34.Cb_le_Vn δ))
  rw [← comm_sup_Cb hS hδ]
  exact sup_le_sup_right le_sup_left _

theorem exists_mul_Uc_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {x : G}
    (hx : x ∈ Vn δ) : ∃ u ∈ Uc δ, ∃ c ∈ Cb δ, x = u * c := by
  rw [← Uc_sup_Cb hS hδ] at hx
  exact S34.exists_mul_of_mem_sup (fun a ha b hb => Vn_comm hS δ (Uc_le_Vn hS hδ ha)
    (S34.Cb_le_Vn δ hb)) hx

theorem cm_mul (hS : Sit H M S) {δ : Geo H M} {f x y : G} (hf : f ∈ stab δ) (hx : x ∈ Vn δ)
    (hy : y ∈ Vn δ) :
    f * (x * y) * f⁻¹ * (x * y)⁻¹ = (f * x * f⁻¹ * x⁻¹) * (f * y * f⁻¹ * y⁻¹) := by
  have h : x⁻¹ * (f * y * f⁻¹ * y⁻¹) = (f * y * f⁻¹ * y⁻¹) * x⁻¹ :=
    Vn_comm hS δ ((Vn δ).inv_mem hx) ((Vn δ).mul_mem (conj_Vn hf hy) ((Vn δ).inv_mem hy))
  calc f * (x * y) * f⁻¹ * (x * y)⁻¹
      = (f * x * f⁻¹) * ((f * y * f⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = (f * x * f⁻¹) * (x⁻¹ * (f * y * f⁻¹ * y⁻¹)) := by rw [h]
    _ = (f * x * f⁻¹ * x⁻¹) * (f * y * f⁻¹ * y⁻¹) := by group

theorem cm_mem_Vn (_hS : Sit H M S) {δ : Geo H M} {f x : G} (hf : f ∈ stab δ) (hx : x ∈ Vn δ) :
    f * x * f⁻¹ * x⁻¹ ∈ Vn δ := (Vn δ).mul_mem (conj_Vn hf hx) ((Vn δ).inv_mem hx)

@[expose] def Chat (hS : Sit H M S) {δ : Geo H M} (_hδ : vtype δ = false) : Subgroup G where
  carrier := {c | c ∈ Cb δ ∧ ∀ f ∈ stab δ, f * c * f⁻¹ * c⁻¹ ∈ Zv δ}
  one_mem' := ⟨(Cb δ).one_mem, fun f _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
    refine ⟨(Cb δ).mul_mem hxC hyC, fun f hf => ?_⟩
    rw [cm_mul hS hf (S34.Cb_le_Vn δ hxC) (S34.Cb_le_Vn δ hyC)]
    exact (Zv δ).mul_mem (hx f hf) (hy f hf)
  inv_mem' := by
    rintro x ⟨hxC, hx⟩
    refine ⟨(Cb δ).inv_mem hxC, fun f hf => ?_⟩
    have h := cm_mul hS hf (S34.Cb_le_Vn δ hxC) (S34.Cb_le_Vn δ ((Cb δ).inv_mem hxC))
    rw [mul_inv_cancel, show f * (1 : G) * f⁻¹ * (1 : G)⁻¹ = 1 by group] at h
    rw [eq_inv_of_mul_eq_one_right h.symm]
    exact (Zv δ).inv_mem (hx f hf)

theorem Zv_le_Chat (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Zv δ ≤ Chat hS hδ := fun z hz => by
  refine ⟨S34.Zv_le_Cb hS.glob hδ hz, fun f hf => ?_⟩
  rw [Zv_cent hS hδ hf hz]
  simp

theorem Chat_le_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Chat hS hδ ≤ Cb δ := fun _ hx => hx.1

theorem comm_mem_Zv_nbr (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) {a z : G} (ha : a ∈ stab δ ⊓ stab l) (hz : z ∈ Zv l) :
    a * z * a⁻¹ * z⁻¹ ∈ Zv δ := by
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) hz
  rw [Subgroup.commutator_comm] at h1
  have h2 := S34.aon_edge hS.glob hδ hl (g := a) ⟨ha.2, ha.1⟩
  have h3 : ⁅Zv l, Subgroup.zpowers a⁆ ≤ Zv δ := by
    by_cases hq : a ∈ Qv l
    · rw [h2.1 hq]; exact bot_le
    · rw [h2.2 hq]
  have h4 := h3 h1
  rwa [commutatorElement_def] at h4

theorem comm_Cb_of_nbr (hS : Sit H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) {u c z : G} (hu : u ∈ Uc δ) (hc : c ∈ Cb δ) (hz : z ∈ Zv μ)
    (hzuc : z = u * c) {d : G} (hd : d ∈ stab δ ⊓ stab μ) : d * c * d⁻¹ * c⁻¹ ∈ Zv δ := by
  have hz' := comm_mem_Zv_nbr hS hδ hμ hd hz
  have huV : u ∈ Vn δ := Uc_le_Vn hS hδ hu
  have hcV : c ∈ Vn δ := S34.Cb_le_Vn δ hc
  have hw1 : d * u * d⁻¹ * u⁻¹ ∈ Uc δ :=
    (Uc δ).mul_mem (conj_Uc hS hδ hd.1 hu) ((Uc δ).inv_mem hu)
  have hw2 : d * c * d⁻¹ * c⁻¹ ∈ Cb δ :=
    (Cb δ).mul_mem (conj_Cb hS hδ hd.1 hc) ((Cb δ).inv_mem hc)
  have hcomm : u⁻¹ * (d * c * d⁻¹ * c⁻¹) = (d * c * d⁻¹ * c⁻¹) * u⁻¹ :=
    Vn_comm hS δ ((Vn δ).inv_mem huV) (cm_mem_Vn hS hd.1 hcV)
  have heq : (d * u * d⁻¹ * u⁻¹) * (d * c * d⁻¹ * c⁻¹) = d * z * d⁻¹ * z⁻¹ := by
    subst hzuc
    calc (d * u * d⁻¹ * u⁻¹) * (d * c * d⁻¹ * c⁻¹)
        = (d * u * d⁻¹) * (u⁻¹ * (d * c * d⁻¹ * c⁻¹)) := by group
      _ = (d * u * d⁻¹) * ((d * c * d⁻¹ * c⁻¹) * u⁻¹) := by rw [hcomm]
      _ = d * (u * c) * d⁻¹ * (u * c)⁻¹ := by group
  have hw2U : d * c * d⁻¹ * c⁻¹ ∈ Uc δ := by
    have : d * c * d⁻¹ * c⁻¹ = (d * u * d⁻¹ * u⁻¹)⁻¹ * (d * z * d⁻¹ * z⁻¹) := by
      rw [← heq]; group
    rw [this]
    exact (Uc δ).mul_mem ((Uc δ).inv_mem hw1) (Zv_le_Uc δ hz')
  have h5 : d * c * d⁻¹ * c⁻¹ ∈ Uc δ ⊓ Cb δ := ⟨hw2U, hw2⟩
  rwa [Uc_inf_Cb hS hδ] at h5

@[expose] def FixC (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) (c : G) : Subgroup G where
  carrier := {f | f ∈ stab δ ∧ f * c * f⁻¹ * c⁻¹ ∈ Zv δ}
  one_mem' := ⟨(stab δ).one_mem, by simp⟩
  mul_mem' := by
    rintro f g ⟨hf, hfz⟩ ⟨hg, hgz⟩
    refine ⟨(stab δ).mul_mem hf hg, ?_⟩
    have e : (f * g) * c * (f * g)⁻¹ * c⁻¹ =
        (f * (g * c * g⁻¹ * c⁻¹) * f⁻¹) * (f * c * f⁻¹ * c⁻¹) := by group
    rw [e, Zv_cent hS hδ hf hgz]
    exact (Zv δ).mul_mem hgz hfz
  inv_mem' := by
    rintro f ⟨hf, hfz⟩
    refine ⟨(stab δ).inv_mem hf, ?_⟩
    have e : f⁻¹ * c * f⁻¹⁻¹ * c⁻¹ = (f⁻¹ * (f * c * f⁻¹ * c⁻¹) * f⁻¹⁻¹)⁻¹ := by group
    rw [e, Zv_cent hS hδ ((stab δ).inv_mem hf) hfz]
    exact (Zv δ).inv_mem hfz

theorem Zv_nbr_le_Uc_sup_Chat (hS : Sit H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) : Zv μ ≤ Uc δ ⊔ Chat hS hδ := by
  intro z hz
  obtain ⟨u, hu, c, hc, hzuc⟩ := exists_mul_Uc_Cb hS hδ (Std.Zv_le_Vn hμ hz)
  have hsyl := sylow_stab_inf_left hS.glob.amalg hμ
  have hF : stab δ ≤ oTwoRes (stab δ) ⊔ (stab δ ⊓ stab μ) :=
    le_oTwoRes_sup_of_isSylowTwoOf hsyl
  have hFix : stab δ ≤ FixC hS hδ c := by
    refine hF.trans (sup_le (fun a ha => ⟨oTwoRes_le _ ha, ?_⟩) (fun d hd => ⟨hd.1, ?_⟩))
    · exact Cb_comm_L δ c hc a ha
    · exact comm_Cb_of_nbr hS hδ hμ hu hc hz hzuc hd
  have hcC : c ∈ Chat hS hδ := ⟨hc, fun f hf => (hFix hf).2⟩
  rw [hzuc]
  exact Subgroup.mul_mem_sup hu hcC

theorem Vn_le_Uc_sup_Chat (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Vn δ ≤ Uc δ ⊔ Chat hS hδ :=
  iSup₂_le fun _ hμ => Zv_nbr_le_Uc_sup_Chat hS hδ hμ

theorem Cb_le_Chat (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) :
    Cb δ ≤ Chat hS hδ := by
  intro x hxC
  obtain ⟨u, hu, c, hc, rfl⟩ := S34.exists_mul_of_mem_sup
    (fun a ha b hb => Vn_comm hS δ (Uc_le_Vn hS hδ ha)
      (S34.Cb_le_Vn δ (Chat_le_Cb hS hδ hb)))
    (Vn_le_Uc_sup_Chat hS hδ (S34.Cb_le_Vn δ hxC))
  have huC : u ∈ Cb δ := by
    have := (Cb δ).mul_mem hxC ((Cb δ).inv_mem (Chat_le_Cb hS hδ hc))
    rwa [mul_inv_cancel_right] at this
  have huZ : u ∈ Zv δ := by
    have h5 : u ∈ Uc δ ⊓ Cb δ := ⟨hu, huC⟩
    rwa [Uc_inf_Cb hS hδ] at h5
  exact (Chat hS hδ).mul_mem (Zv_le_Chat hS hδ huZ) hc

theorem comm_Cb_le_Zv (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {f c : G}
    (hf : f ∈ stab δ) (hc : c ∈ Cb δ) : f * c * f⁻¹ * c⁻¹ ∈ Zv δ :=
  (Cb_le_Chat hS hδ hc).2 f hf

theorem comm_Vn_le_Uc (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {f v : G}
    (hf : f ∈ stab δ) (hv : v ∈ Vn δ) : f * v * f⁻¹ * v⁻¹ ∈ Uc δ := by
  obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_Uc_Cb hS hδ hv
  rw [cm_mul hS hf (Uc_le_Vn hS hδ hu) (S34.Cb_le_Vn δ hc)]
  exact (Uc δ).mul_mem ((Uc δ).mul_mem (conj_Uc hS hδ hf hu) ((Uc δ).inv_mem hu))
    (Zv_le_Uc δ (comm_Cb_le_Zv hS hδ hf hc))

theorem comm_mem_Zv_of_mem_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {f v : G}
    (hf : f ∈ stab δ) (hv : v ∈ Vn δ) (h : f * v * f⁻¹ * v⁻¹ ∈ Cb δ) :
    f * v * f⁻¹ * v⁻¹ ∈ Zv δ := by
  have h5 : f * v * f⁻¹ * v⁻¹ ∈ Uc δ ⊓ Cb δ := ⟨comm_Vn_le_Uc hS hδ hf hv, h⟩
  rwa [Uc_inf_Cb hS hδ] at h5

end S35.Col

end F53.Stellmacher

end CFSG.Quasithin
