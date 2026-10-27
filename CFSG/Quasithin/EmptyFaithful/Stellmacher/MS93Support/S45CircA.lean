module

public import CFSG.Quasithin.MS93.S45Y1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support.S45SplitRestrict

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem uloc_le_vcirc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Uloc c.hyp.le L δ ≤ Vcirc c.hyp.le L δ := by
  rw [← c.commutator_uloc_ltil hδ]
  exact Subgroup.commutator_mono ((uloc_le_zm c.hyp c.full hδ).trans (zm_le_vv c.hyp hδ)) le_rfl

theorem stab_le_normalizer_vcirc (δ : Vtx (puAmalgam c.hyp.le)) :
    stab (puAmalgam c.hyp.le) δ ≤
      Subgroup.normalizer (Vcirc c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [Vcirc, Subgroup.map_commutator,
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv c.hyp δ hg),
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_ltil c.hyp δ hg)]

theorem hloc_le_vcirc (δ : Vtx (puAmalgam c.hyp.le)) :
    Hloc c.hyp.le L δ ≤ Vcirc c.hyp.le L δ :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((qv_le_stab _ δ).trans (stab_le_normalizer_vcirc c δ))

theorem hloc_le_zloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Hloc c.hyp.le L δ ≤ Zloc c.hyp.le L δ :=
  (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hδ)

theorem uloc_sup_hloc_le {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ ≤ Vcirc c.hyp.le L δ ⊓ ZM _ δ :=
  sup_le (le_inf (uloc_le_vcirc c hδ) (uloc_le_zm c.hyp c.full hδ))
    (le_inf (hloc_le_vcirc c δ) ((hloc_le_zloc c hδ).trans (zloc_le_zm c.hyp c.full hδ)))

theorem stab_le_normalizer_hloc (δ : Vtx (puAmalgam c.hyp.le)) :
    stab (puAmalgam c.hyp.le) δ ≤
      Subgroup.normalizer (Hloc c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [Hloc, Subgroup.map_commutator,
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_vcirc c δ hg),
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ δ hg)]

theorem stab_le_normalizer_uloc_sup_hloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    stab (puAmalgam c.hyp.le) δ ≤ Subgroup.normalizer
      ((Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ : Subgroup _) : Set (puAmalgam c.hyp.le).Universal) := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.hyp c.via hδ
  exact le_normalizer_sup hψ.1 (stab_le_normalizer_hloc c δ)

theorem uloc_le_stab {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Uloc c.hyp.le L δ ≤ stab (puAmalgam c.hyp.le) δ :=
  (uloc_le_zm c.hyp c.full hδ).trans ((zm_le_qv_self _ hδ c.hyp.critDist_pos).trans
    (qv_le_stab _ _))

theorem commutator_zm_mem {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {a : (puAmalgam c.hyp.le).Universal} (ha : a ∈ stab (puAmalgam c.hyp.le) δ)
    {z : (puAmalgam c.hyp.le).Universal} (hz : z ∈ ZM (puAmalgam c.hyp.le) δ) :
    a * z * a⁻¹ * z⁻¹ ∈ Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ := by
  have h := c.hyp
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hZc := zloc_le_centralizer_stab h c.full hδ
  have hn : Uloc h.le L δ ≤ Subgroup.normalizer (Zloc h.le L δ : Set _) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hZc) (uloc_le_stab c hδ hu))
  rw [zm_eq_uloc_sup_zloc h c.full hδ, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hz
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hz
  have hwa : a * w * a⁻¹ = w := by
    rw [(Subgroup.mem_centralizer_iff.mp (hZc hw)) a ha, mul_inv_cancel_right]
  have hua : a * u * a⁻¹ ∈ Uloc h.le L δ := (Subgroup.mem_normalizer_iff.mp (hψ.1 ha) u).mp hu
  have e : a * (u * w) * a⁻¹ * (u * w)⁻¹ = (a * u * a⁻¹) * u⁻¹ := by
    calc a * (u * w) * a⁻¹ * (u * w)⁻¹ = (a * u * a⁻¹) * (a * w * a⁻¹) * w⁻¹ * u⁻¹ := by group
      _ = (a * u * a⁻¹) * u⁻¹ := by rw [hwa]; group
  rw [e]
  exact Subgroup.mem_sup_left (mul_mem hua (inv_mem hu))

theorem commutator_vcirc_mem_of_ker {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (a : ↥(stab (puAmalgam c.hyp.le) δ)) (ha : ψ a = 1)
    {v : (puAmalgam c.hyp.le).Universal} (hv : v ∈ Vcirc c.hyp.le L δ) :
    (a : (puAmalgam c.hyp.le).Universal) * v * (a : (puAmalgam c.hyp.le).Universal)⁻¹ * v⁻¹ ∈
      Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ := by
  have hk : a ∈ (toSL3 ψ).ker := by
    rw [MonoidHom.mem_ker, toSL3_eq_one_iff']
    exact ha
  rw [c.ker_toSL3_eq hδ hψ, Subgroup.mem_subgroupOf] at hk
  have hc : ⁅(a : (puAmalgam c.hyp.le).Universal), v⁆ ∈ Hloc c.hyp.le L δ := by
    rw [Hloc, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hk hv
  rw [commutatorElement_def] at hc
  exact Subgroup.mem_sup_right hc

theorem exists_isSum_vcirc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1) :
    ∃ dual : Bool, IsSumOfNaturalModulesVia (stab _ δ) (Vcirc c.hyp.le L δ)
      (Vcirc c.hyp.le L δ ⊓ ZM _ δ) ψ dual 1 := by
  obtain ⟨dual, hd⟩ := c.exists_isSum_vhat hδ hψs hψ
  refine ⟨dual, isSumOfNaturalModulesVia_restrict hd le_sup_left (stab_le_normalizer_vcirc c δ)
    ?_ rfl⟩
  exact ((c.vcirc_le_vv δ).trans ((c.vv_le_qv' hδ).trans (qv_le_stab _ δ))).trans
    (stab_le_normalizer_zm _ δ)

theorem exists_mul_of_mem_zm {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {z : (puAmalgam c.hyp.le).Universal} (hz : z ∈ ZM (puAmalgam c.hyp.le) δ) :
    ∃ u ∈ Uloc c.hyp.le L δ, ∃ w ∈ Zloc c.hyp.le L δ, z = u * w := by
  have h := c.hyp
  have hZc := zloc_le_centralizer_stab h c.full hδ
  have hn : Uloc h.le L δ ≤ Subgroup.normalizer (Zloc h.le L δ : Set _) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hZc) (uloc_le_stab c hδ hu))
  rw [zm_eq_uloc_sup_zloc h c.full hδ, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hz
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hz
  exact ⟨u, hu, w, hw, rfl⟩

theorem commutator_inf_zloc_le_hloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (ha : Vcirc c.hyp.le L δ ⊓ ZM _ δ ≤ Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ)
    (hb : ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ ZM _ δ ≤ Vcirc c.hyp.le L δ) :
    ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ Zloc c.hyp.le L δ ≤ Hloc c.hyp.le L δ := by
  have h := c.hyp
  intro x hx
  obtain ⟨hxV, hxZ⟩ := Subgroup.mem_inf.mp hx
  have hxZM : x ∈ ZM (puAmalgam h.le) δ := zloc_le_zm h c.full hδ hxZ
  have hxUH := ha (Subgroup.mem_inf.mpr ⟨hb (Subgroup.mem_inf.mpr ⟨hxV, hxZM⟩), hxZM⟩)
  have hHZ := hloc_le_zloc c hδ
  have hn : Uloc h.le L δ ≤ Subgroup.normalizer (Hloc h.le L δ : Set _) :=
    (uloc_le_stab c hδ).trans (stab_le_normalizer_hloc c δ)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hxUH
  obtain ⟨u, hu, k, hk, rfl⟩ := Set.mem_mul.mp hxUH
  have huZ : u ∈ Zloc h.le L δ := by
    have := (Zloc h.le L δ).mul_mem hxZ ((Zloc h.le L δ).inv_mem (hHZ hk))
    rwa [mul_inv_cancel_right] at this
  have hu1 : u = 1 := by
    rw [← Subgroup.mem_bot, ← uloc_inf_zloc h c.full δ]
    exact Subgroup.mem_inf.mpr ⟨hu, huZ⟩
  rw [hu1, one_mul]
  exact hk

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
