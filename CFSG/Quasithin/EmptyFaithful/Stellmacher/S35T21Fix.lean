module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColGrp3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Mbl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2bFix
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21Red2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

open S35.II S35.Fin S35.F2b S35.Ch2
open S34 (Cb)
open S35.Col (Uc)

namespace S35.T21

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem card_fixQ_le {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    Nat.card (F2b.fixQ orth D (ellO (fixPt D))) ≤ 4 := by
  obtain ⟨a, b, c, d, h, hdec⟩ := F2b.exists_decomp hD
  have := F2b.card_fixQ_orth hD (isCentInv_zc hD) h hdec
  rw [F2b.card_ellO] at this
  omega

variable {δ : Geo H M}

omit [Finite G] in
theorem act_mul_inv_mem_img (c : Chart2 δ) (g : ↥(stab δ)) (x : ↥(Vn δ)) {U : Subgroup G}
    (hU : (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ ∈ U) :
    orth.act (c.θ g) (c.π x) * (c.π x)⁻¹ ∈ c.img U := by
  have hV : (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ ∈ Vn δ :=
    (Vn δ).mul_mem (S35.Ch.conj_mem_Vn g.2 x.2) ((Vn δ).inv_mem x.2)
  refine (c.mem_img_iff').mpr ⟨⟨_, hV⟩, hU, ?_⟩
  have : (⟨(g : G) * x * (g : G)⁻¹ * (x : G)⁻¹, hV⟩ : ↥(Vn δ)) =
      S35.Ch.conjV g x * x⁻¹ := rfl
  rw [this, map_mul, map_inv, c.π_conj]

theorem fixZ (hS : Sit H M S) : FixZ H M := by
  intro δ l hδ hl
  obtain ⟨c⟩ := Ch2.exists_chart2 hS hδ
  have hlV : Zv l ≤ Vn δ := Std.Zv_le_Vn hl
  have hCV : Cb δ ≤ Vn δ := S34.Cb_le_Vn δ
  have hVn : Vn δ ≤ Subgroup.normalizer (Zv l : Set G) := fun v hv =>
    mem_normalizer_of_comm fun b hb => Col.Vn_comm hS δ hv (hlV hb)
  have hCn : Cb δ ≤ Subgroup.normalizer (Zv l : Set G) := fun x hx =>
    mem_normalizer_of_comm fun b hb => Col.Vn_comm hS δ (hCV hx) (hlV hb)
  have hD : Nat.card (c.Dl l) = 8 := c.card_Dl hS hl
  have hmemY : ∀ y, y ∈ fixSecIn (stab δ ⊓ stab l) (Zv l) (Vn δ) ↔
      y ∈ Vn δ ∧ ∀ a ∈ stab δ ⊓ stab l, a * y * a⁻¹ * y⁻¹ ∈ Zv l := fun y =>
    F53B3.N37.mem_fixSecIn_iff hlV hVn
  set Y := fixSecIn (stab δ ⊓ stab l) (Zv l) (Vn δ) with hY
  have hYV : Y ≤ Vn δ := fun y hy => ((hmemY y).mp hy).1
  have hZδl := Std.Zv_le_Zv_of_nbr hS hδ hl
  have hCY : Cb δ ≤ Y := fun x hx => (hmemY x).mpr ⟨hCV hx, fun a ha =>
    hZδl (Col.comm_Cb_le_Zv hS hδ ha.1 hx)⟩
  have hZY : Zv l ≤ Y := fun z hz => (hmemY z).mpr ⟨hlV hz, fun a ha =>
    hZδl (Col.comm_mem_Zv_nbr hS hδ hl ha hz)⟩
  have hZC : Zv l ⊔ Cb δ ≤ Y := sup_le hZY hCY
  have hm : Nat.card (c.img Y) = (Cb δ).relIndex Y := c.card_img' hYV
  have h2 : (Cb δ).relIndex (Zv l ⊔ Cb δ) = 2 := by
    rw [← c.card_img' (sup_le hlV hCV), c.img_sup_Cb hlV, c.img_Zv_nbr hS hδ hl]
    exact card_zpowers_vp _
  have h3 : (Cb δ).relIndex Y = 2 * (Zv l ⊔ Cb δ).relIndex Y := by
    rw [← h2]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hZC).symm
  have h4 : (Zv l).relIndex Y = (Zv l).relIndex (Zv l ⊔ Cb δ) * (Zv l ⊔ Cb δ).relIndex Y :=
    (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hZC).symm
  have h5 : (Zv l).relIndex (Zv l ⊔ Cb δ) = (Zv δ).relIndex (Cb δ) := by
    have := relIndex_inf_eq_relIndex_sup hCn
    rw [S34.Cb_inf_Zv_eq hS.glob hδ hl, sup_comm] at this
    exact this.symm
  have hb1 : c.img Y ≤ F2b.fixQ orth (c.Dl l) (ellO (fixPt (c.Dl l))) := by
    intro w hw
    obtain ⟨x, hxY, rfl⟩ := (c.mem_img_iff').mp hw
    rw [F2b.mem_fixQ]
    intro σ hσ
    have hσ' : σ ∈ c.bar (stab δ ⊓ stab l) := hσ
    obtain ⟨a, haD, rfl⟩ := (c.mem_bar_iff).mp hσ'
    have := act_mul_inv_mem_img c a x (U := Zv l) (((hmemY x).mp hxY).2 a haD)
    rw [c.img_Zv_nbr hS hδ hl] at this
    exact this
  have hb2 : Cb δ ≠ Zv δ → c.img Y ≤ fixW orth (c.Dl l) := by
    intro hne w hw
    obtain ⟨x, hxY, rfl⟩ := (c.mem_img_iff').mp hw
    rw [mem_fixW]
    intro σ hσ
    have hσ' : σ ∈ c.bar (stab δ ⊓ stab l) := hσ
    obtain ⟨a, haD, rfl⟩ := (c.mem_bar_iff).mp hσ'
    have hx' := (hmemY x).mp hxY
    have h1 : (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ ∈ Zv l := hx'.2 a haD
    have h2 : (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ ∈ Uc δ :=
      Col.comm_Vn_le_Uc hS hδ a.2 x.2
    have h3 : (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ ∈ Zv l ⊓ Uc δ := ⟨h1, h2⟩
    rw [Col.Zv_nbr_inf_Uc hS hδ hl hne] at h3
    exact (c.comm_mem_iff a x).mp (S34.Zv_le_Cb hS.glob hδ h3)
  have hk := Col.relIndex_Zv_Cb_le hS hδ
  have hk0 : (Zv δ).relIndex (Cb δ) ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hm4 : Nat.card (c.img Y) ≤ 4 :=
    (Subgroup.card_le_of_le hb1).trans (card_fixQ_le hD)
  rw [h4, h5]
  have hmb : Nat.card (c.img Y) = 2 * (Zv l ⊔ Cb δ).relIndex Y := by rw [hm, h3]
  by_cases hk1 : (Zv δ).relIndex (Cb δ) = 1
  · rw [hk1]
    omega
  · have hk2 : (Zv δ).relIndex (Cb δ) = 2 := by omega
    have hne : Cb δ ≠ Zv δ := fun h =>
      hk1 (Subgroup.relIndex_eq_one.mpr h.le)
    have hm2 : Nat.card (c.img Y) ≤ 2 :=
      (Subgroup.card_le_of_le (hb2 hne)).trans (card_fixW_sylow hD).le
    rw [hk2]
    omega

end S35.T21

end F53.Stellmacher

end CFSG.Quasithin
