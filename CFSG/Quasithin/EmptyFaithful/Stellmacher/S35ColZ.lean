module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Mbl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColGrp3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Col

open S35.Std S35.Fin S35.Ch S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mul_mem_of_relIndex_two {K V : Subgroup G} (h : K.relIndex V = 2) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) (ha' : a ∉ K) (hb' : b ∉ K) : a * b ∈ K := by
  have h2 : (K.subgroupOf V).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr
    ⟨fun h => absurd (Subgroup.mem_subgroupOf.mp h) ha',
      fun h => absurd (Subgroup.mem_subgroupOf.mp h) hb'⟩
  exact Subgroup.mem_subgroupOf.mp this

variable {δ : Geo H M} (c : Chart2 δ)

include c

theorem π_mem_zpowers (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ)
    {y : G} (hy : y ∈ Zv l) :
    c.π ⟨y, Std.Zv_le_Vn hl hy⟩ ∈ Subgroup.zpowers (vp (c.pt l)) := by
  have h := (c.mem_img_iff'.mpr ⟨⟨y, Std.Zv_le_Vn hl hy⟩, hy, rfl⟩ :
    c.π ⟨y, Std.Zv_le_Vn hl hy⟩ ∈ c.img (Zv l))
  rwa [c.img_Zv_nbr hS hδ hl] at h

theorem π_eq_vp (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ)
    {y : G} (hy : y ∈ Zv l) (hyC : y ∉ Cb δ) :
    c.π ⟨y, Std.Zv_le_Vn hl hy⟩ = vp (c.pt l) := by
  rcases (mem_zpowers_iff_of_mul_self (vp_mul_self (c.pt l))).mp (π_mem_zpowers c hS hδ hl hy)
    with h | h
  · exact absurd ((c.π_eq_one _).mp h) hyC
  · exact h

theorem comm_mem_Zv_of_pt (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) {g : G} (hg : g ∈ c.preθ (ptStab (c.pt l))) {y : G} (hy : y ∈ Zv l) :
    g * y * g⁻¹ * y⁻¹ ∈ Zv δ := by
  have hgS : g ∈ stab δ := c.preθ_le_stab _ hg
  have hθ : c.θ ⟨g, hgS⟩ (c.pt l) = c.pt l := mem_ptStab.mp ((c.mem_preθ_iff ⟨g, hgS⟩).mp hg)
  have hyV : y ∈ Vn δ := Std.Zv_le_Vn hl hy
  have hfix : orth.act (c.θ ⟨g, hgS⟩) (c.π ⟨y, hyV⟩) = c.π ⟨y, hyV⟩ := by
    rcases (mem_zpowers_iff_of_mul_self (vp_mul_self (c.pt l))).mp (π_mem_zpowers c hS hδ hl hy)
      with h | h
    · rw [h, map_one]
    · rw [h, act_vp, hθ]
  exact comm_mem_Zv_of_mem_Cb hS hδ hgS hyV ((c.comm_mem_iff ⟨g, hgS⟩ ⟨y, hyV⟩).mpr hfix)

theorem preθ_pt_le_normalizer_Zv (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : c.preθ (ptStab (c.pt l)) ≤ Subgroup.normalizer (Zv l : Set G) := by
  refine Chart2.le_normalizer_of_forall' fun g hg y hy => ?_
  have h := comm_mem_Zv_of_pt c hS hδ hl hg hy
  have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
  rw [e]
  exact (Zv l).mul_mem (Std.Zv_le_Zv_of_nbr hS hδ hl h) hy

theorem Mbl_eq_preθ (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Mbl δ l = c.preθ (ptStab (c.pt l)) :=
  c.Mbl_eq_preθ_of hS hδ hl (preθ_pt_le_normalizer_Zv c hS hδ hl)

theorem Zv_le_of_pt_eq (hS : Sit H M S) (hδ : vtype δ = false) {l l' : Geo H M}
    (hl : l ∈ nbrs δ) (hl' : l' ∈ nbrs δ) (hp : c.pt l = c.pt l') : Zv l' ≤ Zv l := by
  intro y' hy'
  by_cases hC : y' ∈ Cb δ
  · have : y' ∈ Cb δ ⊓ Zv l' := ⟨hC, hy'⟩
    rw [S34.Cb_inf_Zv_eq hS.glob hδ hl'] at this
    exact Std.Zv_le_Zv_of_nbr hS hδ hl this
  · obtain ⟨y, hy, hyC⟩ : ∃ y ∈ Zv l, y ∉ Cb δ := by
      by_contra hcon
      push Not at hcon
      exact not_Zv_nbr_le_Cb hS hδ hl hcon
    have hπ : c.π ⟨y', Std.Zv_le_Vn hl' hy'⟩ = c.π ⟨y, Std.Zv_le_Vn hl hy⟩ := by
      rw [π_eq_vp c hS hδ hl' hy' hC, π_eq_vp c hS hδ hl hy hyC, hp]
    have hw : y' * y⁻¹ ∈ Cb δ := (c.π_eq_iff _ _).mp hπ
    have hwZ : y' * y⁻¹ ∈ Zv δ := by
      by_cases hCZ : Cb δ = Zv δ
      · rwa [← hCZ]
      · have hyU : y ∉ Uc δ := fun h => hyC (S34.Zv_le_Cb hS.glob hδ
          (Zv_nbr_inf_Uc hS hδ hl hCZ ▸ (⟨hy, h⟩ : y ∈ Zv l ⊓ Uc δ)))
        have hy'U : y' ∉ Uc δ := fun h => hC (S34.Zv_le_Cb hS.glob hδ
          (Zv_nbr_inf_Uc hS hδ hl' hCZ ▸ (⟨hy', h⟩ : y' ∈ Zv l' ⊓ Uc δ)))
        have hrel : (Uc δ).relIndex (Vn δ) = 2 := by
          have h1 := Uc_relIndex_Vn_le hS hδ
          have h2 : (Uc δ).relIndex (Vn δ) ≠ 1 := fun h =>
            hyU (Subgroup.relIndex_eq_one.mp h (Std.Zv_le_Vn hl hy))
          have h3 : (Uc δ).relIndex (Vn δ) ≠ 0 := Subgroup.index_ne_zero_of_finite
          omega
        have hyinv : y⁻¹ ∉ Uc δ := fun h => hyU (by simpa using (Uc δ).inv_mem h)
        have := mul_mem_of_relIndex_two hrel (Std.Zv_le_Vn hl' hy') ((Vn δ).inv_mem
          (Std.Zv_le_Vn hl hy)) hy'U hyinv
        have h5 : y' * y⁻¹ ∈ Uc δ ⊓ Cb δ := ⟨this, hw⟩
        rwa [Uc_inf_Cb hS hδ] at h5
    have e : y' = (y' * y⁻¹) * y := by group
    rw [e]
    exact (Zv l).mul_mem (Std.Zv_le_Zv_of_nbr hS hδ hl hwZ) hy

theorem Zv_eq_iff_pt (hS : Sit H M S) (hδ : vtype δ = false) {l l' : Geo H M}
    (hl : l ∈ nbrs δ) (hl' : l' ∈ nbrs δ) : Zv l = Zv l' ↔ c.pt l = c.pt l' :=
  ⟨c.pt_eq_of_Zv_eq hS hδ hl hl', fun hp =>
    le_antisymm (Zv_le_of_pt_eq c hS hδ hl' hl hp.symm) (Zv_le_of_pt_eq c hS hδ hl hl' hp)⟩

omit c in
theorem fixSecIn_Zv_eq_Cb (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {A : Subgroup G}
    (hA : A ≤ stab δ) : fixSecIn A (Zv δ) (Vn δ) = fixSecIn A (Cb δ) (Vn δ) := by
  unfold fixSecIn
  congr 1
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun a ha => S34.Zv_le_Cb hS.glob hδ (h a ha)⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun a ha => comm_mem_Zv_of_mem_Cb hS hδ (hA ha) hx (h a ha)⟩

end S35.Col

end F53.Stellmacher

end CFSG.Quasithin
