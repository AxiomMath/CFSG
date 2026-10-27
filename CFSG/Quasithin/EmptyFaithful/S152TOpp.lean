module

public import CFSG.Quasithin.EmptyFaithful.S152TBender

public section

open CFSG.Open CFSG.QuasithinUnique

namespace CFSG.Quasithin

variable {Y : Type} [Group Y] [Finite Y]

namespace S152T

omit [Finite Y] in
theorem mem_of_isPGroup_of_mem_normalizer {V : Subgroup Y} (hV : IsSylowTwoOf V ⊤) {x : Y}
    (hx : IsPGroup 2 (Subgroup.zpowers x)) (hxN : x ∈ Subgroup.normalizer (V : Set Y)) : x ∈ V := by
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hV
  have hxN' : Subgroup.zpowers x ≤ Subgroup.normalizer ((Q : Subgroup Y) : Set Y) :=
    (Subgroup.zpowers_le).2 hxN
  have hT : IsPGroup 2 (Subgroup.zpowers x ⊔ (Q : Subgroup Y) : Subgroup Y) :=
    hx.to_sup_of_normal_right' Q.isPGroup' hxN'
  have hmax := Q.is_maximal' hT le_sup_right
  rw [← hmax]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

omit [Finite Y] in
theorem isSylowTwoOf_top_map_conj {V : Subgroup Y} (hV : IsSylowTwoOf V ⊤) (g : Y) :
    IsSylowTwoOf (V.map (MulAut.conj g).toMonoidHom) ⊤ := by
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hV
  refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map _, ?_⟩
  rw [Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective]
  exact hi

omit [Finite Y] in
theorem eq_of_mul_eq_of_mem_normalizer {UC VC : Subgroup Y} (hU : IsSylowTwoOf UC ⊤)
    (hV : IsSylowTwoOf VC ⊤) (hUV : UC ⊓ VC = ⊥) {u u' h h' : Y} (hu : u ∈ UC) (hu' : u' ∈ UC)
    (hh : h ∈ Subgroup.normalizer (VC : Set Y)) (hh' : h' ∈ Subgroup.normalizer (VC : Set Y))
    (heq : u * h = u' * h') : u = u' ∧ h = h' := by
  have hg : u'⁻¹ * u ∈ UC := UC.mul_mem (UC.inv_mem hu') hu
  have hgN : u'⁻¹ * u ∈ Subgroup.normalizer (VC : Set Y) := by
    have e : u'⁻¹ * u = h' * h⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hh' (inv_mem hh)
  have hgV : u'⁻¹ * u ∈ VC := by
    refine mem_of_isPGroup_of_mem_normalizer hV ?_ hgN
    exact (K1.isSylowTwoOf_top_iff.mp hU).1.to_le ((Subgroup.zpowers_le).2 hg)
  have h1 : u'⁻¹ * u = 1 := by
    have : u'⁻¹ * u ∈ UC ⊓ VC := ⟨hg, hgV⟩
    rwa [hUV, Subgroup.mem_bot] at this
  have hu1 : u = u' := by
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  subst hu1
  exact ⟨rfl, mul_left_cancel heq⟩

omit [Finite Y] in
theorem exists_mul_of_mem_normalizer {UC VC : Subgroup Y} (hV : IsSylowTwoOf VC ⊤)
    (hUV : UC ⊓ VC = ⊥)
    (hopp : ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → UC ⊓ S = ⊥ →
      ∃ u ∈ UC, S = VC.map (MulAut.conj u).toMonoidHom) {b : Y}
    (hb : b ∈ Subgroup.normalizer (UC : Set Y)) :
    ∃ u ∈ UC, ∃ h : Y, h ∈ Subgroup.normalizer (UC : Set Y) ∧
      h ∈ Subgroup.normalizer (VC : Set Y) ∧ b = u * h := by
  have hS : IsSylowTwoOf (VC.map (MulAut.conj b).toMonoidHom) ⊤ := isSylowTwoOf_top_map_conj hV b
  have hUS : UC ⊓ VC.map (MulAut.conj b).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyU, v, hv, rfl⟩
    have hv' : v ∈ UC := by
      have h1 : b⁻¹ * (MulAut.conj b v) * b ∈ UC := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hb) (MulAut.conj b v)).1 hyU
        simpa [mul_assoc] using this
      simpa [MulAut.conj_apply, mul_assoc] using h1
    have : v ∈ UC ⊓ VC := ⟨hv', hv⟩
    rw [hUV, Subgroup.mem_bot] at this
    rw [this]
    simp
  obtain ⟨u, hu, hSu⟩ := hopp _ hS hUS
  refine ⟨u, hu, u⁻¹ * b, mul_mem (inv_mem (Subgroup.le_normalizer hu)) hb, ?_, by group⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show VC.map (MulAut.conj (u⁻¹ * b)).toMonoidHom = VC
  have h1 : VC.map (MulAut.conj (u⁻¹ * b)).toMonoidHom =
      (VC.map (MulAut.conj b).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [h1, hSu, Subgroup.map_map]
  ext y
  simp only [Subgroup.mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro hy
    exact ⟨y, hy, by simp [mul_assoc]⟩

omit [Finite Y] in
theorem mem_normalizer_subgroupOf {G : Type} [Group G] {C P : Subgroup G} (hPC : P ≤ C) {g : C}
    (hg : (g : G) ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer ((P.subgroupOf C : Subgroup C) : Set C) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have := Subgroup.mem_normalizer_iff.1 hg (y : G)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, this]
  simp

end S152T

open S152T

theorem bct_of_opposition {UC VC : Subgroup Y} (hU : IsSylowTwoOf UC ⊤) (hV : IsSylowTwoOf VC ⊤)
    (hUV : UC ⊓ VC = ⊥)
    (hopp : ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → UC ⊓ S = ⊥ →
      ∃ u ∈ UC, S = VC.map (MulAut.conj u).toMonoidHom)
    (hrigid : ∀ δ : Y ≃* Y, UC.map δ.toMonoidHom = UC → VC.map δ.toMonoidHom = VC →
      (∃ w ∈ UC, ∀ x ∈ UC, δ x = w * x * w⁻¹) → δ = 1)
    (hZ : Subgroup.center Y = ⊥)
    (hfix : ∀ u ∈ UC, (∀ h : Y, h ∈ Subgroup.normalizer (UC : Set Y) →
      h ∈ Subgroup.normalizer (VC : Set Y) → h * u = u * h) → u = 1) :
    BorelCentralizerTrivial Y := by
  refine borelCentralizerTrivial_of_core hU ?_
  intro x hxc
  have hxCU : x ∈ Subgroup.centralizer (UC : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hxc s (Subgroup.le_normalizer hs)).symm
  have hxN : x ∈ Subgroup.normalizer (UC : Set Y) := by
    apply Subgroup.centralizer_le_normalizer
    exact hxCU
  obtain ⟨u, hu, h, hhU, hhV, hx⟩ := exists_mul_of_mem_normalizer hV hUV hopp hxN
  have hu1 : u = 1 := by
    refine hfix u hu fun h' hh'U hh'V => ?_
    have hc := hxc h' hh'U
    rw [hx] at hc
    have hconj : h' * u * h'⁻¹ ∈ UC := (Subgroup.mem_normalizer_iff.1 hh'U u).1 hu
    have e1 : h' * (u * h) = (h' * u * h'⁻¹) * (h' * h) := by group
    have e2 : u * h * h' = u * (h * h') := by group
    have := eq_of_mul_eq_of_mem_normalizer hU hV hUV hu hconj (mul_mem hhV hh'V)
      (mul_mem hh'V hhV) (e2.symm.trans (hc.trans e1))
    have h3 : u = h' * u * h'⁻¹ := this.1
    calc h' * u = (h' * u * h'⁻¹) * h' := by group
      _ = u * h' := by rw [← h3]
  subst hu1
  rw [one_mul] at hx
  subst hx
  have hδ := hrigid (MulAut.conj x) (Subgroup.mem_normalizer_iff_map_conj_eq.1 hhU)
    (Subgroup.mem_normalizer_iff_map_conj_eq.1 hhV) ⟨1, UC.one_mem, fun y hy => by
      have hc := hxc y (Subgroup.le_normalizer hy)
      simp only [MulAut.conj_apply, inv_one, mul_one, one_mul]
      calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [hc]
        _ = y := by group⟩
  have hzc : x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun φ : Y ≃* Y => φ y) hδ
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hzc

end CFSG.Quasithin
