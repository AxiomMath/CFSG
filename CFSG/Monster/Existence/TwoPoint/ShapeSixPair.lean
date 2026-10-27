module

public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Pair

variable {G : Type} [Group G] {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}

abbrev pairCentB (φ : Subgroup.centralizer ({b} : Set G) →* B) (x y : G) : Subgroup B :=
  Subgroup.centralizer ({coverMap φ x} : Set B) ⊓ Subgroup.centralizer ({coverMap φ y} : Set B)

section Dihedral

variable {x y : G}

theorem cent2_le_cent_of_dihedral (hxy : x * y * x * y = b) : cent2 x y ≤ cent b := by
  intro g hg
  obtain ⟨hgx, hgy⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgx hgy ⊢
  have h1 : Commute g x := hgx
  have h2 : Commute g y := hgy
  rw [← hxy]
  exact (((h1.mul_right h2).mul_right h1).mul_right h2 : Commute g (x * y * x * y))

theorem central_mem_cent2 (hx : x ∈ cent b) (hy : y ∈ cent b) : b ∈ cent2 x y :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 hx).symm,
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hy).symm⟩

theorem cent_inf_cent2_of_dihedral (hxy : x * y * x * y = b) :
    cent b ⊓ cent x ⊓ cent y = cent2 x y := by
  rw [inf_assoc]
  exact inf_eq_right.2 (cent2_le_cent_of_dihedral hxy)

theorem dihedral_conj_right (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y * x * y = b) :
    x * y * x⁻¹ = b * y := by
  rw [inv_eq_of_mul_eq_one_right hxx]
  calc x * y * x = (x * y * x * y) * y⁻¹ := by group
    _ = b * y := by rw [hxy, inv_eq_of_mul_eq_one_right hyy]

theorem dihedral_conj_left (hx : x ∈ cent b) (hxx : x * x = 1) (hyy : y * y = 1)
    (hxy : x * y * x * y = b) : y * x * y⁻¹ = b * x := by
  rw [inv_eq_of_mul_eq_one_right hyy]
  have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  calc y * x * y = x⁻¹ * (x * y * x * y) := by group
    _ = x * b := by rw [hxy, inv_eq_of_mul_eq_one_right hxx]
    _ = b * x := hxb

end Dihedral

section Pattern

variable {x y : G} [Finite G]

omit [Finite G] in
theorem dihedral_left_mem_coverPre (h : IsBabyCover b φ) (hx : x ∈ cent b) (hy : y ∈ cent b)
    (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y * x * y = b) :
    x ∈ coverPre φ (pairCentB φ x y) := by
  have e := (mem_coverPre_inf_centralizer_iff h hx hy (g := x)).2
  refine e ⟨hx, Or.inl ?_, Or.inr (dihedral_conj_right hxx hyy hxy)⟩
  rw [inv_eq_of_mul_eq_one_right hxx, hxx, one_mul]

omit [Finite G] in
theorem dihedral_right_mem_coverPre (h : IsBabyCover b φ) (hx : x ∈ cent b) (hy : y ∈ cent b)
    (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y * x * y = b) :
    y ∈ coverPre φ (pairCentB φ x y) := by
  have e := (mem_coverPre_inf_centralizer_iff h hx hy (g := y)).2
  refine e ⟨hy, Or.inr (dihedral_conj_left hx hxx hyy hxy), Or.inl ?_⟩
  rw [inv_eq_of_mul_eq_one_right hyy, hyy, one_mul]

theorem natCard_cent2_dihedral_mul_four (h : IsBabyCover b φ) (hx : x ∈ cent b) (hy : y ∈ cent b)
    (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y * x * y = b) :
    Nat.card ↥(cent2 x y) * 4 = 2 * Nat.card ↥(pairCentB φ x y) := by
  have hxP := dihedral_left_mem_coverPre h hx hy hxx hyy hxy
  have hyP := dihedral_right_mem_coverPre h hx hy hxx hyy hxy
  have hxmem : x ∈ cent x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have o1 : {z : G | ∃ g ∈ coverPre φ (pairCentB φ x y), g * x * g⁻¹ = z}.ncard = 2 :=
    ncard_orbit_eq_two h.b_ne_one hyP (dihedral_conj_left hx hxx hyy hxy) fun g hg =>
      ((mem_coverPre_inf_centralizer_iff h hx hy (g := g)).1 hg).2.1
  have o2 : {z : G | ∃ g ∈ coverPre φ (pairCentB φ x y) ⊓ cent x, g * y * g⁻¹ = z}.ncard = 2 :=
    ncard_orbit_eq_two h.b_ne_one (Subgroup.mem_inf.2 ⟨hxP, hxmem⟩)
      (dihedral_conj_right hxx hyy hxy) fun g hg =>
        ((mem_coverPre_inf_centralizer_iff h hx hy (g := g)).1 (Subgroup.mem_inf.1 hg).1).2.2
  have := card_inf_inf_mul_orbit h hx hy
  rw [cent_inf_cent2_of_dihedral hxy] at this
  rw [o1, o2] at this
  omega

end Pattern

section Hom

variable {x y : G}

@[expose] noncomputable def dihedralPairHom (φ : Subgroup.centralizer ({b} : Set G) →* B)
    (hK : cent2 x y ≤ cent b) : ↥(cent2 x y) →* B :=
  φ.comp (Subgroup.inclusion hK)

theorem dihedralPairHom_apply (hK : cent2 x y ≤ cent b) (g : ↥(cent2 x y)) :
    dihedralPairHom φ hK g = coverMap φ (g : G) :=
  (coverMap_apply (hK g.2)).symm

theorem dihedralPairHom_eq_one_iff (h : IsBabyCover b φ) (hK : cent2 x y ≤ cent b)
    (g : ↥(cent2 x y)) : dihedralPairHom φ hK g = 1 ↔ (g : G) = 1 ∨ (g : G) = b := by
  rw [dihedralPairHom_apply, h.coverMap_eq_one_iff (hK g.2)]

theorem natCard_ker_dihedralPairHom (h : IsBabyCover b φ) (hK : cent2 x y ≤ cent b)
    (hb : b ∈ cent2 x y) : Nat.card (dihedralPairHom φ hK).ker = 2 := by
  rw [Nat.card_eq_two_iff' (1 : (dihedralPairHom φ hK).ker)]
  refine ⟨⟨⟨b, hb⟩, (dihedralPairHom_eq_one_iff h hK _).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro hh
    apply h.b_ne_one
    have := congrArg (fun z : (dihedralPairHom φ hK).ker => ((z : ↥(cent2 x y)) : G)) hh
    simpa using this
  · intro z hz
    rcases (dihedralPairHom_eq_one_iff h hK z.1).1 z.2 with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hz
    · exact Subtype.ext (Subtype.ext h1)

theorem commutator_pairCentB_le_range_dihedralPairHom (h : IsBabyCover b φ) (hx : x ∈ cent b)
    (hy : y ∈ cent b) (hK : cent2 x y ≤ cent b) (hxy : x * y * x * y = b) :
    ⁅pairCentB φ x y, pairCentB φ x y⁆ ≤ (dihedralPairHom φ hK).range := by
  rw [Subgroup.commutator_le]
  intro r₁ hr₁ r₂ hr₂
  obtain ⟨p₁, hp₁, rfl⟩ := h.exists_coverMap_eq r₁
  obtain ⟨p₂, hp₂, rfl⟩ := h.exists_coverMap_eq r₂
  have hP₁ : p₁ ∈ coverPre φ (pairCentB φ x y) := mem_coverPre.2 ⟨hp₁, hr₁⟩
  have hP₂ : p₂ ∈ coverPre φ (pairCentB φ x y) := mem_coverPre.2 ⟨hp₂, hr₂⟩
  set a : ↥(coverPre φ (pairCentB φ x y)) := ⟨p₁, hP₁⟩ with ha
  set c : ↥(coverPre φ (pairCentB φ x y)) := ⟨p₂, hP₂⟩ with hc
  have hker : ⁅a, c⁆ ∈ (patternMap h hx hy).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hmem := (mem_ker_patternMap h hx hy ⁅a, c⁆).1 hker
  rw [cent_inf_cent2_of_dihedral hxy] at hmem
  refine ⟨⟨((⁅a, c⁆ : ↥(coverPre φ (pairCentB φ x y))) : G), hmem⟩, ?_⟩
  have e : φ ⟨((⁅a, c⁆ : ↥(coverPre φ (pairCentB φ x y))) : G), hK hmem⟩ =
      ⁅φ ⟨p₁, hp₁⟩, φ ⟨p₂, hp₂⟩⁆ := by
    rw [← map_commutatorElement]
    rfl
  rw [dihedralPairHom_apply, coverMap_apply (hK hmem), e, coverMap_apply hp₁, coverMap_apply hp₂]

end Hom

theorem exists_two_shape_of_dihedral_pair [Finite G] (h : IsBabyCover b φ) {x y : G}
    (hx : x ∈ cent b) (hy : y ∈ cent b) (hxx : x * x = 1) (hyy : y * y = 1)
    (hxy : x * y * x * y = b)
    (hR : Nat.card ↥(pairCentB φ x y) = 4 * Nat.card ↥⁅pairCentB φ x y, pairCentB φ x y⁆) :
    ∃ (N : Subgroup ↥(cent2 x y)) (_ : N.Normal), Nat.card N = 2 ∧
      Nonempty (↥(cent2 x y) ⧸ N ≃* ↥⁅pairCentB φ x y, pairCentB φ x y⁆) := by
  have hK := cent2_le_cent_of_dihedral hxy
  have : Finite ↥(dihedralPairHom φ hK).range :=
    Finite.of_surjective _ (dihedralPairHom φ hK).rangeRestrict_surjective
  have hcomm := commutator_pairCentB_le_range_dihedralPairHom h hx hy hK hxy
  have hkc := natCard_ker_dihedralPairHom h hK (central_mem_cent2 hx hy)
  have h4 := natCard_cent2_dihedral_mul_four h hx hy hxx hyy hxy
  have h1 := Subgroup.card_ker_mul_card_range (dihedralPairHom φ hK)
  rw [hkc] at h1
  have hrange : (dihedralPairHom φ hK).range = ⁅pairCentB φ x y, pairCentB φ x y⁆ :=
    (Subgroup.eq_of_le_of_card_ge hcomm (by omega)).symm
  exact ⟨(dihedralPairHom φ hK).ker, inferInstance, hkc,
    ⟨(QuotientGroup.quotientKerEquivRange (dihedralPairHom φ hK)).trans
      (MulEquiv.subgroupCongr hrange)⟩⟩

end Pair

end CFSG.Monster.Existence
