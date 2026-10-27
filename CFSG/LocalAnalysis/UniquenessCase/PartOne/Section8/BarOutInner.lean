module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterInnerThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

private abbrev O2sub (L : Subgroup G) : Subgroup ↥L := CFSG.pCore 2 ↥L

private theorem mem_O2sub_iff {L : Subgroup G} {x : ↥L} :
    x ∈ O2sub L ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
  rw [CFSG.Open.pCoreOf]
  exact (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm

private theorem normalizerMonoidHom_apply_coe (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (y : ↥L) :
    (((Subgroup.normalizerMonoidHom L) n) y : G) = (n : G) * (y : G) * (n : G)⁻¹ :=
  rfl

@[expose] noncomputable def barAction (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (Bar2 L) :=
  MonoidHom.mk'
    (fun n => QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L)
      ((Subgroup.normalizerMonoidHom L) n)
      (by
        rw [← MulEquiv.toMonoidHom_eq_coe]
        exact Subgroup.characteristic_iff_map_eq.mp
          (CFSG.pCore_characteristic (p := 2) (G := ↥L))
          ((Subgroup.normalizerMonoidHom L) n)))
    (by
      intro m n
      apply MulEquiv.ext
      intro a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
      rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply])

theorem barAction_mk (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (y : ↥L) :
    barAction L n (QuotientGroup.mk y) =
      QuotientGroup.mk (((Subgroup.normalizerMonoidHom L) n) y) :=
  rfl

@[expose] noncomputable def barConjAut {L : Subgroup G} (x : G) : MulAut (Bar2 L) := by
  classical
  exact if hx : x ∈ Subgroup.normalizer (L : Set G) then barAction L ⟨x, hx⟩ else 1

@[simp]
theorem barConjAut_of_mem {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    barConjAut (L := L) x = barAction L ⟨x, hx⟩ := by
  classical
  rw [barConjAut, dif_pos hx]

private theorem barAction_eq_conj_mk_iff (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (l : ↥L) :
    barAction L n = MulAut.conj (QuotientGroup.mk l) ↔
      ∀ y ∈ L,
        ((n : G) * y * (n : G)⁻¹) * (((l : G) * y * (l : G)⁻¹)⁻¹) ∈
          CFSG.Open.pCoreOf 2 L := by
  constructor
  · intro h y hy
    let y' : ↥L := ⟨y, hy⟩
    have h1 : barAction L n (QuotientGroup.mk y') =
        MulAut.conj (QuotientGroup.mk l) (QuotientGroup.mk y') := by
      rw [h]
    rw [barAction_mk, MulAut.conj_apply] at h1
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.eq_iff_div_mem, mem_O2sub_iff] at h1
    simpa [Subgroup.coe_div, normalizerMonoidHom_apply_coe, div_eq_mul_inv] using h1
  · intro h
    apply MulEquiv.ext
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    rw [barAction_mk, MulAut.conj_apply]
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    rw [QuotientGroup.eq_iff_div_mem, mem_O2sub_iff]
    simpa [Subgroup.coe_div, normalizerMonoidHom_apply_coe, div_eq_mul_inv] using h (y : G) y.2

theorem barConjAut_mem_inner_iff
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    barConjAut x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) ↔
      ∃ l ∈ L, ∀ y ∈ L,
        (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  rw [barConjAut_of_mem (L := L) hx]
  constructor
  · intro h
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at h
    obtain ⟨q, hq⟩ := h
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨l, l.2, ?_⟩
    intro y hy
    exact (barAction_eq_conj_mk_iff L ⟨x, hx⟩ l).mp hq.symm y hy
  · rintro ⟨l, hl, h⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range]
    exact ⟨QuotientGroup.mk ⟨l, hl⟩,
      ((barAction_eq_conj_mk_iff L ⟨x, hx⟩ ⟨l, hl⟩).mpr h).symm⟩

theorem exists_conj_of_not_three_dvd_outer
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : IsPGroup 3 (Subgroup.zpowers x))
    (hOut : ¬ 3 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L))) :
    ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let n : ↥N := ⟨x, hx⟩
  have hmap : (Subgroup.zpowers n).map N.subtype = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hx3' : IsPGroup 3 (Subgroup.zpowers n) := by
    have h : IsPGroup 3 ((Subgroup.zpowers n).map N.subtype) := by
      rwa [hmap]
    exact h.of_equiv (Subgroup.equivMapOfInjective (Subgroup.zpowers n) N.subtype
      Subtype.coe_injective).symm
  have hφ : IsPGroup 3 (Subgroup.zpowers (barAction L n)) := by
    rw [← MonoidHom.map_zpowers (barAction L) n]
    exact hx3'.map (barAction L)
  have hmem : barConjAut x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    rw [barConjAut_of_mem (L := L) hx]
    exact mem_inner_of_isPGroup_three hφ hOut
  exact (barConjAut_mem_inner_iff x hx).mp hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
