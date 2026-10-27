module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] def mulEquivConjSub (g : G) (X : Subgroup G) : ↥X ≃* ↥(conjSub g X) where
  toFun x := ⟨g * x * g⁻¹, mul_mem_conjSub x.2⟩
  invFun y := ⟨g⁻¹ * y * g, mem_conjSub.mp y.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_mulEquivConjSub (g : G) (X : Subgroup G) (x : ↥X) :
    ((mulEquivConjSub g X x : ↥(conjSub g X)) : G) = g * x * g⁻¹ := rfl

theorem conj_mem_conjSub_iff {g y : G} {C : Subgroup G} : g * y * g⁻¹ ∈ conjSub g C ↔ y ∈ C := by
  rw [mem_conjSub]
  simp [mul_assoc]

theorem cSecIn_conjSub (g : G) (F L N : Subgroup G) :
    cSecIn (conjSub g F) (conjSub g L) (conjSub g N) = conjSub g (cSecIn F L N) := by
  unfold cSecIn
  rw [conjSub_closure]
  congr 1
  ext f'
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hf, h⟩
    refine ⟨g⁻¹ * f' * g, ⟨mem_conjSub.mp hf, fun x hx => ?_⟩, by group⟩
    have h1 := h (g * x * g⁻¹) (mul_mem_conjSub hx)
    rw [mem_conjSub] at h1
    have e : g⁻¹ * (f' * (g * x * g⁻¹) * f'⁻¹ * (g * x * g⁻¹)⁻¹) * g =
        g⁻¹ * f' * g * x * (g⁻¹ * f' * g)⁻¹ * x⁻¹ := by group
    rwa [e] at h1
  · rintro ⟨f, ⟨hf, h⟩, rfl⟩
    refine ⟨mul_mem_conjSub hf, fun x' hx' => ?_⟩
    have h1 := mul_mem_conjSub (g := g) (h (g⁻¹ * x' * g) (mem_conjSub.mp hx'))
    have e : g * (f * (g⁻¹ * x' * g) * f⁻¹ * (g⁻¹ * x' * g)⁻¹) * g⁻¹ =
        g * f * g⁻¹ * x' * (g * f * g⁻¹)⁻¹ * x'⁻¹ := by group
    rwa [e] at h1

theorem map_subgroupOf_mulEquivConjSub (g : G) (L X : Subgroup G) :
    (L.subgroupOf X).map (mulEquivConjSub g X : ↥X →* ↥(conjSub g X)) =
      (conjSub g L).subgroupOf (conjSub g X) := by
  ext ⟨y, hy⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have h1 : g * (x : G) * g⁻¹ = y := congrArg Subtype.val hxy
    rw [← h1]
    exact mul_mem_conjSub hx
  · intro hyL
    refine ⟨⟨g⁻¹ * y * g, mem_conjSub.mp hy⟩, mem_conjSub.mp hyL, ?_⟩
    exact Subtype.ext (by simp [coe_mulEquivConjSub, mul_assoc])

@[expose] def quotEquivConjSub (g : G) (L X : Subgroup G) [(L.subgroupOf X).Normal]
    [((conjSub g L).subgroupOf (conjSub g X)).Normal] :
    ↥X ⧸ L.subgroupOf X ≃* ↥(conjSub g X) ⧸ (conjSub g L).subgroupOf (conjSub g X) :=
  QuotientGroup.congr _ _ (mulEquivConjSub g X) (map_subgroupOf_mulEquivConjSub g L X)

theorem quotEquivConjSub_mk (g : G) (L X : Subgroup G) [(L.subgroupOf X).Normal]
    [((conjSub g L).subgroupOf (conjSub g X)).Normal] (x : ↥X) :
    quotEquivConjSub g L X (QuotientGroup.mk x) = QuotientGroup.mk (mulEquivConjSub g X x) := rfl

theorem IsModelSec.conj {n : ℕ} {M : Model n} {F L X : Subgroup G} (h : IsModelSec M F L X)
    (g : G) : IsModelSec M (conjSub g F) (conjSub g L) (conjSub g X) := by
  obtain ⟨hN, θ, β, hθs, hθk, hsd⟩ := h
  have hN' : ((conjSub g L).subgroupOf (conjSub g X)).Normal := by
    rw [← map_subgroupOf_mulEquivConjSub g L X]
    exact Subgroup.Normal.map hN _ (mulEquivConjSub g X).surjective
  refine ⟨hN', θ.comp (mulEquivConjSub g F).symm.toMonoidHom,
    (quotEquivConjSub g L X).toMonoidHom.comp β, ?_, ?_, ?_, ?_, ?_⟩
  · exact hθs.comp (mulEquivConjSub g F).symm.surjective
  · ext y'
    obtain ⟨y, rfl⟩ := (mulEquivConjSub g F).surjective y'
    have hy : θ y = 1 ↔ (y : G) ∈ cSecIn F L X := by
      have := Set.ext_iff.mp (congrArg (SetLike.coe) hθk) y
      simpa [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] using this
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, cSecIn_conjSub, coe_mulEquivConjSub,
      conj_mem_conjSub_iff]
    simpa using hy
  · exact (quotEquivConjSub g L X).surjective.comp hsd.surj
  · exact (quotEquivConjSub g L X).injective.comp hsd.inj
  · intro k' u x' hu
    obtain ⟨k, rfl⟩ := (mulEquivConjSub g F).surjective k'
    obtain ⟨x, rfl⟩ := (mulEquivConjSub g X).surjective x'
    have hβu : β u = QuotientGroup.mk x := by
      apply (quotEquivConjSub g L X).injective
      rw [quotEquivConjSub_mk]
      exact hu
    obtain ⟨hkx, hk⟩ := hsd.equiv k u x hβu
    have e : ((mulEquivConjSub g F k : ↥(conjSub g F)) : G) *
        ((mulEquivConjSub g X x : ↥(conjSub g X)) : G) *
        ((mulEquivConjSub g F k : ↥(conjSub g F)) : G)⁻¹ =
        g * ((k : G) * (x : G) * (k : G)⁻¹) * g⁻¹ := by
      simp only [coe_mulEquivConjSub]
      group
    have hkx' : ((mulEquivConjSub g F k : ↥(conjSub g F)) : G) *
        ((mulEquivConjSub g X x : ↥(conjSub g X)) : G) *
        ((mulEquivConjSub g F k : ↥(conjSub g F)) : G)⁻¹ ∈ conjSub g X := by
      rw [e]
      exact mul_mem_conjSub hkx
    refine ⟨hkx', ?_⟩
    have hsub : (⟨_, hkx'⟩ : ↥(conjSub g X)) =
        mulEquivConjSub g X ⟨(k : G) * (x : G) * (k : G)⁻¹, hkx⟩ := Subtype.ext e
    rw [hsub]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [hk, quotEquivConjSub_mk]

theorem IsOrthSec.conj {F L X : Subgroup G} (h : IsOrthSec F L X) (g : G) :
    IsOrthSec (conjSub g F) (conjSub g L) (conjSub g X) :=
  IsModelSec.conj h g

theorem IsNatSec.conj {F L X : Subgroup G} (h : IsNatSec F L X) (g : G) :
    IsNatSec (conjSub g F) (conjSub g L) (conjSub g X) :=
  IsModelSec.conj h g

end CFSG.Quasithin.F53Mod
