module

public import CFSG.RankThree.PartOne.K159H.O3Blong
public import CFSG.Quasithin.Vol2.E2NineTI2bDefs
public import CFSG.Quasithin.Vol2.E2SevenPairN

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped MatrixGroups

namespace E2

namespace TI2b

section QU

open Matrix

variable {G : Type} [Group G] {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def QU (ρ : G →* Matrix ι ι k) (U : Submodule k (ι → k)) : Subgroup G where
  carrier := {g | (∀ x, (ρ g - 1) *ᵥ x ∈ U) ∧ ∀ u ∈ U, (ρ g - 1) *ᵥ u = 0}
  one_mem' := by
    refine ⟨fun x => ?_, fun u _ => ?_⟩
    · simp
    · simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun x => ?_, fun u hu => ?_⟩
    · have : (ρ (g * h) - 1) *ᵥ x = (ρ g - 1) *ᵥ (ρ h *ᵥ x) + (ρ h - 1) *ᵥ x := by
        rw [map_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
          Matrix.one_mulVec, Matrix.mulVec_mulVec]
        abel
      rw [this]
      exact U.add_mem (hg1 _) (hh1 x)
    · have h1 : ρ h *ᵥ u = u := by
        have := hh2 u hu
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
        exact this
      have : (ρ (g * h) - 1) *ᵥ u = (ρ g - 1) *ᵥ (ρ h *ᵥ u) + (ρ h - 1) *ᵥ u := by
        rw [map_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
          Matrix.one_mulVec, Matrix.mulVec_mulVec]
        abel
      rw [this, h1, hg2 u hu, hh2 u hu, add_zero]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hfix : ∀ u ∈ U, ρ g *ᵥ u = u := fun u hu => by
      have := hg2 u hu
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    have hfix' : ∀ u ∈ U, ρ g⁻¹ *ᵥ u = u := fun u hu => by
      have h1 : ρ g⁻¹ *ᵥ (ρ g *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      rwa [hfix u hu] at h1
    refine ⟨fun x => ?_, fun u hu => ?_⟩
    · have hy : (ρ g - 1) *ᵥ x ∈ U := hg1 x
      have e1 : ρ g *ᵥ x = x + (ρ g - 1) *ᵥ x := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      have e2 : ρ g⁻¹ *ᵥ (ρ g *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      have e3 : ρ g⁻¹ *ᵥ x = x - (ρ g - 1) *ᵥ x := by
        have h3 := e2
        rw [e1, Matrix.mulVec_add, hfix' _ hy] at h3
        exact eq_sub_of_add_eq h3
      have : (ρ g⁻¹ - 1) *ᵥ x = -((ρ g - 1) *ᵥ x) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, e3]
        abel
      rw [this]
      exact U.neg_mem hy
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix' u hu, sub_self]

theorem QU_mul_self [CharP k 2] {ρ : G →* Matrix ι ι k} (hρ : Function.Injective ρ)
    {U : Submodule k (ι → k)} {g : G} (hg : g ∈ QU ρ U) : g * g = 1 := by
  obtain ⟨hg1, hg2⟩ := hg
  have h2 : ∀ y : ι → k, y + y = 0 := fun y => by
    have : y + y = (2 : k) • y := by rw [two_smul]
    rw [this, CharTwo.two_eq_zero, zero_smul]
  apply hρ
  rw [map_mul, map_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  have hy : (ρ g - 1) *ᵥ x ∈ U := hg1 x
  have e1 : ρ g *ᵥ x = x + (ρ g - 1) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hfix : ρ g *ᵥ ((ρ g - 1) *ᵥ x) = (ρ g - 1) *ᵥ x := by
    have := hg2 _ hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this
  rw [Matrix.one_mulVec]
  calc ρ g *ᵥ (ρ g *ᵥ x) = ρ g *ᵥ (x + (ρ g - 1) *ᵥ x) := by rw [← e1]
    _ = ρ g *ᵥ x + ρ g *ᵥ ((ρ g - 1) *ᵥ x) := Matrix.mulVec_add _ _ _
    _ = (x + (ρ g - 1) *ᵥ x) + (ρ g - 1) *ᵥ x := by rw [hfix, e1]
    _ = x := by rw [add_assoc, h2, add_zero]

theorem conj_mem_QU {ρ : G →* Matrix ι ι k} {U : Submodule k (ι → k)} {y : G}
    (hy : ∀ u ∈ U, ρ y *ᵥ u ∈ U) (hy' : ∀ u ∈ U, ρ y⁻¹ *ᵥ u ∈ U) {w : G} (hw : w ∈ QU ρ U) :
    y * w * y⁻¹ ∈ QU ρ U := by
  obtain ⟨hw1, hw2⟩ := hw
  have hmat : ρ (y * w * y⁻¹) - 1 = ρ y * (ρ w - 1) * ρ y⁻¹ := by
    have h1 : ρ y * ρ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [mul_sub, mul_one, sub_mul, h1, map_mul, map_mul]
  have key : ∀ x, (ρ (y * w * y⁻¹) - 1) *ᵥ x = ρ y *ᵥ ((ρ w - 1) *ᵥ (ρ y⁻¹ *ᵥ x)) := by
    intro x
    rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨fun x => ?_, fun u hu => ?_⟩
  · rw [key]
    exact hy _ (hw1 _)
  · rw [key, hw2 _ (hy' u hu), Matrix.mulVec_zero]

theorem inf_QU_le_pCoreOf [CharP k 2] [Finite G] {ρ : G →* Matrix ι ι k}
    (hρ : Function.Injective ρ) {Y : Subgroup G} {U : Submodule k (ι → k)}
    (hU : ∀ y ∈ Y, ∀ u ∈ U, ρ y *ᵥ u ∈ U) : Y ⊓ QU ρ U ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
  · intro y hy
    refine mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
    · exact ⟨Y.mul_mem (Y.mul_mem hy hx.1) (Y.inv_mem hy),
        conj_mem_QU (hU y hy) (hU y⁻¹ (Y.inv_mem hy)) hx.2⟩
    · have := Y.inv_mem hy
      refine ⟨Y.mul_mem (Y.mul_mem this hx.1) hy, ?_⟩
      have h1 := conj_mem_QU (hU y⁻¹ this) (by simpa using hU y hy) hx.2
      simpa using h1
  · refine fun x => ⟨1, ?_⟩
    have := QU_mul_self hρ x.2.2
    rw [pow_one, pow_two]
    exact Subtype.ext this

end QU

section Transfer

theorem map_pCoreOf_comap_le {G' G : Type} [Group G'] [Finite G'] [Group G] (π : G' →* G)
    (hπ : Function.Surjective π) (Y : Subgroup G) :
    (pCoreOf 2 (Y.comap π)).map π ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
  · intro y hy
    obtain ⟨yt, rfl⟩ := hπ y
    exact Subgroup.le_normalizer_map π ⟨yt,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.comap π) (Subgroup.mem_comap.mpr hy), rfl⟩
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map π

theorem dich_of_sl2_range {k : Type} [Field k] [CharP k 2] (hk : 4 ≤ Nat.card k) {G : Type}
    [Group G] [Finite G] {f : SL(2, k) →* G} (hf : Function.Injective f) {Y R : Subgroup G}
    (hfY : f.range ≤ Y) (hR : R ≤ f.range) : Dich R Y := by
  right
  have hsimp : IsSimpleGroup SL(2, k) :=
    CFSG.RankThree.PartOne.K159H.sl2_isSimpleGroup hk
  have hperf : Group.IsPerfect SL(2, k) := CFSG.RankThree.PartOne.K159H.sl2_isPerfect hk
  set D := f.range with hD
  set N := (CFSG.solvableRadical ↥Y).map Y.subtype with hN
  let e : SL(2, k) ≃* ↥D := MonoidHom.ofInjective hf
  haveI := hsimp
  haveI : IsSimpleGroup ↥D := e.symm.isSimpleGroup
  haveI hn : ((N ⊓ D).subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro d hd
    exact mem_normalizer_inf_of_mem
      (le_normalizer_map_subtype (CFSG.solvableRadical ↥Y) (hfY hd)) (Subgroup.le_normalizer hd)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ D).subgroupOf D) with h0 | h1
  · rw [Subgroup.subgroupOf_eq_bot] at h0
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ N ⊓ D := ⟨hx.2, hR hx.1⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hx1 ((Subgroup.disjoint_def.mp h0) hx' hx'.2)
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h1
    have hDN : D ≤ N := h1.trans inf_le_left
    have hNs : Group.IsSolvable ↥N := by
      have h' : Group.IsSolvable ↥(CFSG.solvableRadical ↥Y) := A3.solvableRadical_isSolvable
      exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ _
        Y.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    haveI : Group.IsSolvable ↥D := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hDN) (Subgroup.inclusion_injective _)
    haveI hsol : Group.IsSolvable SL(2, k) :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) (MulEquiv.surjective _)
    haveI : Nontrivial SL(2, k) := hsimp.toNontrivial
    exact Group.IsPerfect.not_isSolvable SL(2, k) inferInstance

end Transfer

end TI2b

end E2

end CFSG.Quasithin
