module

public import CFSG.LieType.Steinberg.CentralExt.PerfectLift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup

@[expose] def OddCentralSplit (S : Type) [Group S] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π → π.ker ≤ center E →
    Odd (Nat.card π.ker) → ∃ s : S →* E, ∀ x, π (s x) = x

theorem OddCentralSplit.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : OddCentralSplit S) : OddCentralSplit S' := by
  intro E _ _ π hπ hcen hodd
  have hker : (e.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.symm.injective]
  obtain ⟨s, hs⟩ := h E (e.symm.toMonoidHom.comp π) (e.symm.surjective.comp hπ)
    (hker ▸ hcen) (hker ▸ hodd)
  refine ⟨s.comp e.symm.toMonoidHom, fun x => e.symm.injective ?_⟩
  exact hs (e.symm x)

section Product

variable {G : Type*} [Group G] {t : G} {Kh : Subgroup G}
  (hKt : Kh.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kh : Set G))
theorem conj_mem_of_mem_map_conj (htt : t * t = 1) {y : G}
    (hy : y ∈ Kh.map (MulAut.conj t).toMonoidHom) : t * y * t⁻¹ ∈ Kh := by
  obtain ⟨k, hk, rfl⟩ := hy
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have e : t * ((MulAut.conj t).toMonoidHom k) * t⁻¹ = k := by
    change t * (t * k * t⁻¹) * t⁻¹ = k
    rw [ht, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  rw [e]
  exact hk

theorem conj_mem_map_conj {x : G} (hx : x ∈ Kh) :
    t * x * t⁻¹ ∈ Kh.map (MulAut.conj t).toMonoidHom :=
  ⟨x, hx, rfl⟩

include hKt

theorem commute_of_mem_of_mem_map_conj {x y : G} (hx : x ∈ Kh)
    (hy : y ∈ Kh.map (MulAut.conj t).toMonoidHom) : Commute x y :=
  mem_centralizer_iff.1 (hKt hy) x hx

@[expose] def swapMulHom : Kh × Kh.map (MulAut.conj t).toMonoidHom →* G :=
  Kh.subtype.noncommCoprod (Kh.map (MulAut.conj t).toMonoidHom).subtype fun a b =>
    commute_of_mem_of_mem_map_conj hKt a.2 b.2

theorem swapMulHom_apply (x : Kh × Kh.map (MulAut.conj t).toMonoidHom) :
    swapMulHom hKt x = (x.1 : G) * x.2 :=
  rfl

theorem ker_swapMulHom_le_center :
    (swapMulHom hKt).ker ≤ center (Kh × Kh.map (MulAut.conj t).toMonoidHom) := by
  intro x hx
  have hx' : (x.1 : G) * x.2 = 1 := hx
  have h1 : (x.1 : G) = ((x.2 : G))⁻¹ := eq_inv_of_mul_eq_one_left hx'
  have h2 : (x.2 : G) = ((x.1 : G))⁻¹ := eq_inv_of_mul_eq_one_right hx'
  have hx1 : (x.1 : G) ∈ Kh.map (MulAut.conj t).toMonoidHom := by
    rw [h1]
    exact inv_mem x.2.2
  have hx2 : (x.2 : G) ∈ Kh := by
    rw [h2]
    exact inv_mem x.1.2
  rw [mem_center_iff]
  intro y
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact commute_of_mem_of_mem_map_conj hKt y.1.2 hx1
  · exact (commute_of_mem_of_mem_map_conj hKt hx2 y.2.2).symm

theorem card_ker_swapMulHom_dvd :
    Nat.card (swapMulHom hKt).ker ∣
      Nat.card (Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom : Subgroup G) := by
  have hrel : ∀ x : (swapMulHom hKt).ker, ((x.1.1 : Kh) : G) * (x.1.2 : G) = 1 := fun x =>
    MonoidHom.mem_ker.1 x.2
  have hmem : ∀ x : (swapMulHom hKt).ker,
      ((x.1.1 : Kh) : G) ∈ Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom := fun x => by
    refine Subgroup.mem_inf.2 ⟨x.1.1.2, ?_⟩
    rw [eq_inv_of_mul_eq_one_left (hrel x)]
    exact inv_mem x.1.2.2
  let g : (swapMulHom hKt).ker →* (Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom : Subgroup G) :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine card_dvd_of_injective g fun x y hxy => ?_
  have h1 : ((x.1.1 : Kh) : G) = ((y.1.1 : Kh) : G) :=
    congrArg (fun z : (Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom : Subgroup G) => (z : G)) hxy
  have h2 : (x.1.2 : G) = (y.1.2 : G) := by
    rw [eq_inv_of_mul_eq_one_right (hrel x), eq_inv_of_mul_eq_one_right (hrel y), h1]
  exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))

theorem le_range_swapMulHom : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom ≤ (swapMulHom hKt).range :=
  sup_le (fun k hk => ⟨(⟨k, hk⟩, 1), by
      rw [swapMulHom_apply]
      exact mul_one k⟩)
    (fun k hk => ⟨(1, ⟨k, hk⟩), by
      rw [swapMulHom_apply]
      exact one_mul k⟩)

theorem eq_of_mul_conj_eq {S : Type*} [Group S] [Group.IsPerfect S] {φ₁ φ₂ : S →* G}
    (h₁ : ∀ x, φ₁ x ∈ Kh) (h₂ : ∀ x, φ₂ x ∈ Kh)
    (h : ∀ x, φ₁ x * (t * φ₁ x * t⁻¹) = φ₂ x * (t * φ₂ x * t⁻¹)) : φ₁ = φ₂ := by
  let β : ∀ φ : S →* G, (∀ x, φ x ∈ Kh) → S →* Kh × Kh.map (MulAut.conj t).toMonoidHom :=
    fun φ hφ => (φ.codRestrict Kh hφ).prod
      (((MulAut.conj t).toMonoidHom.comp φ).codRestrict _ fun x => ⟨φ x, hφ x, rfl⟩)
  have hβ : β φ₁ h₁ = β φ₂ h₂ := by
    refine CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect (ker_swapMulHom_le_center hKt) ?_
    ext x
    exact h x
  ext x
  exact congrArg (fun γ : S →* Kh × Kh.map (MulAut.conj t).toMonoidHom => ((γ x).1 : G)) hβ

end Product

section Lift

variable {G : Type} [Group G] {t : G} {Kh : Subgroup G}
  (hKt : Kh.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kh : Set G))
include hKt

omit hKt in
@[expose] def swapConjHom (htt : t * t = 1) :
    Kh × Kh.map (MulAut.conj t).toMonoidHom →* Kh × Kh.map (MulAut.conj t).toMonoidHom :=
  ((((MulAut.conj t).toMonoidHom.comp (Kh.map (MulAut.conj t).toMonoidHom).subtype).codRestrict
      Kh fun k => conj_mem_of_mem_map_conj htt k.2).comp (MonoidHom.snd _ _)).prod
    ((((MulAut.conj t).toMonoidHom.comp Kh.subtype).codRestrict _
      fun k => conj_mem_map_conj k.2).comp (MonoidHom.fst _ _))

theorem swapMulHom_swapConjHom (htt : t * t = 1) (x : Kh × Kh.map (MulAut.conj t).toMonoidHom) :
    swapMulHom hKt (swapConjHom htt x) = t * swapMulHom hKt x * t⁻¹ := by
  change t * (x.2 : G) * t⁻¹ * (t * (x.1 : G) * t⁻¹) = t * ((x.1 : G) * x.2) * t⁻¹
  rw [(commute_of_mem_of_mem_map_conj hKt x.1.2 x.2.2).eq]
  group

theorem exists_swapLift [Finite G] (htt : t * t = 1) {S : Type} [Group S] [Finite S]
    [Group.IsPerfect S] (hS : OddCentralSplit S)
    (hodd : Odd (Nat.card (Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom : Subgroup G)))
    (ι : S →* G) (hι : ∀ x, ι x ∈ Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom)
    (hιt : ∀ x, t * ι x * t⁻¹ = ι x) :
    ∃ φ : S →* G, (∀ x, φ x ∈ Kh) ∧ ∀ x, φ x * (t * φ x * t⁻¹) = ι x := by
  set μ := swapMulHom hKt with hμ
  have hsurj : Function.Surjective (CFSG.SectionRank.EvenCover.pullbackFst μ ι) := by
    intro x
    obtain ⟨y, hy⟩ := le_range_swapMulHom hKt (hι x)
    exact ⟨⟨(x, y), hy.symm⟩, rfl⟩
  have hodd' : Odd (Nat.card (CFSG.SectionRank.EvenCover.pullbackFst μ ι).ker) :=
    Odd.of_dvd_nat hodd ((CFSG.SectionRank.EvenCover.card_pullbackFst_ker_dvd μ ι).trans
      (card_ker_swapMulHom_dvd hKt))
  obtain ⟨σ, hσ⟩ := hS _ (CFSG.SectionRank.EvenCover.pullbackFst μ ι) hsurj
    (CFSG.SectionRank.EvenCover.pullbackFst_ker_le_center (ker_swapMulHom_le_center hKt) ι) hodd'
  set σ' : S →* Kh × Kh.map (MulAut.conj t).toMonoidHom :=
    (MonoidHom.snd S _).comp ((CFSG.SectionRank.EvenCover.pullback μ ι).subtype.comp σ) with hσ'
  have hσ'μ : μ.comp σ' = ι := CFSG.SectionRank.EvenCover.comp_snd_section σ hσ
  have hσ'x : ∀ x, ((σ' x).1 : G) * (σ' x).2 = ι x := fun x => DFunLike.congr_fun hσ'μ x
  have hswap : σ' = (swapConjHom htt).comp σ' := by
    refine CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect (ker_swapMulHom_le_center hKt) ?_
    ext x
    change μ (σ' x) = μ (swapConjHom htt (σ' x))
    rw [swapMulHom_swapConjHom, ← hμ, ← MonoidHom.comp_apply μ σ', hσ'μ, hιt]
  have h2 : ∀ x, ((σ' x).2 : G) = t * (σ' x).1 * t⁻¹ := fun x => by
    have h1 : ((σ' x).1 : G) = t * (σ' x).2 * t⁻¹ :=
      congrArg (fun γ : S →* Kh × Kh.map (MulAut.conj t).toMonoidHom => ((γ x).1 : G)) hswap
    have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [h1, ht, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  refine ⟨Kh.subtype.comp ((MonoidHom.fst _ _).comp σ'), fun x => (σ' x).1.2, fun x => ?_⟩
  change ((σ' x).1 : G) * (t * (σ' x).1 * t⁻¹) = ι x
  rw [← h2, hσ'x]

theorem swapLift_comp_eq_conj {S : Type} [Group S] [Group.IsPerfect S] {φ ι : S →* G}
    (hφK : ∀ x, φ x ∈ Kh) (hφ : ∀ x, φ x * (t * φ x * t⁻¹) = ι x) {g : G}
    (hgK : g ∈ normalizer (Kh : Set G)) (hgt : g * t = t * g) (α : S →* S)
    (hα : ∀ x, ι (α x) = g * ι x * g⁻¹) (x : S) : φ (α x) = g * φ x * g⁻¹ := by
  have hK2 : ∀ x, ((MulAut.conj g).toMonoidHom.comp φ) x ∈ Kh := fun x =>
    (mem_normalizer_iff.1 hgK (φ x)).1 (hφK x)
  have h := eq_of_mul_conj_eq hKt (φ₁ := φ.comp α) (φ₂ := (MulAut.conj g).toMonoidHom.comp φ)
    (fun x => hφK (α x)) hK2 (fun x => by
      change φ (α x) * (t * φ (α x) * t⁻¹) = g * φ x * g⁻¹ * (t * (g * φ x * g⁻¹) * t⁻¹)
      rw [hφ, hα, ← hφ x]
      have h1 : g⁻¹ * t * g = t := by
        rw [mul_assoc, ← hgt, ← mul_assoc, inv_mul_cancel, one_mul]
      have h2 : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hgt]
      calc g * (φ x * (t * φ x * t⁻¹)) * g⁻¹ = g * φ x * t * φ x * (t⁻¹ * g⁻¹) := by group
        _ = g * φ x * (g⁻¹ * t * g) * φ x * (g⁻¹ * t⁻¹) := by rw [h1, h2]
        _ = g * φ x * g⁻¹ * (t * (g * φ x * g⁻¹) * t⁻¹) := by group)
  exact DFunLike.congr_fun h x

end Lift

section Param

variable {G : Type*} [Group G] {t : G} {Kh : Subgroup G}
  (hKt : Kh.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kh : Set G))
  {S : Type*} [Group S] {φ : S →* G} (hφK : ∀ x, φ x ∈ Kh)
include hKt hφK

@[expose] def swapParamHom : S × S →* G :=
  φ.noncommCoprod ((MulAut.conj t).toMonoidHom.comp φ) fun x y =>
    commute_of_mem_of_mem_map_conj hKt (hφK x) ⟨φ y, hφK y, rfl⟩

theorem swapParamHom_apply (x : S × S) :
    swapParamHom hKt hφK x = φ x.1 * (t * φ x.2 * t⁻¹) :=
  rfl

theorem conj_swapParamHom (htt : t * t = 1) (x y : S) :
    t * swapParamHom hKt hφK (x, y) * t⁻¹ = swapParamHom hKt hφK (y, x) := by
  rw [swapParamHom_apply, swapParamHom_apply]
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have e : t * (φ x * (t * φ y * t⁻¹)) * t⁻¹ = t * φ x * t⁻¹ * φ y := by
    rw [ht]
    calc t * (φ x * (t * φ y * t)) * t = t * φ x * t * φ y * (t * t) := by group
      _ = t * φ x * t * φ y := by rw [htt, mul_one]
  rw [e, (commute_of_mem_of_mem_map_conj hKt (hφK y) (conj_mem_map_conj (hφK x))).symm.eq]

theorem range_swapParamHom :
    (swapParamHom hKt hφK).range = φ.range ⊔ φ.range.map (MulAut.conj t).toMonoidHom := by
  rw [swapParamHom, MonoidHom.noncommCoprod_range, MonoidHom.range_comp]

theorem ker_swapParamHom_le_center (htt : t * t = 1) (hφ : Function.Injective φ) :
    (swapParamHom hKt hφK).ker ≤ center (S × S) := by
  rintro ⟨x, y⟩ hxy
  have h1 : φ x * (t * φ y * t⁻¹) = 1 := hxy
  have hx : φ x ∈ Kh.map (MulAut.conj t).toMonoidHom := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (conj_mem_map_conj (hφK y))
  have hy : φ y ∈ Kh.map (MulAut.conj t).toMonoidHom := by
    have h2 : t * φ y * t⁻¹ = (φ x)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have h3 : φ y = t * (φ x)⁻¹ * t⁻¹ := by
      rw [← h2, ht]
      calc φ y = (t * t) * φ y * (t * t) := by rw [htt, one_mul, mul_one]
        _ = t * (t * φ y * t) * t := by group
    rw [h3]
    exact conj_mem_map_conj (inv_mem (hφK x))
  have hc : ∀ {u : S}, φ u ∈ Kh.map (MulAut.conj t).toMonoidHom → u ∈ center S := fun {u} hu =>
    mem_center_iff.2 fun z => hφ (by
      rw [map_mul, map_mul]
      exact commute_of_mem_of_mem_map_conj hKt (hφK z) hu)
  rw [Subgroup.center_prod]
  exact ⟨hc hx, hc hy⟩

end Param

end CFSG.SeitzReduction.UnitaryPilot
