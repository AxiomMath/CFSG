module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOmMain

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly LayerFacts FieldFiveOm

section Glue

variable {H G : Type} [Group H] [Group G] {ψ : H →* G}

theorem inv_mul_map_mul_eq {x : G} {s : H} (hs : (x, s) ∈ ggConjPairs ψ) (u : H) :
    x⁻¹ * ψ u * x = ψ (s⁻¹ * u * s) := by
  have h4 := hs (s⁻¹ * u * s)
  rw [show s * (s⁻¹ * u * s) * s⁻¹ = u by group] at h4
  rw [h4]
  group

theorem eq_of_mem_ggConjPairs (hinj : Function.Injective ψ) (hZ : Subgroup.center H = ⊥) {e : G}
    {s s' : H} (hs : (e, s) ∈ ggConjPairs ψ) (hs' : (e, s') ∈ ggConjPairs ψ) : s = s' := by
  have h := (ggConjPairs ψ).mul_mem hs ((ggConjPairs ψ).inv_mem hs')
  rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h
  have h1 := mem_center_of_mem_ggConjPairs_one hinj h
  rw [hZ, Subgroup.mem_bot] at h1
  exact mul_inv_eq_one.mp h1

theorem pow_eq_one_of_mem_ggConjPairs (hinj : Function.Injective ψ)
    (hZ : Subgroup.center H = ⊥) {e : G} {s : H} (hs : (e, s) ∈ ggConjPairs ψ) {n : ℕ}
    (he : e ^ n = 1) : s ^ n = 1 := by
  have h := (ggConjPairs ψ).pow_mem hs n
  rw [Prod.pow_mk, he] at h
  have h1 := mem_center_of_mem_ggConjPairs_one hinj h
  rwa [hZ, Subgroup.mem_bot] at h1

theorem mul_comm_of_mem_ggConjPairs (hinj : Function.Injective ψ) (hZ : Subgroup.center H = ⊥)
    {e e' : G} {s s' : H} (hs : (e, s) ∈ ggConjPairs ψ) (hs' : (e', s') ∈ ggConjPairs ψ)
    (hee : e * e' = e' * e) : s * s' = s' * s := by
  have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs hs')
    ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem hs' hs))
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hee, mul_inv_cancel] at h
  have h1 := mem_center_of_mem_ggConjPairs_one hinj h
  rw [hZ, Subgroup.mem_bot] at h1
  calc s * s' = s * s' * (s' * s)⁻¹ * (s' * s) := by group
    _ = s' * s := by rw [h1, one_mul]

end Glue

section Action

variable {H G : Type} [Group H] [Group G] {ψ : H →* G}

theorem isElemAbelian_conjOf (hinj : Function.Injective ψ) (hZ : Subgroup.center H = ⊥)
    {D : Subgroup G} (hDel : IsElemAbelian 5 D) (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) :
    IsElemAbelian 5 (conjOf ψ D) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun s hs => ?_⟩
  · obtain ⟨e, he, hea⟩ := mem_conjOf.mp a.2
    obtain ⟨e', he', heb⟩ := mem_conjOf.mp b.2
    have hee : e * e' = e' * e :=
      congrArg Subtype.val (hDel.1.is_comm.comm (⟨e, he⟩ : ↥D) ⟨e', he'⟩)
    exact mul_comm_of_mem_ggConjPairs hinj hZ hea heb hee
  · obtain ⟨e, he, hes⟩ := mem_conjOf.mp hs
    exact pow_eq_one_of_mem_ggConjPairs hinj hZ hes (hDel.2 e he)

theorem card_conjOf_of_no_centralizing (hinj : Function.Injective ψ) (hZ : Subgroup.center H = ⊥)
    {D : Subgroup G} (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ)
    (hfree : ∀ y ∈ D, y ≠ 1 → (y, (1 : H)) ∉ ggConjPairs ψ) :
    Nat.card (conjOf ψ D) = Nat.card D := by
  choose f hf using hDs
  let g : D → conjOf ψ D := fun e =>
    ⟨f e e.2, mem_conjOf.mpr ⟨e, e.2, hf e e.2⟩⟩
  have hg : Function.Bijective g := by
    refine ⟨fun e e' hee => ?_, fun s => ?_⟩
    · have h1 : f e e.2 = f e' e'.2 := congrArg Subtype.val hee
      by_contra hne
      have hne' : (e : G) * (e' : G)⁻¹ ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h))
      refine hfree _ (D.mul_mem e.2 (D.inv_mem e'.2)) hne' ?_
      have h2 := (ggConjPairs ψ).mul_mem (hf e e.2) ((ggConjPairs ψ).inv_mem (hf e' e'.2))
      rwa [Prod.inv_mk, Prod.mk_mul_mk, h1, mul_inv_cancel] at h2
    · obtain ⟨e, he, hes⟩ := mem_conjOf.mp s.2
      exact ⟨⟨e, he⟩, Subtype.ext (eq_of_mem_ggConjPairs hinj hZ (hf e he) hes)⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem not_isMulCommutative_centralizer_conjOf (hinj : Function.Injective ψ)
    {D : Subgroup G} (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) {J : Subgroup G}
    (hJ : IsQuasisimple ↥J) (hJle : J ≤ ψ.range ⊓ Subgroup.centralizer (D : Set G)) :
    ¬ IsMulCommutative ↥(Subgroup.centralizer (conjOf ψ D : Set H)) := by
  intro hcomm
  rw [range_inf_centralizer_eq_conjOf hinj hDs] at hJle
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_mul_ne_of_isQuasisimple hJ
  obtain ⟨c, hc, rfl⟩ := hJle ha
  obtain ⟨c', hc', rfl⟩ := hJle hb
  refine hab (Subtype.ext ?_)
  have h : c * c' = c' * c := congrArg Subtype.val
    (hcomm.is_comm.comm (⟨c, hc⟩ : ↥(Subgroup.centralizer (conjOf ψ D : Set H))) ⟨c', hc'⟩)
  show ψ c * ψ c' = ψ c' * ψ c
  rw [← map_mul, ← map_mul, h]

end Action

end FieldFiveE8

end CFSG.StandardType
