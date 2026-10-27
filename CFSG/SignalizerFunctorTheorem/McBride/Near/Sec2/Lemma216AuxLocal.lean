module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216Aux

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem SemisimpleAction.exists_mul_of_mem_kJ
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {y : Γ} (hy : y ∈ kJ A J) :
    ∃ a ∈ CFSG.fittingSubgroupOf (kJ A J), ∃ c ∈ cenIn J (norIn A J), y = a * c := by
  obtain ⟨f, hf, hC, -, hM, hFM⟩ := h.exists_frame_data hJ
  rw [← hM] at hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have hmul := (near_fitting_eq_centralizer (h.nearSimple hJ) hf).2
  have hy'' : y' ∈ ((fixedNormalizer f : Subgroup ↥J) : Set ↥J) := hy'
  rw [← hmul] at hy''
  obtain ⟨a', ha', c', hc', rfl⟩ := hy''
  refine ⟨(a' : Γ), ?_, (c' : Γ), ?_, rfl⟩
  · rw [← hFM]
    exact ⟨a', ha', rfl⟩
  · rw [← hC]
    exact ⟨c', hc', rfl⟩

theorem SemisimpleAction.exists_core1
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ v ∈ cenIn J (norIn A J), v ∉ CFSG.fittingSubgroupOf (kJ A J) ∧
      ∀ c ∈ cenIn J (norIn A J), ⁅v, c⁆ ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
  obtain ⟨f, hf, hC, hC₀, hM, hFM⟩ := h.exists_frame_data hJ
  obtain ⟨⟨-, -, -, V, hV, hVH, hdisj, -, -⟩, -⟩ := near_frobenius (h.nearSimple hJ) hf
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  have hvC1 : v ∈ fixedCore1 f := hVH hvV
  have hvF : v ∉ CFSG.fittingSubgroupOf (fixedNormalizer f) := by
    intro hvF
    have hCM : signalizerFixedSubgroup f ≤ fixedNormalizer f := fixed_le_fixedNormalizer f
    have hN : (signalizerFixedSubgroup f ⊓ CFSG.fittingSubgroupOf (fixedNormalizer f)) ≤
        fixedFitting f := by
      refine le_fittingSubgroupOf_of_nilpotent inf_le_left ?_ ?_
      · refine le_normalizer_of_conj_mem fun c hc x hx => ?_
        obtain ⟨hxC, hxF⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hc hxC) (inv_mem hc),
          fittingSubgroupOf_conj_mem (hCM hc) hxF⟩
      · have : Group.IsNilpotent ↥(CFSG.fittingSubgroupOf (fixedNormalizer f)) :=
          isNilpotent_fittingSubgroupOf _
        exact isNilpotent_of_injective (Subgroup.inclusion inf_le_right)
          (Subgroup.inclusion_injective _)
    have hv0 : v ∈ fixedFitting f ⊓ V :=
      Subgroup.mem_inf.mpr ⟨hN (Subgroup.mem_inf.mpr ⟨hvC1.1, hvF⟩), hvV⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at hv0
    exact hv1 (Subtype.ext hv0)
  refine ⟨(v : Γ), ?_, ?_, fun c hc => ?_⟩
  · rw [← hC]
    exact ⟨v, hvC1.1, rfl⟩
  · intro hvmem
    rw [← hFM] at hvmem
    exact hvF ((Subgroup.mem_map_iff_mem J.subtype_injective).mp hvmem)
  · rw [← hC] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    rw [← hC₀]
    exact ⟨⁅v, c'⁆, hvC1.2 c' hc', rfl⟩

theorem SemisimpleAction.commutator_mem_fitting_kJ
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {x : Γ} (hx : x ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf (kJ A J) : Set Γ))
    (hc : ∀ c ∈ cenIn J (norIn A J), ⁅x, c⁆ ∈ CFSG.fittingSubgroupOf (kJ A J)) {y : Γ}
    (hy : y ∈ kJ A J) : ⁅x, y⁆ ∈ CFSG.fittingSubgroupOf (kJ A J) := by
  obtain ⟨a, ha, c, hcC, rfl⟩ := h.exists_mul_of_mem_kJ hJ hy
  have h1 : ⁅x, a * c⁆ = ⁅x, a⁆ * (a * ⁅x, c⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact mul_mem (Lemma216.commutator_mem_of_mem_normalizer hx ha)
    (mul_mem (mul_mem ha (hc c hcC)) (inv_mem ha))

theorem SemisimpleAction.exists_conj_of_coprime
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {g : Γ} (hgJ : g ∈ Subgroup.normalizer (J : Set Γ)) (hg : Nat.Coprime p (orderOf g))
    (hgF : g ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf (kJ A J) : Set Γ))
    (hgc : ∀ y ∈ kJ A J, ⁅g, y⁆ ∈ CFSG.fittingSubgroupOf (kJ A J)) :
    ∃ m ∈ kJ A J, ∀ x ∈ J, g * x * g⁻¹ = m * x * m⁻¹ := by
  obtain ⟨f, hf, -, -, hM, hFM⟩ := h.exists_frame_data hJ
  let φ : MulAut ↥J := J.normalizerMonoidHom ⟨g, hgJ⟩
  have hφ : ∀ t : ↥J, ((φ t : ↥J) : Γ) = g * t * g⁻¹ := fun t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨g, hgJ⟩ t
  have hcop : Nat.Coprime p (orderOf φ) := by
    have h1 : orderOf φ ∣ orderOf (⟨g, hgJ⟩ : ↥(Subgroup.normalizer (J : Set Γ))) :=
      orderOf_map_dvd J.normalizerMonoidHom _
    rw [Subgroup.orderOf_mk] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hg
  have hmemM : ∀ t : ↥J, t ∈ fixedNormalizer f ↔ (t : Γ) ∈ kJ A J := fun t => by
    rw [← hM]
    exact (Subgroup.mem_map_iff_mem J.subtype_injective).symm
  have hmemF : ∀ t : ↥J, t ∈ CFSG.fittingSubgroupOf (fixedNormalizer f) ↔
      (t : Γ) ∈ CFSG.fittingSubgroupOf (kJ A J) := fun t => by
    rw [← hFM]
    exact (Subgroup.mem_map_iff_mem J.subtype_injective).symm
  have hkJ : ∀ z : Γ, z ∈ kJ A J ↔ z ∈ J ∧
      z ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf (kJ A J) : Set Γ) := fun z => by
    rw [← mem_norIn_iff, h.norIn_fittingSubgroupOf_kJ hJ]
  have hMem : ∀ t : ↥J, (t : Γ) ∈ kJ A J → ((φ t : ↥J) : Γ) ∈ kJ A J := by
    intro t ht
    rw [hkJ]
    refine ⟨(φ t).2, ?_⟩
    rw [hφ]
    exact mul_mem (mul_mem hgF ((hkJ _).1 ht).2) (inv_mem hgF)
  have hF : ∀ t : ↥J, (t : Γ) ∈ kJ A J →
      ((t⁻¹ * φ t : ↥J) : Γ) ∈ CFSG.fittingSubgroupOf (kJ A J) := by
    intro t ht
    have e1 : ((t⁻¹ * φ t : ↥J) : Γ) = (t : Γ)⁻¹ * ⁅g, (t : Γ)⁆ * (t : Γ) := by
      rw [Subgroup.coe_mul, hφ]
      simp only [commutatorElement_def, InvMemClass.coe_inv]
      group
    rw [e1]
    have := fittingSubgroupOf_conj_mem (inv_mem ht) (hgc _ ht)
    simpa using this
  obtain ⟨m, hm, hφm⟩ := near_coprime_aut_inner (h.nearSimple hJ) hf φ hcop
    (fun t ht => (hmemM _).2 (hMem t ((hmemM t).1 ht)))
    (fun t ht => (hmemF _).2 (hF t ((hmemM t).1 ht)))
  refine ⟨(m : Γ), (hmemM m).1 hm, fun x hx => ?_⟩
  have := congrArg (fun ψ : MulAut ↥J => ((ψ ⟨x, hx⟩ : ↥J) : Γ)) hφm
  simpa [hφ] using this

end CFSG.SignalizerFunctorTheorem.McBride.Near
