module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem mem_of_conj_eq_conj_of_isIrrOn {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {S : Subgroup (MulAut U)} (hirr : IsIrrOn S ⊤ ⊥) (hZ : Subgroup.center ↥S = ⊥)
    {s₀ t : MulAut U} (hs₀ : s₀ ∈ S) (ht2 : t * t = 1)
    (h : ∀ s ∈ S, s₀ * s * s₀⁻¹ = t * s * t⁻¹) : t ∈ S := by
  classical
  set c : MulAut U := s₀⁻¹ * t with hc
  have hcs : ∀ s ∈ S, c * s = s * c := by
    intro s hs
    have h1 := h s hs
    calc c * s = s₀⁻¹ * (t * s * t⁻¹) * t := by rw [hc]; group
      _ = s₀⁻¹ * (s₀ * s * s₀⁻¹) * t := by rw [h1]
      _ = s * c := by rw [hc]; group
  have hts : t = s₀ * c := by rw [hc]; group
  have hc2 : c ^ 2 = 1 := by
    have hcomm : Commute c s₀ := hcs s₀ hs₀
    have h1 : s₀ * c * (s₀ * c) = 1 := by rw [← hts]; exact ht2
    have h2 : c * c * (s₀ * s₀) = 1 := by
      rw [hcomm.mul_mul_mul_comm c s₀, hcomm.eq]
      exact h1
    have h3 : c * c = (s₀ * s₀)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have hmem : c * c ∈ S := h3 ▸ S.inv_mem (S.mul_mem hs₀ hs₀)
    have hcent : (⟨c * c, hmem⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg : Commute (g : MulAut U) c := (hcs g g.2).symm
      exact (hg.mul_right hg).eq
    rw [hZ, Subgroup.mem_bot] at hcent
    rw [sq]
    exact congrArg Subtype.val hcent
  have hc1 : c = 1 := Thm14_5.eq_one_of_commute_of_isIrrOn hU hirr hc2 hcs
  rw [hts, hc1, mul_one]
  exact hs₀

theorem mem_of_orderOf_eq_two_of_odd_outer {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {N S : Subgroup (MulAut U)} (hSN : S ≤ N)
    (hnorm : (S.subgroupOf N).Normal) (hirr : IsIrrOn S ⊤ ⊥)
    (hZ : Subgroup.center ↥S = ⊥)
    (hout : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S)))
    {t : MulAut U} (htN : t ∈ N) (ht : orderOf t = 2) : t ∈ S := by
  classical
  haveI : Finite (MulAut U) :=
    Finite.of_injective (fun φ : MulAut U => (φ : U → U)) DFunLike.coe_injective
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hconj : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => by
    have := hnorm.conj_mem ⟨s, hSN hs⟩ (Subgroup.mem_subgroupOf.mpr hs) ⟨t, htN⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hconj' : ∀ s ∈ S, t⁻¹ * s * t ∈ S := fun s hs => by
    have := hnorm.conj_mem ⟨s, hSN hs⟩ (Subgroup.mem_subgroupOf.mpr hs) ⟨t, htN⟩⁻¹
    have h' := Subgroup.mem_subgroupOf.mp this
    simpa [mul_assoc] using h'
  let σ : MulAut ↥S :=
    { toFun := fun s => ⟨t * s * t⁻¹, hconj s s.2⟩
      invFun := fun s => ⟨t⁻¹ * s * t, hconj' s s.2⟩
      left_inv := fun s => by
        apply Subtype.ext
        change t⁻¹ * (t * (s : MulAut U) * t⁻¹) * t = s
        group
      right_inv := fun s => by
        apply Subtype.ext
        change t * (t⁻¹ * (s : MulAut U) * t) * t⁻¹ = s
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        change t * ((a : MulAut U) * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
        group }
  have hσσ : σ * σ = 1 := by
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    change t * (t * (s : MulAut U) * t⁻¹) * t⁻¹ = s
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [hti]
    calc t * (t * (s : MulAut U) * t) * t = (t * t) * s * (t * t) := by group
      _ = s := by rw [ht2, one_mul, mul_one]
  let q := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)
  have hq2 : q σ ^ 2 = 1 := by rw [← map_pow, sq, hσσ, map_one]
  have hq1 : q σ = 1 := by
    have h1 : orderOf (q σ) ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
    have h2 : orderOf (q σ) ∣
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S) :=
      orderOf_dvd_natCard (q σ)
    exact orderOf_eq_one_iff.mp
      ((Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_left.mpr hout)).eq_one_of_dvd h2)
  obtain ⟨s₀, hs₀⟩ := (QuotientGroup.eq_one_iff σ).mp hq1
  refine mem_of_conj_eq_conj_of_isIrrOn hU hirr hZ s₀.2 ht2 ?_
  intro s hs
  have h1 := congrArg (fun φ : MulAut ↥S => ((φ ⟨s, hs⟩ : ↥S) : MulAut U)) hs₀
  change (s₀ : MulAut U) * s * (s₀ : MulAut U)⁻¹ = t * s * t⁻¹ at h1
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
