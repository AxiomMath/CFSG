module

public import CFSG.Permutation.SylowTwoNormalizer.Alt
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.LocalAnalysis.AGLEmbedding.AltSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv Subgroup

theorem mulAut_conj_injective_perm_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    Function.Injective (MulAut.conj : Perm (Fin k) →* MulAut (Perm (Fin k))) := by
  intro a b h
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup k hk
  refine MulEquiv.ext fun g => Subtype.ext ?_
  have hg := congrArg (fun φ : MulAut (Perm (Fin k)) => φ (g : Perm (Fin k))) h
  simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using hg

theorem exists_perm_conj_of_odd_orderOf {k : ℕ} (hk : 5 ≤ k) (α : MulAut (Perm (Fin k)))
    (hα : Odd (orderOf α)) : ∃ β : Perm (Fin k), α = MulAut.conj β := by
  classical
  let α' : MulAut (alternatingGroup (Fin k)) :=
    MulAut.characteristic (alternatingGroup (Fin k)) α
  have hα' : Odd (orderOf α') := hα.of_dvd_nat (orderOf_map_dvd _ α)
  have hcoe : ∀ g : alternatingGroup (Fin k),
      (α' g : Perm (Fin k)) = α (g : Perm (Fin k)) :=
    fun g => MulAut.characteristic_apply_apply_coe _ _ _
  have hex : ∃ β : Perm (Fin k), ∀ g : alternatingGroup (Fin k),
      (α' g : Perm (Fin k)) = β * (g : Perm (Fin k)) * β⁻¹ := by
    by_cases h57 : k = 5 ∨ 7 ≤ k
    · obtain ⟨β, hβ⟩ :=
        CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le h57 α'
      exact ⟨β, fun g => by simpa using hβ g⟩
    · rw [not_or, not_le] at h57
      have hk6 : k = 6 := by omega
      subst hk6
      obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.mem_range_conj_of_odd_orderOf α' hα'
      refine ⟨(a : Perm (Fin 6)), fun g => ?_⟩
      have hg := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ g) ha
      rw [← hg]
      simp [MulAut.conj_apply]
  obtain ⟨β, hβ⟩ := hex
  refine ⟨β, ?_⟩
  let φ : MulAut (Perm (Fin k)) := (MulAut.conj β)⁻¹ * α
  have hinv : (MulAut.conj β)⁻¹ = MulAut.conj β⁻¹ :=
    (map_inv (MulAut.conj : Perm (Fin k) →* MulAut (Perm (Fin k))) β).symm
  have hφA : ∀ g : alternatingGroup (Fin k), φ (g : Perm (Fin k)) = (g : Perm (Fin k)) := by
    intro g
    have hg := hβ g
    rw [hcoe] at hg
    show ((MulAut.conj β)⁻¹ * α) (g : Perm (Fin k)) = (g : Perm (Fin k))
    rw [MulAut.mul_apply, hinv, MulAut.conj_apply, hg]
    group
  have hφ : φ = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.one_apply]
    have hc : x⁻¹ * φ x = 1 := by
      apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup k (by omega)
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [map_one (MulAut.conjNormal (H := alternatingGroup (Fin k))), MulAut.one_apply,
        MulAut.conjNormal_apply]
      have hx : x * (g : Perm (Fin k)) * x⁻¹ ∈ alternatingGroup (Fin k) :=
        (Subgroup.normal_of_characteristic
          (H := alternatingGroup (Fin k))).conj_mem (g : Perm (Fin k)) g.2 x
      have h1 : φ (x * (g : Perm (Fin k)) * x⁻¹) = x * (g : Perm (Fin k)) * x⁻¹ :=
        hφA ⟨x * (g : Perm (Fin k)) * x⁻¹, hx⟩
      have h2 : φ (x * (g : Perm (Fin k)) * x⁻¹) =
          φ x * (g : Perm (Fin k)) * (φ x)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hφA g]
      rw [h2] at h1
      calc (x⁻¹ * φ x) * (g : Perm (Fin k)) * (x⁻¹ * φ x)⁻¹
          = x⁻¹ * (φ x * (g : Perm (Fin k)) * (φ x)⁻¹) * x := by group
        _ = x⁻¹ * (x * (g : Perm (Fin k)) * x⁻¹) * x := by rw [h1]
        _ = (g : Perm (Fin k)) := by group
    calc φ x = x * (x⁻¹ * φ x) := by group
      _ = x * 1 := by rw [hc]
      _ = x := by simp
  have hconj : MulAut.conj β * φ = α := by
    show MulAut.conj β * ((MulAut.conj β)⁻¹ * α) = α
    group
  rw [hφ, mul_one] at hconj
  exact hconj.symm

theorem mulAut_perm_eq_one_or {k : ℕ} (h5 : 5 ≤ k) (α : MulAut (Perm (Fin k)))
    (hα : Odd (orderOf α)) {U : Subgroup (Perm (Fin k))} (hUA : U ≤ alternatingGroup (Fin k))
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.relIndex (alternatingGroup (Fin k)))
    (hαU : U.map α.toMonoidHom = U) : α = 1 ∨ (k = 5 ∧ 3 ∣ orderOf α) := by
  obtain ⟨β, hαeq⟩ := exists_perm_conj_of_odd_orderOf h5 α hα
  have hinj := mulAut_conj_injective_perm_of_four_le (k := k) (by omega)
  have hord : orderOf α = orderOf β := by
    rw [hαeq, orderOf_injective _ hinj β]
  have hβodd : Odd (orderOf β) := hord ▸ hα
  have hβU : β ∈ normalizer (U : Set (Perm (Fin k))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hαeq] at hαU
    simpa using hαU
  rcases eq_or_lt_of_le h5 with hk5 | hk6
  · have hk5' : k = 5 := hk5.symm
    subst k
    have h3 : β ^ 3 = 1 :=
      pow_three_eq_one_of_mem_normalizer_of_le_alternatingGroup (by simp) hUA hU hUi hβodd hβU
    have hdvd : orderOf α ∣ 3 := by
      rw [hord, orderOf_dvd_iff_pow_eq_one]
      exact h3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3'
    · left
      exact orderOf_eq_one_iff.mp h1
    · right
      exact ⟨rfl, by rw [h3']⟩
  · have hβ1 : β = 1 :=
      eq_one_of_mem_normalizer_of_le_alternatingGroup
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hUA hU hUi hβodd hβU
    left
    rw [hαeq, hβ1, map_one]

theorem mulAut_perm_three_eq_one (α : MulAut (Perm (Fin 3))) (hα : Odd (orderOf α))
    {U : Subgroup (Perm (Fin 3))} (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (hαU : U.map α.toMonoidHom = U) : α = 1 := by
  obtain ⟨β, hβ⟩ := CFSG.Quasithin.SBd.perm_three_aut_inner α
  have hαeq : α = MulAut.conj β := by
    refine MulEquiv.ext fun x => ?_
    rw [hβ x, MulAut.conj_apply]
  have hinj : Function.Injective (MulAut.conj : Perm (Fin 3) →* MulAut (Perm (Fin 3))) := by
    intro a b h
    have h1 : CFSG.Quasithin.SBd.conjEquivPerm3 a = CFSG.Quasithin.SBd.conjEquivPerm3 b := by
      refine MulEquiv.ext fun x => ?_
      rw [CFSG.Quasithin.SBd.conjEquivPerm3_apply,
        CFSG.Quasithin.SBd.conjEquivPerm3_apply]
      simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut (Perm (Fin 3)) => φ x) h
    exact CFSG.Quasithin.SBd.conjEquivPerm3.injective h1
  have hord : orderOf α = orderOf β := by
    rw [hαeq, orderOf_injective _ hinj β]
  have hβodd : Odd (orderOf β) := hord ▸ hα
  have hβU : β ∈ normalizer (U : Set (Perm (Fin 3))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hαeq] at hαU
    simpa using hαU
  have hβ1 : β = 1 := eq_one_of_mem_normalizer hU hUi hβodd hβU
  rw [hαeq, hβ1, map_one]

end CFSG.Permutation.SylowTwoNormalizer
