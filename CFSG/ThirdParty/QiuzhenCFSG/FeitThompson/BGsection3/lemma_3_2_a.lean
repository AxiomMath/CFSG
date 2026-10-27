module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1

namespace CFSG
end CFSG
open CFSG


public theorem CFSG.lemma_3_2_a_no_solv {G : Type*} [Group G] [Finite G]
    (K R N : Subgroup G) [N.Normal]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hKnle : ¬ K ≤ N) :
    N ≤ K := by
  by_cases hK_top : K = ⊤
  · simp [hK_top]
  have hcent :=
    (lemma_3_1 (K := K) (R := R) hfrob.kernel_ne_bot hfrob.complement_ne_bot
      hfrob.normal hfrob.isComplement').1 hfrob
  by_contra hN_not_le_K
  have hx_exists : ∃ x, x ∈ N ∧ x ∉ K := by
    classical
    by_contra hx_exists
    apply hN_not_le_K
    intro y hyN
    by_contra hy_notK
    exact hx_exists ⟨y, hyN, hy_notK⟩
  rcases hx_exists with ⟨x, hxN, hx_notK⟩
  rcases hfrob.isComplement'.2 x with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hxr⟩
  have hxr' : (k : G) * r = x := by
    simpa using hxr
  have hr_sub_ne : (⟨r, hrR⟩ : R) ≠ 1 := by
    intro hr_eq_one
    apply hx_notK
    have hr_eq_one' : r = 1 := congrArg Subtype.val hr_eq_one
    rw [← hxr']
    simpa [hr_eq_one'] using hkK
  have hcent_r : elementCentralizerIn K (r : G) = ⊥ := hcent ⟨r, hrR⟩ hr_sub_ne
  let f : K → K := fun y =>
    ⟨(y : G) * r * (y : G)⁻¹ * r⁻¹, by
      have hconj : r * (y : G)⁻¹ * r⁻¹ ∈ K :=
        hfrob.normal.conj_mem (y : G)⁻¹ (K.inv_mem y.property) r
      simpa [mul_assoc] using K.mul_mem y.property hconj⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hab_val : (a : G) * r * (a : G)⁻¹ * r⁻¹ = (b : G) * r * (b : G)⁻¹ * r⁻¹ :=
      congrArg Subtype.val hab
    have hab_mul : (a : G) * r * (a : G)⁻¹ = (b : G) * r * (b : G)⁻¹ := by
      have := congrArg (fun t : G => t * r) hab_val
      simpa [mul_assoc] using this
    have hcomm : (b : G)⁻¹ * (a : G) * r = r * ((b : G)⁻¹ * (a : G)) := by
      have := congrArg (fun t : G => (b : G)⁻¹ * t * (a : G)) hab_mul
      simpa [mul_assoc] using this
    have hba_cent : (b : G)⁻¹ * (a : G) ∈ elementCentralizerIn K (r : G) := by
      refine ⟨K.mul_mem (K.inv_mem b.property) a.property, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hba_eq_one : (b : G)⁻¹ * (a : G) = 1 := by
      have hbot : (b : G)⁻¹ * (a : G) ∈ (⊥ : Subgroup G) := by
        rw [hcent_r] at hba_cent
        simpa using hba_cent
      simpa using hbot
    have := congrArg (fun t : G => (b : G) * t) hba_eq_one
    simpa [mul_assoc] using this
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  obtain ⟨y, hy⟩ := hf_surj ⟨k, hkK⟩
  have hy_val : (y : G) * r * (y : G)⁻¹ * r⁻¹ = k := congrArg Subtype.val hy
  have hx_eq : x = (y : G) * r * (y : G)⁻¹ := by
    calc
      x = (k : G) * r := hxr'.symm
      _ = (((y : G) * r * (y : G)⁻¹ * r⁻¹) : G) * r := by rw [hy_val]
      _ = (y : G) * r * (y : G)⁻¹ := by simp [mul_assoc]
  have hr_mem_N : r ∈ N := by
    have hconjN : (y : G)⁻¹ * x * y ∈ N :=
      (inferInstance : N.Normal).conj_mem' x hxN y
    simpa [hx_eq, mul_assoc] using hconjN
  have hK_le_N : K ≤ N := by
    intro z hzK
    obtain ⟨y, hy⟩ := hf_surj ⟨z, hzK⟩
    have hy_val : (y : G) * r * (y : G)⁻¹ * r⁻¹ = z := congrArg Subtype.val hy
    have hmemN : (y : G) * r * (y : G)⁻¹ * r⁻¹ ∈ N := by
      have hyrN : (y : G) * r * (y : G)⁻¹ ∈ N :=
        (inferInstance : N.Normal).conj_mem r hr_mem_N (y : G)
      exact N.mul_mem hyrN (N.inv_mem hr_mem_N)
    simpa [hy_val] using hmemN
  exact hKnle hK_le_N

public theorem CFSG.lemma_3_2_a {G : Type*} [Group G] [Finite G] (K R N : Subgroup G) [N.Normal]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (_hsolvK : Group.IsSolvable K)
    (hKnle : ¬ K ≤ N) :
    N ≤ K :=
  lemma_3_2_a_no_solv K R N hfrob hKnle
