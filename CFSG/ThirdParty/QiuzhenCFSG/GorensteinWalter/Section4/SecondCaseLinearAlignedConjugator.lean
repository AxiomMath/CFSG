module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearMInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenAlignedConjugator
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The concrete aligned conjugator for equation (11)

For `X = P^g ≤ A`, the subgroup `X` lies in `U ≤ C_G(t)`, so `t` belongs
to `N_G(X)=M^g`.  The one-class theorem for involutions of `M` transports
through conjugation to `M^g`; the generic aligned-conjugator theorem then
adjusts `g` without changing `X` so that it fixes `t`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every conjugate of `P` lying in `A` has a representative fixing `t`. -/
public theorem secondCase_linear_aligned_exists_conjugator_fixing_t
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    (X : Subgroup G) (hXleA : X ≤ post.od.A)
    (hXconj : ∃ g : G, X = conjugateSubgroup post.od.P g) :
    ∃ g : G, conjugateSubgroup post.od.P g = X ∧
      g * c.t * g⁻¹ = c.t := by
  classical
  obtain ⟨g, hgX⟩ := hXconj
  have hNP : Subgroup.normalizer (post.od.P : Set G) = w.M :=
    secondCase_linear_P_normalizer_eq_M c w d post.od
  have hXleU : X ≤ c.U :=
    hXleA.trans post.od.A_le_FU |>.trans (fittingSubgroupOf_le c.U)
  have htCX : c.t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : x ∈ c.H :=
      (Subgroup.map_subtype_le (pPrimeCore 2 c.H)) (hXleU hx)
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hxH
    exact hxH
  have htNX : c.t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) htCX
  have hNX : Subgroup.normalizer (X : Set G) = conjugateSubgroup w.M g := by
    calc
      Subgroup.normalizer (X : Set G) =
          Subgroup.normalizer ((conjugateSubgroup post.od.P g) : Set G) := by
            rw [hgX]
      _ = conjugateSubgroup (Subgroup.normalizer (post.od.P : Set G)) g := by
        change Subgroup.normalizer
            ((post.od.P.map (MulAut.conj g).toMonoidHom) : Set G) =
          (Subgroup.normalizer (post.od.P : Set G)).map
            (MulAut.conj g).toMonoidHom
        exact (Subgroup.map_normalizer_eq_of_bijective post.od.P
          (MulAut.conj g).bijective).symm
      _ = conjugateSubgroup w.M g := by rw [hNP]
  have htMg : c.t ∈ conjugateSubgroup w.M g := by
    rwa [← hNX]
  have hclasses : ∀ a b : G,
      a ∈ conjugateSubgroup w.M g → IsInvolution a →
      b ∈ conjugateSubgroup w.M g → IsInvolution b →
        ∃ n : G, n ∈ conjugateSubgroup w.M g ∧ n * a * n⁻¹ = b := by
    intro a b ha haI hb hbI
    rcases Subgroup.mem_map.mp ha with ⟨a0, ha0M, ha0a⟩
    rcases Subgroup.mem_map.mp hb with ⟨b0, hb0M, hb0b⟩
    have haVal : a = g * a0 * g⁻¹ := by
      simpa [MulAut.conj_apply] using ha0a.symm
    have hbVal : b = g * b0 * g⁻¹ := by
      simpa [MulAut.conj_apply] using hb0b.symm
    have ha0I : IsInvolution a0 := by
      constructor
      · intro ha01
        apply haI.1
        rw [haVal, ha01]
        simp
      · have h := congrArg (fun z : G => g⁻¹ * z * g) haI.2
        simpa [haVal, pow_two, mul_assoc] using h
    have hb0I : IsInvolution b0 := by
      constructor
      · intro hb01
        apply hbI.1
        rw [hbVal, hb01]
        simp
      · have h := congrArg (fun z : G => g⁻¹ * z * g) hbI.2
        simpa [hbVal, pow_two, mul_assoc] using h
    obtain ⟨n0, hn0M, hn0⟩ :=
      secondCase_linear_M_involutions_conjugate c w d K post
        a0 b0 ha0M ha0I hb0M hb0I
    refine ⟨g * n0 * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨n0, hn0M, rfl⟩
    · rw [haVal, hbVal]
      calc
        (g * n0 * g⁻¹) * (g * a0 * g⁻¹) * (g * n0 * g⁻¹)⁻¹ =
            g * (n0 * a0 * n0⁻¹) * g⁻¹ := by group
        _ = g * b0 * g⁻¹ := by rw [hn0]
  exact secondCase_equation11_aligned_exists_conjugator_fixing_t
    c w post.od.P X g hNP hgX htMg hclasses

end CFSG.GorensteinWalter
