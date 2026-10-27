module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_5

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 11.6(a)

This file contains the Section 11 Corollary 11.6(a) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 11.6(a). -/
public theorem CFSG.corollary_11_6_a
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A = section11OmegaOne p (section10AmbientSylowSubgroup M P) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M P
  have hPcomm : IsMulCommutative (P : Subgroup M) := theorem_11_5 h11 P
  have hPambcomm : IsMulCommutative Pamb := by
    simpa [Pamb] using section11_isMulCommutative_ambient_of_sylow (G := G) hPcomm
  letI : IsMulCommutative Pamb := hPambcomm
  rcases h11.A_rank_two with ⟨_hAcard, hAelem⟩
  rcases h11.rankTwoMaximal with ⟨_hArank, _hAmax⟩
  rcases _hAmax with ⟨_hAelemMax, hAmaximal⟩
  let Ω : Subgroup G := section11OmegaOne p Pamb
  have hΩelem : IsElementaryAbelian p.val Ω := by
    let Ωsub : Subgroup Pamb := omega₁ (G := Pamb) (p := p.val)
    have hΩsub : IsElementaryAbelian p.val Ωsub :=
      section11_omega1_isElementaryAbelian_of_commutative (H := Pamb) (p := p.val)
    letI : IsElementaryAbelian p.val Ωsub := hΩsub
    change IsElementaryAbelian p.val (Ωsub.map Pamb.subtype)
    exact section11_isElementaryAbelian_map (G := Pamb) (p := p.val)
      (A := Ωsub) Pamb.subtype
  have hA_le_Ω : A ≤ Ω := by
    intro a ha
    have haP : a ∈ Pamb := by
      simpa [Pamb] using h11.A_le_ambient_sylow ha
    let aP : Pamb := ⟨a, haP⟩
    have hapow : a ^ p.val = 1 := by
      letI : IsElementaryAbelian p.val A := hAelem
      exact elemPow_eq_one_of_isElementaryAbelian (p := p.val) (A := A) a ha
    have haΩ : aP ∈ omega₁ (G := Pamb) (p := p.val) := by
      rw [omega₁, omega]
      refine Subgroup.subset_closure ?_
      apply Subtype.ext
      simpa [aP, pow_one] using hapow
    exact Subgroup.mem_map.mpr ⟨aP, haΩ, rfl⟩
  have hA_eq_Ω : A = Ω := hAmaximal Ω hA_le_Ω hΩelem
  simpa [Ω, Pamb] using hA_eq_Ω

end Section11
