module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The fixed-factor centralizer of an aligned conjugate

An aligned conjugator fixes the distinguished involution `t`, hence lies in
`H = C_G(t)` and normalizes `F(U)`.  The fixed-factor centralizer transport
therefore identifies the centralizer of the conjugate order-`p` subgroup
inside `F(U)` with the conjugate of `F ⊔ K₀`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Transport the fixed-factor centralizer identity to an aligned conjugate
`X = P^h` whose conjugator fixes `t`. -/
public theorem secondCase_linear_conjugate_P_centralizer_FU_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    {X : Subgroup G} (h : G)
    (hX : X = conjugateSubgroup od.P h)
    (hfix : h * c.t * h⁻¹ = c.t) :
    (Subgroup.centralizer (X : Set G)) ⊓ c.FU =
      conjugateSubgroup (od.F ⊔ od.K0) h := by
  have hFU : h ∈ Subgroup.normalizer (c.FU : Set G) := by
    have hh : h ∈ c.H := by
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      calc
        h * c.t = (h * c.t * h⁻¹) * h := by group
        _ = c.t * h := by rw [hfix]
    exact (le_normalizer_of_isNormalIn
      (centralizerSetup_FU_isNormalIn_H c)) hh
  have hP : (Subgroup.centralizer (od.P : Set G)) ⊓ c.FU =
      od.F ⊔ od.K0 :=
    secondCase_linear_P_centralizer_FU_eq_sup c w d od
  have hmap := secondCase_linear_P_centralizer_FU_map_conj_eq h hX hFU
    (P := od.P) (X := X) (FU := c.FU)
  rw [← hmap, hP]
  rfl

end CFSG.GorensteinWalter
