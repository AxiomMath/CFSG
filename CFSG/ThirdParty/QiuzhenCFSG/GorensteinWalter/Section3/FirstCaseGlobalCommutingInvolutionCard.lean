module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseBaseInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! Transport the involution fiber of an arbitrary involution to the fixed
centralizer fiber.  This is the ambient half of the commuting-pair count. -/

public theorem firstCase_global_commuting_involution_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {s : G} (hs : IsInvolution s) :
    Nat.card {x : G // IsInvolution x ∧ Commute s x} =
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} := by
  classical
  obtain ⟨g, hgs⟩ := fact_2_preamble_involutions_conjugate hmin s c.t hs c.t_involution
  let A : Type u := {x : G // IsInvolution x ∧ Commute s x}
  let B : Type u := {x : G // IsInvolution x ∧ x ∈ c.H}
  let f : A → B := fun x =>
    ⟨g * (x : G) * g⁻¹, by
      have hxI : IsInvolution (g * (x : G) * g⁻¹) := by
        refine ⟨?_, ?_⟩
        · intro h
          apply x.2.1.1
          calc
            (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
            _ = 1 := by rw [h]; simp
        · rw [pow_two]
          calc
            (g * (x : G) * g⁻¹) * (g * (x : G) * g⁻¹) =
                g * ((x : G) * (x : G)) * g⁻¹ := by group
            _ = 1 := by rw [← pow_two, x.2.1.2]; simp
      refine ⟨hxI, ?_⟩
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hcomm : Commute (g * s * g⁻¹) (g * (x : G) * g⁻¹) :=
        x.2.2.conj g
      simpa [hgs] using hcomm.eq.symm⟩
  let fInv : B → A := fun x =>
    ⟨g⁻¹ * (x : G) * g, by
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro h
          apply x.2.1.1
          calc
            (x : G) = g * (g⁻¹ * (x : G) * g) * g⁻¹ := by group
            _ = 1 := by rw [h]; simp
        · rw [pow_two]
          calc
            (g⁻¹ * (x : G) * g) * (g⁻¹ * (x : G) * g) =
                g⁻¹ * ((x : G) * (x : G)) * g := by group
            _ = 1 := by rw [← pow_two, x.2.1.2]; simp
      · have hcomm : Commute (g⁻¹ * c.t * g) (g⁻¹ * (x : G) * g) := by
          have hxC : (x : G) * c.t = c.t * (x : G) := by
            simpa [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
              using x.2.2
          simpa [inv_inv] using (show Commute c.t (x : G) from hxC.symm).conj g⁻¹
        have hgs' : g⁻¹ * c.t * g = s := by
          calc
            g⁻¹ * c.t * g = g⁻¹ * (g * s * g⁻¹) * g := by rw [hgs]
            _ = s := by group
        simpa [hgs'] using hcomm⟩
  have hfInv : Function.LeftInverse fInv f := by
    intro x
    apply Subtype.ext
    dsimp [fInv, f]
    change g⁻¹ * (g * (x.1 : G) * g⁻¹) * g = (x.1 : G)
    group
  have hfInv' : Function.RightInverse fInv f := by
    intro x
    apply Subtype.ext
    dsimp [fInv, f]
    change g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G)
    group
  exact Nat.card_congr (Equiv.ofBijective f ⟨
    (fun a b h => by exact hfInv.injective h),
    (fun b => ⟨fInv b, hfInv' b⟩)⟩)

end CFSG.GorensteinWalter
