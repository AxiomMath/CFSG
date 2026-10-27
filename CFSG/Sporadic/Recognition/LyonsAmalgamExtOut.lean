module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open CFSG.ComponentClassification.PerfectAutomorphisms

section Out

variable {M : Type*} [Group M]

theorem card_mulAut_le_of_centerQuot [Group.IsPerfect M] {Q : Type*} [Group Q]
    [Finite (MulAut Q)] (e : M ⧸ Subgroup.center M ≃* Q) :
    Nat.card (MulAut M) ≤ Nat.card (MulAut Q) :=
  Nat.card_le_card_of_injective _
    ((MulAut.congr e).injective.comp (centerQuotientHom_injective M))

end Out

section CentralKernel

variable {M S : Type*} [Group M] [Group S]

theorem ker_eq_center_of_central_ker (q : M →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center M) (hS : Subgroup.center S = ⊥) :
    q.ker = Subgroup.center M := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hqz : q z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨m, rfl⟩ := hq s
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) m]
  rwa [hS, Subgroup.mem_bot] at hqz

@[expose] noncomputable def centerQuotMulEquivOfCentralKer (q : M →* S)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center M)
    (hS : Subgroup.center S = ⊥) : M ⧸ Subgroup.center M ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq_center_of_central_ker q hq hker hS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

end CentralKernel

end CFSG.Sporadic.Recognition.LyonsSims
