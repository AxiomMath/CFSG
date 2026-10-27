module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux2
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux3
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux4
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux5
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux6
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux7
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux8
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux9
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux10

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

private theorem ggNSPosPA_transposition_reflection (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) (hab : a ≠ b) :
    GGIsReflection p (((ggNSPosPA_permAutEquiv h hd (Equiv.swap a b) :
      ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)) := by
  refine ⟨?_, ggNSPosPA7_card_fixed h hd hab⟩
  have h2 : (ggNSPosPA_permAutEquiv h hd (Equiv.swap a b)) ^ 2 = 1 := by
    rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
  have h3 := congrArg (fun x : ↥(ggAutomizer ψ.range Bs) => (x : MulAut ↥Bs)) h2
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h3

theorem ggNSDiag_automizer_perm (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    ∃ ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer ψ.range Bs),
      (∀ (σ : Equiv.Perm (Fin n)) (s : ↥Bs),
        ((((ε σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
          ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹) ∧
      ∀ a b : Fin n, a ≠ b → GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
  refine ⟨ggNSPosPA_permAutEquiv h hd, ?_, ?_⟩
  · intro σ s
    exact ggNSPosPA_permAutEquiv_apply h hd σ s
  · intro a b hab
    exact ggNSPosPA_transposition_reflection h hd a b hab

end CFSG.StandardType

end
