module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpZ3
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpE9
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpA5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {B : LinearMap.BilinForm (ZMod 2) W} {a b : W ≃ₗ[ZMod 2] W}

theorem PairHyp.symm (h : PairHyp B a b) : PairHyp B b a :=
  ⟨h.nondeg, h.alt, h.hb, h.ha⟩

theorem pairShapeHom_closure_pair (h : PairHyp B a b) :
    PairShapeHom ↥(Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W))) := by
  by_cases hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥
  · exact pairShapeHom_z3 h hQ0
  by_cases hP0 : commSp a ⊓ B.orthogonal (commSp b) = ⊥
  · have h' := pairShapeHom_z3 h.symm hP0
    rwa [Set.pair_comm] at h'
  by_cases hperp : ∀ p ∈ commSp a, ∀ q ∈ commSp b, B p q = 0
  · exact pairShapeHom_e9 h hperp
  obtain ⟨p₀, hp₀mem, hp₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨q₀, hq₀mem, hq₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  obtain ⟨hp₀, hp₀o⟩ := Submodule.mem_inf.mp hp₀mem
  obtain ⟨hq₀, hq₀o⟩ := Submodule.mem_inf.mp hq₀mem
  push_neg at hperp
  obtain ⟨p₁, hp₁, q₁, hq₁, hne⟩ := hperp
  have d : A5Data B a b p₀ q₀ :=
    ⟨hp₀, hp₀0,
      fun q hq => by
        rw [bil_comm_of_alt h.alt]
        exact LinearMap.BilinForm.mem_orthogonal_iff.mp hp₀o q hq,
      hq₀, hq₀0, fun p hp => LinearMap.BilinForm.mem_orthogonal_iff.mp hq₀o p hp,
      ⟨p₁, hp₁, q₁, hq₁, hne⟩⟩
  exact pairShapeHom_of_fiveVec (d.fiveVec h)

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
