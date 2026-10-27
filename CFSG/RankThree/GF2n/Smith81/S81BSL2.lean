module

public import CFSG.RankThree.GF2n.Smith81.Lin26Torus

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.inZClass_of_mem_sup (hc : Ctx M Q Z B) {w : G} (hw : w ∈ Z ⊔ B) (hw1 : w ≠ 1) :
    InZClass Z w := by
  obtain ⟨m, φ, ψ, -, hs, hcompat, -, -, hV⟩ := Ctx.inducesSL2' hc
  have hXW : ∀ u ∈ Q ⊔ QB B, ∀ v ∈ Z ⊔ B, u * v * u⁻¹ ∈ Z ⊔ B := fun u hu v hv =>
    (Subgroup.mem_normalizer_iff.mp (Ctx.sup_QB_le_normalizer_ZB hc hu) v).mp hv
  have hA : ∀ u : Fin 2 → GaloisField 2 m,
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m),
        ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) *ᵥ u) 1 = 0 := by
    intro u
    by_cases hy : u 1 = 0
    · exact ⟨1, by simp [hy]⟩
    · refine ⟨⟨!![0, -(u 1)⁻¹; u 1, -(u 0)], by simp [Matrix.det_fin_two_of, hy]⟩, ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  obtain ⟨A, hA1⟩ := hA (Multiplicative.toAdd (ψ ⟨w, hw⟩))
  obtain ⟨s, hsA⟩ := hs A
  have hw' : (s : G) * w * (s : G)⁻¹ ∈ Z ⊔ B := hXW (s : G) s.2 w hw
  have hcomp := hcompat s ⟨w, hw⟩ ⟨(s : G) * w * (s : G)⁻¹, hw'⟩ rfl
  have hwZ : (s : G) * w * (s : G)⁻¹ ∈ Z := by
    refine (hV ⟨(s : G) * w * (s : G)⁻¹, hw'⟩).mpr ?_
    rw [hcomp, hsA]
    exact hA1
  unfold InZClass
  refine ⟨(s : G)⁻¹, (s : G) * w * (s : G)⁻¹, hwZ, ?_, ?_⟩
  · intro h
    apply hw1
    calc w = (s : G)⁻¹ * ((s : G) * w * (s : G)⁻¹) * (s : G) := by group
      _ = 1 := by rw [h]; group
  · group

end CFSG.RankThree.GF2n.Smith81
