module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

import CFSG.LocalAnalysis.StandardType.GGRCLinRefl

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem xDatumGraph_holds : XDatumGraphLeaf := by
  intro G _ _ p _ Bs X hD V _ _ ι
  obtain ⟨Λ, _, _, M, C, V₀, _, _, ι₀, φ, h, α, hW, hCartan, hform, hrefl, hpair,
    ⟨f, hf⟩, hgen⟩ := hD
  refine ⟨Set.range (fun i : Λ => ggLin (p := p) ι (φ i)), ?_, ?_, ?_⟩
  · rintro s ⟨i, rfl⟩
    refine ⟨?_, (ggRC_isReflection_iff_linRefl (p := p) ι (φ i)).mp (hrefl i)⟩
    rw [Subgroup.mem_map]
    exact ⟨φ i, by rw [hgen]; exact Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
  · rw [hgen, MonoidHom.map_closure]
    congr 1
    ext s
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ i, ⟨i, rfl⟩, rfl⟩
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩
    have hstep : ∀ u v : Λ, (u ≠ v ∧ M.M u v ≠ 2) →
        (fun a b : V ≃ₗ[ZMod p] V =>
          a ∈ Set.range (fun k : Λ => ggLin (p := p) ι (φ k)) ∧
          b ∈ Set.range (fun k : Λ => ggLin (p := p) ι (φ k)) ∧ ¬ Commute a b)
          (ggLin (p := p) ι (φ u)) (ggLin (p := p) ι (φ v)) := by
      rintro u v ⟨huv, hMuv⟩
      refine ⟨⟨u, rfl⟩, ⟨v, rfl⟩, ?_⟩
      intro hcomm
      have hφcomm : φ u * φ v = φ v * φ u := by
        apply ggLin_injective (p := p) ι
        rw [map_mul, map_mul]
        exact hcomm.eq
      have hsimple_comm : M.simple u * M.simple v = M.simple v * M.simple u := by
        apply f.injective
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul, hf u, hf v]
        exact hφcomm
      have hsq : (M.simple u * M.simple v) ^ 2 = 1 := by
        have hc : Commute (M.simple u) (M.simple v) := hsimple_comm
        rw [hc.mul_pow]
        rw [show M.simple u ^ 2 = 1 from by
              rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
              exact CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem u,
            show M.simple v ^ 2 = 1 from by
              rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
              exact CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem v]
        simp
      have horder : orderOf (M.simple u * M.simple v) = M.M u v := by
        rw [← CoxeterMatrix.toCoxeterSystem_simple]
        exact CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem u v
      have hdvd : M.M u v ∣ 2 := by
        rw [← horder]
        exact orderOf_dvd_iff_pow_eq_one.mpr hsq
      have h1 : M.M u v ≠ 1 := M.off_diagonal u v huv
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exact h1 h'
      · exact hMuv h'
    exact Relation.ReflTransGen.lift (fun k : Λ => ggLin (p := p) ι (φ k)) hstep i j
      (ggRC_weyl_connected hW i j)

end CFSG.StandardType.HdRo7C
