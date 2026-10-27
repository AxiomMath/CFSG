module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

theorem noCQ425_of_comm_centralizer {S : Type} [Group S] [Finite S]
    (h : ∀ s : S, orderOf s = 3 → ∀ a b : S, a ∈ Subgroup.centralizer ({s} : Set S) →
      b ∈ Subgroup.centralizer ({s} : Set S) → a * b = b * a) : NoCQ425 S := by
  intro s K hs3 _ hKs hKq _
  obtain ⟨a, b, hab⟩ := hKq.2.2
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (h s hs3 a b (hKs a.2) (hKs b.2))

theorem noCQ425_projSL_two {F : Type} [Field F] [Finite F] {S : Type} [Group S] [Finite S]
    (φ : S ≃* projSL 2 F) : NoCQ425 S := by
  refine noCQ425_of_comm_centralizer fun s hs3 a b ha hb => ?_
  set ψ : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := φ.trans (projSLEquivPSL F)
  have hπ : GH74.GLS.IVK.Proofs2.IsCentralQuot
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    ⟨QuotientGroup.mk'_surjective _, fun x => QuotientGroup.eq_one_iff x⟩
  have hs1 : ψ s ≠ 1 := by
    intro h1
    have : s = 1 := ψ.injective (by rw [h1, map_one])
    rw [this, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have hs3' : ψ s ^ 3 = 1 := by
    rw [← map_pow, ← hs3, pow_orderOf_eq_one, map_one]
  have hca : ψ a * ψ s = ψ s * ψ a := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp ha]
  have hcb : ψ b * ψ s = ψ s * ψ b := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hb]
  have h := hπ.centralizer_comm_of_odd hs1 (r := 3) (by decide) hs3' hca hcb
  apply ψ.injective
  rw [map_mul, map_mul, h]

theorem noCQOf_projSL_two (F : Type) [Field F] [Finite F] : NoCQOf (projSL 2 F) :=
  fun _ _ _ _ _ ⟨e⟩ => noCQ425_projSL_two e

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
