module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21o
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sa
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s

variable {G : Type} [Group G] [Finite G]

namespace P22s

omit [Finite G] in
theorem mem_normalizer_of_map_conj {A : Subgroup G} {g : G} (h : A.map (MulAut.conj g).toMonoidHom = A) :
    g ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    rwa [← this]

theorem mem_normalizer_jOf (D : Data G) {g : G} (hg : g ∈ normalizer (proofS D : Set G)) :
    g ∈ normalizer (jOf D.T : Set G) := by
  have hJS := jOf_le_proofS D
  have key : ∀ y ∈ normalizer (proofS D : Set G), ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := by
    intro y hy
    refine uc22p22e_conj_jOf fun x hx => ?_
    exact (Subgroup.mem_inf.1 ((Subgroup.mem_normalizer_iff.1 hy x).1 (hJS hx))).1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end P22s

end CFSG.LocalAnalysis.UniquenessCase.UC22
