module

public import CFSG.LocalAnalysis.StandardType.ExcPay.RootsE

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F Matrix


theorem excPaySquare_pair {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ}
    [NeZero f] {Bs X : Subgroup G} {ht : GGExcFive t}
    (hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) (S : ExcPaySquare t ht f p Bs X) {i j : Fin (langTag t).rank}
    (hA2 : CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair (τ := langTag t)
      (Pi.single i 1) (Pi.single j 1)) :
    ∃ θG : Su (actualQuadraticSubfield f) 2 f 3 →* G,
      Function.Injective θG ∧ θG.range ≤ X ∧
      (B12 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs (S.s i) ∧
      (B23 (actualQuadraticSubfield f) 2 f).map θG = ggRankOneIn X Bs (S.s j) ∧
      UnitaryBlockStandardPair (actualQuadraticSubfield f) 2 f θG.range
        (ggRankOneIn X Bs (S.s i)) (ggRankOneIn X Bs (S.s j)) := by
  have hFi : Finite (rootKerFam (langTag t) p i) := finite_rootKerFam (langTag t) hp.pos i
  have hFj : Finite (rootKerFam (langTag t) p j) := finite_rootKerFam (langTag t) hp.pos j
  exact pair_of_toral_a2_roots_original_member_actualField S.M hp hp2 hplus
    (Pi.single i 1) (Pi.single j 1) hA2
    (fun a : rootKerFam (langTag t) p i => a.1)
    (fun a : rootKerFam (langTag t) p j => a.1)
    (fun a : rootKerFam (langTag t) p i => S.torus a.1 a.2.1)
    (fun a : rootKerFam (langTag t) p j => S.torus a.1 a.2.1)
    (fun a : rootKerFam (langTag t) p i => ⟨1, by
      rw [pow_one]
      funext k
      exact a.2.1 k⟩)
    (fun a : rootKerFam (langTag t) p j => ⟨1, by
      rw [pow_one]
      funext k
      exact a.2.1 k⟩)
    (famKernel_rootKerFam hτ hp hp2 i)
    (famKernel_rootKerFam hτ hp hp2 j)
    S.ψ S.ψ_inj S.ψ_range S.β S.pres S.compat (S.s i) (S.s j) (S.fix i) (S.fix j)

theorem excPaySquare_comm {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    {Bs X : Subgroup G} {ht : GGExcFive t}
    (hτ : langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    (S : ExcPaySquare t ht f p Bs X) {i j : Fin (langTag t).rank}
    (horth : ∀ α ∈ ({Pi.single i 1, -Pi.single i 1} : Set (Fin (langTag t).rank → ℤ)),
      ∀ β ∈ ({Pi.single j 1, -Pi.single j 1} : Set (Fin (langTag t).rank → ℤ)),
        α ⬝ᵥ ((langTag t).symmetrizedCartan *ᵥ β) = 0) :
    ∀ a ∈ ggRankOneIn X Bs (S.s i), ∀ b ∈ ggRankOneIn X Bs (S.s j), a * b = b * a := by
  have hFi : Finite (rootKerFam (langTag t) p i) := finite_rootKerFam (langTag t) hp.pos i
  have hFj : Finite (rootKerFam (langTag t) p j) := finite_rootKerFam (langTag t) hp.pos j
  have hY : S.M.D.Γ ≤ adjointGroup (langTag t) GGL :=
    (Subgroup.commutator_le_self S.M.D.model).trans inf_le_left
  have hdisj : langTag t = .D4 ∨ langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  refine CFSG.StandardType.ResidualA2Pair.commutation_of_orthogonal_families_original_member
    (τ := langTag t) (L := GGL) hdisj hp hp2
    (fun a : rootKerFam (langTag t) p i => a.1)
    (fun a : rootKerFam (langTag t) p j => a.1)
    (fun a : rootKerFam (langTag t) p i => ⟨1, by
      rw [pow_one]
      funext k
      exact a.2.1 k⟩)
    (fun a : rootKerFam (langTag t) p j => ⟨1, by
      rw [pow_one]
      funext k
      exact a.2.1 k⟩)
    S.M.D.Γ hY ?_ S.ψ S.ψ_inj S.ψ_range S.β S.pres S.compat (S.s i) (S.s j)
    (S.fix i) (S.fix j)
  intro α hα β hβ
  rw [famKernel_rootKerFam hτ hp hp2 i] at hα
  rw [famKernel_rootKerFam hτ hp hp2 j] at hβ
  exact horth α hα β hβ

end CFSG.StandardType.ExcPay
