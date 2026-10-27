module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8Inner
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projOmegaPlus)
open CFSG.EvenSmallLie.OmegaEight


theorem nonempty_mulEquiv_omegaT_projOmegaPlus :
    Nonempty (projOmegaPlus 4 (GaloisField 2 1) ≃* omegaT) := by
  have hmodel : CFSG.Open.StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1))
      .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero, ⟨Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  have hlm : CFSG.Blueprint.LieModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    Or.inl ⟨by decide, hmodel⟩
  exact nonempty_mulEquiv_omegaT hlm

theorem congr_conj {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem noCfgS429_o8p {S : Type} [Group S] [Finite S] (hna : ∃ a b : S, a * b ≠ b * a)
    [IsSimpleGroup S] (e : S ≃* projOmegaPlus 4 (GaloisField 2 1)) : NoCfgS429 S := by
  obtain ⟨eT⟩ := nonempty_mulEquiv_omegaT_projOmegaPlus
  let φT : S ≃* omegaT := e.trans eT
  let φM : S ≃* O8.OM := e.trans O8.projEquiv
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hna
  refine noCfgS429_of_good fun σ h3 h1 => ?_
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs3 : s ^ 3 = 1 := by
      have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, h3]
      have hz : s ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut S => φ g) h'
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
          _ = s ^ 3 * g := by group
      rw [hZ, Subgroup.mem_bot] at hz
      exact hz
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact h1 (map_one _)
    have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
    rw [autFix_conj]
    exact Good429.of_mulEquiv_centralizer φM
      (O8.good429_OM (φM s) (by rwa [MulEquiv.orderOf_eq]))
  · set τ := MulAut.congr φT σ with hτ
    have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, h3, map_one]
    have hτout : τ ∉ (MulAut.conj : omegaT →* MulAut omegaT).range := by
      rintro ⟨y, hy⟩
      apply hin
      refine ⟨φT.symm y, ?_⟩
      have h2 : MulAut.congr φT (MulAut.conj (φT.symm y)) = MulAut.congr φT σ := by
        rw [congr_conj, MulEquiv.apply_symm_apply]
        exact hy
      exact (MulAut.congr φT).injective h2
    have hg := O8Out.good429_outer τ hτ3 hτout
    rw [hτ, autFix_congr] at hg
    exact Good429.of_map φT.toMonoidHom φT.injective hg

theorem eight_OmegaPlus : RowSOf429 (projOmegaPlus 4 (GaloisField 2 1)) :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_o8p hna e

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
