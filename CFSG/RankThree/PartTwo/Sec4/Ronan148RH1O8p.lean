module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1LieOrd
public import CFSG.HardMathSupport.Dickson.Bal207.Closed
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowGF2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projOmegaPlus)
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section O8p


theorem fixSubgroup_conj' {X : Type} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  rw [← autFix_eq_fixSubgroup, autFix_conj]

theorem noCfgS427_o8p {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* projOmegaPlus 4 (GaloisField 2 1)) :
    NoCfgS427 S := by
  obtain ⟨eT⟩ := RonanK429E.nonempty_mulEquiv_omegaT_projOmegaPlus
  let φT : S ≃* omegaT := e.trans eT
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hna
  have hM : CFSG.Open.StatedClassicalModel S .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero, ⟨e.trans Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  obtain ⟨F, _, _, _, Q, eQ, hF, hQ, hT, hV, -, -⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.exists_coords_of_model
      (Or.inl ⟨rfl, ⟨2, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩) hM
  have hF' : Nat.card F = 2 ∨ Nat.card F = 8 := Or.inl (by rw [hF]; norm_num)
  intro σ h3 h1
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
    refine Good427.of_mulEquiv_centralizer eQ ?_
    have hsh := CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthInnerShapeInput_holds hF'
      (by norm_num : 0 < 2 * 4) hQ hT rfl (le_refl 4) hV (t := eQ s)
      (by rwa [MulEquiv.orderOf_eq])
    have hg := good427_of_layer_type not_isA5Type_of_orthCompType hsh.layer hsh.type
    rwa [fixSubgroup_conj'] at hg
  · set τ := MulAut.congr φT σ with hτ
    have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, h3, map_one]
    have hτout : τ ∉ (MulAut.conj : omegaT →* MulAut omegaT).range := by
      rintro ⟨y, hy⟩
      apply hin
      refine ⟨φT.symm y, ?_⟩
      have h2 : MulAut.congr φT (MulAut.conj (φT.symm y)) = MulAut.congr φT σ := by
        rw [RonanK429E.congr_conj, MulEquiv.apply_symm_apply]
        exact hy
      exact (MulAut.congr φT).injective h2
    have hg : Good427 (Sec4.autFix τ) :=
      good427_of_not_five_dvd (RonanK429E.O8Out.not_five_dvd_autFix τ hτ3 hτout)
    rw [hτ, autFix_congr] at hg
    exact Good427.of_map φT.toMonoidHom φT.injective hg



theorem rowOf427_o8p
    : RowOf427 (projOmegaPlus 4 (GaloisField 2 1)) :=
  rowOf427_of_noCfgS fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    refine ⟨noCfgS427_o8p hna e, noONS427_of_card ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projOmegaPlus_four_two_gf2]
    norm_num

end O8p

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
