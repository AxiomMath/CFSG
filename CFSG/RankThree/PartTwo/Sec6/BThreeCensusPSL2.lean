module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL2
public import CFSG.RankThree.PartOne.KC.LinearSubfieldDescent

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem map_eq_one_of_perfect_threePrime_projectiveSL_two
    {G F : Type} [Group G] [Finite G] [Group.IsPerfect G] [Field F] [Finite F]
    (ρ : G →* projectiveSL 2 F) (hG3 : ¬ 3 ∣ Nat.card G) (g : G) : ρ g = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, f, hp, hF⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  let e : projectiveSL 2 F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 F)
  let σ : G →* ProjectiveSpecialLinearGroup (Fin 2) F := e.toMonoidHom.comp ρ
  have : Group.IsPerfect σ.range := Group.IsPerfect.range σ
  have hσs : Group.IsSolvable σ.range := isSolvable_of_not_three_dvd_psl2
    (F := F) (p := p) (f := f) (by rw [Nat.card_eq_fintype_card, hF]) σ.range
      (fun hd => hG3 (hd.trans (Subgroup.card_range_dvd σ)))
  have hσeq : σ.range = ⊥ := eq_bot_of_isPerfect_of_isSolvable inferInstance hσs
  apply e.injective
  have hg : σ g ∈ σ.range := ⟨g, rfl⟩
  simpa only [hσeq, Subgroup.mem_bot, σ, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_one] using hg

theorem map_eq_one_of_perfect_threePrime_projectiveSL_two_algebraic
    {G K Ω : Type} [Group G] [Finite G] [Group.IsPerfect G] [Field K] [Finite K]
    [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (ρ : G →* projectiveSL 2 Ω) (hG3 : ¬ 3 ∣ Nat.card G) (g : G) : ρ g = 1 := by
  obtain ⟨E, hE, -, κ, hκ, hcard, ρE, hcomp, hkerE⟩ :=
    CFSG.RankThree.PartOne.exists_finite_subfield_projectiveSL_lift
      (K := K) (by decide : 0 < 2) ρ ∅
  let : Finite E := hE
  have hg : ρE g = 1 := map_eq_one_of_perfect_threePrime_projectiveSL_two ρE hG3 g
  have h := DFunLike.congr_fun hcomp g
  simpa only [MonoidHom.comp_apply, hg, map_one] using h.symm

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
