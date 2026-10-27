module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunLowerBound
public import CFSG.ClassicalInvolution.Asc77.AscMuTabRoots
import CFSG.ClassicalInvolution.Q3.Q3MTLarge
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Asc77.MuTab
open CFSG.LocalAnalysis.UniquenessCase
open F14


theorem threeOrth_of_funManyType {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hmany : FunManyType t n) :
    ThreeOrth (modelUniv t n p f Fact.out).D := by
  cases t with
  | PSL => exact threeOrth_psl hadm hmany
  | PSU =>
    by_cases he : Even n
    · exact threeOrth_psu_even hadm he hmany
    · exact threeOrth_psu_odd hadm he (by
        change 6 ≤ n at hmany
        have hn6 : n ≠ 6 := fun h => he (h ▸ (by decide : Even 6))
        omega)
  | PSp => exact threeOrth_psp hmany
  | POmegaOdd => exact threeOrth_pOmegaOdd hadm hmany
  | POmegaPlus =>
    change 4 ≤ n at hmany
    by_cases hn4 : n = 4
    · subst n
      have hl : ∀ i : Fin (modelUniv .POmegaPlus 4 p f Fact.out).D.rank,
          CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
            (modelUniv .POmegaPlus 4 p f Fact.out).D (Pi.single i 1) :=
        fun i => CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single
          .POmegaPlus 4 p f Fact.out trivial hadm i trivial
      have h : modelUniv .POmegaPlus 4 p f Fact.out =
          ⟨spinGroup
            (CFSG.LieType.Universal.Spin.quadPlus 4 (GaloisField p f)),
            CFSG.LieType.Universal.Spin.plusDatum 4 (GaloisField p f) (by omega)⟩ :=
        CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (n := 4) (by omega)
      generalize modelUniv .POmegaPlus 4 p f Fact.out = L at h hl ⊢
      subst h
      refine threeOrth_of_nodes _ (a := (0 : Fin 4)) (b := (2 : Fin 4)) (c := (3 : Fin 4))
        (hl _) (hl _) (hl _) ?_ ?_ ?_ <;>
        · show CFSG.LieType.Universal.Spin.cartanD 4 _ _ = 0
          simp [CFSG.LieType.Universal.Spin.cartanD]
    · exact threeOrth_pOmegaPlus hadm (by omega)
  | POmegaMinus => exact threeOrth_pOmegaMinus hadm hmany
  | F4 => obtain rfl : n = 0 := hadm.2.2; exact threeOrth_F4 hadm
  | E6 => obtain rfl : n = 0 := hadm.2.2; exact threeOrth_E6 hadm
  | E7 => obtain rfl : n = 0 := hadm.2.2; exact threeOrth_E7 hadm
  | E8 => obtain rfl : n = 0 := hadm.2.2; exact threeOrth_E8 hadm
  | twistedE6 => obtain rfl : n = 0 := hadm.2.2; exact threeOrth_twistedE6 hadm
  | G2 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits => exact hmany.elim

theorem three_le_ncard_funSet_of_funManyType {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (hmany : FunManyType t n) (P : Sylow 2 X) :
    3 ≤ (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard := by
  have : Fact p.Prime := ⟨hp⟩
  have hfund : IsFundTag t := by
    cases t <;> simp_all [FunManyType, IsFundTag]
  have hG2 : t ≠ .G2 := by rintro rfl; exact hmany.elim
  have hD4 : t ≠ .trialityD4 := by rintro rfl; exact hmany.elim
  have horth := threeOrth_of_funManyType hadm hmany
  have htrip : ∃ R₁ ∈ ModelFund p t n f, ∃ R₂ ∈ ModelFund p t n f,
      ∃ R₃ ∈ ModelFund p t n f, R₁ ≠ R₂ ∧ R₁ ≠ R₃ ∧ R₂ ≠ R₃ ∧
        Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
    by_cases hq : 5 ≤ p ^ f
    · exact exists_triple_of_threeOrth hp2 hq hfund hadm horth
    · have hp3f1 : p = 3 ∧ f = 1 :=
        Nat.prime_three.pow_eq_iff.mp
          ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
            hp hp2 hadm.2.1).resolve_right hq)
      obtain ⟨rfl, rfl⟩ := hp3f1
      exact CFSG.ClassicalInvolution.Q3.Q3MT.exists_triple_of_threeOrth3
        hfund hadm hG2 hD4 horth
  obtain ⟨R₁, h₁, R₂, h₂, R₃, h₃, h12, h13, h23, c12, c13, c23⟩ := htrip
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p f hp hp2 hfund hadm X hX
  have hsl : ∀ R ∈ ModelFund p t n f, Nonempty (R ≃* Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField p f)) := fun R hR =>
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm hG2 hD4 hR
  let K : Fin 3 → Subgroup X := ![R₁.map ψ, R₂.map ψ, R₃.map ψ]
  have hK : ∀ i, IsFundamentalOver (p ^ f) (K i) := by
    intro i
    have key : ∀ R ∈ ModelFund p t n f, IsFundamentalOver (p ^ f) (R.map ψ) :=
      fun R hR => ⟨t, n, p, f, hp, hp2, rfl, hfund, hadm, ψ, hψs, hψk, R, hR, rfl⟩
    fin_cases i
    · exact key _ h₁
    · exact key _ h₂
    · exact key _ h₃
  have n12 := F14.map_ne_of_commuting_of_equiv_sl2 ψ hψk (Classical.choice (hsl R₁ h₁)) c12
  have n13 := F14.map_ne_of_commuting_of_equiv_sl2 ψ hψk (Classical.choice (hsl R₁ h₁)) c13
  have n23 := F14.map_ne_of_commuting_of_equiv_sl2 ψ hψk (Classical.choice (hsl R₂ h₂)) c23
  have hinj : Function.Injective K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals change _ at hij
    all_goals first | rfl | exact (n12 hij).elim | exact (n13 hij).elim |
      exact (n23 hij).elim | exact (n12 hij.symm).elim | exact (n13 hij.symm).elim |
      exact (n23 hij.symm).elim
  have hcomm : ∀ i j, i ≠ j → Commutes (K i) (K j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim |
      exact CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ c12 |
      exact CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ c13 |
      exact CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ c23 |
      exact (CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ c12).symm |
      exact (CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ c13).symm |
      exact (CFSG.ClassicalInvolution.Asc77.ih8_commutes_map ψ c23).symm
  have hnorm : ∀ i j, K j ≤ Subgroup.normalizer (K i : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j; exact Subgroup.le_normalizer
    · exact (show K j ≤ Subgroup.centralizer (K i : Set X) from
        fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha =>
          hcomm i j hij a ha b hb).trans (Subgroup.centralizer_le_normalizer _)
  have h := F14.natCard_le_ncard_funSet_of_normalizing_family
    (𝔉 := fundPred (p ^ f))
    (fun g _ hK => isFundamentalOver_map_mulEquiv (MulAut.conj g) hK) K hK hinj hnorm P
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.UC22
