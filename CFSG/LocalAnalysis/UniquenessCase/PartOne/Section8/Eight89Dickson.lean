module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.AltThreeRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open Matrix
open scoped commutatorElement

private theorem k89di_commutator_le_ker {K M : Type*} [Group K] [Group M] [IsMulCommutative M]
    (f : K →* M) : commutator K ≤ f.ker := by
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr ?_
  intro a _ b _
  change f ⁅a, b⁆ = 1
  rw [map_commutatorElement, commutatorElement_def, mul_comm' (f a) (f b)]
  group

private theorem k89di_perfect_hom_eq_one {K M : Type*} [Group K] [Group M] [IsMulCommutative M]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (f : K →* M) (k : K) : f k = 1 := by
  have : Group.IsPerfect K := ⟨hperf⟩
  exact MonoidHom.mem_ker.1 (k89di_commutator_le_ker f (Group.IsPerfect.mem_commutator (g := k)))

private theorem k89di_end_comm_of_finrank_le_one (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V]
    (h : Module.finrank (ZMod q) V ≤ 1) (f g : Module.End (ZMod q) V) : f * g = g * f := by
  have key : ∀ f : Module.End (ZMod q) V, ∃ c : ZMod q, f = c • 1 := by
    intro f
    obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := ZMod q) (V := V)).mp h
    obtain ⟨c, hc⟩ := hv (f v)
    refine ⟨c, ?_⟩
    ext w
    obtain ⟨d, rfl⟩ := hv w
    simp only [map_smul, hc, LinearMap.smul_apply, Module.End.one_apply]
  obtain ⟨c, hc⟩ := key f
  obtain ⟨d, hd⟩ := key g
  rw [hc, hd]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [smul_comm]

private theorem k89di_pRank_statedSL_two (q : ℕ) [Fact q.Prime] (hq7 : 7 ≤ q) :
    CFSG.Open.pRank 3 (StatedSL 2 (ZMod q)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : ZMod q) ≠ 0 := by
    intro h
    have hdvd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp h
    have := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
    omega
  simpa using
    CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSL_le (F := ZMod q) (r := 3) (m := 2)
      (by norm_num) h3

theorem s889_dickson (hAct : S889Act) : S889Dickson := by
  intro q hq hq7 K _ _ hperf hK V _ _ _ hfin ρ k
  have : Fact q.Prime := ⟨hq⟩
  by_cases hfr : Module.finrank (ZMod q) V = 2
  · let b : Module.Basis (Fin 2) (ZMod q) V := Module.finBasisOfFinrankEq (ZMod q) V hfr
    let eEnd : Module.End (ZMod q) V ≃* Matrix (Fin 2) (Fin 2) (ZMod q) :=
      (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
    let ψ : K →* GL (Fin 2) (ZMod q) := (eEnd.toMonoidHom.comp ρ).toHomUnits
    have hψcoe : ∀ x : K, (ψ x : Matrix (Fin 2) (Fin 2) (ZMod q)) = eEnd (ρ x) := by
      intro x
      simp [ψ, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply]
    have hdet : ∀ x : K, Matrix.GeneralLinearGroup.det (ψ x) = 1 := by
      intro x
      have : IsMulCommutative ((ZMod q)ˣ) :=
        IsMulCommutative.of_comm fun a b => Units.ext (mul_comm (a : ZMod q) (b : ZMod q))
      exact k89di_perfect_hom_eq_one hperf (Matrix.GeneralLinearGroup.det.comp ψ) x
    have hleSL : ψ.range ≤ StatedSL 2 (ZMod q) := by
      rintro y ⟨x, rfl⟩
      refine CFSG.Open.StatedAPI.mem_statedSL_of_det ?_
      have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) (hdet x)
      simpa using this
    by_contra hρk
    have hψk : ψ k ≠ 1 := by
      intro h1
      apply hρk
      have hcoe : eEnd (ρ k) = 1 := by
        have := congrArg
          (fun u : GL (Fin 2) (ZMod q) => (u : Matrix (Fin 2) (Fin 2) (ZMod q))) h1
        rwa [hψcoe k] at this
      exact eEnd.injective (by simpa using hcoe)
    have hψrange : ψ.range ≠ ⊥ := by
      intro hbot
      have hmem : ψ k ∈ ψ.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
      rw [hbot] at hmem
      exact hψk (Subgroup.mem_bot.mp hmem)
    obtain ⟨W, hWn, hAlt⟩ := hAct K hperf hK (GL (Fin 2) (ZMod q)) ψ hψrange
    have : W.Normal := hWn
    have hH : CFSG.pRank 3 ↥ψ.range ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup ψ.range]
      exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hleSL).trans
        (k89di_pRank_statedSL_two q hq7)
    have hpr : CFSG.pRank 3 (↥ψ.range ⧸ W) ≤ 1 :=
      CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
        Nat.prime_three (by norm_num) hH (QuotientGroup.mk' W) (QuotientGroup.mk'_surjective W)
    obtain ⟨e⟩ := hAlt
    have heq : CFSG.pRank 3 (↥ψ.range ⧸ W) = CFSG.pRank 3 (alternatingGroup (Fin 6)) := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    rw [heq] at hpr
    have h2 : 2 ≤ CFSG.pRank 3 (alternatingGroup (Fin 6)) := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_three_alternating
        (n := 6) (by norm_num)
    omega
  · have hle : Module.finrank (ZMod q) V ≤ 1 := by omega
    have hcomm : ∀ f g : Module.End (ZMod q) V, f * g = g * f :=
      k89di_end_comm_of_finrank_le_one q V hle
    have : IsMulCommutative (Module.End (ZMod q) V)ˣ :=
      IsMulCommutative.of_comm fun a b => Units.ext (hcomm a b)
    have h1 : ρ.toHomUnits k = 1 := k89di_perfect_hom_eq_one hperf ρ.toHomUnits k
    exact congrArg (fun u : (Module.End (ZMod q) V)ˣ => (u : Module.End (ZMod q) V)) h1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
