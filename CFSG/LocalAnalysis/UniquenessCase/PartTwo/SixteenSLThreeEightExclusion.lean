module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLThreeEightRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
open scoped commutatorElement

theorem s168e3_false_of_sl3Eight_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL : IsSLn ↥(lBar V₀ V hV L) 3 3)
    (hs : 1 < s15 D.M V₀ V hV L) : False := by
  classical
  have hsne : s15 D.M V₀ V hV L ≠ 1 := by omega
  obtain ⟨φ, hφ, hφN⟩ :=
    C163.exists_notMem_normalizer_of_s15_ne_one (M := D.M) hV hsne
  rcases c.conc with ⟨t, ht, ht2, htne, htrk, hW⟩
  have hcomm : ⁅lBar V₀ V hV L,
      (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom⁆ = ⊥ :=
    (hW.2.1 φ hφ hφN).1
  let N : Fin 2 → Subgroup (MulAut (Vtil V₀ V hV)) :=
    ![lBar V₀ V hV L, (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom]
  have hNcomp : ∀ j, IsComponentOf (N j) (Mbar D.M V₀ V hV) := by
    intro j
    fin_cases j
    · simpa [N] using hcomp
    · simpa [N] using
        (CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hcomp hφ)
  have hNSL : ∀ j, IsSLn ↥(N j) 3 3 := by
    intro j
    fin_cases j
    · change IsSLn ↥(lBar V₀ V hV L) 3 3
      exact hSL
    · change IsSLn ↥((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) 3 3
      obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
      exact ⟨K, hKf, hKfin, hKcard, ⟨((lBar V₀ V hV L).equivMapOfInjective
        (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective).symm.trans e⟩⟩
  have hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x := by
    intro j l hjl x hx y hy
    fin_cases j <;> fin_cases l
    · exact (hjl rfl).elim
    · have hmem : ⁅x, y⁆ ∈ (⁅lBar V₀ V hV L,
          (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom⁆ :
            Subgroup (MulAut (Vtil V₀ V hV))) :=
        Subgroup.commutator_mem_commutator hx hy
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    · have hmem : ⁅y, x⁆ ∈ (⁅lBar V₀ V hV L,
          (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom⁆ :
            Subgroup (MulAut (Vtil V₀ V hV))) :=
        Subgroup.commutator_mem_commutator hy hx
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
    · exact (hjl rfl).elim
  have hfour := C163.four_le_pRank_of_sl3_eight_pair D c.std.h127 c.std.h119
    c.setting.hyp16.hyp125 hV N hNcomp hNSL hNcomm
  have hupper : CFSG.Open.pRank 7 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank
      7 Nat.prime_seven (by norm_num) D.M D.maxLocal.1
  have he3 := c.std.h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
