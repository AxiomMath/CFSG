module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.BorelRoute
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.U3Borel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.U3Gen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.U3Normal
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UG
import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec16.Proof166Res6 (permSU)

theorem kGenSpans_of_su3 {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (hq : p ^ f % 3 = 1) (hp7 : p ≠ 7) {B R : Subgroup (unitarySU p f F 3)}
    (hBR : IsKGenPair B R) : KGenSpans B R := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases h7 : 7 ∣ p ^ f + 1
  · obtain ⟨g, hBg, hRg⟩ := exists_conj_eq_zpowers_permSU h hq h7 hBR
    refine KGenSpans.of_map (MulAut.conj g) ?_
    intro H hBH hYH
    have hq7 : 7 < p ^ f := by omega
    have hR7 : IsPGroup 7 (R.map (MulAut.conj g).toMonoidHom) :=
      (hBR.map (MulAut.conj g)).2.1.isPGroup
    refine su3_eq_top_of_diag_mem_of_centralizer_le h hq hq7 (fun x hx => ?_) ?_
    · exact hYH _ le_rfl hR7 (Subgroup.centralizer_le_normalizer _ (hRg x hx))
    · have hcz : centralizer ({permSU h} : Set (unitarySU p f F 3)) ≤
          normalizer ((zpowers (permSU h) : Subgroup (unitarySU p f F 3)) :
            Set (unitarySU p f F 3)) := by
        rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
        exact Subgroup.centralizer_le_normalizer _
      rw [← hBg] at hcz
      exact hcz.trans hBH
  · exfalso
    obtain ⟨P, hRP⟩ := hBR.2.1.isPGroup.exists_le_sylow
    have hcyc : IsCyclic (P : Subgroup (unitarySU p f F 3)) :=
      CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow h.card_eq_sq
        (by norm_num) (Ne.symm hp7) h7 P
    have h1 : IsCyclic (R.subgroupOf (P : Subgroup (unitarySU p f F 3))) := Subgroup.isCyclic _
    let eR := Subgroup.subgroupOfEquivOfLe hRP
    have hRc : IsCyclic R := isCyclic_of_surjective eR.toMonoidHom eR.surjective
    exact CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_isElemAbelian hBR.2.1
      (by rw [hBR.2.2.1]; norm_num) hRc

theorem kGenSpans_of_lieModel_psu3 {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hq : p ^ f % 3 = 1) (h : CFSG.Blueprint.LieModel K .PSU 3 p f) (hG : IsSimpleGroup K)
    (hna : ∃ a b : K, a * b ≠ b * a) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1)
    {B R : Subgroup K} (hBR : IsKGenPair B R) : KGenSpans B R := by
  have hS := h.statedClassicalModel_of_ne_zero three_ne_zero
  by_cases hp7 : p = 7
  · subst hp7
    exact kGenSpans_of_isCoatom_normalizer hG hna h3 hBR
      (exists_isCoatom_normalizer_of_psu hS hBR.2.1.isPGroup)
  · obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := hS
    have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm f 2]⟩
    have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := hU.charP
    have hbot := CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.scalars_subgroupOf_statedSU_eq_bot hF hq
    let e' : K ≃* unitarySU p f F 3 :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
    exact KGenSpans.of_map e' (kGenSpans_of_su3 hU hq hp7 (hBR.map e'))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
