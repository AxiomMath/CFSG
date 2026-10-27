module

public import CFSG.LocalAnalysis.StandardType.GGK1CDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivFactors

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

private theorem ggK1CDv_fixSub_conj {G : Type*} [Group G] (g : G) :
    ggFixSub (MulAut.conj g) = Subgroup.centralizer ({g} : Set G) := by
  ext x
  rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem ggK1CDv_centralizer_zpowers {G : Type*} [Group G] (g : G) :
    Subgroup.centralizer (Subgroup.zpowers g : Set G) = Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem ggK1C_core_dvd {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) :
    GGK1Dvd p (StatedProj (StatedSp r K)) (MulAut.conj (proj r K x)) := by
  classical
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  intro J hJ
  have hpF : p ∣ Nat.card K ^ 2 - 1 :=
    LayerPDiv.dvd_sq_sub_one (by rw [hK]; exact hdvd)
  have hker : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have hxp : (proj r K x) ^ p = 1 := by rw [← map_pow, hx, map_one]
  have hpair : (proj r K x, x) ∈ LayerFacts.ggConjPairs (proj r K) :=
    LayerFacts.mem_ggConjPairs.mpr fun u => by simp only [map_mul, map_inv]
  have hlift : ∀ e ∈ Subgroup.zpowers (proj r K x),
      ∃ t, (e, t) ∈ LayerFacts.ggConjPairs (proj r K) := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨x ^ k, (LayerFacts.ggConjPairs (proj r K)).zpow_mem hpair k⟩
  have hsub : (proj r K).range ⊓
      Subgroup.centralizer (Subgroup.zpowers (proj r K x) : Set (StatedProj (StatedSp r K))) =
      ggFixSub (MulAut.conj (proj r K x)) := by
    rw [MonoidHom.range_eq_top.mpr
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective, top_inf_eq,
      ggK1CDv_centralizer_zpowers, ggK1CDv_fixSub_conj]
  rw [← hsub] at hJ
  exact LayerPDiv.dvd_card_of_isComponentOf_sp LayerPDiv.altFactorPDivInput_holds
    LayerPDiv.hermFactorPDivInput_holds hker hp hp2 hpF
    (ggIsPGroup_zpowers_of_pow_eq_one hxp) hlift hJ

end CFSG.StandardType

end
