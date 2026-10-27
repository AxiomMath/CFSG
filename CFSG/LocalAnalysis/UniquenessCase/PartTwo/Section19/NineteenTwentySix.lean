module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenGlueSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThirteenUse
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentySixOrbitThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentySixOrbitOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactCentralOmega)

variable {G : Type} [Group G] [Finite G]

theorem nineteen_twentysix (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) (hr3 : 3 ∈ piSet A → r = 3)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx22.ctx) (h12wc : Concl19_12wc A)
    (h13 : Concl19_13 D A) (hAV : A ≤ centralizer (V₀ : Set G))
    (h332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hCO : KFactCentralOmega)
    (hK1 : K_19_26_rankOne) :
    R19_26At D V₀ V p L A t B r A₀ H h := by
  change Odd (S17.nOf L)
  rcases Nat.even_or_odd (S17.nOf L) with heven | hodd
  · exfalso
    have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard
    have hcardA : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
      card_eq_of_isZModSq h.ctx22.ctx.hAcard
    have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := by
      have h2 : 2 ∣ S17.nOf L := even_iff_two_dvd.mp heven
      have h := Nat.pow_sub_one_dvd_pow_sub_one 2 h2
      norm_num at h ⊢
      exact h
    have h3dvdA : 3 ∣ Nat.card A := by
      rw [hcardA]
      exact h3dvd.mul_right _
    have h3mem : 3 ∈ piSet A := ⟨Nat.prime_three, h3dvdA⟩
    have hr : r = 3 := hr3 h3mem
    subst r
    obtain ⟨E, hEA, hEel, hEcard⟩ :=
      exists_isElemAbelian_card_nine_of_isZModSq h.ctx22.ctx.hAcard h3dvdA
    have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := h12 E hEA hEel hEcard
    have hNEM : normalizer (E : Set G) ≤ D.M :=
      CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hEU
    have hA₀E : A₀ ≤ E := by
      intro a ha
      rw [@eq_powTorsionSubgroup_of_isElemAbelian_card G _ _ A E hAcomm
        (S17.nOf L) 3 h.ctx22.ctx.hAcard Nat.prime_three h3dvdA hEA hEel hEcard,
        @mem_powTorsionSubgroup G _ _ A hAcomm 3 a]
      refine ⟨h.ctx22.hA₀ ha, ?_⟩
      have hdvd : orderOf a ∣ 3 := by
        simpa [h.ctx22.hcard] using Subgroup.orderOf_dvd_natCard A₀ ha
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    obtain ⟨K, hKH, hKcomp, hfaith⟩ := nineteen_glue_six D h
    obtain ⟨hZodd, hZV⟩ := center_facts_of_ctx19_23 D h hKH hKcomp
    have hΩ : ∀ Q : Subgroup G, IsPGroup 3 Q → ∀ x ∈ Q, x ^ 3 = 1 → ∀ y ∈ Q, y ^ 3 = 1 →
        x * y = y * x :=
      fun Q hQ x hxQ hx y hyQ hy => commute_of_concl19_13 h13 h3mem hQ hxQ hx hyQ hy
    have hrk : ∀ X : Subgroup G, IsElemAbelian 3 X → Nat.card X ≤ 27 :=
      fun X hX => card_le_27_of_concl19_13 h.ctx22.ctx h13 h3mem hX
    by_cases hEN : E ≤ normalizer (K : Set G)
    · exact nineteen_twentysix_orbit_one D h hAV hΩ hrk h12wc h332 hCO hK1 hEA hEel hEcard
        hA₀E hNEM hKH hKcomp hfaith hZodd hZV hEN
    · exact nineteen_twentysix_orbit_three D h hEA hEel hEcard hA₀E hNEM hKH hKcomp hfaith
        hZodd hEN
  · exact hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
