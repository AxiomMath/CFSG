module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411T
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Omega
public import CFSG.RankThree.PartTwo.Sec21.FF84S411Twist

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] [Finite G]

section
variable (h48 : FF84_4_8) (h47 : FF84_4_7) (hCSb : HypS48CSb) (hb2 : HypS48b2)
  (h49 : HypS49orbits) (h49S6 : HypS49S6) (hE27 : HypOmNormalizerE27)
  (hPar : HypOmParabolic) (hPair : HypOmPair) (hTr : HypTransvRank) (hNoAlt : HypOmNoAlt)
  {b : G} {L B K : Subgroup G} {b₁ b₂ : G} (h : FF84Post b L B K b₁ b₂) {U : Subgroup G}
  (hU : U ∈ PiStar (Cen b) B 2) {s t : G} (hd : FF84MData b (Op 2 (Nor U)) s t)
include h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair hTr hNoAlt h hU hd

theorem S411_ctx :
    ∃ (e : ↥(Op 2 (Nor U)) ≃* Multiplicative F6) (ψ : ↥(Nor (Op 2 (Nor U))) →* OmG)
      (hs : s ∈ Op 2 (Nor U)) (ht : t ∈ Op 2 (Nor U)),
      Ctx411 (Op 2 (Nor U)) e ψ ⟨s, hs⟩ ⟨t, ht⟩ b := by
  obtain ⟨-, hsS, htS, hs1, ht1, hst, hbs, hbt, hSs, hSt, hSst, -⟩ := hd
  obtain ⟨e0, hfor, -⟩ := S410_omega_pair h48 h47 hCSb hb2 h49 h49S6 hE27 h hU
  obtain ⟨ψ0, H0⟩ := exists_omSet hfor
  obtain ⟨-, hSE, -, -, -, -, -⟩ := h48 G b L B K b₁ b₂ h.sec U hU
  have hBE : IsElemAb 3 3 B := h.sec.mono.1
  have hgen : B = Subgroup.closure {b, b₁, b₂} := h.sec.mono.2.1
  have hbB : b ∈ B := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have hc0 : Nat.card ↥(Op 2 (Nor U) ⊓ Cen b) = 16 := by
    rw [hCSb G b L B K b₁ b₂ h U hU]
    obtain ⟨U₁, U₂, -, -, -, hU47⟩ := h47 G b L B K b₁ b₂ h.sec
    exact (hU47 U hU).1.2
  let sS : ↥(Op 2 (Nor U)) := ⟨s, hsS⟩
  let tS : ↥(Op 2 (Nor U)) := ⟨t, htS⟩
  have hqs : qMinus (Multiplicative.toAdd (e0 sS)) = 1 := (H0.hq sS hs1).2 hSs.symm
  have hz : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  have hqt : qMinus (Multiplicative.toAdd (e0 tS)) = 0 :=
    hz _ (fun hh => hSt ((H0.hq tS ht1).1 hh).symm)
  have hsq : ∀ x : ↥(Op 2 (Nor U)), x * x = 1 := fun x => sq_S e0 x
  have hst1 : ((sS * tS : ↥(Op 2 (Nor U))) : G) ≠ 1 := by
    intro hh
    have h1 : sS * tS = 1 := Subtype.ext hh
    have h2 : tS = sS := by
      have := congrArg (fun w => sS * w) h1
      simp only [← mul_assoc, hsq sS, one_mul, mul_one] at this
      exact this
    exact hst (congrArg Subtype.val h2).symm
  have hqst : qMinus (Multiplicative.toAdd (e0 sS) + Multiplicative.toAdd (e0 tS)) = 0 := by
    rw [← toAdd_e_mul]
    exact hz _ (fun hh => hSst ((H0.hq (sS * tS) hst1).1 hh).symm)
  have ht0 : Multiplicative.toAdd (e0 tS) ≠ 0 := by
    intro hh
    exact ht1 (congrArg Subtype.val (eq_one_of_toAdd_e_zero (e := e0) hh))
  obtain ⟨e, ψ, H, hes, het⟩ := exists_twist H0 hqs hqt hqst ht0
  have hb1 : b ≠ 1 := by
    intro hb
    subst hb
    have hall : Op 2 (Nor U) ⊓ Cen (1 : G) = Op 2 (Nor U) := by
      ext x
      simp only [Subgroup.mem_inf, and_iff_left_iff_imp]
      exact fun _ => Subgroup.mem_centralizer_singleton_iff.2 (by simp)
    rw [hall, hSE.2] at hc0
    norm_num at hc0
  have hb3 : orderOf b = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI := hBE.1
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := B) b hbB) hb1
  have hbs' : b ∈ Cen s := hbs
  have htb : t ∈ Op 2 (Nor U) ⊓ Cen b :=
    Subgroup.mem_inf.2 ⟨htS,
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm⟩
  refine ⟨e, ψ, hsS, htS, ⟨H, hes, het, h.sec.hyp.char2, hbs, hbt, hb3, hc0, ?_, hSE.1, hPar,
    hPair, hNoAlt⟩⟩
  intro A hA hAE
  exact hTr G b L B K b₁ b₂ h U hU t htb ht1 (fun hh => hSt hh.symm) A hA hAE

theorem S411_Rstar :
    IsExtraspecialPlus 4 (Op 2 (Cen t) ⊓ Nor (Op 2 (Nor U) ⊓ Op 2 (Cen t))) := by
  obtain ⟨e, ψ, hs, ht, C⟩ := S411_ctx h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair hTr hNoAlt h hU hd
  exact C.Rstar_extraspecial

theorem S411_T : Op 2 (Cen t) = Op 2 (Cen t) ⊓ Nor (Op 2 (Nor U) ⊓ Op 2 (Cen t)) := by
  obtain ⟨e, ψ, hs, ht, C⟩ := S411_ctx h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair hTr hNoAlt h hU hd
  exact C.T_eq

theorem S411_main : IsExtraspecialPlus 4 (Op 2 (Cen t)) := by
  have h1 := S411_Rstar h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair hTr hNoAlt h hU hd
  rwa [← S411_T h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair hTr hNoAlt h hU hd] at h1

end

theorem ff84_4_11m_of (h43 : FF84_4_3) (h44 : FF84_4_4) (h46 : FF84_4_6) (h47 : FF84_4_7)
    (h48 : FF84_4_8) (hCSb : HypS48CSb) (hb2 : HypS48b2) (h49 : HypS49orbits)
    (h49S6 : HypS49S6) (hE27 : HypOmNormalizerE27) (hPar : HypOmParabolic)
    (hPair : HypOmPair) (hTr : HypTransvRank) (hNoAlt : HypOmNoAlt) : FF84_4_11m := by
  intro G _ _ b L B K b₁ b₂ hsec U hU s t hd
  exact S411_main h48 h47 hCSb hb2 h49 h49S6 hE27 hPar hPair hTr hNoAlt
    (post_of_items h43 h44 h46 hsec) hU hd

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
