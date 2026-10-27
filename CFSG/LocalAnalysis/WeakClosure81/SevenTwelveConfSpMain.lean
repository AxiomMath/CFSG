module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfRoot
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpRad
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.CTP CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem exists_spForm_eq_one_of_ne_zero {k : ℕ} {F : Type} [Field F]
    {e : Fin k ⊕ Fin k → F} (he : e ≠ 0) : ∃ f, spForm k F e f = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, spForm k F e x ≠ 0 := by
    by_contra h
    exact he (spForm_nondegenerate.1 e (fun x => not_not.mp (not_exists.mp h x)))
  exact ⟨(spForm k F e x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩

theorem exists_sevenTwelveConfig_statedSp {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) {g : ↥(StatedSp k F)}
    (hg : IsSymplecticTransvectionIn k g) :
    ∃ (g₂ g₃ y : ↥(StatedSp k F)) (W T : Subgroup ↥(StatedSp k F)),
      SevenTwelveConfig (Subgroup.zpowers g) g₂ g₃ y W T := by
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hF
  obtain ⟨a, c₀, ha, hc₀, rfl⟩ := borel86_spn_eq_spTransvection hg
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c₀
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hc₀ (by rw [hl, mul_zero])
  have he0 : l • a ≠ 0 := smul_ne_zero hl0 ha
  have hgt : spTransvection a c₀ = spConfT (l • a) := by
    rw [spConfT, spTransvection_smul, hl, mul_one]
  obtain ⟨f, hef⟩ := exists_spForm_eq_one_of_ne_zero he0
  obtain ⟨c, hc0, hc1, m, j, hm, hj⟩ := exists_zech_of_card_two_pow hF hn
  rw [hgt]
  exact ⟨_, _, _, _, _, sevenTwelveConfig_of_root (t := spConfT (l • a))
    (y := spConfY (l • a) f c) (n := spConfN (l • a) f c) (u := spConfU f) (m := m) (j := j)
    (Q := spConfRad (l • a)) (spConfT_mul_self _) rfl
    (spConfU_eq hef hc0) (spConfN_eq hef hc0 hm) (spConf_zech hef hc0 hj)
    (spConf_ne_t hef hc0 hc1) (spConf_comm_tn hef hc0) (spConf_comm_ytn hef hc0)
    (isPGroup_spConfRad _)
    (by simpa [spConfT] using spTransvection_mem_spConfRad (l • a) 1 1)
    (by
      rw [spConfT, spTransvection_conj, (spConfY_apply hef hc0).1]
      exact spTransvection_mem_spConfRad _ c 1)
    (fun q hq => commute_spConfT_of_mem_spConfRad _ hq)
    (mem_normalizer_spConfRad _ hc0 (spConfY_apply hef hc0).1)
    (fun H hn hQ => spConf_gen hef hc0 H hn hQ)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
