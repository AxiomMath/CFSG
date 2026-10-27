module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
public import CFSG.RankThree.PartTwo.Sec19.Item1922Full
import CFSG.RankThree.PartTwo.Sec19.Item1923One
import CFSG.RankThree.PartTwo.Sec19.Item1923Two
import CFSG.RankThree.PartTwo.Sec19.Item1923Three
import CFSG.RankThree.PartTwo.Sec19.Item1923Four
import CFSG.RankThree.PartTwo.Sec19.Item1923Five
import CFSG.RankThree.PartTwo.Sec19.Item1923Six
import CFSG.RankThree.PartTwo.Sec19.Item1924Omega
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic

public section

namespace CFSG.RankThree.PartTwo

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec19 (starIm)

theorem item1922Facts_of_item1922Full (h : Item1922Full) : Late.Item1922Facts := by
  intro G _ _ A M N L c hyp hc
  obtain ⟨hNL, hNeq, ⟨c', hc'3, hc', hA⟩, hsyl, hcard, hΩ, hsup, hLM, hO2, hNB⟩ :=
    h G A M N L hyp
  have hz : Subgroup.zpowers c = Subgroup.zpowers c' :=
    SetLike.coe_injective (hc.symm.trans hc')
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers, hz, Nat.card_zpowers, hc'3]
  have hA' : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [hz]; exact hA
  exact ⟨hc, hc3, hNL, hNeq, hA', hsyl, hcard, hΩ, hsup, hLM, hO2, hNB⟩

theorem item1923_of_kfacts
    (h1912 : Late.Item1912) (hkf : Late.KFacts1923)
    (h22 : Late.Item1922Facts) : Item1923 := by
  intro G _ _ A M N L c hyp hc K hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hET := h1912 G hyp.toSec19Std
  have hF := h22 G A M N L c hyp hc
  have hone : ∀ K' ∈ Late.scriptJ M N, ∀ b ∈ A ⊓ L, ∀ k ∈ K',
      b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K' :=
    fun K' hK' => Late.item1923_one hkf hyp hF hK'
  obtain ⟨h2, hm3, hL3⟩ := Late.item1923_two hkf.kf3a hkf.kf2 hkf.h194 hyp hF hK hone
  have hone' := hone K hK
  obtain ⟨hcK, hAK⟩ := Late.item1923_three_a hkf.kf4 hyp hF hK h2 hL3 hone'
  have hKM := Late.item1923_three_b hkf.kf1 hyp hF hK h2 hL3 hone' hcK hAK
  have hKeq := Late.item1923_three_c hyp hF hK hcK hKM hL3
  obtain ⟨hpar, hC⟩ := Late.item1923_four hkf hyp hF hK h2 hL3 hcK
  obtain ⟨n, hn, hiso, ε, hε, hidx⟩ :=
    Late.item1923_five hkf hyp hF hK hKM hL3 hpar hcK hC
  have h6 : ∀ P : Subgroup G, IsSylowOf 3 P (M ⊓ N) → A ≤ P →
      IsSylowOf 3 P M ∧ IsSylowOf 3 P N ∧ Sec18.omegaOneThree P = A ∧
      (∃ C : Subgroup G, (C : Set G) = Late.sectionCentralizer M K (CFSG.Open.pCoreOf 2 M) ∧
        P ⊓ C = A ⊓ L ∧ IsSylowOf 3 (A ⊓ L) C) := by
    intro P hP hAP
    obtain ⟨hPM, hPN, hΩ⟩ := Late.item1923_six_sylow hyp hF hε hidx hn hP hAP
    exact ⟨hPM, hPN, hΩ,
      Late.item1923_six_C hkf.kf5 hyp hF hK hcK hKM hL3 hone' hP hAP hPM hΩ⟩
  have hAMN : A ≤ M ⊓ N := le_inf hyp.le_M hyp.le_N
  obtain ⟨P₀, hP₀, hAP₀⟩ := Sec20.exists_isSylowOf_le hyp.isE27.isPGroup hAMN
  obtain ⟨hP₀M, -, hΩ₀, C₀, hC₀e, hP₀C₀, hC₀s⟩ := h6 P₀ hP₀ hAP₀
  have hBO2 := Late.item1923_six_BO2 hyp hET hF hK hKM hC hP₀ hAP₀ hC₀e hP₀C₀ hC₀s
  refine ⟨hone', h2, hm3, ⟨n, hn, hiso, ε, hε, hidx⟩, hcK, hAK, hKM, hKeq, hpar, hC, hBO2,
    ?_, Late.item1924_of_omega hyp hF hcK hAK hKM hP₀M hAP₀ hΩ₀⟩
  intro P hP hAP
  obtain ⟨hPM, hPN, hΩ, C, hCe, hPC, hCs⟩ := h6 P hP hAP
  have hBO2P := Late.item1923_six_BO2 hyp hET hF hK hKM hC hP hAP hCe hPC hCs
  obtain ⟨hPeq, hdisj, hcomm, hcyc, hΩK, hKC⟩ :=
    Late.item1923_six_abelian hkf.kf5 hkf.kfl3aut3 hyp hF hK hcK hAK hKM hL3 hBO2P hP hAP hPM
      hΩ hCe hPC hCs
  exact ⟨hPM, hPN, hΩ, hPeq, hdisj, hcomm, hcyc, hΩK, C, hCe, hPC, hCs, hKC⟩

end CFSG.RankThree.PartTwo
