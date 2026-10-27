module

public import CFSG.Quasithin.EmptyFaithful.S1421QL12Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Quot
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Res
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Coincide

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem lemma14212Three_of_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h128Four : Lemma128Four)
    (hL34 : Q9.L34Maximal) :
    Lemma14212Three := by
  intro G _ _ T M H K1 st _ hK _ hs3
  by_cases hO : pCoreOf 2 M ≤ S1421.sOf T K1
  · exact Or.inl hO
  right
  obtain ⟨t, htQ, -, htK1⟩ := QA12.exists_mem_pCore_not_mem_normalizer st hO
  obtain ⟨hKc, hKN⟩ := QA12.cComp_mcOf_of_inputs h37 h38 h39 h128Four hL34 st hK hs3
  have hMc3 : CFSG.Open.pRank 3 (mcOf T) ≤ 2 :=
    pRank_le_two_of_isTwoLocal st.hyp.qtke st.hyp.mc_max.1 Nat.prime_three (by norm_num)
  obtain ⟨B₀, hB₀⟩ := S1421.exists_isHallOdd_borel st
  have hstep := fun {B : Subgroup G} (hB : S1421.IsHallOdd B (M ⊓ oTwoUpper H)) =>
    QA12.lie_step QA12.lieSylowLePerfectCore QA12.lieTorusCoincide st hK hs3 htQ htK1 hB
  obtain ⟨hpsl, -, -⟩ := hstep hB₀
  exact ⟨hKc, hpsl, hs3.diag, fun B hB => (hstep hB).2,
    QA12.eq_residual_of_psl34 hpsl hKc hKN hMc3⟩

end CFSG.Quasithin
