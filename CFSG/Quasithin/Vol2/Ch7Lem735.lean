module

public import CFSG.Quasithin.Vol2.Ch7Sp4PairA6
public import CFSG.Quasithin.Vol2.Ch7E61
public import Certificates.Certificate7067
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped IsMulCommutative

theorem stmt7_3_5_of_E63
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hmod : StmtFSUModule)
    (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h3228 : Stmt3_2_2_eight)
    (h63 : ASInputs.AS_E_6_3) (h734 : Stmt7_3_4) : Stmt7_3_5 := by
  intro G _ _ T L I hyp h731 hc hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h711n G T L I hyp hc
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl hrow)))))))))))))
  have hTI := isTISetUnder_of_le_normalizer h325 hyp.fsu hTL
  obtain ⟨-, hwn, -, hn'⟩ := h734 G T L I hyp h731 hV
  obtain ⟨-, -, -, -, -, hSp, hA6, -, -⟩ := hn' hc
  obtain ⟨htw, hrow'⟩ := hrow
  have htab := stmt7_2_1_Sp4Pair G T L I hyp hV hN hNM hc htw
  have key : ∀ k : ℕ, nPrime (autI hV ⊤) = k → 2 < mParam (autI hV ⊤) →
      aParam (autI hV ⊤) < mParam (autI hV ⊤) →
      mParam (autI hV ⊤) - aParam (autI hV ⊤) ≤ k := by
    intro k hk hm2 ham
    have hm := mParam_le_rParam_of_ti h37 h38 h39 hmod h3228 h63 hyp hTI hV hm2
    have hw := lemma_7_3_3 hyp hV hN hm ham
    have h1 : ((mParam (autI hV ⊤) - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
      rw [← hk]
      exact hw.trans hwn
    exact_mod_cast h1
  rcases hrow' with ⟨n, hn2, hsp⟩ | halt
  · obtain ⟨ha, hm3⟩ := htab.1 n hn2 hsp
    have := key n (hSp n hn2 htw hsp) (by omega) (by omega)
    omega
  · obtain ⟨ha, hm3⟩ := htab.2 halt
    have := key 1 (hA6 htw halt) (by omega) (by omega)
    omega

end CFSG.Quasithin.H13
