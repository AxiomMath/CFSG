module

public import CFSG.Quasithin.Vol2.Ch11SecB36Fin
public import CFSG.Quasithin.Vol2.Ch11SecB36Amal
public import CFSG.Quasithin.Vol2.Ch11SecB36Claim
public import CFSG.Quasithin.Vol2.Ch11SecB36Flag
public import CFSG.Quasithin.Vol2.Ch11SecB36R

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

theorem stmt11_3_6_of (hFV : FactsVM) (hFL : FactsL2) (hPT : FactPointTrans)
    (hG2o : FactG2DerivedOrder) (hNF : NatFacts) (hG16 : ASInputs.AS_G_1_6)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4) (h1121 : Stmt11_2_1)
    (h1122 : Stmt11_2_2) (h1123 : Stmt11_2_3) (h1133 : Stmt11_3_3) (h1135 : Stmt11_3_5) :
    Stmt11_3_6 := by
  intro G _ _ T L I n V₁ H hyp hV₁ h31 hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases nParam_cases36 hNF h1102 h1121 h1122 h1133 hyp hV₁ h31 hnot with
    hk | ⟨-, hk3, hVM2, -, hLJ, hk2n⟩
  · exact hk
  exfalso
  obtain ⟨-, V₂, -, -, hV₂, -⟩ := exists_isVi hNF h1102 hyp
  have hfl := flag36_of hNF hG2o h331 h1102 h1103 h1104 hyp hV₁ hV₂ hk3 hVM2 hLJ
  have hE61 := hypE61_VM h331 h1102 h1103 hyp
  have hn := hfl.two_le
  have hmP : E3.mParam (autI hfl.elemW (Subgroup.normalizer (L : Set G))) = 2 * n := by
    rw [← autI_top_eq_VM h331 h1103 hyp hfl.elemW]
    exact hFV.param G L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n hfl
  have h63' := h63 G T _ (VM T L I) hfl.elemW hE61 (by rw [hmP]; omega)
  have hs : E3.sParam hfl.elemW = 2 * n := by rw [h63'.2, hmP]
  have hr : ((2 * n : ℕ) : ℕ∞) ≤ E3.rParam (VM T L I) := by
    rw [← hmP]
    exact h63'.1
  have hCV₁ := h31.sl3 hk3
  have hN1 := (h1123 G T L I n V₁ hyp hV₁).2 hCV₁
  have hNV₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    fun x hx => normalizer_inf_le h1103 hyp hV₁ ⟨hN1 hx, hx⟩
  have hV3 := relIndex_fsuV_of_SL3 hG2o h1102 hyp hk3
  have hW0 := wClos_VM_not_le h331 h1102 h1103 hyp h31.hstar
    fun g hgT hgc hgN => claim36 hFV hPT hyp hfl hs hV3 hNV₁ hgT hgc hgN
  have hsk := sParam_le_nParam_gen hyp h31 hfl.elemW hW0
  rw [hs] at hsk
  obtain ⟨k, hk', K, -, -, ⟨F, hFf, hFfin, hFc, ⟨eK⟩⟩, hK2⟩ :=
    h1135 G T L I n V₁ H hyp hV₁ h31 hnot
  have hk2 : k = 2 * n := by
    rw [hk'] at hsk hk2n
    have h1 : k ≤ 2 * n := by exact_mod_cast hk2n
    have h2 : 2 * n ≤ k := by exact_mod_cast hsk
    omega
  subst hk2
  have hKO := hK2 fun _ => rfl
  have hrlt := lt_rParam_VM hFV h612 h331 h1102 h1103 hyp hfl hr hV3 hCV₁
  exact false_of_VH hFV hFL hG16 h331 hyp h31 hfl hs hrlt hW0 hKO hFc eK

end CFSG.Quasithin.Vol2.Ch11.SecB
