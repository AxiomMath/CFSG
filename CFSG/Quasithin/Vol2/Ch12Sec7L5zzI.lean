module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzH
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.L715 S127.Mod
open scoped IsMulCommutative

theorem ident12714R2_of
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1)
    (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) (h331 : Stmt3_3_1) (h316 : Theorem316Statement) :
    Ident12714R2 := by
  intro G _ _ T L V t hS z hz hz1 hTz hVz hU
  have s : Set714 G T L V t z := ⟨hS, hz, hz1, hTz, hVz⟩
  have h := hS.hyp
  have : IsMulCommutative ↥V := (S127.card_eq_of_1222 h1222 h).1
  have h712 := lemma12_7_12_of h1222 h129 h1241 h10 h11
  obtain ⟨hne, C, hC, hT, hbig, hcomm⟩ :=
    s.comm_le_V_of_ne h1222 h331 h712 h316 hU
  have hCV := centralizer_V_eq h1222 h1226 h129 h1241 h10 h11 hS hcomm
  have hM : Subgroup.normalizer (L : Set G) = L ⊔ T :=
    ((lemma12_7_6_of h1222 h1226 G T L V h (isHatA6Block_of_comm_le h1222 h hcomm)).2
      (h712 G T L V t hS)).2.2.2
  exact s.false_of_e8 h1222 hC hne hT hbig hCV hM

end CFSG.Quasithin.H13
