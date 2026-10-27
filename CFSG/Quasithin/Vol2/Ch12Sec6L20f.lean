module

public import CFSG.Quasithin.Vol2.Ch12Sec6L1d
public import CFSG.Quasithin.Vol2.KGFactA8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem lemma12_6_19_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h1229 : Stmt12_2_9) (h3228 : Stmt3_2_2_eight) (h51 : AsB51)
    (h1262 : Theorem12_6_2) (hNF : NoFuse1261926) (hA8 : FactA8SolvNormPartition) :
    Lemma12_6_19 := by
  intro G _ _ T L V _ F hH
  refine ⟨?_, fun hZ v hv => S126L19d.part2 h331 h1222 h1228 h3228 hA8 h1229 F hH
    (S126L1d.part6 h51 h1222 hH) hZ v hv⟩
  by_cases hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · exact S126L19.fusion_of_bot h1262 h1222 F hH hZ
  · exact S126L19d.fusion_of_ne_bot h331 h1222 h1228 h3228 hA8 h1262 hNF F hH hZ

theorem lemma12_6_19_of_cert (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) (h3228 : Stmt3_2_2_eight)
    (h51 : AsB51) (h1262 : Theorem12_6_2) (hNF : NoFuse1261926) : Lemma12_6_19 :=
  lemma12_6_19_of h331 h1222 h1228 h1229 h3228 h51 h1262 hNF
    KGA8.factA8SolvNormPartition_holds

end CFSG.Quasithin.H13
