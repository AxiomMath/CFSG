module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Conj

public section

namespace CFSG.StandardType.F4TwoNonToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.TableBF4TwoTB CFSG.StandardType.TableBExcTwoFusion CFSG.Assembly
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section Frame


theorem exists_conj_frame_of_card_F4 (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) :
    ∃ c : adjointGroup .F4 K, E = (tE K).range.map (MulAut.conj c).toMonoidHom := by
  have h3 : 3 ∣ Nat.card (FiniteField.Extension K 2 2) - 1 := three_dvd_natCard_ext_sub_one hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := FiniteField.Extension K 2 2)
    (p := 3) h3
  haveI : Finite (adjointGroup .F4 (FiniteField.Extension K 2 2)) := generated_group_finite .F4 _
  haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  refine X1F4Conj.exists_conj_eq_of_descent (TableBExcTwo.adjointMap_injective _)
    (X := TableBF4.weylX (FiniteField.Extension K 2 2)) (fun m hm => ?_)
    (TableBF4.not_three_dvd_index_weylX h3) (X1F4Conj.map_conj_range_tE_eq_torusPow hK hωo)
    (fun E' hE' hEX hc => ?_) hE hcard
  · exact X1F4Conj.exists_adjointMap_eq_of_frob_F4
      (X1F4Conj.adjointMap_frob_conj_langEltF4 hK hωo (TableBF4.mem_weylX.mp hm).1)
  · rw [← X1F4Conj.torusPow_F4_eq]
    exact TableBF4.eq_torusPow_of_le_weylX h3 hE' hEX hc

end Frame

end CFSG.StandardType.F4TwoNonToral
