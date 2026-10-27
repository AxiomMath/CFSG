module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeA
public import CFSG.Quasithin.Vol2.KGFactRankL52
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import Certificates.Certificate7145
public import Certificates.Certificate7146
public import Certificates.Certificate7147
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.KGRank

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint CFSG.Sporadic.SmallF2

theorem elemAbelianLt_m24 :
    ElemAbelianLt (NativeSporadic.Carrier .M24) (2 ^ 8) := by
  have h : ElemAbelianLt ↥NativeSporadic.M24 (2 ^ 8) := by
    refine elemAbelianLt_of_baseCertS (n := 24) (List.range 24)
      (fun b hb => List.mem_range.mp hb) base_of_faithful CFSG.Sporadic.Mathieu.m24a
      CFSG.Sporadic.Mathieu.m24b m24Prog m24_valid m24Qp 162 213 216 214 217 m24Enum.1
      m24Enum.2.1 m24Enum.2.2 10 239085 (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
      (by decide) ?_ Certificates.certificate7145
    rw [m24_tab_a, m24_tab_b]
    exact m24_cert
  exact h

theorem elemAbelianLt_he :
    ElemAbelianLt (NativeSporadic.Carrier .He) (2 ^ 8) := by
  have ha : tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ _ CFSG.Sporadic.He.rep_alpha]
    simp [heTa, CFSG.Sporadic.He.orb]
  have hb : tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ _ CFSG.Sporadic.He.rep_beta]
    simp [heTb, CFSG.Sporadic.He.orb]
  have hJ : ElemAbelianLt CFSG.Sporadic.He.J (2 ^ 8) := by
    refine elemAbelianLt_of_baseCertS (n := 8330) heB he_base_lt he_base_property
      CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg he_valid heQp 170 249 253 251 255 heEnum.1
      heEnum.2.1 heEnum.2.2 10 3935925 (by rw [CFSG.Sporadic.He.card_J]; norm_num) (by decide) ?_
      Certificates.certificate7146
    rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
    exact he_cert
  have h : ElemAbelianLt NativeSporadic.He (2 ^ 8) :=
    ElemAbelianLt.of_mulEquiv (X := NativeSporadic.He) (Y := ↥CFSG.Sporadic.He.J)
      CFSG.Sporadic.He.heEquivJ hJ
  exact h

open CFSG.Sporadic.Ru.Native (ruData) in
theorem elemAbelianLt_ru :
    ElemAbelianLt (NativeSporadic.Carrier .Ru) (2 ^ 8) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have ha : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
    simp [ruTa]
  have hb : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
    simp [ruTb]
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hJ : ElemAbelianLt (J ruData) (2 ^ 8) := by
    refine elemAbelianLt_of_baseCertS (n := ruData.n) ruB (base_lt hF) (base_property hF)
      (a ruData) (b ruData) ruProg ru_valid ruQp 154 187 191 189 193 ruEnum.1 ruEnum.2.1
      ruEnum.2.2 14 8906625 (by rw [hcard0]; norm_num) (by decide) ?_
      Certificates.certificate7147
    rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
    exact ru_cert
  have h : ElemAbelianLt NativeSporadic.Ru (2 ^ 8) :=
    ElemAbelianLt.of_mulEquiv (X := NativeSporadic.Ru) (Y := ↥(J ruData))
      (seedEquiv hF.toBaseFacts) hJ
  exact h

theorem heInspRankEight_holds :
    HeInspRankEight :=
  ⟨fun _ _ _ hX => elemAbelianLt_psl52 hX, elemAbelianLt_m24, elemAbelianLt_he, elemAbelianLt_ru⟩

end CFSG.Quasithin.H13.KGRank
