module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvPerm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvCore

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint.NativeSporadic

theorem zpUniq_j2 :
    ZPUniq (Carrier .J2) := by
  have hJ : ZPUniq CFSG.Sporadic.J2.J := by
    obtain ⟨Q, z, hQ2, hQi, hQc⟩ := sylow_center_of_baseCertS (n := 315) (List.range 315)
      (fun b hb => List.mem_range.mp hb) base_of_faithful (CFSG.Sporadic.J2.a : CFSG.Sporadic.J2.J)
      (CFSG.Sporadic.J2.b : CFSG.Sporadic.J2.J) j2Prog j2_valid j2Qp
      143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 4725
      (by rw [CFSG.Sporadic.J2.card_J]; norm_num) (by decide)
      (by rw [j2_tab_a, j2_tab_b]; exact j2_cert)
    exact zpUniq_of_central_subset (center_eq_bot_of_simple CFSG.Sporadic.J2.isSimpleGroup_J
      CFSG.Sporadic.J2.card_J (by norm_num) (by norm_num)) Q hQ2 hQi z hQc
  have h : ZPUniq CFSG.Blueprint.NativeSporadic.J2 := by
    refine ZPUniq.of_mulEquiv (Γ := CFSG.Blueprint.NativeSporadic.J2)
      (Γ' := ↥CFSG.Sporadic.J2.J) ?_ hJ
    exact CFSG.Sporadic.J2.nativeEquiv
  exact h

theorem zpUniq_he :
    ZPUniq (Carrier .He) := by
  have hJ : ZPUniq CFSG.Sporadic.He.J := by
    have ha : tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J) = heTa.toList := by
      rw [tab_eq_of_rep (n := 8330) _ (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)
        CFSG.Sporadic.He.rep_alpha]
      simp [heTa, CFSG.Sporadic.He.orb]
    have hb : tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J) = heTb.toList := by
      rw [tab_eq_of_rep (n := 8330) _ (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)
        CFSG.Sporadic.He.rep_beta]
      simp [heTb, CFSG.Sporadic.He.orb]
    obtain ⟨Q, z, hQ2, hQi, hQc⟩ := sylow_center_of_baseCertS (n := 8330) heB he_base_lt
      he_base_property (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)
      (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J) heProg he_valid heQp
      170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10 3935925
      (by rw [CFSG.Sporadic.He.card_J]; norm_num) (by decide)
      (by rw [ha, hb, Array.toArray_toList, Array.toArray_toList]; exact he_cert)
    exact zpUniq_of_central_subset (center_eq_bot_of_simple CFSG.Sporadic.He.isSimpleGroup_J
      CFSG.Sporadic.He.card_J (by norm_num) (by norm_num)) Q hQ2 hQi z hQc
  have h : ZPUniq CFSG.Blueprint.NativeSporadic.He := by
    refine ZPUniq.of_mulEquiv (Γ := CFSG.Blueprint.NativeSporadic.He)
      (Γ' := ↥CFSG.Sporadic.He.J) ?_ hJ
    exact CFSG.Sporadic.He.heEquivJ
  exact h

end CFSG.Quasithin.ZPInv
