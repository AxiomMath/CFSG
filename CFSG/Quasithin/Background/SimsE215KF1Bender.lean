module

public import CFSG.Quasithin.Background.SimsE215KF1Defs
import CFSG.Quasithin.Background.SimsE215KF1Star
import CFSG.Quasithin.Vol2.E2SevenKG1Sz
import CFSG.Quasithin.Vol2.E2SevenKG1U3
import CFSG.Quasithin.Vol2.E2NineTIBender

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M

theorem pkgBenderSingleKF1 : PkgBenderSingleKF1 := by
  intro G _ _ H T M V K hS hC2 n hBen hB
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hTH : T ≤ H := hS.hyp.minParabolic.isSylow.1
  have hmpY := E2P.minParabolic_star hS.hyp.minParabolic
  have hJY : kerIn (E2.star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  have hY28 := hS.hyp.star (E2.sqtkGroup_top hS.sqtk)
  have hKT : E2.star M H K ⊔ E2.star M H T = ⊤ := by
    rw [← E2.star_sup hKH hTH, ← hS.eq_sup, E2P.star_top]
  have hTN : E2.star M H T ≤
      Subgroup.normalizer (E2.star M H K : Set (E2.StarQuot M H)) := by
    rintro _ ⟨⟨t, htH⟩, ht, rfl⟩
    exact E2.starMap_mem_normalizer htH (hC2.1 (Subgroup.mem_subgroupOf.mp ht))
  have hKN : (⊤ : Subgroup (E2.StarQuot M H)) ≤
      Subgroup.normalizer (E2.star M H K : Set (E2.StarQuot M H)) := by
    rw [← hKT]
    exact sup_le Subgroup.le_normalizer hTN
  have hKn : (E2.star M H K).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hKN)
  have hs : IsSimpleGroup ↥(E2.star M H K) := E2.isSimpleGroup_of_isBenderOf' hBen
  have hnab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a :=
    E2.nonabelian_of_isBenderOf hBen
  have hcent := E2.centralizer_eq_bot_of_simple hmpY hJY hKn hs hnab hKT
  have hMK := E2.star_inf_eq_of_isBorelIn hS.hyp.minParabolic hKN hB
  have hKG1 := E2.kgBenderInner_of_parts E2.kgBenderInnerL2_holds E2.kgBenderInnerSz_holds
    E2.kgBenderInnerU3_holds
  obtain ⟨hO2K, hcentral⟩ := hKG1 (E2.StarQuot M H) ⊤ (E2.star M H T) (E2.star M H M)
    (E2.star M H K) n hmpY hJY le_top hKN (by rw [top_inf_eq]; exact hcent) hKT hBen hMK
  exact starCentral_of_kg1 hY28 hKn ⟨hO2K, hcentral⟩

end CFSG.Quasithin.SimsE2.KF1
