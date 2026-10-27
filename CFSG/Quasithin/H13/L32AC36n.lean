module

public import CFSG.Quasithin.H13.L32AC36a
public import CFSG.Quasithin.H13.L32AC36m
public import CFSG.Quasithin.H13.L32AC36i

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem lemma14_7_36_of
    (hIrr : MathieuSmallIrr22) (hSmall : HatM22SmallModules) (hA21 : AsA21SQTKSection)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h56 : AsB56) (hD310 : D310) (hD391 : D391)
    (hI4 : Insp4) (hFine : F918Fine4) (hdisj : SporadicFourListDisjoint)
    (h16 : CFSG.Quasithin.H.Mathieu.StmtH16_2_1M22)
    (h12H : CFSG.Quasithin.H.Mathieu.StmtH12_1HatM22) (h28 : Lemma14_7_28) (h29 : Thm14_7_29)
    (h30 : Lemma14_7_30) (h32 : Lemma14_7_32) (h36H : Lemma14_7_36_HatIrr) :
    Lemma14_7_36 := by
  intro G _ _ T L V H S K hK s hs
  obtain ⟨hq, hTK, S₀, hF⟩ := reduce_KL1T h30 h32 S hK
  have hK₀ : conjClosure K T = K := conjClosure_T_eq_self hTK
  rcases m22_or_hat_of_sporadic h30 h32 hD310 hD391 hI4 hFine hdisj S hK hs with hM | hHat
  ·
    have hKc : K ∈ cComp (K ⊔ (l1 T L V ⊔ T)) := hF.K_cComp
    have hl1H₀ : l1 T L V ≤ K ⊔ (l1 T L V ⊔ T) := le_sup_left.trans le_sup_right
    have hL3 := relIndex_l1 h1222 h1332 h1334 S.hyp
    have hQ' : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (cStarEquiv K) hq
    have hKeq := eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38 (sqtkGroup_of_setting S₀)
      hKc hQ' (cStarEquiv K).symm (a318Exclusion_m22 hM)
    have hl1K : l1 T L V ≤ K := by
      rw [hKeq]
      exact oTwoUpper_le_oPrimeResidualOf_three hL3 hl1H₀
    have hHeq : K ⊔ (l1 T L V ⊔ T) = conjClosure K T ⊔ T := by
      rw [hK₀, ← sup_assoc, sup_eq_left.mpr hl1K]
    exact false_of_m22_core hIrr hA21 h1222 h1332 h1334 h56 hD310 hD391 hI4 hFine h16 S₀ hF hK₀
      hHeq hl1K hM
  · exact false_of_hat_core hSmall hA21 h1222 h1332 h1334 h28 h29 h36H h12H S₀ hF hK₀ rfl hHat

end CFSG.Quasithin.H13.L32A.C
