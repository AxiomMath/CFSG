module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitBridge
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSetup
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelRootSmall
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelRootSym
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelRootAlt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

theorem shape86DeltaT'_of_shape86Delta (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (g1 : W3Lem85TwoGap1) (g4 : W3Lem85TwoGap4) (g6 : W3Lem85TwoGap6) (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) (hδ : Shape86Delta V H T) : Shape86DeltaT' V H T := by
  obtain ⟨m, n, hm, hn, hr, hsh⟩ := hδ
  let X : Type := ↥(kGenIn V H) ⧸ CFSG.pCore 2 ↥(kGenIn V H)
  let φ : ↥(kGenIn V H) →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥(kGenIn V H))
  have hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ := isBarMap_mk_pCore (kGenIn V H)
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨φ', hφ', hS⟩ := exists_ambient_barMap h hKT hφ
  have hSit : BarSituation X (barSub (kGenIn V H) φ V) := by
    rw [← hS]
    exact barSituation_of_hyp711 (AmbientH.hyp711 h hKT) hφ'
  have hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2 := by
    rw [h.card_barSub_eq_two_pow_rankBarV hKT hφ, hr, pow_one]
  have hc : CentralInSylow X (barSub (kGenIn V H) φ V) := by
    rw [← hS]
    exact centralInSylow_of_hyp83 h hKT hφ' (by rw [hS]; exact hS2)
  have hY : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n := by
    rcases hsh with hSp | hPU
    · obtain ⟨Y, _, ⟨k, hk, F, hF, hFin, hcard, ⟨e'⟩⟩, ⟨e⟩⟩ :=
        nonempty_mulEquiv_of_kBarCenterShape h hKT hSp hφ
      exact Or.inl ⟨k, hk, F, hF, hFin, hcard, ⟨e.trans e'⟩⟩
    · obtain ⟨Y, _, hPY, ⟨e⟩⟩ := nonempty_mulEquiv_of_kBarCenterShape h hKT hPU hφ
      exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hPY)
  have hAlt := ((h711 H) _ _ _ (AmbientH.hyp711 h hKT)).2 X φ' hφ'
  rw [hS] at hAlt
  rcases hAlt with ⟨⟨n', h1⟩, -⟩ | h2 | ⟨-, h3⟩ | ⟨-, m', n', h4⟩ | ⟨-, n', h5⟩ |
    ⟨-, h6⟩
  · exact (borel86_ra_false_of_rootGroupShape hSit g1 hS2 hm hn hY h1).elim
  · exact absurd (borel86_ra_four_le_card_of_linearShape h2) (by omega)
  · exact absurd h3.2.1 (by omega)
  · obtain ⟨hn', hT⟩ := borel86_ra_of_alt4 hSit hc g4 hS2 hm hn hY h4
    exact ⟨m', n', hn', hr, X, inferInstance, φ, hφ, hT⟩
  · have hodd := borel86_rs_odd_card_of_isSymGp hSit.pCore_eq_bot
      (borel86_rs_isPerfect hm hn hY) h5
    have hdvd : 2 ∣ Nat.card X := hS2 ▸ Subgroup.card_subgroup_dvd_card _
    exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hodd)
  · exact (g6 X _ hSit hS2 h6 hc).elim

end CFSG.LocalAnalysis.WeakClosure81

end
