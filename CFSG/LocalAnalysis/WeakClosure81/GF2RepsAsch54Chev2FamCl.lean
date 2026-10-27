module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.LieType.Universal.Unitary.RootGroupCardRankTwo
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.Timmesfeld.LieEmbed.UnitaryForms

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.LieEmbed CFSG.LieType.BorelTits

variable {X : Type} [Group X] {n f : ℕ}

theorem hasBQRank_psl (hm : CFSG.Models.LieModel X .PSL n 2 f) : HasBQRank X (n - 1) := by
  obtain ⟨⟨-, -, hn, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm⟩
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _,
    borelQuotient_sl ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (m + 1) F).trans e.symm), rfl⟩

theorem hasBQRank_psu (hm : CFSG.Models.LieModel X .PSU n 2 f) : HasBQRank X (n / 2) := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _,
    borelQuotient_su hcard (by omega) ζ hζ e, rfl⟩

theorem hasBQRank_psp (hm : CFSG.Models.LieModel X .PSp n 2 f) : HasBQRank X n := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_sp e, rfl⟩

theorem hasBQRank_pomegaPlus (hm : CFSG.Models.LieModel X .POmegaPlus n 2 f) :
    HasBQRank X n := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup
      (CFSG.LieType.Universal.Spin.quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_spinPlus hn3 e, rfl⟩

theorem hasBQRank_pomegaMinus
    (hm : CFSG.Models.LieModel X .POmegaMinus n 2 f) :
    HasBQRank X (n - 1) := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _,
    borelQuotient_spinMinus hirr (by omega) e, rfl⟩

theorem hasBQUneven_psu (hn : n = 4 ∨ n = 5) (hm : CFSG.Models.LieModel X .PSU n 2 f) :
    HasBQUneven X := by
  obtain ⟨⟨-, hf, hn3, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide)
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm)
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  have hBQ := borelQuotient_su hcard (by omega) ζ hζ e
  rcases hn with rfl | rfl
  · refine ⟨SU (unitaryInvolution F 2 f) 4, inferInstance, inferInstance,
      CFSG.LieType.Universal.Unitary.rootDatum hcard 4, _, _, _, _, hBQ,
      ⟨(0 : Fin 2), (1 : Fin 2), card_rootGroup_four_zero_ne_one hcard⟩⟩
  · refine ⟨SU (unitaryInvolution F 2 f) 5, inferInstance, inferInstance,
      CFSG.LieType.Universal.Unitary.rootDatum hcard 5, _, _, _, _, hBQ,
      ⟨(0 : Fin 2), (1 : Fin 2), card_rootGroup_five_zero_ne_one hcard⟩⟩

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
