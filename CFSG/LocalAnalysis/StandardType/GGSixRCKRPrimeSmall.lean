module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSUPos
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.Open (StatedLieTag)

theorem rckRP_admissible_PSL_of_quasisimple_range
    {G : Type} [Group G] {k f : ℕ} (hf : 1 ≤ f) (ρ : (ggU .PSL (k + 1) f).K →* G)
    (hq : CFSG.Assembly.IsQuasisimple ↥ρ.range) :
    CFSG.Open.StatedLieAdmissible .PSL (k + 1) 2 f := by
  have h := CFSG.StandardType.isQuasisimple_specialLinear_of_quasisimple_range
    (ι := Fin (k + 1)) (Q := GaloisField 2 f) ρ hq
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  unfold CFSG.Open.StatedLieAdmissible
  refine ⟨Nat.prime_two, hf, ?_, ?_, ?_⟩
  · simpa using h.1
  · intro heq
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    rcases h.2.1 with hh | hh
    · exact hh (by simpa using h1)
    · exact hh (by rw [hcard]; exact h2)
  · intro heq
    have h3 : 2 ^ f = 3 := (Prod.mk.inj heq).2
    have hd : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega : f ≠ 0)
    rw [h3] at hd
    norm_num at hd

theorem rckRP_admissible_PSU_of_quasisimple_range
    {G : Type} [Group G] {r g : ℕ} (hg : 1 ≤ g) (ρ : (ggU .PSU r g).K →* G)
    (hq : CFSG.Assembly.IsQuasisimple ↥ρ.range) :
    CFSG.Open.StatedLieAdmissible .PSU r 2 g ∨ (r = 2 ∧ 2 ≤ g) := by
  have hns : ¬ Group.IsSolvable ↥ρ.range := by
    intro hs
    haveI : Group.IsSolvable ↥ρ.range := hs
    exact CFSG.StandardType.LinSemisimple.false_of_isQuasisimple_of_le_isSolvable hq le_rfl
  have hdim := CFSG.StandardType.LieKnownR2.PSU.jDim_selfDual_psu ρ hns
  by_cases hr : r = 2
  · right
    exact ⟨hr, hdim.2 (by omega)⟩
  · left
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨Nat.prime_two, hg, by omega, ?_⟩
    intro heq
    obtain ⟨hr3, h2g⟩ := Prod.mk.inj heq
    have hg1 : g = 1 := by
      have hpow : 2 ^ g = 2 ^ 1 := by rw [h2g, pow_one]
      exact Nat.pow_right_injective (le_refl 2) hpow
    have hg2 := hdim.2 (by omega)
    omega

theorem rckRP_nonempty_mulEquiv_PSL_two_PSp_one
    {f : ℕ} (hf : 1 ≤ f) : Nonempty ((ggU .PSL 2 f).K ≃* (ggU .PSp 1 f).K) := by
  change Nonempty (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) ≃*
    ↥(CFSG.Open.StatedSp 1 (GaloisField 2 f)))
  exact ⟨CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
    (K := GaloisField 2 f)⟩

theorem rckRP_nonempty_mulEquiv_PSL_two_PSU_two
    {g : ℕ} (hg : 1 ≤ g) : Nonempty ((ggU .PSL 2 g).K ≃* (ggU .PSU 2 g).K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases g with _ | g
  · omega
  let F := GaloisField 2 (2 * (g + 1))
  have hF : Nat.card F = (2 ^ (g + 1)) ^ 2 := by
    dsimp only [F]
    rw [GaloisField.card 2 (2 * (g + 1)) (by omega), ← pow_mul, mul_comm]
  obtain ⟨⟨eSU⟩, hcard⟩ :=
    CFSG.StandardType.RCSTSU.exists_equiv_sl2 (F := F) (f := g + 1) hF
  let φ : GaloisField 2 (g + 1) ≃+*
      CFSG.LieType.Steinberg.fixedSubfield F 2 (g + 1) :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField
      (CFSG.LieType.Steinberg.fixedSubfield F 2 (g + 1)) 2 (g + 1) (by omega) hcard).symm
  change Nonempty (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (g + 1)) ≃*
    Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) 2)
  exact ⟨(CFSG.ClassicalModels.specialLinearFieldEquiv φ (Fin 2)).trans eSU⟩

end CFSG.StandardType.RCKRP
