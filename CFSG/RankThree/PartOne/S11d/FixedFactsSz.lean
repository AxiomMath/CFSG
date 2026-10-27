module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSuzukiMain
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.RankThree.PartOne.S11c.Sec66Degen
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

theorem tagFixedFacts_Sz : TagFixedFacts .twistedB2 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hadm : StatedLieAdmissible .twistedB2 n 2 f₀ := by
    rcases admissible_of_fixModel hX₀ with h | ⟨h, -, -⟩
    · exact h
    · exact absurd h (by decide)
  have hf₀3 : 3 ≤ f₀ := hadm.2.2.2.2.2
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hn0, -, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := lieModel_twistedB2_iff.mp hM
  subst hn0
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have hfinG : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  obtain ⟨σ, h, b, k, _, _, hσord, hbp, hkcard, hconj, ⟨efix⟩⟩ :=
    KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 (MulAut.congr e α) hα'ord hα'inn
  have hbf : 2 * b + 1 = f₀ := by
    have h1 : (2 * b + 1) * p = f₀ * p := by rw [hbp, ← hfa, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hb1 : 1 ≤ b := by omega
  obtain ⟨-, hnt, hsimple⟩ := suzuki_simple hb1 hkcard
  have hnab : ∃ x y : suzukiGroup b k, x * y ≠ y * x :=
    exists_noncomm_of_perfect (suzuki_perfect hb1 hkcard).1
  have hX : LieModel (suzukiGroup b k) .twistedB2 0 2 f₀ := by
    rw [← hbf]
    exact lieModel_twistedB2_iff.mpr ⟨rfl, rfl, b, hb1, k, inferInstance, inferInstance, rfl,
      hkcard, ⟨MulEquiv.refl _⟩⟩
  have hpa : p ≠ 2 * a + 1 := by
    intro hpa
    have h1 : p * f₀ = p * 1 := by rw [hfa, hpa, mul_one]
    have := Nat.eq_of_mul_eq_mul_left hp.pos h1
    omega
  have hNL := SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedSuzuki a ha K hK p hp hp2
    hpa σ hσord
  set φ : T ≃* suzukiGroup a K := e.trans (MulAut.conj h) with hφ
  have hφα : MulAut.congr φ α = szFieldAut a K σ := by
    have : MulAut.congr φ α = MulAut.conj h * MulAut.congr e α * (MulAut.conj h)⁻¹ := rfl
    rw [this, hconj]
  have : IsSimpleGroup (suzukiGroup b k) := hsimple
  exact fixedFacts_of_simple φ α hM hf₀
    ((MulEquiv.subgroupCongr (by rw [hφα]; rfl)).trans efix) hnab (by rw [hφα]; exact hNL)
    (Or.inl hX)

theorem tagFixedFacts_twistedG2 : TagFixedFacts .twistedG2 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM
  exact absurd (statedLieAdmissible_of_lieModel hM).2.2.2.1 (by norm_num)

theorem tagFixedFacts_Tits : TagFixedFacts .Tits := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM
  have h := (statedLieAdmissible_of_lieModel hM).2.2.2.2
  have : p ≤ p * f₀ := Nat.le_mul_of_pos_right p hf₀
  omega

end CFSG.RankThree.PartOne.FieldFix
