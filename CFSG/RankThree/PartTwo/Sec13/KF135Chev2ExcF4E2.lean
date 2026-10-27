module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcF4
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcE2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcF4E2Sing
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixedEmbed
import CFSG.Quasithin.EmptyFaithful.R3c18G

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration CFSG.LieType.Ree
  CFSG.LieType.Chevalley


theorem false_of_kF135Hyp_F4_E2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)} {m : ℕ}
    {hv : (TauCeti.LieTypeIndex.reeF4 m).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) (h : KF135Hyp S p P x u V)
    (hn : p ∣ 2 * m + 1) (h4 : p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1)
    (h1 : ¬ p ∣ 2 ^ (2 * m + 1) - 1) : False := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by omega
  have hout : CFSG.RankThree.PartOne.OutStructure.OutPChain p S :=
    (CFSG.RankThree.PartOne.OutStructure.outPNice_twistedF4 hp
      (CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 m hv e)).toChain
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e₁⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  have f : S ≃* ↥(ReeTag.F4.reeGamma X m) := e.trans e₁
  obtain ⟨r, hr⟩ := hn
  have hq : 2 ^ (2 * m + 1) = (2 ^ r) ^ p := by rw [hr, ← pow_mul, mul_comm]
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, mul_zero] at hr
      omega
    · exact h0
  have hq₀2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
  have hpq₀ : ¬ p ∣ 2 ^ r := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  obtain ⟨d, hd, hpd⟩ : ∃ d, (d = 1 ∨ d = 2 ∨ d = 4) ∧
      p ∣ CFSG.RankThree.PartOne.K128.phiF4 d (2 ^ (2 * m + 1)) := by
    rw [pow_four_sub_one_eq hq1] at h4
    rcases (Nat.Prime.dvd_mul hp).mp h4 with h4 | h4
    · rcases (Nat.Prime.dvd_mul hp).mp h4 with h4 | h4
      · exact absurd h4 h1
      · exact ⟨2, Or.inr (Or.inl rfl), h4⟩
    · exact ⟨4, Or.inr (Or.inr rfl), h4⟩
  have hshS := CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv f
    (CFSG.RankThree.PartOne.K128.sylowShape_ree (K := X) (a := m) hX hd hp hp5 hpd)
  have he2 : 2 ≤ (CFSG.RankThree.PartOne.K128.phiF4 d (2 ^ (2 * m + 1))).factorization p := by
    rw [hq] at hpd ⊢
    have h0 := CFSG.RankThree.PartOne.K128.dvd_phiF4_of_dvd_pow hp (by omega) hd hpd
    rw [CFSG.RankThree.PartOne.K128.factorization_phiF4_pow hp hp5 hq₀2 hpq₀ hd h0]
    have := (hp.dvd_iff_one_le_factorization
      (CFSG.RankThree.PartOne.K128.phiF4_ne_zero hd hq₀2)).mp h0
    omega
  refine false_of_E2 h hout hshS he2 f fun φ₀ hφ₀ => ?_
  obtain ⟨g, β, hβ, hφ₀β⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeF4_stdDescent_odd hm1 hX hp
      φ₀ hφ₀
  obtain ⟨b, hchar, hkb, hbp, ι, hιinj, hιrange⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_fixedPoints_reeGammaFieldAut_odd hX hp hp2
      β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  refine ⟨(MulAut.conj g)⁻¹, ReeTag.F4.reeGammaFieldAut X m β, by rw [hφ₀β]; group,
    ↥(ReeTag.F4.reeGamma (fixSubfield β) b), inferInstance, ι, hιinj,
    fun t ht => (hιrange t).mpr ht, fun y => (hιrange (ι y)).mp (MonoidHom.mem_range.mpr ⟨y, rfl⟩),
    fun A hA hAc => exists_singular_reeF4_E2 hkb hp hp7 ?_ ?_ hA hAc⟩
  · have hq' : 2 ^ (2 * m + 1) = (2 ^ (2 * b + 1)) ^ p := by rw [← hbp, pow_mul]
    rw [hq'] at h4
    exact (CFSG.Quasithin.R3c18.dvd_pow_sub_one_iff_of_pow hp (by positivity) 4).mp h4
  · have hq' : 2 ^ (2 * m + 1) = ((2 ^ (2 * b + 1)) ^ p) ^ 1 := by rw [← hbp, pow_mul, pow_one]
    rw [hq'] at h1
    intro h1'
    apply h1
    rw [CFSG.Quasithin.R3c18.dvd_pow_sub_one_iff_of_pow hp (by positivity) 1, pow_one]
    exact h1'

theorem false_of_kF135Hyp_F4 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)} {m : ℕ}
    {hv : (TauCeti.LieTypeIndex.reeF4 m).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) (h : KF135Hyp S p P x u V) :
    False := by
  by_cases hres : p ∣ 2 * m + 1 ∧ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 ∧ ¬ p ∣ 2 ^ (2 * m + 1) - 1
  · exact false_of_kF135Hyp_F4_E2 e h hres.1 hres.2.1 hres.2.2
  · exact false_of_kF135Hyp_F4_of_not_E2 e h hres

theorem kF135At_fam7F4 : KF135At Fam7F4 := by
  intro S _ _ p P x u V hS h
  obtain ⟨m, hm, ⟨e⟩⟩ := hS
  exact (false_of_kF135Hyp_F4 e h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
