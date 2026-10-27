module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldSubgroup
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLift
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KF4.EvenDescent

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TwE6RootKill


theorem exists_fixed_two_of_entrywise (hRK : RootKill) (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (δ : K ≃+* K)
    (hδ : orderOf δ = p) {X : Subgroup (ModGL TwistTag.E6.tag K)}
    (hXI : X ≤ twistedE6InndiagGL K σ) (hX : IsElemAbelian p X)
    (hr : p ^ (if p = 3 then 4 else 5) ≤ Nat.card X)
    (hXδ : ∀ x ∈ X, Units.map (entrywiseHom δ.toRingHom) x = x) (hU : TwNormTwo K σ X) :
    ∃ u ∈ twistedE6RootGroup K σ, u ≠ 1 ∧ (∃ k : ℕ, u ^ 2 ^ k = 1) ∧
      Units.map (entrywiseHom δ.toRingHom) u = u ∧ ∀ x ∈ X, Commute u x := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hpq
    omega
  have hpo : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hδo : Odd (orderOf δ) := hδ ▸ hpo
  obtain ⟨hdn, hK₀⟩ := fixSubfield_card_of_odd hn hK δ hδo
  obtain ⟨hmap, hX₀I⟩ := exists_descent_of_entrywise hn hK hσ δ hδo hXI hXδ
  rw [hδ] at hdn hK₀
  obtain ⟨m, rfl⟩ : ∃ m, n = m * p := ⟨n / p, (Nat.div_mul_cancel hdn).symm⟩
  rw [Nat.mul_div_cancel m hp.pos] at hK₀
  have hm : 1 ≤ m := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  set ι := (fixSubfield δ).subtype with hι
  have hσ₀ := fixSubfieldRestrict_eq_pow hK₀ hpo hσ
  haveI : CharP K 2 := charP_two_of_card_sq hK
  haveI : CharP (fixSubfield δ) 2 := charP_two_of_card_sq hK₀
  have hpq₀ : p ∣ 2 ^ m + 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have h := (ZMod.natCast_eq_zero_iff (2 ^ (m * p) + 1) p).mpr hpq
    push_cast at h
    rw [pow_mul, ZMod.pow_card] at h
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h
  have hX₀ := IsElemAbelian.comap hX (baseChangeGL_injective ι)
  have hcard : Nat.card (X.comap (baseChangeGL ι)) = Nat.card X := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective (baseChangeGL_injective ι)).symm
  generalize X.comap (baseChangeGL ι) = X₀ at hmap hX₀I hX₀ hcard
  subst hmap
  obtain ⟨D₀, hc₀⟩ := exists_twLangData_fixSubfield h5 h3 h34 ι σ hm hK₀ hK hσ₀ hσ hp hpq₀ hX₀I
    hX₀ (by rw [hcard]; exact hr) hU
  obtain ⟨D, -, hkill⟩ := exists_lift_twLangData ι σ hm hpo hK hσ D₀ hc₀ hXI
  obtain ⟨α, hα, hαD⟩ := hRK K σ (2 ^ (m * p)) hK hσ (ringChar.eq K 2) p hp hpq _ hXI hX hr hU D
  obtain ⟨u₀, hu₀, hu₁, ⟨k, hk⟩, hcomm⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof (fixSubfield δ)
      (fixSubfieldRestrict σ δ) (2 ^ m)
      (by rw [ringChar.eq (fixSubfield δ) 2]; norm_num) hσ₀ hK₀ X₀ D₀ α hα (hkill α hαD)
  rw [ringChar.eq (fixSubfield δ) 2] at hk
  refine ⟨baseChangeGL ι u₀, baseChangeGL_mem_twistedE6RootGroup σ δ hu₀,
    fun h => hu₁ (baseChangeGL_injective ι (h.trans (map_one _).symm)), ⟨k, ?_⟩,
    CFSG.LieType.AlgebraicGroups.entrywise_baseChangeGL_fixSubfield δ u₀, ?_⟩
  · rw [← map_pow, hk, map_one]
  · rintro _ ⟨x₀, hx₀, rfl⟩
    exact (hcomm x₀ hx₀).map _

end CFSG.StandardType.TwE6FieldCore

end
