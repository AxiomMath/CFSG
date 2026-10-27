module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

private lemma s16h_pow_two_modEq_seven {a b : ℕ} (hb : b ≤ a) (ha : a ≤ 3)
    (h : (2 : ℕ) ^ a ≡ (2 : ℕ) ^ b [MOD 7]) :
    b = a ∨ (b = 0 ∧ a = 3) := by
  interval_cases a <;> interval_cases b <;> simp_all [Nat.ModEq]

theorem s16h_fpf_of_orderOf_seven_card_le_eight
    {Z : Type} [CommGroup Z] [Finite Z] (hZ2 : ∀ z : Z, z ^ 2 = 1)
    (hZle : Nat.card Z ≤ 8) {f : MulAut Z} (hf : orderOf f = 7) :
    ∀ z : Z, f z = z → z = 1 := by
  classical
  set K : Subgroup Z := fixV (Subgroup.zpowers f) with hK
  have hZpow : Nat.card Z = 2 ^ rk Z :=
    CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Quasithin.isPGroup_two_of_sq_eq_one hZ2)
  have hKpow : Nat.card ↥K = 2 ^ rk ↥K :=
    CFSG.Quasithin.card_eq_two_pow hZ2 K
  have hrkZ : rk Z ≤ 3 := by
    have h' : 2 ^ rk Z ≤ 2 ^ 3 := by
      calc 2 ^ rk Z = Nat.card Z := hZpow.symm
        _ ≤ 8 := hZle
        _ = 2 ^ 3 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h'
  have hrkK : rk ↥K ≤ rk Z := by
    have h := CFSG.Quasithin.rk_mono (le_top : K ≤ ⊤)
    simpa [CFSG.Quasithin.rk_top] using h
  have hcardzp : Nat.card ↥(Subgroup.zpowers f) = 7 := by
    rw [Nat.card_zpowers, hf]
  have h7grp : IsPGroup 7 ↥(Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [hcardzp]; norm_num)
  have hcong : Nat.card Z ≡ Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) Z) [MOD 7] :=
    h7grp.card_modEq_card_fixedPoints Z
  have hfixcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) Z) = Nat.card ↥K := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro z
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      rw [hK, mem_fixV]
      intro g hg
      have h' := h ⟨g, hg⟩
      rwa [Subgroup.smul_def, MulAut.smul_def] at h'
    · intro h m
      rw [Subgroup.smul_def, MulAut.smul_def]
      exact mem_fixV.mp (hK ▸ h) m m.2
  have hcongK : Nat.card Z ≡ Nat.card ↥K [MOD 7] := by
    rwa [hfixcard] at hcong
  have hmod : (2 : ℕ) ^ rk Z ≡ (2 : ℕ) ^ rk ↥K [MOD 7] := by
    rw [← hZpow, ← hKpow]
    exact hcongK
  have hcase : rk ↥K = rk Z ∨ (rk ↥K = 0 ∧ rk Z = 3) :=
    s16h_pow_two_modEq_seven hrkK hrkZ hmod
  rcases hcase with heq | ⟨hK0, hZ3⟩
  · exfalso
    have hKtop : K = ⊤ :=
      CFSG.Quasithin.eq_of_le_of_rk_le hZ2 le_top
        (by rw [CFSG.Quasithin.rk_top]; exact heq.ge)
    have hf1 : f = 1 := by
      refine MulEquiv.ext fun z => ?_
      have hz : z ∈ K := hKtop ▸ Subgroup.mem_top z
      exact mem_fixV.mp hz f (Subgroup.mem_zpowers f)
    rw [hf1, orderOf_one] at hf
    exact absurd hf (by norm_num)
  · intro z hz
    have hzK : z ∈ K := by
      rw [hK]
      exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr hz
    have hKbot : K = ⊥ := (CFSG.Quasithin.rk_eq_zero_iff hZ2).mp hK0
    rw [hKbot] at hzK
    simpa using hzK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
