module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item134Holds
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms

theorem nonempty_outer_j2 :
    Nonempty (Outer CFSG.Blueprint.NativeSporadic.J2 ≃* Multiplicative (ZMod 2)) :=
  CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2

theorem center_eq_bot_of_j2' (hspor : SporadicModels131) {X : Type} [Group X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) : Subgroup.center X = ⊥ := by
  obtain ⟨-, -, ⟨-, hJ2z⟩⟩ := hspor
  exact Sec13.center_eq_bot_of_mulEquiv e hJ2z

theorem pow_three_eq_one_of_pow_nine_of_j2
    (h415 : Sec4.Item4_15) (hspor : SporadicModels131)
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    {σ : MulAut X} (hσ : σ ^ 9 = 1) : σ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ := nonempty_outer_j2
  set φ : Outer X ≃* Multiplicative (ZMod 2) := (equivalence e).trans f
  have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 : φ (σ : Outer X) = 1 := by
    have h9 : φ (σ : Outer X) ^ 9 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one, map_one]
    have e9 : φ (σ : Outer X) ^ 9 = (φ (σ : Outer X) ^ 2) ^ 4 * φ (σ : Outer X) := by
      rw [← pow_mul, ← pow_succ]
    rw [e9, hsq, one_pow, one_mul] at h9
    exact h9
  have h2 : (σ : Outer X) = 1 := φ.injective (h1.trans (map_one φ).symm)
  obtain ⟨κ, rfl⟩ : σ ∈ inner X := (QuotientGroup.eq_one_iff σ).mp h2
  have hZ : ∀ w : X, MulAut.conj w = 1 → w = 1 := by
    intro w hw
    have hwZ : w ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => by
      have := congrArg (fun g : MulAut X => g y) hw
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * w = w * y * w⁻¹ * w := by rw [this]
        _ = w * y := by group
    have hc : Subgroup.center X = ⊥ := center_eq_bot_of_j2' hspor e
    rw [hc] at hwZ
    exact (Subgroup.mem_bot).mp hwZ
  have hκ9 : κ ^ 9 = 1 := hZ _ (by rw [map_pow]; exact hσ)
  have hκp : IsPGroup 3 (Subgroup.zpowers κ) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((3 ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, hκ9, one_zpow]
  obtain ⟨P, hP⟩ := hκp.exists_le_sylow
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X ⟨e⟩ P _ rfl _ rfl
  have hexp : Monoid.exponent (P : Subgroup X) = 3 := hHeis.2.2
  have hκ3 : κ ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨κ, hP (Subgroup.mem_zpowers κ)⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  rw [← map_pow, hκ3, map_one]

variable {G : Type} [Group G] [Finite G]

theorem not_cube_of_j2
    (h45 : Sec4.Item4_5) (h415 : Sec4.Item4_15) (hspor : SporadicModels131)
    (hG : TheoremFourHyp G) {E : Subgroup G} (hEe : CFSG.Assembly.IsElemAbelian 3 E) {e : G}
    (he : orderOf e = 3) {K : Subgroup G} (hK : K ∈ Sec12.lA422 E e)
    (hJ : Nonempty (K ⧸ CFSG.pCore 2 K ≃* CFSG.Blueprint.NativeSporadic.J2))
    {c : G} (hcE : c ∈ E) (hce : c ∉ Subgroup.zpowers e) {x : G} (hxe : x * e = e * x)
    (hx3 : x ^ 3 = c) : False := by
  have hc3 : c ^ 3 = 1 := hEe.2 c hcE
  have hx9 : x ^ 9 = 1 := by
    rw [show 9 = 3 * 3 from rfl, pow_mul, hx3, hc3]
  have hxP : IsPGroup 3 (Subgroup.zpowers x) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((3 ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, hx9, one_zpow]
  have hxH : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Sec13.centralizer_le_normalizer_zpowers e
      (Subgroup.mem_centralizer_singleton_iff.mpr hxe)
  have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hG he hK.1 hxP hxH (Subgroup.mem_zpowers x)
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hK.2.1 hcE
  set φ := (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hφ
  have hxc : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = ⟨c, hcN⟩ :=
    Subtype.ext (by simpa using hx3)
  have hσ3 : φ ⟨x, hxN⟩ ^ 3 = φ ⟨c, hcN⟩ := by rw [← map_pow, hxc]
  have hσ9 : φ ⟨x, hxN⟩ ^ 9 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 9 = 1 :=
      Subtype.ext (by simpa using hx9)
    rw [this, map_one]
  have hγ : φ ⟨c, hcN⟩ ≠ 1 := by
    intro h1
    apply hce
    have hcT : c ∈ Sec4.thetaQuotCentralizer K := ⟨⟨c, hcN⟩, h1, rfl⟩
    have hsc := hK.2.2.1
    rw [Sec13.sectionCentralizer_eq_inf hK.2.1] at hsc
    have : c ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := ⟨hcE, hcT⟩
    rw [hsc] at this
    exact this
  have hJθ := Sec13.nonempty_thetaQuot_equiv_j2 CFSG.Sporadic.J2.isSimpleGroup_J2 hspor hJ
  exact hγ (hσ3 ▸ pow_three_eq_one_of_pow_nine_of_j2 h415 hspor hJθ hσ9)

end CFSG.RankThree.PartTwo.Sec13.Res2Proof
