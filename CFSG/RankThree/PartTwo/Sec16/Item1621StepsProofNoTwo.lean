module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail23
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item169General
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def KS1623SU3Aut : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2 ^ n % 3 = 2 → ¬ (2 ^ n % 9 = 8) →
    ∀ E : Subgroup ↥(projSU 3 2 n), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ T : Subgroup (MulAut ↥(projSU 3 2 n)), IsPGroup 2 T →
      (∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (T : Set (MulAut ↥(projSU 3 2 n)))) →
        T = ⊥

namespace Proof1623NoTwo

variable {G : Type} [Group G] [Finite G]

theorem checkSU_20160 : ∀ q < 28, 2 ≤ q → q ^ 3 ∣ 20160 →
    20160 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

omit [Finite G] in
theorem congr_normalizerMonoidHom_eq_conj {L : Subgroup G} {U : Type*} [Group U] (φ : ↥L ≃* U)
    {ℓ : G} (hℓL : ℓ ∈ L) (hℓN : ℓ ∈ Subgroup.normalizer (L : Set G)) :
    MulAut.congr φ (L.normalizerMonoidHom ⟨ℓ, hℓN⟩) = MulAut.conj (φ ⟨ℓ, hℓL⟩) := by
  ext u
  obtain ⟨x, rfl⟩ := φ.surjective u
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply]
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1

end Proof1623NoTwo

open Proof1623NoTwo

theorem step1623NoTwo_of (h1612 : Step1612) (h138 : Item138N) (hK : KS1623SU3Aut) :
    Step1623NoTwo := by
  intro G _ _ A c L h hLs n hz h2 hφ T hT
  obtain ⟨φ⟩ := hφ
  obtain ⟨hTH, hT2, hAT⟩ := hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2' : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT2
  obtain ⟨hn, hiso, hprod⟩ := hz
  have hS := h.toSec13Data
  have hn2 : 2 ≤ n := by
    have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
    have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hqs.1
    have hne := (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hiso).2
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact hne (by norm_num)
  have h9 : ¬ (2 ^ n % 9 = 8) := fun h8 =>
    Sec15.not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn hiso hprod (Or.inr h8)
  have h3L : 3 ∣ Nat.card L :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hiso).trans
      (Subgroup.card_quotient_dvd_card _)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    hTH.trans (normalizer_zpowers_le_normalizer_L h.toSec15R h3L)
  have h9AL : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine hS (isPerfect_lBar hS) hprod.some
  set E : Subgroup ↥(projSU 3 2 n) := ((A ⊓ L).subgroupOf L).map φ.toMonoidHom with hE
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
      apply Subtype.ext
      change φ x * φ y = φ y * φ x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (h.commute (Subgroup.mem_subgroupOf.mp hx).1
        (Subgroup.mem_subgroupOf.mp hy).1)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by
        simpa using h.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
      rw [this, map_one]
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective φ.injective, ← h9AL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  set κ := L.normalizerMonoidHom with hκ
  set Θ : Subgroup.normalizer (L : Set G) →* MulAut ↥(projSU 3 2 n) :=
    (MulAut.congr φ).toMonoidHom.comp κ with hΘ
  set T' : Subgroup ↥(Subgroup.normalizer (L : Set G)) := T.subgroupOf _ with hT'
  set That : Subgroup (MulAut ↥(projSU 3 2 n)) := T'.map Θ with hThat
  have hT'2 : IsPGroup 2 T' :=
    hT2'.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hThat2 : IsPGroup 2 That := hT'2.map Θ
  have hstep : ∀ ℓ : G, ∀ (hℓL : ℓ ∈ L), ℓ ∈ A → ∀ τ ∈ That,
      MulAut.conj (φ ⟨ℓ, hℓL⟩) * τ * (MulAut.conj (φ ⟨ℓ, hℓL⟩))⁻¹ ∈ That := by
    intro ℓ hℓL hℓA τ hτ
    have hℓN : ℓ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hℓL
    have hconj : MulAut.conj (φ ⟨ℓ, hℓL⟩) = Θ ⟨ℓ, hℓN⟩ :=
      (congr_normalizerMonoidHom_eq_conj φ hℓL hℓN).symm
    obtain ⟨t, ht, rfl⟩ := hτ
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hℓt : ℓ * t * ℓ⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hAT hℓA) t).mp htT
    refine ⟨⟨ℓ, hℓN⟩ * t * ⟨ℓ, hℓN⟩⁻¹, Subgroup.mem_subgroupOf.mpr hℓt, ?_⟩
    rw [hconj, map_mul, map_mul, map_inv]
  have hnorm : ∀ e ∈ E, MulAut.conj e ∈
      Subgroup.normalizer (That : Set (MulAut ↥(projSU 3 2 n))) := by
    rintro _ ⟨⟨ℓ, hℓL⟩, hℓ, rfl⟩
    have hℓA : ℓ ∈ A := (Subgroup.mem_subgroupOf.mp hℓ).1
    rw [Subgroup.mem_normalizer_iff]
    intro τ
    refine ⟨fun hτ => hstep ℓ hℓL hℓA τ hτ, fun hτ => ?_⟩
    have h1 := hstep ℓ⁻¹ (inv_mem hℓL) (inv_mem hℓA) _ hτ
    have h2 : (⟨ℓ⁻¹, inv_mem hℓL⟩ : ↥L) = (⟨ℓ, hℓL⟩ : ↥L)⁻¹ := rfl
    rw [h2, map_inv, map_inv] at h1
    simpa [mul_assoc] using h1
  have hbot := hK n hn2 h2 h9 E hEel hE9 That hThat2 hnorm
  have hTC : T ≤ Subgroup.centralizer (L : Set G) := by
    intro t ht
    have h1 : Θ ⟨t, hTL ht⟩ = 1 := by
      have : Θ ⟨t, hTL ht⟩ ∈ That := ⟨⟨t, hTL ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have h2' : κ ⟨t, hTL ht⟩ = 1 := by
      have h1' : MulAut.congr φ (κ ⟨t, hTL ht⟩) = 1 := h1
      exact (MulEquiv.map_eq_one_iff _).mp h1'
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) h2'
    simp only [MulAut.one_apply] at this
    change t * l * t⁻¹ = l at this
    calc l * t = t * l * t⁻¹ * t := by rw [this]
      _ = t * l := by group
  rcases h1612 G A c L h with ⟨-, hno⟩ | hψ
  · exact hno T ⟨hTC, hT2, hAT⟩
  · exfalso
    obtain ⟨ψ⟩ := hψ
    obtain ⟨η⟩ := nonempty_thetaQuot_equiv hS (isPerfect_lBar hS) hprod.some
    have h1 := Nat.card_congr hprod.some.toEquiv
    have h2'' := Nat.card_congr ψ.toEquiv
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]
    rw [Nat.card_prod, h3] at h1 h2''
    rw [card_projSL_three_four] at h2''
    have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 20160 := by
      rw [Nat.card_congr η.toEquiv]
      omega
    rcases hiso with ⟨hq, -⟩ | ⟨-, ⟨χ⟩⟩
    · omega
    · exact (KFacts.KS14.isEmpty_mulEquiv_projSU_three_of_card hcard
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_20160) 2 n hn).false
          χ

end CFSG.RankThree.PartTwo.Sec16
