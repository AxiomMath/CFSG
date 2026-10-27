module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsRank
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Cyc
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoBound
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.Sporadic.Schreier.J4SOrder

public section

namespace CFSG.StandardType

namespace FieldFiveRank

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem card_le_five_mul_of_cyclic {G : Type} [Group G] [Finite G] {G₀ E : Subgroup G}
    (hE5 : ∀ e ∈ E, e ^ 5 = 1) (hEN : E ≤ Subgroup.normalizer (G₀ : Set G)) {y₀ : G}
    (hy₀ : y₀ ∈ E) (hcyc : ∀ y ∈ E, ∃ k : ℕ, y * (y₀ ^ k)⁻¹ ∈ G₀) :
    Nat.card E ≤ 5 * Nat.card (E ⊓ G₀ : Subgroup G) := by
  classical
  let F : Fin 5 × ↥(E ⊓ G₀) → ↥E := fun p =>
    ⟨y₀ ^ (p.1 : ℕ) * p.2, E.mul_mem (E.pow_mem hy₀ _) (Subgroup.mem_inf.mp p.2.2).1⟩
  have hF : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hcyc y hy
    have hyk : y₀ ^ k = y₀ ^ (k % 5) := by
      conv_lhs => rw [← Nat.mod_add_div k 5, pow_add, pow_mul, hE5 y₀ hy₀, one_pow, mul_one]
    set h := (y₀ ^ (k % 5))⁻¹ * y with hh
    have hhG : h ∈ G₀ := by
      have h1 : y₀ ^ (k % 5) ∈ Subgroup.normalizer (G₀ : Set G) := hEN (E.pow_mem hy₀ _)
      have h2 := (Subgroup.mem_normalizer_iff''.mp h1 (y * (y₀ ^ k)⁻¹)).mp hk
      rw [hyk] at h2
      convert h2 using 1
      rw [hh]
      group
    have hhE : h ∈ E := E.mul_mem (E.inv_mem (E.pow_mem hy₀ _)) hy
    refine ⟨(⟨k % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨h, Subgroup.mem_inf.mpr ⟨hhE, hhG⟩⟩), ?_⟩
    apply Subtype.ext
    show y₀ ^ (k % 5) * ((y₀ ^ (k % 5))⁻¹ * y) = y
    group
  calc Nat.card E ≤ Nat.card (Fin 5 × ↥(E ⊓ G₀)) := Nat.card_le_card_of_surjective F hF
    _ = 5 * Nat.card (E ⊓ G₀ : Subgroup G) := by rw [Nat.card_prod, Nat.card_eq_fintype_card,
        Fintype.card_fin]

theorem not_dvd_ordTwistedE6 : ¬ 5 ^ 3 ∣ (2 ^ 1) ^ 36 * ((2 ^ 1) ^ 12 - 1) * ((2 ^ 1) ^ 9 + 1) *
    ((2 ^ 1) ^ 8 - 1) * ((2 ^ 1) ^ 6 - 1) * ((2 ^ 1) ^ 5 + 1) * ((2 ^ 1) ^ 2 - 1) := by
  norm_num

end FieldFiveRank

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  FieldFiveRank

theorem not_dvd_card_twistedE6Group :
    ¬ 5 ^ 3 ∣ Nat.card (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 1) := by
  classical
  open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
    CFSG.EvenSmallLie.TwoE6 in
  have hU : Nat.card (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 1) =
      Nat.card stdGroup * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup isogenyStd.ker,
      CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.card_ker_isogenyStd,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ isogenyStd_surjective).toEquiv]
  open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std in
  have hord : ordProj[5] (Nat.card stdGroup) = ordProj[5] ((2 ^ 1) ^ 36 * ((2 ^ 1) ^ 12 - 1) *
      ((2 ^ 1) ^ 9 + 1) * ((2 ^ 1) ^ 8 - 1) * ((2 ^ 1) ^ 6 - 1) * ((2 ^ 1) ^ 5 + 1) *
        ((2 ^ 1) ^ 2 - 1)) := by
    have : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [Nat.card_eq_fintype_card, card_K]; norm_num
    obtain ⟨-, -, -, -, -, hcard, hp⟩ :=
      CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order Nat.prime_two le_rfl K
        hK barHom (fun c => by rw [barHom_apply, pow_one]; rfl) (AlgebraicClosure K)
        (frobenius (AlgebraicClosure K) 2) (fun c => by rw [pow_one, frobenius_def])
    rw [← hcard, ← hp 5 (by norm_num) (by norm_num),
      Subgroup.card_map_of_injective (baseChangeGL_injective _)]
    rfl
  intro h125
  have hS : 5 ^ 3 ∣ Nat.card CFSG.LieType.Chevalley.C2E6Std.stdGroup := by
    rw [hU] at h125
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h125)
  have hS0 : Nat.card CFSG.LieType.Chevalley.C2E6Std.stdGroup ≠ 0 := Nat.card_pos.ne'
  rw [(Nat.Prime.pow_dvd_iff_dvd_ordProj (by norm_num) hS0), hord] at hS
  exact not_dvd_ordTwistedE6 (hS.trans (Nat.ordProj_dvd _ _))

theorem ggFieldFiveRankTag_twistedE6 : GGFieldFiveRankTag .twistedE6 := by
  intro G _ _ n ψ G₀ hpres hC E hE hEN hEdiag
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hker := hpres.2.1.2
  obtain ⟨y₀, hy₀, hcyc⟩ := ggTwE6InnerDiagCyclicInput_holds G n 1 ψ hpres.1.1 hker
    (hrange ▸ hC) E (hrange ▸ hEN) hEdiag
  rw [hrange] at hcyc
  have h1 := card_le_five_mul_of_cyclic hE.2 hEN hy₀ hcyc
  have hEG : IsElemAbelian 5 (E ⊓ G₀) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => hE.2 e (Subgroup.mem_inf.mp he).1⟩
    have h := hE.1.is_comm.comm (⟨a, (Subgroup.mem_inf.mp a.2).1⟩ : ↥E)
      ⟨b, (Subgroup.mem_inf.mp b.2).1⟩
    simpa using congrArg Subtype.val h
  have hU : Nat.card G₀ ∣ Nat.card (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 1) :=
    hrange ▸ Subgroup.card_range_dvd ψ
  have h2 := card_lt_of_not_dvd hEG inf_le_right hU not_dvd_card_twistedE6Group
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 (E ⊓ G₀ : Subgroup G) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hEG.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  rw [hk] at h2 h1
  have hk2 : k ≤ 3 := by
    by_contra hk4
    have : 5 ^ 4 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk2' : k ≤ 2 := by
    by_contra hk3
    have hk3' : k = 3 := by omega
    subst hk3'
    exact absurd ((pow_dvd_pow 5 le_rfl).trans ((hk ▸ Subgroup.card_dvd_of_le inf_le_right :
      5 ^ 3 ∣ Nat.card G₀).trans hU)) not_dvd_card_twistedE6Group
  calc Nat.card E ≤ 5 * 5 ^ k := h1
    _ ≤ 5 * 5 ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk2')
    _ < 5 ^ 4 := by norm_num

end CFSG.StandardType
