module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Walter.PSL2Facts.Even
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.CGT.Timmesfeld75.ListWCSzU3

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

namespace Item228Census6Proof

theorem exists_of_autIn_mulEquiv_dihedral {Y : Type} [Group Y] {B : Subgroup Y}
    (e : Sec4.autIn ⊤ B ≃* DihedralGroup 6) :
    ∃ g : Y, (∀ b ∈ B, g * b * g⁻¹ ∈ B) ∧ (∀ b ∈ B, g ^ 3 * b = b * g ^ 3) ∧
      ∃ b ∈ B, g * b ≠ b * g := by
  set σ : Sec4.autIn ⊤ B := e.symm (DihedralGroup.r 2) with hσ
  have hr3 : (DihedralGroup.r 2 : DihedralGroup 6) ^ 3 = 1 := by decide
  have hr1 : (DihedralGroup.r 2 : DihedralGroup 6) ≠ 1 := by decide
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, hr3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hr1
    have h' := congrArg e h
    rwa [hσ, MulEquiv.apply_symm_apply, map_one] at h'
  obtain ⟨g, hN, -, hg⟩ := Sec4.mem_autIn_iff.mp σ.2
  have hcube : B.normalizerMonoidHom (⟨g, hN⟩ ^ 3) = 1 := by
    rw [map_pow, hg, ← Subgroup.coe_pow, hσ3, Subgroup.coe_one]
  refine ⟨g, fun b hb => (Subgroup.mem_normalizer_iff.mp hN b).mp hb, fun b hb => ?_, ?_⟩
  · have h := congrArg (fun τ : MulAut B => ((τ ⟨b, hb⟩ : B) : Y)) hcube
    have e1 : ((B.normalizerMonoidHom (⟨g, hN⟩ ^ 3) ⟨b, hb⟩ : B) : Y) =
        g ^ 3 * b * (g ^ 3)⁻¹ := rfl
    simp only [e1, MulAut.one_apply] at h
    calc g ^ 3 * b = g ^ 3 * b * (g ^ 3)⁻¹ * g ^ 3 := by group
      _ = b * g ^ 3 := by rw [h]
  · by_contra hall
    push Not at hall
    apply hσ1
    apply Subtype.ext
    rw [← hg]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    change g * (b : Y) * g⁻¹ = b
    rw [hall b b.2, mul_inv_cancel_right]

theorem exists_invariant_sylow_of_not_dvd {A G : Type*} [Group A] [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hA : IsPGroup p A)
    (hnd : ¬ p ∣ Nat.card (Sylow q G)) (φ : A →* MulAut G) :
    ∃ P : Sylow q G, ∀ a : A, (P : Subgroup G).map (φ a).toMonoidHom = P := by
  let := MulDistribMulAction.compHom G φ
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q G) hnd
  refine ⟨P, fun a => ?_⟩
  have h := congrArg (fun Q : Sylow q G => (Q : Subgroup G)) (MulAction.mem_fixedPoints.mp hP a)
  rw [Sylow.pointwise_smul_def] at h
  exact h

theorem two_pow_mod_three_of_even {m : ℕ} (hm : Even m) : 2 ^ m % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem not_three_dvd_card_sylow_and_two_dvd {Y : Type} [Group Y] [Finite Y]
    {N Kb : Subgroup Y} {m : ℕ} (hKN : Kb ≤ N)
    (hKb : Nonempty (Kb ≃* projSL 2 (GaloisField 2 m))) (hm0 : 0 < m) (hme : Even m)
    (hor : Kb = N ∨ StatedClassicalModel N .PSU 3 2 2) :
    ¬ 3 ∣ Nat.card (Sylow 2 N) ∧ 2 ∣ Nat.card N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hKb
  have h2m := two_pow_mod_three_of_even hme
  refine ⟨?_, ?_⟩
  · rcases hor with rfl | hU
    · rw [CFSG.LargeExtraspecial.Bender.card_sylow_congr (e.trans (Sec4.projSLEquivPSL _)) 2,
        CFSG.Walter.psl2_even_card_sylow (by omega)]
      omega
    · rw [CFSG.CGT.Timmesfeld75.card_sylow_psu3 hU]
      norm_num
  · have hK : Nat.card Kb = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr (e.trans (Sec4.projSLEquivPSL _)).toEquiv,
        CFSG.Walter.psl2_even_card (by omega)]
    have h1 : 2 ∣ Nat.card Kb := by
      rw [hK]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
    exact h1.trans (Subgroup.card_dvd_of_le hKN)

theorem exists_two_subgroup_normalized {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y}
    (hB : IsElemAbelian 3 B) {y : Y} (hyB : y ∈ B) {N Kb : Subgroup Y} {m : ℕ}
    (hnorm : ∀ g : Y, g * y = y * g → ∀ k ∈ N, g * k * g⁻¹ ∈ N) (hKN : Kb ≤ N)
    (hKb : Nonempty (Kb ≃* projSL 2 (GaloisField 2 m))) (hm0 : 0 < m) (hme : Even m)
    (hor : Kb = N ∨ StatedClassicalModel N .PSU 3 2 2) :
    ∃ T : Subgroup Y, IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ b ∈ B, b * y = y * b := fun b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨y, hyB⟩)
  have hBN : B ≤ Subgroup.normalizer (N : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hnorm b (hcomm b hb) k hk, fun hk => ?_⟩
    have hb' := hnorm b⁻¹ (hcomm _ (inv_mem hb)) _ hk
    rwa [inv_inv, show b⁻¹ * (b * k * b⁻¹) * b = k by group] at hb'
  obtain ⟨hsyl, h2N⟩ := not_three_dvd_card_sylow_and_two_dvd hKN hKb hm0 hme hor
  set φ : B →* MulAut N := N.normalizerMonoidHom.comp (Subgroup.inclusion hBN) with hφ
  have hBp : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hB.2 b b.2)⟩
  obtain ⟨P, hP⟩ := exists_invariant_sylow_of_not_dvd hBp hsyl φ
  refine ⟨(P : Subgroup N).map N.subtype, P.isPGroup'.map _, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
    exact P.ne_bot_of_dvd_card h2N
  · have hfwd : ∀ c ∈ B, ∀ t ∈ (P : Subgroup N).map N.subtype,
        c * t * c⁻¹ ∈ (P : Subgroup N).map N.subtype := by
      rintro c hc _ ⟨n, hn, rfl⟩
      have hmem : (φ ⟨c, hc⟩) n ∈ (P : Subgroup N).map (φ ⟨c, hc⟩).toMonoidHom := ⟨n, hn, rfl⟩
      rw [hP] at hmem
      exact ⟨_, hmem, rfl⟩
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hfwd b hb t, fun ht => ?_⟩
    have ht' := hfwd b⁻¹ (inv_mem hb) _ ht
    rwa [inv_inv, show b⁻¹ * (b * t * b⁻¹) * b = t by group] at ht'

end Item228Census6Proof

end CFSG.RankThree.PartTwo.Sec21
