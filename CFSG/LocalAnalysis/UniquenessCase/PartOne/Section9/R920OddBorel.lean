module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups

theorem exists_conj_pow_of_isL2Odd {Y : Type} [Group Y] {q : ℕ} (hq : 5 < q)
    (hY : IsL2Odd Y q) :
    ∃ (u d : Y) (k : ℕ), orderOf u = q ∧ d * u * d⁻¹ = u ^ k ∧
      orderOf (k : ZMod q) = (q - 1) / 2 := by
  classical
  have hqp : q.Prime := hY.admissible.1
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  obtain ⟨-, K, _, hKf, hcard, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hY
    (by decide)
  haveI := Fintype.ofFinite K
  have hcard' : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
  haveI : CharP K q := charP_of_card_eq_prime hcard'
  have hchar : ringChar K = q := ringChar.eq K q
  have hF2 : ringChar K ≠ 2 := by omega
  let ψ : SL(2, K) →* Y := e.symm.toMonoidHom.comp
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).toMonoidHom.comp
      CFSG.PSL2Table.mk)
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hcard, pow_one] at hμ
  obtain ⟨z, hz⟩ := (ZMod.castHom_bijective K hcard').2 ((μ : K) ^ 2)
  have hk : ((z.val : ℕ) : K) = (μ : K) ^ 2 := by
    rw [ZMod.natCast_val]
    exact hz
  refine ⟨ψ (CFSG.PSL2Table.unip 1), ψ (CFSG.PSL2Table.diag μ), z.val, ?_, ?_, ?_⟩
  · change orderOf (e.symm (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      2 K (CFSG.PSL2Table.mk (CFSG.PSL2Table.unip 1)))) = q
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq,
      CFSG.Walter.Ward.PSLTable.orderOf_unip hF2 one_ne_zero, hchar]
  · rw [← map_inv, ← map_mul, ← map_mul, CFSG.PSL2Table.diag_conj_unip, ← map_pow,
      CFSG.Walter.Ward.PSLTable.unip_pow, hk]
  · have h1 : orderOf z = orderOf ((μ : K) ^ 2) := by
      rw [← hz]
      exact (orderOf_injective (ZMod.castHom (dvd_refl q) K).toMonoidHom
        (ZMod.castHom_bijective K hcard').1 z).symm
    have hodd : 2 ∣ q - 1 := by
      have := hqp.eq_two_or_odd
      omega
    rw [ZMod.natCast_zmod_val, h1, ← Units.val_pow_eq_pow_val, orderOf_units,
      orderOf_pow' μ two_ne_zero, hμ, Nat.gcd_eq_right hodd]

theorem exists_conj_pow_of_quotient {Γ : Type} [Group Γ] [Finite Γ] {q : ℕ} (hq : q.Prime)
    (O : Subgroup Γ) [O.Normal] (hO : ¬ q ∣ Nat.card O) {u₀ d₀ : Γ ⧸ O} {k : ℕ}
    (hu : orderOf u₀ = q) (hdu : d₀ * u₀ * d₀⁻¹ = u₀ ^ k) :
    ∃ u d : Γ, orderOf u = q ∧ d * u * d⁻¹ = u ^ k := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨u, hu', rfl⟩ := CFSG.GroupTheory.CoprimeTransport.exists_orderOf_eq_prime_mk_eq hO hu
  have hS : IsPGroup q (zpowers u) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hu', pow_one])
  have hd₀ : d₀ ∈ normalizer (((zpowers u).map (QuotientGroup.mk' O) : Subgroup (Γ ⧸ O)) :
      Set (Γ ⧸ O)) := by
    rw [MonoidHom.map_zpowers]
    exact TauCeti.mem_normalizer_zpowers_of_mul_mul_inv_eq_pow
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨q, hq.pos, by rw [← hu, pow_orderOf_eq_one]⟩) hdu
  obtain ⟨d, hdN, rfl⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer hq O
    ((Nat.Prime.coprime_iff_not_dvd hq).mpr hO) hS hd₀
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hdN u).mp (mem_zpowers u))
  have hmk : QuotientGroup.mk' O u ^ j = QuotientGroup.mk' O u ^ (k : ℤ) := by
    rw [← map_zpow, hj, map_mul, map_mul, map_inv, hdu, zpow_natCast]
  rw [zpow_eq_zpow_iff_modEq, hu, ← hu', ← zpow_eq_zpow_iff_modEq, hj, zpow_natCast] at hmk
  exact ⟨u, d, hu', hmk⟩

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem exists_conj_pow_lbar9 (S : Slice D L D₃ Y H q) :
    ∃ (a b : F09.Lbar9 Y H) (k : ℕ), orderOf a = q ∧ b * a * b⁻¹ = a ^ k ∧
      orderOf (k : ZMod q) = (q - 1) / 2 := by
  classical
  have hqp := S.prime
  haveI : Fact q.Prime := ⟨hqp⟩
  have hq2 : q ≠ 2 := by
    have := S.gt
    omega
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  obtain ⟨u₀, d₀, k, hu₀, hdu₀, hk⟩ := exists_conj_pow_of_isL2Odd S.gt S.shape_opp
  have hO : ¬ q ∣ Nat.card (CFSG.pCore 2 ↥(Opp 3 Y)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp 3 Y)))
    rw [hn]
    exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h))
  obtain ⟨u, d, hu, hdu⟩ := exists_conj_pow_of_quotient hqp (CFSG.pCore 2 ↥(Opp 3 Y)) hO hu₀ hdu₀
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono fun y hy => F09.opp_le_L9 Y H hy
  let ι : ↥(Opp 3 Y) →* F09.Lbar9 Y H := (Subgroup.inclusion hle).comp (toImg9 hXH)
  refine ⟨ι u, ι d, k, orderOf_eq_prime ?_ ?_, by rw [← map_inv, ← map_mul, ← map_mul, hdu,
    map_pow], hk⟩
  · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  · intro h1
    have hker : u ∈ (toImg9 hXH).ker :=
      (Subgroup.inclusion_injective hle) (by rw [map_one]; exact h1)
    obtain ⟨n, hn⟩ := S.isPGroup_ker_toImg9 hXH ⟨u, hker⟩
    have hu2 : u ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h2 : q ∣ 2 ^ n := hu ▸ orderOf_dvd_of_pow_eq_one hu2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h2))

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
