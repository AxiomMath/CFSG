module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeNamed
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF14Lin
import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUAlg
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8U42

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence inner_map_congr)
open CFSG.StandardType.PRankBounds (charP_two_of_card_four scalars_statedSU_five_eq_bot
  card_outer_psu5 false_of_suFive_outer)

theorem pow_fifteen_eq_one_of_commute_su5 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {t y : StatedSU 5 (2 ^ 1) K} (h5 : t ^ 5 = 1) (ht : t ≠ 1)
    (hyt : y * t = t * y) : y ^ 15 = 1 := by
  have : CharP K 2 := charP_two_of_card_four hK
  set φ : StatedSU 5 (2 ^ 1) K →* Matrix (Fin 5) (Fin 5) K :=
    (Units.coeHom (Matrix (Fin 5) (Fin 5) K)).comp (StatedSU 5 (2 ^ 1) K).subtype
  have hφinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
  obtain ⟨hu, -⟩ := CFSG.HardMathSupport.Foote.ModuleExclusions.unitary_of_mem_statedSU
    (frobenius K 2) (fun x => by rw [frobenius_def, pow_one]) t.2
  apply hφinj
  rw [map_pow, map_one]
  refine pow_fifteen_eq_one_of_commute' (by rw [hK]; norm_num) hu ?_ ?_
    (Units.isUnit (y : GL (Fin 5) K)) ?_
  · change φ t ^ 5 = 1
    rw [← map_pow, h5, map_one]
  · intro h
    exact ht (hφinj (by rw [map_one]; exact h))
  · change φ y * φ t = φ t * φ y
    rw [← map_mul, hyt, map_mul]

theorem pow_three_eq_one_of_forall_commute {G : Type} [Group G] {X Xk : Subgroup G}
    (hX : StatedClassicalModel X .PSU 5 2 1) (hXk : StatedClassicalModel Xk .PSU 4 2 1)
    (hle : Xk ≤ X) {y : G} (hy : y ∈ X) (hc : ∀ x ∈ Xk, y * x = x * y) : y ^ 3 = 1 := by
  have hcX := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hX
  have hcXk := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hXk
  have : Finite Xk := Nat.finite_of_card_ne_zero (by rw [hcXk]; norm_num)
  have : IsSimpleGroup Xk := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hXk
  have hZ : center Xk = ⊥ := center_eq_bot_of_noncomm
    (exists_noncomm_of_simple Nat.prime_two (by rw [hcXk]; norm_num) (by rw [hcXk]; norm_num))
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Xk) 5 (by rw [hcXk]; norm_num)
  have ht5 : t ^ 5 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    norm_num at ht
  have h15 : y ^ 15 = 1 := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    let j : X ≃* StatedSU 5 (2 ^ 1) K := e.trans
      ((QuotientGroup.quotientMulEquivOfEq (scalars_statedSU_five_eq_bot hK)).trans
        QuotientGroup.quotientBot)
    have hj5 : j (Subgroup.inclusion hle t) ^ 5 = 1 := by
      rw [← map_pow, ← map_pow, ht5, map_one, map_one]
    have hj1 : j (Subgroup.inclusion hle t) ≠ 1 := fun h =>
      ht1 (Subgroup.inclusion_injective hle (j.injective (by rw [h, map_one, map_one])))
    have hjc : j ⟨y, hy⟩ * j (Subgroup.inclusion hle t) =
        j (Subgroup.inclusion hle t) * j ⟨y, hy⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg j (Subtype.ext (hc t t.2))
    have h := pow_fifteen_eq_one_of_commute_su5 hK hj5 hj1 hjc
    rw [← map_pow, ← map_one j] at h
    simpa using congrArg Subtype.val (j.injective h)
  by_contra hz
  have hz5 : (y ^ 3) ^ 5 = 1 := by rw [← pow_mul]; exact h15
  have hzo : orderOf (y ^ 3) = 5 := orderOf_eq_prime hz5 hz
  have hzX : zpowers (y ^ 3) ≤ X := zpowers_le.mpr (X.pow_mem hy 3)
  have hcz : ∀ x ∈ Xk, ∀ w ∈ zpowers (y ^ 3), Commute x w := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((show Commute y x from hc x hx).pow_left 3).symm.zpow_right k
  set φ : Xk × zpowers (y ^ 3) →* G := MonoidHom.noncommCoprod Xk.subtype
    (zpowers (y ^ 3)).subtype (fun a b => hcz a a.2 b b.2)
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun ⟨a, b⟩ hab => ?_
    change (a : G) * (b : G) = 1 at hab
    have hb : (b : G) ∈ Xk := by
      rw [eq_inv_of_mul_eq_one_right hab]
      exact Xk.inv_mem a.2
    have hbc : (⟨b, hb⟩ : Xk) ∈ center Xk :=
      mem_center_iff.mpr fun g => Subtype.ext (hcz g g.2 b b.2).eq
    rw [hZ, mem_bot] at hbc
    have hb1 : b = 1 := Subtype.ext (show (b : G) = 1 from congrArg Subtype.val hbc)
    rw [hb1, OneMemClass.coe_one, mul_one] at hab
    exact Prod.ext (Subtype.ext hab) hb1
  have hrange : φ.range ≤ X := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change (a : G) * (b : G) ∈ X
    exact X.mul_mem (hle a.2) (hzX b.2)
  have hd := Subgroup.card_dvd_of_le hrange
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
    hzo, hcXk, hcX] at hd
  norm_num at hd

theorem false_of_outer_fix_u42 {G : Type} [Group G] {X Xk : Subgroup G}
    (hX : StatedClassicalModel X .PSU 5 2 1) (hXk : StatedClassicalModel Xk .PSU 4 2 1)
    (hle : Xk ≤ X) {α : MulAut X} (hα : α ∉ inner X)
    (hfix : ∀ y : X, (y : G) ∈ Xk → α y = y) : False := by
  obtain ⟨F, hF, hF27⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27
      (.inl ⟨by simp [CFSG.Blueprint.classicalTags], hXk⟩)
  have hOutX := card_outer_psu5 hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_four hK
  set j : X ≃* StatedSU 5 (2 ^ 1) K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (scalars_statedSU_five_eq_bot hK)).trans
      QuotientGroup.quotientBot)
  have hOutS : Nat.card (Outer (StatedSU 5 (2 ^ 1) K)) = 2 :=
    (Nat.card_congr (equivalence j).toEquiv).symm.trans hOutX
  have hα' : MulAut.congr j α ∉ inner (StatedSU 5 (2 ^ 1) K) := by
    intro h
    apply hα
    rw [← inner_map_congr j] at h
    obtain ⟨β, hβ, hβα⟩ := h
    have hβα' : β = α := (MulAut.congr j).injective hβα
    rwa [hβα'] at hβ
  set f : Xk →* StatedSU 5 (2 ^ 1) K := j.toMonoidHom.comp (Subgroup.inclusion hle)
  have hfinj : Function.Injective f := j.injective.comp (Subgroup.inclusion_injective hle)
  refine false_of_suFive_outer hK hOutS _ hα' (F.map f) (hF.map f) ?_ ?_
  · rw [Subgroup.card_map_of_injective hfinj, hF27]
    norm_num
  · rintro _ ⟨x, -, rfl⟩
    show j (α (j.symm (j (Subgroup.inclusion hle x)))) = j (Subgroup.inclusion hle x)
    rw [MulEquiv.symm_apply_apply, hfix (Subgroup.inclusion hle x) x.2]

theorem f14Input_holds : F14Input := by
  intro G _ X Xk hX hXk hle α hfix
  have hX' := hX.statedClassicalModel_of_ne_zero (by norm_num)
  have hXk' := hXk.statedClassicalModel_of_ne_zero (by norm_num)
  by_cases hα : α ∈ inner X
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hα
    have hy3 : (y : G) ^ 3 = 1 := pow_three_eq_one_of_forall_commute hX' hXk' hle y.2 fun x hx => by
      have h := congrArg Subtype.val (hfix ⟨x, hle hx⟩ hx)
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
      calc (y : G) * x = (y : G) * x * (y : G)⁻¹ * y := by group
        _ = x * y := by rw [h]
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using hy3), map_one]
  · exact (false_of_outer_fix_u42 hX' hXk' hle hα hfix).elim

end CFSG.GGQ2Prime
