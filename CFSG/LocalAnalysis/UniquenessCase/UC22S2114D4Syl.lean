module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.RankThree.PartOne.K128.D4Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.RankThree.PartOne.K1214 (SylowShape)

theorem uc22s2114_two_pow_two_pow_mod (k : ℕ) :
    2 ^ 2 ^ k % 49 = 2 ∨ 2 ^ 2 ^ k % 49 = 4 ∨ 2 ^ 2 ^ k % 49 = 16 ∨ 2 ^ 2 ^ k % 49 = 11 ∨
      2 ^ 2 ^ k % 49 = 23 ∨ 2 ^ 2 ^ k % 49 = 39 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, pow_mul, Nat.pow_mod]
    rcases ih with h | h | h | h | h | h <;> rw [h] <;> norm_num

theorem uc22s2114_seven_factorization {f : ℕ} (hf : IsPowTwo f) :
    7 ∣ (2 ^ f) ^ 2 + 2 ^ f + 1 ∧ ((2 ^ f) ^ 2 + 2 ^ f + 1).factorization 7 = 1 := by
  obtain ⟨k, rfl⟩ := hf
  have hm : ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 =
      ((2 ^ 2 ^ k % 49) ^ 2 + 2 ^ 2 ^ k % 49 + 1) % 49 :=
    ((((Nat.mod_modEq (2 ^ 2 ^ k) 49).pow 2).add (Nat.mod_modEq (2 ^ 2 ^ k) 49)).add_right
      1).symm
  have h49 : ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 = 7 ∨
      ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 = 21 ∨
      ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 = 28 ∨
      ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 = 35 ∨
      ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 = 14 ∨
      ((2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1) % 49 = 42 := by
    rw [hm]
    rcases uc22s2114_two_pow_two_pow_mod k with h | h | h | h | h | h <;> rw [h] <;> norm_num
  have hN0 : (2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1 ≠ 0 := by positivity
  generalize (2 ^ 2 ^ k) ^ 2 + 2 ^ 2 ^ k + 1 = N at h49 hN0 ⊢
  have h7 : 7 ∣ N := by
    apply Nat.dvd_of_mod_eq_zero
    rw [← Nat.mod_mod_of_dvd N (by norm_num : 7 ∣ 49)]
    rcases h49 with h | h | h | h | h | h <;> rw [h]
  have h72 : ¬ 7 ^ 2 ∣ N := by
    intro h
    have h0 : N % 49 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h)
    rcases h49 with h | h | h | h | h | h <;> omega
  refine ⟨h7, ?_⟩
  have h1 := (Nat.prime_seven.pow_dvd_iff_le_factorization hN0).1 (by rwa [pow_one])
  have h2 := mt (Nat.prime_seven.pow_dvd_iff_le_factorization (k := 2) hN0).2 h72
  omega


theorem uc22s2114_sylowSeven_of_is3D4 {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : Is3D4 X f) (hf : IsPowTwo f) (P : Sylow 7 X) :
    IsElemAbelian 7 (P : Subgroup X) ∧ Nat.card (P : Subgroup X) = 49 := by
  obtain ⟨⟨-, hf1, -⟩, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX).2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4
      Nat.prime_two hf1 hmod
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := by simpa [TwistTag.order] using hK
  obtain ⟨h7, hfac⟩ := uc22s2114_seven_factorization hf
  have hphi : CFSG.RankThree.PartOne.K128.phiNat 3 (2 ^ f) = (2 ^ f) ^ 2 + 2 ^ f + 1 := rfl
  have hshapeC : SylowShape 7 2 1 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have h := CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) (f := f) hf1 K
      hK3 σ hσ (m := 3) (by decide) (p := 7) (by norm_num) (by norm_num) (hphi ▸ h7)
    rwa [hphi, hfac] at h
  obtain ⟨eP⟩ := CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv e hshapeC (P : Subgroup X)
    P.isPGroup'
    (@Sylow.not_dvd_index 7 X inferInstance ⟨by norm_num⟩ P inferInstance)
  have hcard7 : Nat.card (Multiplicative (ZMod (7 ^ 1))) = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    norm_num
  have h7' : ∀ y : Fin 2 → Multiplicative (ZMod (7 ^ 1)), y ^ 7 = 1 := by
    intro y
    funext i
    have h := pow_card_eq_one' (x := y i)
    rwa [hcard7] at h
  refine ⟨⟨⟨⟨fun a b => eP.injective ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_comm _ _
  · have hxP : (⟨x, hx⟩ : ↥P) ^ 7 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact h7' (eP ⟨x, hx⟩)
    exact congrArg Subtype.val hxP
  · rw [Nat.card_congr eP.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
      Fintype.card_fin, hcard7]
    norm_num

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_exists_fortyNine_of_is3D4 {L : Subgroup G} {f : ℕ}
    (h3D4 : Is3D4 (Bar2 L) f) (hf : IsPowTwo f) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 7 E ∧ Nat.card E = 49 := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow 7 (Bar2 L)) := inferInstance
  obtain ⟨hPel, hPcard⟩ := uc22s2114_sylowSeven_of_is3D4 h3D4 hf P
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, -, hQmap, hQdisj⟩ :=
    UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker
      Nat.prime_seven (by norm_num) (P : Subgroup (Bar2 L)) P.isPGroup'
  refine ⟨Q.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map
      (UC6S846.isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hPel)) _
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← UC6S846.card_map_of_disjoint_ker π Q hQdisj, hQmap, hPcard]

end CFSG.LocalAnalysis.UniquenessCase.UC22
