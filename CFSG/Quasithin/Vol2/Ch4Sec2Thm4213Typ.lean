module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C9
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4

variable {G : Type} [Group G] [Finite G]

namespace T4213

section PCore

variable {A C : Type*} [Group A] [Group C]

theorem comap_pCore_eq_of_surjective {f : A →* C} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : (CFSG.pCore 2 C).comap f = CFSG.pCore 2 A := by
  have hPC : IsPGroup 2 (CFSG.pCore 2 C) := CFSG.pCore_isPGroup
  have hPA : IsPGroup 2 (CFSG.pCore 2 A) := CFSG.pCore_isPGroup
  refine le_antisymm ?_ ?_
  · have hn : ((CFSG.pCore 2 C).comap f).Normal := CFSG.pCore_normal.comap f
    have h2 : IsPGroup 2 ((CFSG.pCore 2 C).comap f) := by
      intro x
      obtain ⟨k, hk⟩ := hPC ⟨f x, x.2⟩
      have hk' : f ((x : A) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      obtain ⟨m, hm⟩ := hker ⟨(x : A) ^ 2 ^ k, hk'⟩
      refine ⟨k + m, Subtype.ext ?_⟩
      have hm' : ((x : A) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      rw [pow_add, pow_mul]
      simpa using hm'
    exact le_sSup ⟨hn, h2⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((CFSG.pCore 2 A).map f).Normal := CFSG.pCore_normal.map f hf
    exact le_sSup ⟨hn, hPA.map f⟩

theorem pCore_quotient_eq_bot : CFSG.pCore 2 (A ⧸ CFSG.pCore 2 A) = ⊥ := by
  have hf := QuotientGroup.mk'_surjective (CFSG.pCore 2 A)
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have h1 := comap_pCore_eq_of_surjective hf hker
  rw [← Subgroup.map_comap_eq_self_of_surjective hf (CFSG.pCore 2 (A ⧸ CFSG.pCore 2 A)), h1]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

end PCore

omit [Finite G] in
theorem nonempty_modO2_equiv {L LH : Subgroup G} (hLHL : LH ≤ L)
    (hL : L ≤ LH ⊔ pCoreOf 2 L) : Nonempty (ModO2 LH ≃* ModO2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥LH →* ModO2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hLHL)
    with hf
  have hmem : ∀ x : ↥L, (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.pCore 2 ↥L := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by
      have : y = x := Subtype.ext hyx
      subst this
      assumption, fun hx => ⟨x, by assumption, rfl⟩⟩
  have hLHO : LH ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hLHL.trans (le_normalizer_pCoreOf 2 L)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    obtain ⟨a, ha, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hLHO).mp (hL hl)
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hoL : o ∈ L := pCoreOf_le 2 L ho
    have e : (Subgroup.inclusion hLHL ⟨a, ha⟩)⁻¹ * ⟨a * o, hl⟩ = ⟨o, hoL⟩ := by
      apply Subtype.ext
      simp
    rw [e]
    exact (hmem _).mp ho
  have hker : IsPGroup 2 f.ker := by
    have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hLHL)) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective _
        (Subgroup.inclusion_injective hLHL)
    have hk : f.ker = (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hLHL) := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [hk]
    exact h2
  have hk : f.ker = CFSG.pCore 2 ↥LH := by
    rw [← comap_pCore_eq_of_surjective hsurj hker, pCore_quotient_eq_bot, MonoidHom.comap_bot]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem isPSL_of_mulEquiv (e : X ≃* Y) {n p f : ℕ} (h : IsPSL n p f X) : IsPSL n p f Y := by
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem isPSU_of_mulEquiv (e : X ≃* Y) {n p f : ℕ} (h : IsPSU n p f X) : IsPSU n p f Y := by
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem isPSL_of_lieModel {n f : ℕ} (hn : 1 ≤ n) (h : LieModel X .PSL n 2 f) : IsPSL n 2 f X := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  all_goals omega

theorem isPSU_of_lieModel (h : LieModel X .PSU 3 3 1) : IsPSU 3 3 1 X := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  all_goals omega

theorem card_of_lieModel_psl32 (h : LieModel X .PSL 3 2 1) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two (h.statedClassicalModel (by decide))

theorem card_of_lieModel_psl42 (h : LieModel X .PSL 4 2 1) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two (h.statedClassicalModel (by decide))

theorem card_of_lieModel_psu331 (h : LieModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (h.statedClassicalModel (by decide))

theorem card_of_hatA6 (h : Group.IsPerfect X ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), h3,
    Nat.card_congr e.toEquiv, C489.card_alt6]

end Transport

theorem psl2_card_ne (n : ℕ) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 20160 ∧
      2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 1080 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 6048 := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num
  · have h1 : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 1023 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 1024 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have h3 : 32 * 1023 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end T4213

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem nonempty_modO2_equiv : Nonempty (ModO2 (perfectCore (L ⊓ H)) ≃* ModO2 L) :=
  T4213.nonempty_modO2_equiv ((perfectCore_le _).trans inf_le_left) c.L_le

theorem type_of_case1
    (h1 : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    ∃ n : ℕ, 2 ≤ n ∧ LieModel (ModO2 L) .PSL 2 2 n ∧
      Nat.card (ModO2 L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨n, hpsl, -⟩ := h1
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  have h := T4213.isPSL_of_mulEquiv e hpsl
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, h1, -, h2, -⟩, -⟩ := hpsl
    by_contra hn
    have h1' : n = 1 := by omega
    subst h1'
    exact h2 rfl
  exact ⟨n, hn, Or.inl ⟨by decide, h⟩, C489.card_of_isPSL_two_two h⟩

theorem type_of_case2
    (h2 : C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    (LieModel (ModO2 L) .PSL 3 2 1 ∧ Nat.card (ModO2 L) = 168) ∨
      (LieModel (ModO2 L) .PSL 4 2 1 ∧ Nat.card (ModO2 L) = 20160) := by
  obtain ⟨m, hm, hpsl, -⟩ := h2
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  have h := T4213.isPSL_of_mulEquiv e hpsl
  have hL : LieModel (ModO2 L) .PSL m 2 1 := Or.inl ⟨by decide, h⟩
  rcases hm with rfl | rfl
  · exact Or.inl ⟨hL, T4213.card_of_lieModel_psl32 hL⟩
  · exact Or.inr ⟨hL, T4213.card_of_lieModel_psl42 hL⟩

theorem equiv_alt_of_isAltBlockType {m : ℕ} (h : IsAltBlockType (perfectCore (L ⊓ H)) m) :
    Nonempty (ModO2 L ≃* alternatingGroup (Fin m)) := by
  obtain ⟨-, α, hα, hker, -⟩ := h
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  exact ⟨e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα))⟩

theorem equiv_alt7_of_isExcA7Block (h : CFSG.Quasithin.IsExcA7Block (perfectCore (L ⊓ H))) :
    Nonempty (ModO2 L ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := h
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  exact ⟨e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα))⟩

theorem hat_of_isHatA6Block (h : CFSG.Quasithin.IsHatA6Block (perfectCore (L ⊓ H))) :
    Group.IsPerfect (ModO2 L) ∧ Nat.card (Subgroup.center (ModO2 L)) = 3 ∧
      Nonempty (ModO2 L ⧸ Subgroup.center (ModO2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨-, ⟨-, h3, ⟨e'⟩⟩, -⟩ := h
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  refine ⟨c.hyp421.quasisimple.1, ?_, ?_⟩
  · rw [← h3]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  · exact ⟨(QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).trans e'⟩

theorem lieModel_of_isG2Block (h : CFSG.Quasithin.IsG2Block (perfectCore (L ⊓ H))) :
    LieModel (ModO2 L) .PSU 3 3 1 := by
  obtain ⟨-, hU, -⟩ := h
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  exact Or.inl ⟨by decide, T4213.isPSU_of_mulEquiv e hU⟩

end Conf4212

end CFSG.Quasithin.H13.Ch4
