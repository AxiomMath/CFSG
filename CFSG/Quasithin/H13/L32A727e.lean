module

public import CFSG.Quasithin.H13.L32A727d
public import CFSG.Quasithin.H13.L32A727Sk

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_27_of (h714 : Thm14_7_14) (h79 : Lemma14_7_9) (h78 : Lemma14_7_8)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (hB2 : Input14727B2) :
    Lemma14_7_27 := by
  intro G _ _ T L V H S
  suffices key : ∀ n : ℕ, ∀ H : Subgroup G, Nat.card H = n → Setting147 G T L V H →
      R727.Concl T L V H from key _ H rfl S
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro H hn S
  have ih : ∀ H₀ : Subgroup G, H₀ < H → Setting147 G T L V H₀ → R727.Concl T L V H₀ :=
    fun H₀ hlt S₀ => ihn _ (hn ▸ Subgroup.card_lt_of_lt hlt) H₀ rfl S₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hc
  simp only [R727.Concl, not_or] at hc
  obtain ⟨hP1, hPL⟩ := hc
  set P := CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) with hP
  have hP3 : IsPGroup 3 ↥P := CFSG.pCore_isPGroup
  have : P.Normal := CFSG.pCore_normal
  obtain ⟨X, hX, hXf⟩ := exists_isSupercritical_faithful (P := ↥P) (p := 3) (by norm_num) hP3
  have : X.Characteristic := hX.characteristic
  set K := X.map P.subtype with hK
  have hKn : K.Normal := normal_map_of_characteristic X
  have hK3 : IsPGroup 3 ↥K := (hP3.to_subgroup X).map P.subtype
  have hexp : ∀ x ∈ K, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg Subtype.val (hX.pow_eq_one x hx)
  have hKP : K ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcent : ∀ x ∈ P, (∀ y ∈ K, x * y = y * x) → orderOf x = 3 → x ∈ K := by
    intro x hx hc ho
    refine ⟨⟨x, hx⟩, hX.mem_of_orderOf_eq ⟨x, hx⟩ ?_ ?_, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hc y ⟨y, hy, rfl⟩).symm
    · rw [Subgroup.orderOf_mk]
      exact ho
  have hKne : K ≠ ⊥ := by
    have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
    intro h
    exact hX.ne_bot hP3 ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h)
  by_cases hKM : R727.pre H K ≤ Subgroup.normalizer (L : Set G)
  · exact R727.false_of_A S h1222 h1332 h1334 h79 h78 hKn hK3 hexp hKP hcent hKne hKM hPL
  have hHe := R727.eq_sup_of_not_le S h1332 h1334 ih hKn hK3 hKM
  have hLP := hB2 G T L V H S X hX hXf hKM hHe
  by_cases hlt : pCoreOf 2 (oTwoUpper (R727.pre H K)) <
      oTwoUpper (R727.pre H K) ⊓ Subgroup.normalizer (L : Set G)
  · exact R727.false_of_B1a S h1332 h79 h714 hKn hK3 hexp hKM hHe hlt
  have hYH : oTwoUpper (R727.pre H K) ≤ H := (oTwoUpper_le _).trans (R727.pre_le K)
  have hHY : H ≤ Subgroup.normalizer (oTwoUpper (R727.pre H K) : Set G) :=
    (R727.le_normalizer_pre hKn).trans (normalizer_le_normalizer_oTwoUpper _)
  have hO2 : pCoreOf 2 (oTwoUpper (R727.pre H K)) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hYH)
      (hHY.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hle0 : pCoreOf 2 (oTwoUpper (R727.pre H K)) ≤
      oTwoUpper (R727.pre H K) ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf (pCoreOf_le 2 _) (hO2.trans ((pCoreOf_le_of_le S.hyp (le_sup_right.trans S.hz.1.1)).trans
      (le_sup_right.trans (R727.l1T_le_M S.hyp h1332))))
  have hle : oTwoUpper (R727.pre H K) ⊓ Subgroup.normalizer (L : Set G) ≤
      pCoreOf 2 (oTwoUpper (R727.pre H K)) :=
    ((lt_or_eq_of_le hle0).resolve_left hlt).symm.le
  exact R727.false_of_B1b S h1222 h1332 h1334 ih hKn hK3 hKP hcent hKne hle hLP

end CFSG.Quasithin.H13.L32A
