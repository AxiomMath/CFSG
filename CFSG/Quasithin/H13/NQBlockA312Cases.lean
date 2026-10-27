module

public import CFSG.Quasithin.H13.NQBlockRadicalR2Max
public import CFSG.Quasithin.H13.NQBlockEscapingPair
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

theorem isQuasisimple_of_isSimpleGroup_of_isPerfect {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : CFSG.IsQuasisimple X :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (exists_mul_ne_mul_of_isPerfect (Q := X))).1

theorem le_pCore_two_of_isPGroup {X : Type*} [Group X] {V : Subgroup X} [V.Normal]
    (hV : IsPGroup 2 V) : V ≤ CFSG.pCore 2 X := by
  exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hV

theorem isQuasisimple_quotient_pCore_of_ext {X : Type*} [Group X] [Finite X] {V : Subgroup X}
    [V.Normal] (hV : IsPGroup 2 V) (hY : CFSG.IsQuasisimple (X ⧸ V)) :
    CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVP := le_pCore_two_of_isPGroup hV
  set φ : X ⧸ V →* X ⧸ CFSG.pCore 2 X := QuotientGroup.map V (CFSG.pCore 2 X) (MonoidHom.id X)
    hVP with hφdef
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(x : X ⧸ V), rfl⟩
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hY hsurj ?_
  by_contra hall
  push Not at hall
  have htop : ∀ x : X, x ∈ CFSG.pCore 2 X := fun x => by
    have := hall (x : X ⧸ V)
    exact (QuotientGroup.eq_one_iff x).mp this
  have hX2 : IsPGroup 2 X := fun x => by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)) ⟨x, htop x⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hY2 : IsPGroup 2 (X ⧸ V) := hX2.to_quotient V
  have := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have := hY.1
  exact Group.IsPerfect.not_isNilpotent (X ⧸ V) hY2.isNilpotent

theorem isQuasisimple_quotient_pCore {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  let e : X ⧸ (⊥ : Subgroup X) ≃* X := QuotientGroup.quotientBot
  exact isQuasisimple_quotient_pCore_of_ext (V := ⊥) (IsPGroup.of_bot)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hX)

theorem isPGroup_of_isE2 {V : Type} [Group V] {n : ℕ} (h : IsE2 n V) : IsPGroup 2 V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h
  intro v
  refine ⟨1, ?_⟩
  rw [pow_one]
  have h1 := pow_prime_eq_one_of_elem (e v)
  rwa [← map_pow, MulEquiv.map_eq_one_iff] at h1

theorem isPGroup_of_isExtraspecial2 {V : Type} [Group V] {m : ℕ} (h : IsExtraspecial2 m V) :
    IsPGroup 2 V :=
  IsPGroup.of_card h.2

theorem isPGroup_of_isZ4Cubed {V : Type} [Group V] (h : IsZ4Cubed V) : IsPGroup 2 V := by
  obtain ⟨e⟩ := h
  intro v
  refine ⟨2, e.injective ?_⟩
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  funext i
  have h4 : ∀ x : ZMod 4, (2 ^ 2 : ℕ) • x = 0 := by decide
  exact h4 _

theorem isPGroup_of_isZ4StarExtra2 {V : Type} [Group V] (h : IsZ4StarExtra2 V) :
    IsPGroup 2 V := by
  obtain ⟨Z, E, hZ4, -, hE, hZc, hZE, -⟩ := h
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by rw [hZ4]; norm_num)
  have hE2 : IsPGroup 2 E := isPGroup_of_isExtraspecial2 hE
  have hZn : Z.Normal := ⟨fun n hn g => by
    have h1 := mem_center_iff.mp (hZc hn) g
    rw [h1, mul_inv_cancel_right]
    exact hn⟩
  intro v
  have hv : v ∈ Z ⊔ E := hZE ▸ mem_top v
  obtain ⟨z, hz, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
  obtain ⟨a, ha⟩ := hZ2 ⟨z, hz⟩
  obtain ⟨b, hb⟩ := hE2 ⟨e, he⟩
  have ha' : z ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hb' : e ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hcomm : Commute z e := (mem_center_iff.mp (hZc hz) e).symm
  refine ⟨a + b, ?_⟩
  rw [hcomm.mul_pow, pow_add, pow_mul, ha', one_pow, one_mul, mul_comm, pow_mul, hb', one_pow]

theorem isSimpleGroup_of_isAlt {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n) (h : IsAlt n X) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have := alternatingGroup.isSimpleGroup (α := Fin n)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  exact e.isSimpleGroup

theorem isSimpleGroup_of_isPSL {X : Type} [Group X] {n p e : ℕ} (h : IsPSL n p e X) :
    IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity X n p e h).2

theorem isSimpleGroup_of_isSz {X : Type} [Group X] {e : ℕ} (h : IsSz e X) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 e h).2

theorem isSimpleGroup_of_isM22 {X : Type} [Group X]
    (h : IsSporadic .M22 X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  exact e.isSimpleGroup

theorem isSimpleGroup_of_isM24 {X : Type} [Group X]
    (h : IsSporadic .M24 X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  exact e.isSimpleGroup

theorem isQuasisimple_of_isSL2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : IsSL2 p X) : CFSG.IsQuasisimple X := by
  obtain ⟨e⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have h1 := CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (K := ZMod p)
    (by rw [Nat.card_zmod]; omega)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h1

theorem a312Case_quasisimple_or_linear
    {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} [hBp : Group.IsPerfect ↥B]
    (hcase : A312Case B L) :
    CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) ∨
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧ (IsPSL 3 p 1 ↥L ∨ IsSL3 p ↥L) := by
  classical
  have hext : ∀ (V : Subgroup ↥B) [V.Normal], IsPGroup 2 V → CFSG.IsQuasisimple (↥B ⧸ V) →
      CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := fun V _ hV hq =>
    isQuasisimple_quotient_pCore_of_ext hV hq
  have hextS : ∀ (V : Subgroup ↥B) [V.Normal], IsPGroup 2 V → IsSimpleGroup (↥B ⧸ V) →
      CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := fun V _ hV hs =>
    hext V hV (isQuasisimple_of_isSimpleGroup_of_isPerfect)
  have hselfQ : CFSG.IsQuasisimple ↥B → CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) :=
    isQuasisimple_quotient_pCore
  have hselfS : IsSimpleGroup ↥B → CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := fun hs =>
    hselfQ (isQuasisimple_of_isSimpleGroup_of_isPerfect)
  have hmodS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) →
      CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := fun hs =>
    isQuasisimple_of_isSimpleGroup_of_isPerfect
  unfold A312Case at hcase
  by_cases h10 : A312C10 B L
  · obtain ⟨p, hp, hp3, -, hL⟩ := h10
    exact Or.inr ⟨p, hp, hp3, hL⟩
  left
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨n, hn⟩, -⟩ := h
    exact hmodS (isSimpleGroup_of_isPSL hn)
  ·
    obtain ⟨f, hf, -⟩ := h
    exact hmodS (isSimpleGroup_of_isSz hf)
  ·
    exact hmodS (isSimpleGroup_of_isPSL h.1)
  ·
    exact hmodS (isSimpleGroup_of_isPSL h.1)
  ·
    rcases h.1 with h5 | h3
    · exact hselfS (isSimpleGroup_of_isAlt (by norm_num) h5)
    · exact hselfS (isSimpleGroup_of_isPSL h3)
  ·
    rcases h with ⟨h6, -⟩ | ⟨h6, -⟩
    · exact hselfS (isSimpleGroup_of_isAlt (by norm_num) h6)
    · exact hselfQ h6.1
  ·
    rcases h with ⟨p, -, -, hB, -⟩ | ⟨h5, -⟩
    · exact hselfS (isSimpleGroup_of_isPSL hB)
    · exact hselfS (isSimpleGroup_of_isAlt (by norm_num) h5)
  ·
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩
    · exact hselfQ (isQuasisimple_of_isSL2 hp hp3 hB)
    · exact hselfS (isSimpleGroup_of_isAlt (by norm_num) h6)
    · exact hselfQ h6.1
  ·
    exact absurd h h10
  ·
    exact hselfS (isSimpleGroup_of_isAlt (by norm_num) h.1)
  ·
    rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> obtain ⟨V, hVn, hV, hY⟩ := h
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
    · exact hext V (isPGroup_of_isE2 hV) hY.1
  ·
    rcases h.1 with hB | hB | hB | hB | hB | hB | hB
    · exact hselfS (isSimpleGroup_of_isM22 hB)
    · exact hselfS (isSimpleGroup_of_isPSL hB)
    all_goals obtain ⟨V, hVn, hV, hY⟩ := hB
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isPSL hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isPSL hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
  ·
    rcases h.1 with hB | hB | hB | hB <;> obtain ⟨V, hVn, hV, hY⟩ := hB
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isPSL hY)
    · exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isPSL hY)
    · exact hextS V (isPGroup_of_isExtraspecial2 hV) (isSimpleGroup_of_isPSL hY)
    · exact hext V (isPGroup_of_isE2 hV) hY.1
  ·
    exact hselfS (isSimpleGroup_of_isAlt (by norm_num) h.1)
  ·
    obtain ⟨⟨V, hVn, hV, hY⟩, -⟩ := h
    exact hextS V (isPGroup_of_isExtraspecial2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
  ·
    rcases h.2 with hB | hB | hB | hB | hB | hB
    · obtain ⟨V, hVn, hV, hY⟩ := hB
      exact hext V (isPGroup_of_isExtraspecial2 hV) hY.1
    · obtain ⟨V, hVn, hV, hY⟩ := hB
      exact hextS V (isPGroup_of_isE2 hV) (isSimpleGroup_of_isM24 hY)
    · exact hmodS (isSimpleGroup_of_isAlt (by norm_num) hB)
    · exact hB.1
    · exact hmodS (isSimpleGroup_of_isPSL hB)
    · exact hmodS (isSimpleGroup_of_isPSL hB)
  ·
    rcases h.1 with hB | hB <;> obtain ⟨V, hVn, hV, hY⟩ := hB
    · exact hextS V (isPGroup_of_isZ4StarExtra2 hV) (isSimpleGroup_of_isAlt (by norm_num) hY)
    · exact hextS V (isPGroup_of_isZ4Cubed hV) (isSimpleGroup_of_isPSL hY)
  ·
    rcases h.1 with hB | hB <;> obtain ⟨V, hVn, hV, hY⟩ := hB
    · exact hextS V (isPGroup_of_isExtraspecial2 hV) (isSimpleGroup_of_isPSL hY)
    · exact hext V (isPGroup_of_isE2 hV) hY.1
  ·
    rcases h.1 with hB | hB
    · exact hmodS (isSimpleGroup_of_isAlt (by norm_num) hB)
    · exact hmodS (isSimpleGroup_of_isPSL hB)

end CFSG.Quasithin.H13.NQBlock
