module

public import CFSG.RankThree.PartTwo.KFacts.K71Basic
public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem entrywiseFixedGroup_G2_eq_fixedFieldImage [Finite K] (hK : ringChar K = 2)
    (σ : K ≃+* K) : entrywiseFixedGroup Tag.G2 σ = fixedFieldImage Tag.G2 σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup Tag.G2 K σ
  have hT := (even_power_two_Cartan_root_diagonals_inner Tag.G2 (Or.inl rfl) K hK).2.2.2 σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup Tag.G2 σ : Set (ModGL Tag.G2 K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  have hh' : h ∈ torusGroup Tag.G2 K ⊓
      (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) := ⟨hh.1, hh.2.2⟩
  rw [hT] at hh'
  obtain ⟨t, ht, rfl⟩ := hh'
  have hle : torusGroup Tag.G2 (fixSubfield σ) ≤ adjointGroup Tag.G2 (fixSubfield σ) :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨t, hle ht, rfl⟩

theorem baseChangeGL_mem_adjointGroup (σ : K ≃+* K) (g : adjointGroup Tag.G2 (fixSubfield σ)) :
    baseChangeGL (fixSubfield σ).subtype (g : ModGL Tag.G2 (fixSubfield σ)) ∈
      adjointGroup Tag.G2 K := by
  have hJ : baseChangeGL (fixSubfield σ).subtype (g : ModGL Tag.G2 (fixSubfield σ)) ∈
      fixedFieldImage Tag.G2 σ := Subgroup.mem_map_of_mem _ g.2
  exact (Subgroup.mem_inf.mp (fixedFieldImage_le hJ)).1

@[expose] noncomputable def g2Incl (σ : K ≃+* K) :
    adjointGroup Tag.G2 (fixSubfield σ) →* adjointGroup Tag.G2 K :=
  ((baseChangeGL (fixSubfield σ).subtype).comp
    (adjointGroup Tag.G2 (fixSubfield σ)).subtype).codRestrict (adjointGroup Tag.G2 K)
      (baseChangeGL_mem_adjointGroup σ)

theorem coe_g2Incl (σ : K ≃+* K) (g : adjointGroup Tag.G2 (fixSubfield σ)) :
    ((g2Incl σ g : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      baseChangeGL (fixSubfield σ).subtype (g : ModGL Tag.G2 (fixSubfield σ)) :=
  rfl

theorem g2Incl_injective (σ : K ≃+* K) : Function.Injective (g2Incl σ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))

theorem mem_range_g2Incl_iff [Finite K] (hK : ringChar K = 2) (σ : K ≃+* K)
    (h : adjointGroup Tag.G2 K) : h ∈ (g2Incl σ).range ↔ g2FieldHom K σ h = h := by
  have key : g2FieldHom K σ h = h ↔ (h : ModGL Tag.G2 K) ∈ entrywiseFixedGroup Tag.G2 σ := by
    rw [mem_entrywiseFixedGroup]
    constructor
    · intro h1
      exact ⟨h.2, by rw [← coe_g2FieldHom, h1]⟩
    · rintro ⟨-, h1⟩
      exact Subtype.ext (by rw [coe_g2FieldHom, h1])
  rw [key, entrywiseFixedGroup_G2_eq_fixedFieldImage hK σ]
  constructor
  · rintro ⟨g, rfl⟩
    rw [coe_g2Incl]
    exact Subgroup.mem_map_of_mem _ g.2
  · rintro ⟨g, hg, hgh⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hgh⟩

theorem card_fixSubfield_pow [Finite K] (σ : K ≃+* K) :
    Nat.card (fixSubfield σ) ^ orderOf σ = Nat.card K := by
  have heq : fixSubfield σ = CFSG.GH74.GLS.IVK.fixedField σ := by
    ext x
    rw [mem_fixSubfield, CFSG.GH74.GLS.IVK.mem_fixedField_iff]
  rw [heq]
  exact CFSG.GH74.GLS.IVK.fixedField_card_pow σ

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [Finite K]

theorem exists_barCentralizer_mulEquiv_g2 (hK : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K) :
    InducesKindG2 K L a .field ∧
      ∃ σ : K ≃+* K, orderOf σ = 3 ∧ Nat.card (fixSubfield σ) ^ 3 = Nat.card K ∧
        Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃*
          adjointGroup Tag.G2 (fixSubfield σ)) := by
  have hK3 : ringChar K ≠ 3 := by rw [hK]; decide
  obtain ⟨hN, -⟩ := id hout
  set α := inducedAutHom L e ⟨a, hN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one L e hN ha3
  have hnot : ¬ IsInnerAut α := (not_isInnerAut_inducedAutHom_iff L e hN).mpr hout
  refine ⟨inducesKindG2_field L hK3 hK4 ha3 hout e, ?_⟩
  obtain ⟨σ, hσ3, k, hαk⟩ := g2_order_three_field_descent hK3 hK4 hα3 hnot
  have hcard := card_fixSubfield_pow σ
  rw [hσ3] at hcard
  refine ⟨σ, hσ3, hcard, nonempty_barCentralizer_mulEquiv hN e
    ((MulAut.conj k : adjointGroup Tag.G2 K ≃* adjointGroup Tag.G2 K).toMonoidHom.comp
      (g2Incl σ)) ((MulAut.conj k).injective.comp (g2Incl_injective σ)) fun z => ?_⟩
  rw [← hαdef, hαk]
  exact mem_range_conj_comp_iff _ _ _ (mem_range_g2Incl_iff hK σ) z

theorem barCentralizer_mulEquiv_g2 {n : ℕ} (hn : n ≠ 0) (hK : Nat.card K = 2 ^ (3 * n))
    {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K) :
    InducesStdKind L a .field ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ n ∧
        Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃* adjointGroup Tag.G2 k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    obtain ⟨p, hp, m, hpr, hm⟩ := FiniteField.card' K
    have h1 : p ∣ 2 ^ (3 * n) := by
      rw [← hK, Nat.card_eq_fintype_card, hm]
      exact dvd_pow_self p m.ne_zero
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h1)
    subst h2
    exact ringChar.eq K 2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  obtain ⟨hkind, σ, -, hcard, hC⟩ := exists_barCentralizer_mulEquiv_g2 hchar hK4 ha3 hout e
  refine ⟨InducesStdKind.g2 K hK3 hK4 hkind, fixSubfield σ, inferInstance, inferInstance, ?_, hC⟩
  rw [hK, pow_mul'] at hcard
  exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hcard

end Bar

end CFSG.RankThree.PartTwo.KFacts
