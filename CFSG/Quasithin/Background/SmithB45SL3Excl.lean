module

public import CFSG.Quasithin.Background.SmithB45SL3Move
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Outer

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply
  natCard_eq_two_pow_finrank)
open CFSG.Semidihedral.Principal (repMultiplicity)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep repFixedSpace)
open CFSG.Quasithin.B42SL3 (innerPart mem_innerPart exists_lift_of_inner elem_mul_self)
open CFSG.QuasithinUnique.K1 (stdAut descendAut_stdAut)
open scoped MatrixGroups Matrix

section Counting

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

omit [Fintype F] [CharP F 2] in
theorem isPGroup_two : IsPGroup 2 ↥A := fun a =>
  ⟨1, by rw [pow_one, pow_two]; exact elem_mul_self A a⟩

theorem card_le_four_mul_innerPart (hf : 2 ≤ f) (hNat : Nat.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) :
    Nat.card ↥A ≤ 4 * Nat.card ↥(innerPart ρ hker A hA) := by
  classical
  have := B42SL3.isElementaryAbelian_range ρ hker A hA
  obtain ⟨-, h2, -, -⟩ := elementary_automorphism_rank_bound hf hNat
    (normalizerHom ρ hker A hA).range
  set Φ := normalizerHom ρ hker A hA with hΦ
  set Inn := (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range with hInn
  have hinj := B42SL3.normalizerHom_injective ρ hker A hA hirr
  have hmap : Φ.range ⊓ Inn = (innerPart ρ hker A hA).map Φ := by
    ext x
    constructor
    · rintro ⟨⟨a, rfl⟩, hx⟩
      exact ⟨a, hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, ha⟩
  have hmul := Subgroup.relIndex_mul_card (H := Φ.range ⊓ Inn) (K := Φ.range)
  have hinf : Φ.range ⊓ Inn ⊓ Φ.range = Φ.range ⊓ Inn := inf_eq_left.mpr inf_le_left
  rw [hinf] at hmul
  have hcardΦ : Nat.card Φ.range = Nat.card ↥A :=
    (Nat.card_congr (Equiv.ofInjective Φ hinj)).symm
  have hcardI : Nat.card ↥(Φ.range ⊓ Inn) = Nat.card ↥(innerPart ρ hker A hA) := by
    rw [hmap]
    exact Subgroup.card_map_of_injective hinj
  rw [← hcardΦ, ← hmul, hcardI]
  exact Nat.mul_le_mul_right _ h2

omit [Fintype F] [CharP F 2] [CFSG.IsElementaryAbelian 2 A] in
theorem mem_innerPart_of_eq_rep (a : ↥A) (s : SL(3, F))
    (h : ∀ u, (a : U ≃ₗ[ZMod 2] U) u = ρ s u) : a ∈ innerPart ρ hker A hA := by
  rw [mem_innerPart]
  refine ⟨proj 3 F s, ?_⟩
  ext p
  obtain ⟨x, rfl⟩ := proj_surjective 3 F p
  obtain ⟨y, hy, hpy⟩ := exists_induced ρ hker A hA a x
  rw [MulAut.conj_apply, ← hpy, ← map_inv, ← map_mul, ← map_mul]
  have hρ : ρ y = ρ (s * x * s⁻¹) := by
    refine LinearMap.ext fun u => ?_
    obtain ⟨w, rfl⟩ : ∃ w, (a : U ≃ₗ[ZMod 2] U) w = u :=
      ⟨(a : U ≃ₗ[ZMod 2] U).symm u, LinearEquiv.apply_symm_apply _ _⟩
    rw [← hy w, h, h, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ s⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hk : (s * x * s⁻¹)⁻¹ * y ∈ scalars 3 F := by
    refine hker _ ?_
    rw [map_mul, hρ, ← map_mul, inv_mul_cancel, map_one]
  have h1 : proj 3 F ((s * x * s⁻¹)⁻¹ * y) = 1 := proj_eq_one_iff.mpr hk
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end Counting

section Excl

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

omit [Fintype F] [CharP F 2] [CFSG.IsElementaryAbelian 2 A] in
theorem card_fix_eq :
    Nat.card {u : U // ∀ a ∈ A, a u = u} = 2 ^ Module.finrank (ZMod 2) (fixOf A) := by
  rw [← natCard_eq_two_pow_finrank]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => mem_fixOf.symm)

omit [Fintype F] [CharP F 2] [Finite U] [CFSG.IsElementaryAbelian 2 A] in
theorem fixOf_le_repFixedSpace {t₁ t₂ : SL(3, F)}
    (h₁ : ∃ b ∈ A, ∀ u, b u = ρ t₁ u) (h₂ : ∃ b ∈ A, ∀ u, b u = ρ t₂ u) :
    fixOf A ≤ repFixedSpace ρ {t₁, t₂} := by
  intro u hu s hs
  rcases hs with rfl | hs
  · obtain ⟨b, hb, hbt⟩ := h₁
    rw [← hbt]
    exact mem_fixOf.mp hu b hb
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    obtain ⟨b, hb, hbt⟩ := h₂
    rw [← hbt]
    exact mem_fixOf.mp hu b hb

theorem codim_data (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f) (hirr : ρ.IsIrreducible)
    {mA k : ℕ} (hmA : Nat.card ↥A = 2 ^ mA) (hk : Nat.card ↥(innerPart ρ hker A hA) = 2 ^ k) :
    k ≤ mA ∧ mA ≤ k + 2 ∧ k ≤ 2 * f ∧ (k < mA → k ≤ f) ∧
      (1 ≤ k → Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) +
        Module.finrank (ZMod 2) (fixOf A) ≤ Module.finrank (ZMod 2) U) ∧
      (k < mA → Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) +
        2 * Module.finrank (ZMod 2) (fixOf A) ≤ 2 * Module.finrank (ZMod 2) U) := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  set I := innerPart ρ hker A hA with hI
  have hpow : ∀ {x y : ℕ}, 2 ^ x ≤ 2 ^ y → x ≤ y := fun h =>
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hkA : k ≤ mA := by
    apply hpow
    rw [← hk, ← hmA]
    exact Subgroup.card_le_card_group I
  have hAk : mA ≤ k + 2 := by
    apply hpow
    rw [← hmA, pow_add, hk.symm]
    calc Nat.card ↥A ≤ 4 * Nat.card ↥I := card_le_four_mul_innerPart ρ hker A hA hf hNat hirr
      _ = Nat.card ↥I * 2 ^ 2 := by ring
  have hk2f : k ≤ 2 * f := by
    apply hpow
    rw [← hk]
    exact B42SL3.card_innerPart_le ρ hker A hA hf hNat hirr
  have hout : k < mA → ∃ a₀ : ↥A, a₀ ∉ I := by
    intro hlt
    by_contra hcon
    push Not at hcon
    have : Nat.card ↥A ≤ Nat.card ↥I :=
      Nat.card_le_card_of_injective (fun a => (⟨a, hcon a⟩ : ↥I))
        (fun a b hab => congrArg Subtype.val hab)
    rw [hmA, hk] at this
    have := hpow this
    omega
  refine ⟨hkA, hAk, hk2f, fun hlt => ?_, fun hk1 => ?_, fun hlt => ?_⟩
  · obtain ⟨a₀, ha₀⟩ := hout hlt
    apply hpow
    rw [← hk, ← hNat]
    exact card_innerPart_le_of_outer ρ hker A hA (by omega) hNat hirr a₀ ha₀
  ·
    have hI1 : 1 < Nat.card ↥I := by
      rw [hk]
      exact Nat.one_lt_two_pow (by omega)
    have : Nontrivial ↥I := Finite.one_lt_card_iff_nontrivial.mp hI1
    obtain ⟨⟨b₀, hb₀I⟩, hb₀1⟩ := exists_ne (1 : ↥I)
    obtain ⟨t, ht2, htρ⟩ := exists_lift_of_inner ρ hker A hA (by omega) hNat hirr b₀ hb₀I
    have ht1 : t ≠ 1 := by
      intro h1
      apply hb₀1
      apply Subtype.ext
      apply Subtype.ext
      refine LinearEquiv.ext fun u => ?_
      rw [htρ u, h1, map_one]
      rfl
    have h1 := finrank_range_add_finrank_fixOf_le (A := A) b₀.2
    have heqmap : (b₀ : U ≃ₗ[ZMod 2] U).toLinearMap = ρ t := LinearMap.ext htρ
    rw [heqmap, B42SL3.finrank_range_involution ρ ht1 ht2] at h1
    exact h1
  · obtain ⟨a₀, ha₀⟩ := hout hlt
    obtain ⟨t, ht, hrk⟩ := B42SL3.exists_transvection_of_outer ρ hker A hA hf hNat a₀ ha₀
    rw [B42SL3.finrank_range_involution ρ (ne_one_of_isTransvection ht)
      (isTransvection_sq ht)] at hrk
    have h1 := finrank_range_add_finrank_fixOf_le (A := A) a₀.2
    omega

include hker hA in
theorem natural_or_row (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f) (hirr : ρ.IsIrreducible)
    (hA1 : A ≠ ⊥) (h2F : Nat.card U ≤ Nat.card ↥A ^ 2 * Nat.card {u : U // ∀ a ∈ A, a u = u})
    {n : ℕ} (bas : Module.Basis (Fin n) (ZMod 2) U) {a b : Fin f → Bool}
    (hne : a ≠ zeros f ∨ b ≠ zeros f)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (hW₀ : W₀.toRepresentation.IsIrreducible)
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b)))
    (hO : ∀ c ∈ pairOrbit f (a, b), 0 < repMultiplicity
      (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)))
      (matRep (tensorRep (F := F) F c.1 c.2))) :
    (cntS a b = 1 ∧ cntH a b = 0) ∨
      (cntS a b = 2 ∧ cntH a b = 0 ∧ (pairOrbit f (a, b)).card < f) := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  set O := pairOrbit f (a, b) with hOdef
  set R := Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) with hRdef
  have hdim : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  have hsum := sum_rank_le hF (by omega) ρ bas O hO (up3 0 0 1)
  have htypeO : ∀ c ∈ O, cntS c.1 c.2 = cntS a b ∧ cntH c.1 c.2 = cntH a b := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨card_feat_iterate (fun x : Bool × Bool => x.1 ≠ x.2) (a, b) s,
      card_feat_iterate (fun x : Bool × Bool => x.1 = true ∧ x.2 = true) (a, b) s⟩
  suffices key : 4 * f ≤ R → (4 * f + 1 ≤ R ∨ (O.card = f ∧
      ((cntS a b = 2 ∧ cntH a b = 0) ∨ (cntS a b = 0 ∧ cntH a b = 1)))) → False by
    rcases label_cases' (by omega) a b hne _ hdim hsum with hnat | ⟨hS, hH, hR4, hfo⟩ |
      ⟨hS, hH, hof, hR4⟩ | hR5
    · exact Or.inl hnat
    · by_cases hlt : O.card < f
      · exact Or.inr ⟨hS, hH, hlt⟩
      · exfalso
        have hof : O.card = f := le_antisymm (card_pairOrbit_le _) (not_lt.mp hlt)
        refine key (by rw [← hof]; exact hR4) (Or.inr ⟨hof, Or.inl ⟨hS, hH⟩⟩)
    · exact absurd (key hR4 (Or.inr ⟨hof, Or.inr ⟨hS, hH⟩⟩)) id
    · exact absurd (key (by omega) (Or.inl hR5)) id
  intro hR4 hspec
  obtain ⟨mA, hmA⟩ := IsPGroup.iff_card.mp (isPGroup_two A)
  set I := innerPart ρ hker A hA with hI
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((isPGroup_two A).to_subgroup I)
  set nU := Module.finrank (ZMod 2) U with hnU
  set c := Module.finrank (ZMod 2) (fixOf A) with hc
  have hcU : c ≤ nU := Submodule.finrank_le _
  have h2F' : nU ≤ 2 * mA + c := by
    rw [natCard_eq_two_pow_finrank U, hmA, card_fix_eq A, ← pow_mul, ← pow_add] at h2F
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2F
    omega
  have hmA1 : 1 ≤ mA := by
    by_contra h0
    push Not at h0
    have hm0 : mA = 0 := by omega
    rw [hm0, pow_zero, Subgroup.card_eq_one] at hmA
    exact hA1 hmA
  obtain ⟨hkA, hAk, hk2f, hkf, hinner, houter⟩ := codim_data ρ hker A hA hf hF hirr hmA hk
  have hroot : O.card = f → ((cntS a b = 2 ∧ cntH a b = 0) ∨ (cntS a b = 0 ∧ cntH a b = 1)) →
      (∃ t₁ ∈ liftSub ρ hker A hA, ∃ t₂ ∈ liftSub ρ hker A hA, IsRootPair t₁ t₂) →
      5 * f + c ≤ nU := by
    rintro hof htype ⟨t₁, ht₁, t₂, ht₂, hpair⟩
    have htype' : ∀ c ∈ O, (cntS c.1 c.2 = 2 ∧ cntH c.1 c.2 = 0) ∨
        (cntS c.1 c.2 = 0 ∧ cntH c.1 c.2 = 1) := by
      intro c hc
      rw [(htypeO c hc).1, (htypeO c hc).2]
      exact htype
    have h5 := five_mul_card_le_codim hF (by omega) ρ bas O hO htype' hpair
    have hle : fixOf A ≤ repFixedSpace ρ {t₁, t₂} := by
      refine fixOf_le_repFixedSpace ρ A ?_ ?_
      · obtain ⟨-, b, -, hbt⟩ := ht₁
        exact ⟨b, (b : ↥A).2, hbt⟩
      · obtain ⟨-, b, -, hbt⟩ := ht₂
        exact ⟨b, (b : ↥A).2, hbt⟩
    have h6 := Submodule.finrank_mono hle
    have h7 := Submodule.finrank_le (repFixedSpace ρ {t₁, t₂})
    rw [hof] at h5
    omega
  have hpow : ∀ {x y : ℕ}, x < y → 2 ^ x < 2 ^ y := fun h =>
    Nat.pow_lt_pow_right (by norm_num) h
  rcases Nat.lt_or_ge k mA with hlt | hge
  · have hkf' := hkf hlt
    have hR2 := houter hlt
    rcases Nat.lt_or_ge (k + 1) mA with hlt2 | hge2
    ·
      have hmAk : mA = k + 2 := by omega
      have hfield : ∃ a₁ : ↥A, IsFieldType ρ hker A hA a₁ := by
        refine exists_field_of_card ρ hker A hA hirr ?_
        rw [hmA, hk, hmAk, pow_add]
        have : 0 < 2 ^ k := Nat.two_pow_pos k
        omega
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      ·
        subst hk0
        rcases Nat.lt_or_ge 2 f with hf3 | hf2
        · omega
        have hf2' : f = 2 := by omega
        rcases hspec with hR5 | ⟨hof, htype⟩
        · omega
        ·
          obtain ⟨a₁, M, σ, hσ1, hΦ⟩ := hfield
          obtain ⟨j, hj⟩ := CFSG.QuasithinUnique.Setup.X7Sec.exists_frob_eq hF (by omega) σ
          have hint : ∀ x u, (a₁ : U ≃ₗ[ZMod 2] U) (ρ x u) =
              ρ (stdAut M σ 0 x) ((a₁ : U ≃ₗ[ZMod 2] U) u) :=
            fun x u => intertwines_psi ρ (normalizerHom ρ hker A hA a₁) (stdAut M σ 0)
              (by rw [descendAut_stdAut, hΦ, pow_zero, mul_one]) (a₁ : U ≃ₗ[ZMod 2] U)
              (exists_induced ρ hker A hA a₁) x u
          have hmove := not_equiv_comp_of_shift_ne hF (by omega) M σ hj a b
            (shift_ne_of_card_eq hF a b hof hσ1 hj)
          have hrk := card_le_rank_of_moved ρ bas W₀ hW₀ e₀ (a₁ : U ≃ₗ[ZMod 2] U)
            (stdAut M σ 0) hint hmove
          rw [card_TIdx_eq] at hrk
          have h8 : 8 ≤ 3 ^ cntS a b * 8 ^ cntH a b := by
            rcases htype with ⟨hS, hH⟩ | ⟨hS, hH⟩ <;> rw [hS, hH] <;> norm_num
          have h1 := finrank_range_add_finrank_fixOf_le (A := A) a₁.2
          omega
      ·
        have hR1 := hinner hk1
        rcases Nat.lt_or_ge 2 f with hf3 | hf2
        · nlinarith
        have hf2' : f = 2 := by omega
        subst hf2'
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · omega
        ·
          have hk2' : k = 2 := by omega
          rcases hspec with hR5 | ⟨hof, htype⟩
          · omega
          · obtain ⟨a₁, ha₁⟩ := hfield
            have hrp := exists_rootPair_of_field ρ hker A hA (by omega) hNat hirr ha₁
              (by rw [hk, hNat, hk2'])
            have := hroot hof htype hrp
            omega
    ·
      have hmAk : mA = k + 1 := by omega
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · omega
      · have hR1 := hinner hk1
        omega
  ·
    have hmAk : mA = k := by omega
    have hR1 := hinner (by omega)
    rcases hspec with hR5 | ⟨hof, htype⟩
    · omega
    · rcases Nat.lt_or_ge k (2 * f) with hk2 | hk2
      · omega
      · have hk2' : k = 2 * f := by omega
        have hcard : Nat.card F < Nat.card ↥I := by
          rw [hk, hNat, hk2']
          exact hpow (by omega)
        have hrp := exists_rootPair_of_card ρ hker A hA (by omega) hNat hirr hcard
        have := hroot hof htype hrp
        omega

include hker hA in
theorem five_mul_le_four_mul_codim (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (hirr : ρ.IsIrreducible) (hsd : ¬ Nonempty (ρ.Equiv ρ.dual)) (hA1 : A ≠ ⊥)
    {n : ℕ} (bas : Module.Basis (Fin n) (ZMod 2) U) {a b : Fin f → Bool}
    (hS : cntS a b = 2) (hH : cntH a b = 0) (hfo : f ≤ 2 * (pairOrbit f (a, b)).card)
    (hO : ∀ c ∈ pairOrbit f (a, b), 0 < repMultiplicity
      (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)))
      (matRep (tensorRep (F := F) F c.1 c.2)))
    {mA : ℕ} (hmA : Nat.card ↥A = 2 ^ mA) :
    5 * mA ≤ 4 * (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (fixOf A)) := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  set O := pairOrbit f (a, b) with hOdef
  set R := Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) with hRdef
  have htypeO : ∀ c ∈ O, cntS c.1 c.2 = 2 ∧ cntH c.1 c.2 = 0 := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨(card_feat_iterate (fun x : Bool × Bool => x.1 ≠ x.2) (a, b) s).trans hS,
      (card_feat_iterate (fun x : Bool × Bool => x.1 = true ∧ x.2 = true) (a, b) s).trans hH⟩
  have hR : 4 * O.card ≤ R := by
    have hsum := sum_rank_le hF (by omega) ρ bas O hO (up3 0 0 1)
    have h4 : ∀ c ∈ O, 4 ≤ (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank := by
      intro c hc
      have h := dim_le_two_mul_rank_tensorRep (F := F) c.1 c.2
      rw [(htypeO c hc).1, (htypeO c hc).2] at h
      norm_num at h
      omega
    calc 4 * O.card = ∑ _c ∈ O, 4 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum h4
      _ ≤ R := hsum
  set I := innerPart ρ hker A hA with hI
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((isPGroup_two A).to_subgroup I)
  set nU := Module.finrank (ZMod 2) U with hnU
  set c := Module.finrank (ZMod 2) (fixOf A) with hc
  have hcU : c ≤ nU := Submodule.finrank_le _
  have hmA1 : 1 ≤ mA := by
    by_contra h0
    push Not at h0
    have hm0 : mA = 0 := by omega
    rw [hm0, pow_zero, Subgroup.card_eq_one] at hmA
    exact hA1 hmA
  obtain ⟨hkA, -, hk2f, hkf, hinner, houter⟩ := codim_data ρ hker A hA hf hF hirr hmA hk
  have he : mA ≤ k + 1 := by
    have h := B42SL3.card_le_two_mul_innerPart ρ hker A hA (by omega) hF hirr hsd
    rw [hmA, hk] at h
    have h2 : 2 ^ mA ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  rcases Nat.lt_or_ge k mA with hlt | hge
  · have hmAk : mA = k + 1 := by omega
    have hkf' := hkf hlt
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · have := houter hlt
      omega
    · have := hinner hk1
      omega
  · have hmAk : mA = k := by omega
    have hR1 := hinner (by omega)
    rcases Nat.lt_or_ge f k with hfk | hfk
    ·
      have hcard : Nat.card F < Nat.card ↥I := by
        rw [hk, hNat]
        exact Nat.pow_lt_pow_right (by norm_num) hfk
      obtain ⟨t₁, ht₁, t₂, ht₂, hpair⟩ :=
        exists_rootPair_of_card ρ hker A hA (by omega) hNat hirr hcard
      have h5 := five_mul_card_le_codim hF (by omega) ρ bas O hO
        (fun c hc => Or.inl (htypeO c hc)) hpair
      have hle : fixOf A ≤ repFixedSpace ρ {t₁, t₂} := by
        refine fixOf_le_repFixedSpace ρ A ?_ ?_
        · obtain ⟨-, b, -, hbt⟩ := ht₁
          exact ⟨b, (b : ↥A).2, hbt⟩
        · obtain ⟨-, b, -, hbt⟩ := ht₂
          exact ⟨b, (b : ↥A).2, hbt⟩
      have h6 := Submodule.finrank_mono hle
      have h7 := Submodule.finrank_le (repFixedSpace ρ {t₁, t₂})
      omega
    · omega

end Excl

end B45SL3

end CFSG.Quasithin
