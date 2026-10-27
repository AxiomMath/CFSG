module

public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

namespace P22x

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped Matrix

section NatSL2

variable {F : Type} [Field F]

@[expose] def sl2Fix (B : Subgroup ↥(StatedSL 2 F)) : Submodule F (Fin 2 → F) where
  carrier := {v | ∀ g ∈ B,
    (((g : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v}
  add_mem' {v w} hv hw g hg := by rw [Matrix.mulVec_add, hv g hg, hw g hg]
  zero_mem' g _ := Matrix.mulVec_zero _
  smul_mem' c v hv g hg := by rw [Matrix.mulVec_smul, hv g hg]

theorem sl2Fix_bot : sl2Fix (⊥ : Subgroup ↥(StatedSL 2 F)) = ⊤ := by
  refine eq_top_iff.2 fun v _ g hg => ?_
  rw [Subgroup.mem_bot.1 hg]
  simp

theorem sl2_fixed_ne_univ {M : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 1) :
    {v : Fin 2 → F | M *ᵥ v = v} ≠ Set.univ := by
  intro h
  apply hM
  ext i j
  have hv : M *ᵥ Pi.single j 1 = Pi.single j 1 := by
    have : Pi.single j (1 : F) ∈ {v : Fin 2 → F | M *ᵥ v = v} := by rw [h]; trivial
    exact this
  have := congrFun hv i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem sl2Fix_ne_top {B : Subgroup ↥(StatedSL 2 F)} (hB : B ≠ ⊥) : sl2Fix B ≠ ⊤ := by
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
  intro htop
  have hM : (((b : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h
    exact hb1 (Subtype.ext (Subtype.ext (Units.ext h)))
  apply sl2_fixed_ne_univ hM
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have : v ∈ sl2Fix B := by rw [htop]; trivial
  exact this b b.2

variable [Finite F]

theorem card_le_of_ne_top {S : Submodule F (Fin 2 → F)} (hS : S ≠ ⊤) :
    Nat.card S ≤ Nat.card F := by
  have h1 := Submodule.finrank_lt hS
  rw [Module.finrank_fin_fun] at h1
  rw [Module.natCard_eq_pow_finrank (K := F)]
  calc Nat.card F ^ Module.finrank F S ≤ Nat.card F ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos (by omega)
    _ = Nat.card F := pow_one _

theorem card_vec2 : Nat.card (Fin 2 → F) = Nat.card F ^ 2 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

theorem one_le_of_card_eq_two_pow {n : ℕ} (hF : Nat.card F = 2 ^ n) : 1 ≤ n := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  by_contra h
  have : n = 0 := by omega
  rw [this, pow_zero] at hF
  omega

theorem odd_card_sq_sub_one {n : ℕ} (hF : Nat.card F = 2 ^ n) : Odd (Nat.card F ^ 2 - 1) := by
  have hn := one_le_of_card_eq_two_pow hF
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hev : Even (Nat.card F) := by
    rw [hF]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨r, hr⟩ := hev
  have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨2 * r ^ 2 - 1, ?_⟩
  have h2 : Nat.card F ^ 2 = 4 * r ^ 2 := by rw [hr]; ring
  have h3 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem sl2_card_le {n : ℕ} (hF : Nat.card F = 2 ^ n) (B : Subgroup ↥(StatedSL 2 F))
    (hB : IsPGroup 2 B) :
    Nat.card B ≤ Nat.card F ∧ (B ≠ ⊥ → Nat.card (sl2Fix B) ≤ Nat.card F) := by
  refine ⟨?_, fun hB1 => ?_⟩
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hB)
    have hdvd : Nat.card B ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [← card_statedSL_two]
      exact Subgroup.card_subgroup_dvd_card B
    have hodd : Odd (Nat.card F ^ 2 - 1) := odd_card_sq_sub_one hF
    have hcop : Nat.Coprime (Nat.card B) (Nat.card F ^ 2 - 1) := by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    have := Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)
    exact this
  · exact (card_le_of_ne_top (sl2Fix_ne_top hB1)) |> fun h => by
      simpa using h

@[expose] def sl2Perm : ↥(StatedSL 2 F) →* Equiv.Perm (Fin 2 → F) where
  toFun g :=
    { toFun := fun v => (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v
      invFun := fun v => ((((g : GL (Fin 2) F))⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v
      left_inv := fun v => by
        simp only [Matrix.mulVec_mulVec]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      right_inv := fun v => by
        simp only [Matrix.mulVec_mulVec]
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v : 1
    simp only [Equiv.Perm.mul_apply, Equiv.coe_fn_mk, Subgroup.coe_mul, Units.val_mul,
      Matrix.mulVec_mulVec]

theorem exists_ne_zero_mem_sl2Fix {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (B : Subgroup ↥(StatedSL 2 F)) (hB : IsPGroup 2 B) : ∃ v : Fin 2 → F, v ≠ 0 ∧ v ∈ sl2Fix B := by
  letI : MulAction B (Fin 2 → F) := MulAction.compHom (Fin 2 → F) (sl2Perm.comp B.subtype)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hB.card_modEq_card_fixedPoints (Fin 2 → F)
  have hev : 2 ∣ Nat.card (Fin 2 → F) := by
    rw [card_vec2, hF, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  have hfix : ∀ v : Fin 2 → F, v ∈ MulAction.fixedPoints B (Fin 2 → F) ↔ v ∈ sl2Fix B := by
    intro v
    constructor
    · intro h g hg
      exact h ⟨g, hg⟩
    · intro h g
      exact h g g.2
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints B (Fin 2 → F)) := by
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hev))
  by_contra hcon
  push Not at hcon
  have hsub : MulAction.fixedPoints B (Fin 2 → F) ⊆ {0} := fun v hv => by
    by_contra h0
    exact hcon v h0 ((hfix v).1 hv)
  have hle : Nat.card (MulAction.fixedPoints B (Fin 2 → F)) ≤ 1 := by
    calc Nat.card (MulAction.fixedPoints B (Fin 2 → F))
        ≤ Nat.card ({0} : Set (Fin 2 → F)) := Nat.card_mono (Set.toFinite _) hsub
      _ = 1 := by simp
  have hpos : 0 < Nat.card (MulAction.fixedPoints B (Fin 2 → F)) := by
    have : (0 : Fin 2 → F) ∈ MulAction.fixedPoints B (Fin 2 → F) := (hfix 0).2 (sl2Fix B).zero_mem
    exact Nat.card_pos_iff.2 ⟨⟨⟨0, this⟩⟩, inferInstance⟩
  have := Nat.le_of_dvd hpos h2
  omega

theorem card_sl2Fix_top : Nat.card (⊤ : Submodule F (Fin 2 → F)) = Nat.card F ^ 2 := by
  rw [← card_vec2]
  exact Nat.card_congr Submodule.topEquiv.toEquiv

theorem sl2_card_mul_fix_le {n : ℕ} (hF : Nat.card F = 2 ^ n) (B : Subgroup ↥(StatedSL 2 F))
    (hB : IsPGroup 2 B) : Nat.card B * Nat.card (sl2Fix B) ≤ Nat.card F ^ 2 := by
  by_cases h : B = ⊥
  · subst h
    rw [sl2Fix_bot, card_sl2Fix_top, Subgroup.card_bot, one_mul]
  · obtain ⟨h1, h2⟩ := sl2_card_le hF B hB
    calc Nat.card B * Nat.card (sl2Fix B) ≤ Nat.card F * Nat.card F :=
          Nat.mul_le_mul h1 (h2 h)
      _ = Nat.card F ^ 2 := (sq _).symm

@[expose] def sl2Transvection (i j : Fin 2) (hij : i ≠ j) (c : F) : ↥(StatedSL 2 F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero),
    mem_statedSL_of_det (by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_transvection_of_ne i j hij c])⟩

theorem sl2Transvection_mulVec (i j : Fin 2) (hij : i ≠ j) (c : F) (v : Fin 2 → F) :
    (((sl2Transvection i j hij c : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v
      = v + Pi.single i (c * v j) := by
  simp only [sl2Transvection, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  exact CFSG.Quasithin.H.transvection_mulVec i j c v

theorem sl2_exists_decomp (y : Fin 2 → F) :
    ∃ (g₁ g₂ : ↥(StatedSL 2 F)) (u₁ u₂ : Fin 2 → F),
      y = ((((g₁ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ u₁ - u₁) +
        ((((g₂ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ u₂ - u₂) := by
  refine ⟨sl2Transvection 0 1 (by decide) (y 0), sl2Transvection 1 0 (by decide) (y 1),
    Pi.single 1 1, Pi.single 0 1, ?_⟩
  rw [sl2Transvection_mulVec, sl2Transvection_mulVec]
  ext k
  fin_cases k <;> simp

theorem sl2_eq_one_of_fix {g : ↥(StatedSL 2 F)}
    (h : ∀ v : Fin 2 → F,
      (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : g = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hv := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hv
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hv

end NatSL2

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
