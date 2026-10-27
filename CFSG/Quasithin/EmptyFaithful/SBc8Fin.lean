module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.Quasithin.EmptyFaithful.SBc7Cent
import CFSG.Quasithin.EmptyFaithful.SBd6Tw

public section

namespace CFSG.Quasithin

namespace SBc8

open CFSG.QuasithinUnique

section Finite

set_option maxRecDepth 100000 in
private theorem zmod2_mul_self_eq_one :
    ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ a b : Fin 3 → ZMod 2,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a →
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b → a ≠ 0 → b ≠ 0 → a ≠ b → g * g = 1 := by
  decide +kernel

end Finite

section Transport

variable {F : Type} [Field F] [Fintype F]

private theorem sq_eq_one_of_fixes_two (hF : Fintype.card F = 2)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) {a b : Fin 3 → F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hga : (g : Matrix (Fin 3) (Fin 3) F).mulVec a = a)
    (hgb : (g : Matrix (Fin 3) (Fin 3) F).mulVec b = b) : g ^ 2 = 1 := by
  let ε : F →+* ZMod 2 := (SBd6.eZ2 hF : F →+* ZMod 2)
  let f : Matrix.SpecialLinearGroup (Fin 3) F →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    Matrix.SpecialLinearGroup.map ε
  have hinj : Function.Injective f := SBd6.map_eZ2_injective hF
  have hεinj : Function.Injective ε := (SBd6.eZ2 hF).injective
  have hne : ∀ v w : Fin 3 → F, v ≠ w → (ε ∘ v) ≠ (ε ∘ w) := fun v w hvw h =>
    hvw (funext fun i => hεinj (congrFun h i))
  have hne0 : ∀ v : Fin 3 → F, v ≠ 0 → (ε ∘ v) ≠ 0 := fun v hv h =>
    hv (funext fun i => hεinj (by simpa using congrFun h i))
  have hfix : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F).mulVec v = v →
      (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (ε ∘ v) = ε ∘ v := by
    intro v hv
    funext i
    have h1 := RingHom.map_mulVec ε (g : Matrix (Fin 3) (Fin 3) F) v i
    rw [hv] at h1
    exact h1.symm
  have h := zmod2_mul_self_eq_one (f g) (ε ∘ a) (ε ∘ b) (hfix a hga) (hfix b hgb) (hne0 a ha)
    (hne0 b hb) (hne a b hab)
  apply hinj
  rw [map_pow, pow_two, map_one]
  exact h

end Transport

section Fixed

private def fixedVectors {F : Type} [Field F]
    (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) : AddSubgroup (Fin 3 → F) where
  carrier := {v | ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F).mulVec v = v}
  zero_mem' := fun y _ => Matrix.mulVec_zero _
  add_mem' := fun {a b} ha hb y hy => by rw [Matrix.mulVec_add, ha y hy, hb y hy]
  neg_mem' := fun {a} ha y hy => by rw [Matrix.mulVec_neg, ha y hy]

private theorem mem_fixedVectors {F : Type} [Field F]
    {Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} {v : Fin 3 → F} :
    v ∈ fixedVectors Y ↔ ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F).mulVec v = v := Iff.rfl

private theorem mulVec_mem_fixedVectors {F : Type} [Field F]
    {Y T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hN : ∀ τ ∈ T, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) {τ : Matrix.SpecialLinearGroup (Fin 3) F}
    (hτ : τ ∈ T) {c : Fin 3 → F} (hc : c ∈ fixedVectors Y) :
    (τ : Matrix (Fin 3) (Fin 3) F).mulVec c ∈ fixedVectors Y := by
  rw [mem_fixedVectors] at hc ⊢
  intro y hy
  have hy' : τ⁻¹ * y * τ ∈ Y := by simpa using hN τ⁻¹ (T.inv_mem hτ) y hy
  have h1 := hc _ hy'
  have h2 : y * τ = τ * (τ⁻¹ * y * τ) := by group
  have h3 : (y : Matrix (Fin 3) (Fin 3) F) * (τ : Matrix (Fin 3) (Fin 3) F) =
      (τ : Matrix (Fin 3) (Fin 3) F) *
        ((τ⁻¹ * y * τ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h2]
  rw [Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec, h1]

private theorem two_dvd_card_fixedVectors {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
    {u : Fin 3 → F} (hu : u ∈ fixedVectors Y) (hu0 : u ≠ 0) :
    2 ∣ Nat.card (fixedVectors Y) := by
  have h8 : Nat.card (Fin 3 → F) = 2 ^ 3 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have hd := AddSubgroup.card_addSubgroup_dvd_card (fixedVectors Y)
  rw [h8] at hd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [hi]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exfalso
    subst h0
    have hbot : fixedVectors Y = ⊥ :=
      AddSubgroup.eq_bot_of_card_eq (fixedVectors Y) (by rw [hi, pow_zero])
    rw [hbot] at hu
    exact hu0 (AddSubgroup.mem_bot.mp hu)
  · exact dvd_pow_self 2 hpos.ne'

private theorem exists_fixed_vector_of_invariant {F : Type} [Field F] [Finite F]
    {T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hT : IsPGroup 2 T)
    (A : AddSubgroup (Fin 3 → F))
    (hA : ∀ τ ∈ T, ∀ a ∈ A, (τ : Matrix (Fin 3) (Fin 3) F).mulVec a ∈ A)
    (hcard : 2 ∣ Nat.card A) :
    ∃ a ∈ A, a ≠ 0 ∧ ∀ τ ∈ T, (τ : Matrix (Fin 3) (Fin 3) F).mulVec a = a := by
  let _ : MulAction T A :=
    { smul := fun τ a =>
        ⟨((τ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec a,
          hA τ τ.2 a a.2⟩
      one_smul := fun a => Subtype.ext (by
        show (((1 : T) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec a = a
        simp)
      mul_smul := fun τ σ a => Subtype.ext (by
        show (((τ * σ : T) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec a =
          ((τ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
            (((σ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec a)
        simp [Matrix.mulVec_mulVec]) }
  have h0 : (0 : A) ∈ MulAction.fixedPoints T A := by
    rw [MulAction.mem_fixedPoints]
    intro τ
    exact Subtype.ext (Matrix.mulVec_zero
      ((τ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
  obtain ⟨b, hb, hb0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hcard h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun τ hτ => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨τ, hτ⟩)

end Fixed

theorem eq_zero_of_fixed_of_plane {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {Y T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hT : IsSylowTwoOf T ⊤)
    (hN : ∀ τ ∈ T, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y)
    (E : AddSubgroup (Fin 3 → F)) (hE : Nat.card E = 4)
    (hET : ∀ τ ∈ T, ∀ e ∈ E, (τ : Matrix (Fin 3) (Fin 3) F).mulVec e ∈ E)
    (hCE : ∀ e ∈ E, (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F).mulVec e = e) → e = 0) :
    ∀ u : Fin 3 → F, (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F).mulVec u = u) → u = 0 := by
  intro u hu
  by_contra hu0
  obtain ⟨c, hcC, hc0, hcT⟩ := exists_fixed_vector_of_invariant hT.2.1 (fixedVectors Y)
    (fun τ hτ c hc => mulVec_mem_fixedVectors hN hτ hc)
    (two_dvd_card_fixedVectors hF Y (mem_fixedVectors.mpr hu) hu0)
  obtain ⟨e, heE, he0, heT⟩ := exists_fixed_vector_of_invariant hT.2.1 E hET (by rw [hE]; decide)
  have hce : c ≠ e := by
    rintro rfl
    exact hc0 (hCE _ heE (mem_fixedVectors.mp hcC))
  obtain ⟨τ, hτ, hτ2⟩ := SBc7.exists_sq_ne_one_of_sylow hF hT
  exact hτ2 (sq_eq_one_of_fixes_two hF τ hc0 he0 hce (hcT τ hτ) (heT τ hτ))

end SBc8

end CFSG.Quasithin
