module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial

section MatrixFacts

variable {F : Type*} [Field F]

private def upperRange (F : Type*) [Field F] : Subgroup (SL(2, F)) where
  carrier := Set.range (sl2Upper F)
  one_mem' := ⟨0, by simp [sl2Upper_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [sl2Upper_add]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, sl2Upper_neg a⟩

private lemma mem_upperRange_iff {k : SL(2, F)} :
    k ∈ upperRange F ↔ ∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [coe_sl2Upper]⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext (by rw [coe_sl2Upper]; exact ht.symm)⟩

private lemma upper_mulVec (t : F) (u : Fin 2 → F) :
    ((sl2Upper F t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec u =
      ![u 0 + t * u 1, u 1] := by
  ext i
  fin_cases i <;> simp [sl2Upper, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma diag_mulVec (l : Fˣ) (u : Fin 2 → F) :
    ((sl2Diag F l : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec u =
      ![(l : F) * u 0, ((l⁻¹ : Fˣ) : F) * u 1] := by
  ext i
  fin_cases i <;> simp [sl2Diag, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma diag_mul (l m : Fˣ) : sl2Diag F l * sl2Diag F m = sl2Diag F (l * m) := by
  ext i j
  change (!![(l : F), 0; 0, ((l⁻¹ : Fˣ) : F)] *
      !![(m : F), 0; 0, ((m⁻¹ : Fˣ) : F)]) i j =
    (!![((l * m : Fˣ) : F), 0; 0, (((l * m)⁻¹ : Fˣ) : F)]) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul, _root_.mul_inv_rev]
  all_goals ring

private lemma diag_one : sl2Diag F (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Diag]

private def diagHom (F : Type*) [Field F] : Fˣ →* SL(2, F) where
  toFun := sl2Diag F
  map_one' := diag_one
  map_mul' := fun x y => (diag_mul x y).symm

private lemma diag_inv (l : Fˣ) : (sl2Diag F l)⁻¹ = sl2Diag F l⁻¹ :=
  (map_inv (diagHom F) l).symm

private lemma diag_conj_upper (l : Fˣ) (t : F) :
    sl2Diag F l * sl2Upper F t * (sl2Diag F l)⁻¹ = sl2Upper F ((l : F) ^ 2 * t) := by
  rw [sl2Diag_mul_upper, mul_assoc, mul_inv_cancel, mul_one]

private lemma weyl_mulVec [CharP F 2] (u : Fin 2 → F) :
    ((sl2Weyl F 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec u = ![u 1, u 0] := by
  ext i
  fin_cases i <;> simp [sl2Weyl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, CharTwo.neg_eq]

private lemma diag_mul_weyl [CharP F 2] (l : Fˣ) :
    sl2Diag F l * sl2Weyl F 1 = sl2Weyl F 1 * (sl2Diag F l)⁻¹ := by
  rw [diag_inv]
  ext i j
  change (!![(l : F), 0; 0, ((l⁻¹ : Fˣ) : F)] * !![0, 1; -1, 0] :
      Matrix (Fin 2) (Fin 2) F) i j =
    (!![0, 1; -1, 0] * !![((l⁻¹ : Fˣ) : F), 0; 0, (l : F)] :
      Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private lemma weyl_mul_self [CharP F 2] : sl2Weyl F 1 * sl2Weyl F 1 = 1 := by
  ext i j
  change (!![0, 1; -1, 0] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) i j
    = (1 : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private lemma weyl_mul_upper_weyl [CharP F 2] (t : F) :
    sl2Weyl F 1 * sl2Upper F t * sl2Weyl F 1 = sl2Lower F t := by
  ext i j
  change (!![0, 1; -1, 0] * !![1, t; 0, 1] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) i j
    = (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private lemma sp4_upper_mulVec (t : F) (v : Fin 3 → F) :
    (sp4RadMat (sl2Upper F t)).mulVec v = ![v 0 + t * v 2, v 1 + t ^ 2 * v 2, v 2] := by
  rw [sp4RadMat_mulVec]
  ext i
  fin_cases i <;> simp [sl2Upper]

private lemma sp4_diag_mulVec (l : Fˣ) (v : Fin 3 → F) :
    (sp4RadMat (sl2Diag F l)).mulVec v =
      ![v 0, (l : F) ^ 2 * v 1, (((l⁻¹ : Fˣ) : F)) ^ 2 * v 2] := by
  rw [sp4RadMat_mulVec]
  ext i
  fin_cases i <;> simp [sl2Diag]

private lemma sp4_weyl_mulVec [CharP F 2] (v : Fin 3 → F) :
    (sp4RadMat (sl2Weyl F 1)).mulVec v = ![v 0, v 2, v 1] := by
  rw [sp4RadMat_mulVec]
  ext i
  fin_cases i <;> simp [sl2Weyl, CharTwo.neg_eq]

end MatrixFacts

section FixedPoints

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {V : Type*} [AddCommGroup V] [Finite V]

private def upperFixed (ρ : SL(2, F) →* AddMonoid.End V) : AddSubgroup V where
  carrier := {v : V | ∀ k ∈ upperRange F, ρ k v = v}
  zero_mem' := by
    intro k _
    exact map_zero (ρ k)
  add_mem' := by
    intro x y hx hy k hk
    rw [map_add, hx k hk, hy k hk]
  neg_mem' := by
    intro x hx k hk
    rw [map_neg, hx k hk]

private def kerCoordOne (β : V →+ (Fin 2 → F)) : AddSubgroup V where
  carrier := {v : V | β v 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have hx' : β x 1 = 0 := hx
    have hy' : β y 1 = 0 := hy
    show β (x + y) 1 = 0
    simp [map_add, hx', hy']
  neg_mem' := by
    intro x hx
    have hx' : β x 1 = 0 := hx
    show β (-x) 1 = 0
    simp [hx']

private def coordZero : AddSubgroup (Fin 2 → F) where
  carrier := {y : Fin 2 → F | y 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x 1 + y 1 = 0
    rw [hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change -x 1 = 0
    rw [hx, neg_zero]

private lemma card_pi_two : Nat.card (Fin 2 → F) = Nat.card F ^ 2 := by
  rw [Nat.card_fun, Nat.card_fin]

private lemma card_coordZero : Nat.card ↥(coordZero (F := F)) = Nat.card F := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => y.1 0
      invFun := fun a => ⟨![a, 0], by rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    ext i
    fin_cases i
    · rfl
    · exact y.2.symm
  · intro a
    rfl

private def coordMap (β : V →+ (Fin 2 → F)) :
    ↥(kerCoordOne β) →+ ↥(coordZero (F := F)) where
  toFun v := ⟨β v.1, v.2⟩
  map_zero' := by
    ext i
    show β 0 i = 0
    simp
  map_add' := by
    intro x y
    ext i
    show β (x.1 + y.1) i = (β x.1 + β y.1) i
    simp

private def coordMapKerEquiv (β : V →+ (Fin 2 → F)) :
    ↥(coordMap β).ker ≃ ↥(β.ker) where
  toFun v :=
    ⟨v.1.1, by
      have hv : coordMap β v.1 = 0 := v.2
      have := congrArg Subtype.val hv
      simpa [coordMap] using this⟩
  invFun z :=
    ⟨⟨z.1, by
        show β z.1 1 = 0
        simpa using congrFun z.2 1⟩,
      by
        exact Subtype.ext z.2⟩
  left_inv v := by ext; rfl
  right_inv z := by ext; rfl

private lemma card_ker (hcard : Nat.card V = Nat.card F ^ 3)
    (β : V →+ (Fin 2 → F)) (hβ : Function.Surjective β) : Nat.card ↥β.ker = Nat.card F := by
  have h := AddSubgroup.card_ker_mul_card_of_surjective hβ
  rw [card_pi_two, hcard] at h
  have hq : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
  have h' : Nat.card ↥β.ker * Nat.card F ^ 2 = Nat.card F * Nat.card F ^ 2 := by
    calc Nat.card ↥β.ker * Nat.card F ^ 2 = Nat.card F ^ 3 := h
      _ = Nat.card F * Nat.card F ^ 2 := by ring
  exact Nat.eq_of_mul_eq_mul_right hq h'

private lemma card_kerCoordOne (hcard : Nat.card V = Nat.card F ^ 3)
    (β : V →+ (Fin 2 → F)) (hβ : Function.Surjective β) :
    Nat.card ↥(kerCoordOne β) = Nat.card F ^ 2 := by
  have hf : Function.Surjective (coordMap β) := by
    intro y
    obtain ⟨v, hv⟩ := hβ y.1
    refine ⟨⟨v, ?_⟩, ?_⟩
    · show β v 1 = 0
      rw [hv]
      exact y.2
    · exact Subtype.ext hv
  have h := AddSubgroup.card_ker_mul_card_of_surjective hf
  rw [Nat.card_congr (coordMapKerEquiv β), card_ker hcard β hβ, card_coordZero] at h
  rw [← h, pow_two]

private lemma upperFixed_eq_kerCoordOne (hcard : Nat.card V = Nat.card F ^ 3)
    (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (hβ : Function.Surjective β)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = (k : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hC : Nat.card F ^ 2 ≤ Nat.card {v : V // ∀ k : SL(2, F),
      (∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) → ρ k v = v}) :
    upperFixed ρ = kerCoordOne β := by
  have hC' : Nat.card F ^ 2 ≤ Nat.card ↥(upperFixed ρ) := by
    have he : Nat.card {v : V // ∀ k : SL(2, F),
        (∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) → ρ k v = v} =
        Nat.card ↥(upperFixed ρ) := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl V) ?_)
      intro v
      constructor
      · intro hv k hk
        exact hv k ((mem_upperRange_iff).mp hk)
      · intro hv k hk
        exact hv k ((mem_upperRange_iff).mpr hk)
    rw [he] at hC
    exact hC
  have hsub : (upperFixed ρ : Set V) ⊆ (kerCoordOne β : Set V) := by
    intro v hv
    have h1 : ρ (sl2Upper F 1) v = v := hv (sl2Upper F 1) ⟨1, rfl⟩
    have h2 := hβρ (sl2Upper F 1) v
    rw [h1] at h2
    have h0 := congrFun h2 0
    rw [upper_mulVec (F := F)] at h0
    have h0' : β v 0 = β v 0 + β v 1 := by
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, one_mul] using h0
    exact add_eq_left.mp h0'.symm
  have hcardC : Nat.card ↥(upperFixed ρ) = Nat.card F ^ 2 := by
    refine le_antisymm ?_ hC'
    have hle : Nat.card ↥(upperFixed ρ) ≤ Nat.card ↥(kerCoordOne β) := by
      let f : ↥(upperFixed ρ) → ↥(kerCoordOne β) := fun x => ⟨x.1, hsub x.2⟩
      refine Nat.card_le_card_of_injective f ?_
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : ↥(kerCoordOne β) => (z : V)) h
    calc Nat.card ↥(upperFixed ρ) ≤ Nat.card ↥(kerCoordOne β) := hle
      _ = Nat.card F ^ 2 := card_kerCoordOne hcard β hβ
  exact SetLike.ext' (Set.Finite.eq_of_subset_of_card_le (s := (upperFixed ρ : Set V))
    (t := (kerCoordOne β : Set V)) (kerCoordOne β : Set V).toFinite hsub
    (by
      change Nat.card ↥(kerCoordOne β) ≤ Nat.card ↥(upperFixed ρ)
      rw [card_kerCoordOne hcard β hβ, hcardC]))

end FixedPoints

section Section

variable {F : Type*} [Field F]

private lemma nsmul_eq_self_of_odd {n : ℕ} (hn : Odd n) {V : Type*} [AddCommGroup V]
    (hx : ∀ x : V, 2 • x = 0) (x : V) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, hx, smul_zero, zero_add, one_nsmul]

private lemma even_card_of_char_two [Finite F] [CharP F 2] : Even (Nat.card F) := by
  letI : Fintype F := Fintype.ofFinite F
  have h := FiniteField.even_card_of_char_two (F := F) (by rw [ringChar.eq F 2])
  rw [Nat.card_eq_fintype_card, Nat.even_iff]
  exact h

private lemma odd_card_units [Finite F] [CharP F 2] : Odd (Nat.card Fˣ) := by
  have hEven : Even (Nat.card F) := even_card_of_char_two
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hodd : Odd (Nat.card F - 1) := Nat.Even.sub_odd (by omega) hEven (by decide)
  simpa only [Nat.card_units F] using hodd

private def l2Act (F : Type*) [Field F] (k : SL(2, F)) (u : Fin 2 → F) : Fin 2 → F :=
  ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec u

private lemma l2Act_add (k : SL(2, F)) (u v : Fin 2 → F) :
    l2Act F k (u + v) = l2Act F k u + l2Act F k v := by
  simp [l2Act, Matrix.mulVec_add]

private lemma l2Act_mul (k l : SL(2, F)) (u : Fin 2 → F) :
    l2Act F (k * l) u = l2Act F k (l2Act F l u) := by
  simp only [l2Act]
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact (Matrix.mulVec_mulVec u _ _).symm

private lemma l2Act_one (u : Fin 2 → F) : l2Act F 1 u = u := by
  simp [l2Act]

variable [Finite F] [CharP F 2] {V : Type*} [AddCommGroup V]

private lemma exists_addSection (h2 : ∀ v : V, v + v = 0) (β : V →+ (Fin 2 → F))
    (hβ : Function.Surjective β) :
    ∃ s : (Fin 2 → F) →+ V, ∀ u, β (s u) = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul, h2 v])
  letI : Module (ZMod 2) (Fin 2 → F) := AddCommGroup.zmodModule (fun u => by
    rw [two_nsmul]
    ext i
    exact CharTwo.add_self_eq_zero (u i))
  have hβlin : Function.Surjective (β.toZModLinearMap 2) := hβ
  obtain ⟨s, hs⟩ := (β.toZModLinearMap 2).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top_of_surjective _ hβlin)
  refine ⟨s.toAddMonoidHom, fun u => ?_⟩
  have := LinearMap.congr_fun hs u
  simpa using this

private noncomputable def addSection (h2 : ∀ v : V, v + v = 0) (β : V →+ (Fin 2 → F))
    (hβ : Function.Surjective β) : (Fin 2 → F) →+ V :=
  Classical.choose (exists_addSection h2 β hβ)

private lemma addSection_spec (h2 : ∀ v : V, v + v = 0) (β : V →+ (Fin 2 → F))
    (hβ : Function.Surjective β) (u : Fin 2 → F) :
    β (addSection h2 β hβ u) = u :=
  Classical.choose_spec (exists_addSection h2 β hβ) u

section Ave

variable [Fintype F] [DecidableEq F]

variable (ρ : SL(2, F) →* AddMonoid.End V) (s₀ : (Fin 2 → F) →+ V)

private noncomputable def sectionAve : (Fin 2 → F) →+ V where
  toFun u := ∑ l : Fˣ, ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u))
  map_zero' := by
    simp [l2Act]
  map_add' := by
    intro u v
    simp [l2Act_add, map_add, Finset.sum_add_distrib]

private lemma sectionAve_beta (β : V →+ (Fin 2 → F)) (hβs : ∀ u, β (s₀ u) = u)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (u : Fin 2 → F) : β (sectionAve ρ s₀ u) = u := by
  classical
  have hodd : Odd (Nat.card Fˣ) := odd_card_units
  have hterm : ∀ l : Fˣ,
      β (ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u))) = u := by
    intro l
    rw [hβρ, hβs]
    change l2Act F (sl2Diag F l) (l2Act F (sl2Diag F l)⁻¹ u) = u
    rw [← l2Act_mul, mul_inv_cancel, l2Act_one]
  have hsum : sectionAve ρ s₀ u =
      ∑ l : Fˣ, ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u)) := rfl
  rw [hsum, map_sum]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  have htwo : ∀ x : Fin 2 → F, 2 • x = 0 := fun x => by
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero x
  exact nsmul_eq_self_of_odd hodd htwo u

private lemma sectionAve_diag (m : Fˣ) (u : Fin 2 → F) :
    sectionAve ρ s₀ (l2Act F (sl2Diag F m) u) =
      ρ (sl2Diag F m) (sectionAve ρ s₀ u) := by
  classical
  have hL : sectionAve ρ s₀ (l2Act F (sl2Diag F m) u) =
      ∑ l : Fˣ, ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹
        (l2Act F (sl2Diag F m) u))) := rfl
  have hR : ρ (sl2Diag F m) (sectionAve ρ s₀ u) =
      ∑ l : Fˣ, ρ (sl2Diag F m)
        (ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u))) := by
    rw [show sectionAve ρ s₀ u =
      ∑ l : Fˣ, ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u)) from rfl, map_sum]
  rw [hL, hR]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft m) _ _ ?_
  intro l
  calc ρ (sl2Diag F m) (ρ (sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u)))
      = ρ (sl2Diag F m * sl2Diag F l) (s₀ (l2Act F (sl2Diag F l)⁻¹ u)) := by
        simp [map_mul]
    _ = ρ (sl2Diag F (m * l)) (s₀ (l2Act F (sl2Diag F l)⁻¹ u)) := by rw [diag_mul]
    _ = ρ (sl2Diag F (m * l))
          (s₀ (l2Act F (sl2Diag F (m * l))⁻¹ (l2Act F (sl2Diag F m) u))) := by
        congr 1
        rw [← diag_mul, ← l2Act_mul]
        rw [show (sl2Diag F m * sl2Diag F l)⁻¹ * sl2Diag F m = (sl2Diag F l)⁻¹ by
          rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]]

end Ave

end Section

section Zeta

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {V : Type*} [AddCommGroup V] [Finite V]

private structure SectionData (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) : Prop where
  beta_s : ∀ u, β (s u) = u
  diag : ∀ (l : Fˣ) (u : Fin 2 → F),
    s (l2Act F (sl2Diag F l) u) = ρ (sl2Diag F l) (s u)
  upper : ∀ (t a : F), ρ (sl2Upper F t) (s ![a, 0]) = s ![a, 0]

private def zetaV (ρ : SL(2, F) →* AddMonoid.End V) (s : (Fin 2 → F) →+ V)
    (t b : F) : V :=
  ρ (sl2Upper F t) (s ![0, b]) - s ![t * b, b]

private lemma zetaV_mem (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (t b : F) : zetaV ρ s t b ∈ β.ker := by
  have h1 : ((sl2Upper F t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec ![0, b] =
      ![t * b, b] := by
    rw [upper_mulVec]
    ext i
    fin_cases i <;> simp
  show β (zetaV ρ s t b) = 0
  rw [zetaV, map_sub, hβρ (sl2Upper F t) (s ![0, b]), hsec.beta_s ![0, b], h1,
    hsec.beta_s ![t * b, b]]
  simp

private lemma upper_action (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s) (t a b : F) :
    ρ (sl2Upper F t) (s ![a, b]) = s ![a + t * b, b] + zetaV ρ s t b := by
  have hdecomp : s ![a, b] = s ![a, 0] + s ![0, b] := by
    rw [← map_add]
    congr 1
    ext i
    fin_cases i <;> simp
  have hzeta : ρ (sl2Upper F t) (s ![0, b]) = s ![t * b, b] + zetaV ρ s t b := by
    simp [zetaV, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc ρ (sl2Upper F t) (s ![a, b])
      = ρ (sl2Upper F t) (s ![a, 0]) + ρ (sl2Upper F t) (s ![0, b]) := by
        rw [hdecomp, map_add]
    _ = s ![a, 0] + (s ![t * b, b] + zetaV ρ s t b) := by
        rw [hsec.upper, hzeta]
    _ = s ![a + t * b, b] + zetaV ρ s t b := by
        have hs : s ![a, 0] + s ![t * b, b] = s ![a + t * b, b] := by
          rw [← map_add]
          congr 1
          ext i
          fin_cases i <;> simp
        rw [← add_assoc, hs]

private lemma zetaV_add_t (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (t t' b : F) :
    zetaV ρ s (t + t') b = zetaV ρ s t b + zetaV ρ s t' b := by
  have hx2 : ρ (sl2Upper F t') (s ![0, b]) = s ![t' * b, b] + zetaV ρ s t' b := by
    simp [zetaV, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hz : zetaV ρ s t' b ∈ β.ker := zetaV_mem ρ β s hsec hβρ t' b
  have hfix : ρ (sl2Upper F t) (zetaV ρ s t' b) = zetaV ρ s t' b := hker _ _ hz
  have hx : ρ (sl2Upper F (t + t')) (s ![0, b]) =
      ρ (sl2Upper F t) (ρ (sl2Upper F t') (s ![0, b])) := by
    rw [sl2Upper_add, map_mul]
    rfl
  calc zetaV ρ s (t + t') b
      = ρ (sl2Upper F (t + t')) (s ![0, b]) - s ![(t + t') * b, b] := rfl
    _ = ρ (sl2Upper F t) (ρ (sl2Upper F t') (s ![0, b])) -
          s ![(t + t') * b, b] := by rw [hx]
    _ = ρ (sl2Upper F t) (s ![t' * b, b] + zetaV ρ s t' b) -
          s ![(t + t') * b, b] := by rw [hx2]
    _ = (ρ (sl2Upper F t) (s ![t' * b, b]) + zetaV ρ s t' b) -
          s ![(t + t') * b, b] := by rw [map_add, hfix]
    _ = (s ![t' * b + t * b, b] + zetaV ρ s t b + zetaV ρ s t' b) -
          s ![(t + t') * b, b] := by
        rw [upper_action ρ β s hsec t (t' * b) b]
    _ = zetaV ρ s t b + zetaV ρ s t' b := by
        have hvec : (![(t + t') * b, b] : Fin 2 → F) = ![t' * b + t * b, b] := by
          ext i
          fin_cases i <;> simp [add_mul, add_comm, add_left_comm]
        rw [hvec]
        abel

private lemma zetaV_scale (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s) (l : Fˣ) (t b : F) :
    ρ (sl2Diag F l) (zetaV ρ s t b) =
      zetaV ρ s ((l : F) ^ 2 * t) (((l⁻¹ : Fˣ) : F) * b) := by
  have hdiag0 : l2Act F (sl2Diag F l) (![0, b] : Fin 2 → F) =
      ![0, ((l⁻¹ : Fˣ) : F) * b] := by
    rw [l2Act, diag_mulVec]
    ext i
    fin_cases i <;> simp
  have hdiag1 : l2Act F (sl2Diag F l) (![t * b, b] : Fin 2 → F) =
      ![(l : F) * (t * b), ((l⁻¹ : Fˣ) : F) * b] := by
    rw [l2Act, diag_mulVec]
    ext i
    fin_cases i <;> simp
  have hconj : sl2Diag F l * sl2Upper F t * (sl2Diag F l)⁻¹ =
      sl2Upper F ((l : F) ^ 2 * t) := diag_conj_upper l t
  have hconj' : sl2Diag F l * sl2Upper F t =
      sl2Upper F ((l : F) ^ 2 * t) * sl2Diag F l := by
    have := congrArg (fun z => z * sl2Diag F l) hconj
    simpa [mul_assoc, mul_inv_cancel, mul_one] using this
  have hfirst : ρ (sl2Diag F l) (ρ (sl2Upper F t) (s ![0, b])) =
      ρ (sl2Upper F ((l : F) ^ 2 * t)) (ρ (sl2Diag F l) (s ![0, b])) := by
    change (ρ (sl2Diag F l) * ρ (sl2Upper F t)) (s ![0, b]) = _
    rw [← map_mul, hconj']
    rw [map_mul]
    rfl
  calc ρ (sl2Diag F l) (zetaV ρ s t b)
      = ρ (sl2Diag F l) (ρ (sl2Upper F t) (s ![0, b])) -
          ρ (sl2Diag F l) (s ![t * b, b]) := by
        rw [zetaV, map_sub]
    _ = ρ (sl2Upper F ((l : F) ^ 2 * t)) (ρ (sl2Diag F l) (s ![0, b])) -
          ρ (sl2Diag F l) (s ![t * b, b]) := by rw [hfirst]
    _ = ρ (sl2Upper F ((l : F) ^ 2 * t)) (s ![0, ((l⁻¹ : Fˣ) : F) * b]) -
          s ![(l : F) * (t * b), ((l⁻¹ : Fˣ) : F) * b] := by
        rw [← hsec.diag l ![0, b], hdiag0, ← hsec.diag l ![t * b, b], hdiag1]
    _ = zetaV ρ s ((l : F) ^ 2 * t) (((l⁻¹ : Fˣ) : F) * b) := by
        rw [zetaV]
        congr 1
        rw [show ((l : F) ^ 2 * t) * (((l⁻¹ : Fˣ) : F) * b) =
          (l : F) * (t * b) by
          rw [Units.val_inv_eq_inv_val]
          field_simp
          try ring]

private noncomputable def gHom (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) : F →+ β.ker where
  toFun t := ⟨zetaV ρ s t 1, zetaV_mem ρ β s hsec hβρ t 1⟩
  map_zero' := by
    ext
    show zetaV ρ s 0 1 = 0
    rw [zetaV, sl2Upper_zero, map_one]
    simp [AddMonoid.End.one_apply]
  map_add' := by
    intro t t'
    ext
    exact zetaV_add_t ρ β s hsec hβρ hker t t' 1

private lemma zetaV_eq_g (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (t b : F) :
    zetaV ρ s t b = ((gHom ρ β s hsec hβρ hker (t * b ^ 2) : β.ker) : V) := by
  rcases eq_or_ne b 0 with rfl | hb
  · have hz0 : zetaV ρ s t 0 = 0 := by
      have h0 : (![0, 0] : Fin 2 → F) = 0 := by
        ext i
        fin_cases i <;> rfl
      have h1 : (![t * 0, 0] : Fin 2 → F) = 0 := by
        ext i
        fin_cases i <;> simp
      rw [zetaV, h0, h1, map_zero, map_zero, sub_zero]
    have hg0 : ((gHom ρ β s hsec hβρ hker (t * 0 ^ 2) : β.ker) : V) = 0 := by
      rw [show t * 0 ^ 2 = 0 by ring, map_zero]
      rfl
    rw [hz0, hg0]
  · let l : Fˣ := Units.mk0 b hb
    have hscale := zetaV_scale ρ β s hsec l t b
    have hval : (l : F) = b := rfl
    have hinv : ((l⁻¹ : Fˣ) : F) = b⁻¹ := by
      rw [Units.val_inv_eq_inv_val, hval]
    rw [hval, hinv, inv_mul_cancel₀ hb] at hscale
    have hfix : ρ (sl2Diag F l) (zetaV ρ s t b) = zetaV ρ s t b :=
      hker _ _ (zetaV_mem ρ β s hsec hβρ t b)
    rw [hfix] at hscale
    rw [hscale]
    congr 1
    ring

end Zeta

section Weyl

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Fintype F] [DecidableEq F]
variable {V : Type*} [AddCommGroup V] [Finite V]

private def deltaV (ρ : SL(2, F) →* AddMonoid.End V) (s : (Fin 2 → F) →+ V)
    (a b : F) : V :=
  ρ (sl2Weyl F 1) (s ![a, b]) - s ![b, a]

private lemma deltaV_mem (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (a b : F) : deltaV ρ s a b ∈ β.ker := by
  have h1 : ((sl2Weyl F 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
      (![a, b] : Fin 2 → F) = ![b, a] := by
    rw [weyl_mulVec]
    ext i
    fin_cases i <;> rfl
  show β (deltaV ρ s a b) = 0
  rw [deltaV, map_sub, hβρ (sl2Weyl F 1) (s ![a,b]), hsec.beta_s ![a,b], h1,
    hsec.beta_s ![b,a]]
  simp

private lemma deltaV_add (ρ : SL(2, F) →* AddMonoid.End V)
    (s : (Fin 2 → F) →+ V) (a a' b b' : F) :
    deltaV ρ s (a + a') (b + b') = deltaV ρ s a b + deltaV ρ s a' b' := by
  have h0 : (![a + a', b + b'] : Fin 2 → F) = ![a, b] + ![a', b'] := by
    ext i
    fin_cases i <;> simp
  have h1 : (![b + b', a + a'] : Fin 2 → F) = ![b, a] + ![b', a'] := by
    ext i
    fin_cases i <;> simp
  simp only [deltaV]
  rw [h0, h1]
  simp only [map_add]
  abel

private lemma deltaV_split (ρ : SL(2, F) →* AddMonoid.End V)
    (s : (Fin 2 → F) →+ V) (a b : F) :
    deltaV ρ s a b = deltaV ρ s a 0 + deltaV ρ s 0 b := by
  have h := deltaV_add ρ s a 0 0 b
  simpa using h

private lemma deltaV_scale (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s) (l : Fˣ) (a b : F) :
    ρ (sl2Diag F l) (deltaV ρ s a b) =
      deltaV ρ s (((l⁻¹ : Fˣ) : F) * a) ((l : F) * b) := by
  have hdiag0 : l2Act F (sl2Diag F l) (![a, b] : Fin 2 → F) =
      ![(l : F) * a, ((l⁻¹ : Fˣ) : F) * b] := by
    rw [l2Act, diag_mulVec]
    ext i
    fin_cases i <;> simp
  have hdiag1 : l2Act F (sl2Diag F l) (![b, a] : Fin 2 → F) =
      ![(l : F) * b, ((l⁻¹ : Fˣ) : F) * a] := by
    rw [l2Act, diag_mulVec]
    ext i
    fin_cases i <;> simp
  have hdiag0' : l2Act F (sl2Diag F l⁻¹) (![a, b] : Fin 2 → F) =
      ![((l⁻¹ : Fˣ) : F) * a, (l : F) * b] := by
    rw [l2Act, diag_mulVec]
    ext i
    fin_cases i <;> simp
  have hw : sl2Diag F l * sl2Weyl F 1 =
      sl2Weyl F 1 * (sl2Diag F l)⁻¹ := diag_mul_weyl l
  have hfirst : ρ (sl2Diag F l) (ρ (sl2Weyl F 1) (s ![a,b])) =
      ρ (sl2Weyl F 1) (ρ ((sl2Diag F l)⁻¹) (s ![a,b])) := by
    change (ρ (sl2Diag F l) * ρ (sl2Weyl F 1)) (s ![a,b]) = _
    rw [← map_mul, hw]
    rw [map_mul]
    rfl
  calc ρ (sl2Diag F l) (deltaV ρ s a b)
      = ρ (sl2Diag F l) (ρ (sl2Weyl F 1) (s ![a,b])) -
          ρ (sl2Diag F l) (s ![b,a]) := by
        rw [deltaV, map_sub]
    _ = ρ (sl2Weyl F 1) (ρ ((sl2Diag F l)⁻¹) (s ![a,b])) -
          ρ (sl2Diag F l) (s ![b,a]) := by rw [hfirst]
    _ = ρ (sl2Weyl F 1) (s ![((l⁻¹ : Fˣ) : F) * a, (l : F) * b]) -
          s ![(l : F) * b, ((l⁻¹ : Fˣ) : F) * a] := by
        rw [show ρ ((sl2Diag F l)⁻¹) = ρ (sl2Diag F l⁻¹) by rw [diag_inv],
          ← hsec.diag (l⁻¹) ![a,b], hdiag0', ← hsec.diag l ![b,a], hdiag1]
    _ = deltaV ρ s (((l⁻¹ : Fˣ) : F) * a) ((l : F) * b) := by
        rw [deltaV]

private lemma deltaV_zero_a (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) {a : F} (ha : a ≠ 0) :
    deltaV ρ s a 0 = 0 := by
  classical
  have hconst : ∀ b : F, b ≠ 0 → deltaV ρ s b 0 = deltaV ρ s 1 0 := by
    intro b hb
    let l : Fˣ := Units.mk0 b hb
    have hval : (l : F) = b := rfl
    have hinv : ((l⁻¹ : Fˣ) : F) = b⁻¹ := by
      rw [Units.val_inv_eq_inv_val, hval]
    have hscale := deltaV_scale ρ β s hsec l b 0
    rw [hval, hinv, inv_mul_cancel₀ hb, mul_zero] at hscale
    have hfix : ρ (sl2Diag F l) (deltaV ρ s b 0) = deltaV ρ s b 0 :=
      hker _ _ (deltaV_mem ρ β s hsec hβρ b 0)
    rw [hfix] at hscale
    exact hscale
  have hD0 : deltaV ρ s 1 0 = 0 := by
    have hcard : 4 ≤ Fintype.card F := by simpa [Nat.card_eq_fintype_card] using hF
    have hlt : 1 < Fintype.card Fˣ := by
      rw [Fintype.card_units]
      omega
    obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : Fˣ)
    have hc0 : (c : F) ≠ 0 := Units.ne_zero c
    have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
    have hsum0 : (1 : F) + (c : F) ≠ 0 := by
      intro h
      apply hc1
      have hcneg : (c : F) = -1 := by linear_combination h
      simpa [CharTwo.neg_eq] using hcneg
    have hD1 : deltaV ρ s (1 + (c : F)) 0 = deltaV ρ s 1 0 := hconst _ hsum0
    have hDc : deltaV ρ s (c : F) 0 = deltaV ρ s 1 0 := hconst _ hc0
    have hadd : deltaV ρ s (1 + (c : F)) 0 =
        deltaV ρ s 1 0 + deltaV ρ s (c : F) 0 := by
      have h := deltaV_add ρ s 1 (c : F) 0 0
      simpa using h
    have hDD : deltaV ρ s 1 0 = deltaV ρ s 1 0 + deltaV ρ s 1 0 := by
      have h' := hadd
      rw [hD1, hDc] at h'
      exact h'
    exact add_eq_left.mp hDD.symm
  rw [hconst a ha, hD0]

private lemma deltaV_zero_b (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) {b : F} (hb : b ≠ 0) :
    deltaV ρ s 0 b = 0 := by
  classical
  have hconst : ∀ c : F, c ≠ 0 → deltaV ρ s 0 c = deltaV ρ s 0 1 := by
    intro c hc
    let l : Fˣ := Units.mk0 c hc
    have hval : (l : F) = c := rfl
    have hscale := deltaV_scale ρ β s hsec l 0 1
    have hscale' : ρ (sl2Diag F l) (deltaV ρ s 0 1) = deltaV ρ s 0 c := by
      simpa [hval] using hscale
    have hfix : ρ (sl2Diag F l) (deltaV ρ s 0 1) = deltaV ρ s 0 1 :=
      hker _ _ (deltaV_mem ρ β s hsec hβρ 0 1)
    rw [hfix] at hscale'
    exact hscale'.symm
  have hD0 : deltaV ρ s 0 1 = 0 := by
    have hcard : 4 ≤ Fintype.card F := by simpa [Nat.card_eq_fintype_card] using hF
    have hlt : 1 < Fintype.card Fˣ := by
      rw [Fintype.card_units]
      omega
    obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : Fˣ)
    have hc0 : (c : F) ≠ 0 := Units.ne_zero c
    have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
    have hsum0 : (1 : F) + (c : F) ≠ 0 := by
      intro h
      apply hc1
      have hcneg : (c : F) = -1 := by linear_combination h
      simpa [CharTwo.neg_eq] using hcneg
    have hD1 : deltaV ρ s 0 (1 + (c : F)) = deltaV ρ s 0 1 := hconst _ hsum0
    have hDc : deltaV ρ s 0 (c : F) = deltaV ρ s 0 1 := hconst _ hc0
    have hadd : deltaV ρ s 0 (1 + (c : F)) =
        deltaV ρ s 0 1 + deltaV ρ s 0 (c : F) := by
      have h := deltaV_add ρ s 0 0 1 (c : F)
      simpa using h
    have hDD : deltaV ρ s 0 1 = deltaV ρ s 0 1 + deltaV ρ s 0 1 := by
      have h' := hadd
      rw [hD1, hDc] at h'
      exact h'
    exact add_eq_left.mp hDD.symm
  rw [hconst b hb, hD0]

private lemma deltaV_eq_zero (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) (a b : F) :
    deltaV ρ s a b = 0 := by
  have h00 : deltaV ρ s 0 0 = 0 := by
    have h0 : (![0, 0] : Fin 2 → F) = 0 := by
      ext i
      fin_cases i <;> rfl
    rw [deltaV, h0, map_zero]
    simp
  rw [deltaV_split ρ s a b]
  rcases eq_or_ne a 0 with rfl | ha
  · rw [h00, zero_add]
    rcases eq_or_ne b 0 with rfl | hb
    · exact h00
    · exact deltaV_zero_b ρ β s hsec hβρ hker hF hb
  · rw [deltaV_zero_a ρ β s hsec hβρ hker hF ha]
    rcases eq_or_ne b 0 with rfl | hb
    · rw [h00, add_zero]
    · rw [deltaV_zero_b ρ β s hsec hβρ hker hF hb, add_zero]

private lemma weyl_action (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) (a b : F) :
    ρ (sl2Weyl F 1) (s ![a, b]) = s ![b, a] := by
  have h := deltaV_eq_zero ρ β s hsec hβρ hker hF a b
  rw [deltaV] at h
  exact sub_eq_zero.mp h

end Weyl

section Global

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Fintype F] [DecidableEq F]
variable {V : Type*} [AddCommGroup V] [Finite V]

private def endHom (ρ : SL(2, F) →* AddMonoid.End V) (k : SL(2, F)) : V →+ V := ρ k

private lemma endHom_one (ρ : SL(2, F) →* AddMonoid.End V) :
    endHom ρ 1 = AddMonoidHom.id V := by
  ext x
  change (ρ 1) x = x
  rw [map_one]
  exact AddMonoid.End.one_apply x

private lemma endHom_mul (ρ : SL(2, F) →* AddMonoid.End V) (k l : SL(2, F)) :
    endHom ρ (k * l) = (endHom ρ k).comp (endHom ρ l) := by
  ext x
  change (ρ (k * l)) x = (ρ k) ((ρ l) x)
  rw [map_mul]
  rfl

private noncomputable def gV (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) : F →+ V :=
  β.ker.subtype.comp (gHom ρ β s hsec hβρ hker)

private lemma beta_gV (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (a : F) :
    β (gV ρ β s hsec hβρ hker a) = 0 := by
  show β ((gHom ρ β s hsec hβρ hker a : β.ker) : V) = 0
  exact (gHom ρ β s hsec hβρ hker a).2

private noncomputable def Wsub (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) : AddSubgroup V :=
  s.range ⊔ (gV ρ β s hsec hβρ hker).range

private lemma Wsub_le_comap (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (k : SL(2, F))
    (hs : ∀ u, ρ k (s u) ∈ Wsub ρ β s hsec hβρ hker)
    (hg : ∀ a, ρ k (gV ρ β s hsec hβρ hker a) ∈ Wsub ρ β s hsec hβρ hker) :
    Wsub ρ β s hsec hβρ hker ≤
      AddSubgroup.comap (endHom ρ k) (Wsub ρ β s hsec hβρ hker) := by
  rw [Wsub, AddSubgroup.sup_eq_closure, AddSubgroup.closure_le]
  rintro x (hx | hx)
  · obtain ⟨u, rfl⟩ := hx
    change s u ∈ AddSubgroup.comap (endHom ρ k)
      (AddSubgroup.closure (↑s.range ∪ ↑(gV ρ β s hsec hβρ hker).range))
    rw [AddSubgroup.mem_comap, ← AddSubgroup.sup_eq_closure]
    exact hs u
  · obtain ⟨a, rfl⟩ := hx
    change gV ρ β s hsec hβρ hker a ∈ AddSubgroup.comap (endHom ρ k)
      (AddSubgroup.closure (↑s.range ∪ ↑(gV ρ β s hsec hβρ hker).range))
    rw [AddSubgroup.mem_comap, ← AddSubgroup.sup_eq_closure]
    exact hg a

private lemma Wsub_upper (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (t : F) :
    Wsub ρ β s hsec hβρ hker ≤
      AddSubgroup.comap (endHom ρ (sl2Upper F t)) (Wsub ρ β s hsec hβρ hker) := by
  refine Wsub_le_comap ρ β s hsec hβρ hker (sl2Upper F t) ?_ ?_
  · intro u
    have hu : u = ![u 0, u 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hu, upper_action ρ β s hsec t (u 0) (u 1),
      zetaV_eq_g ρ β s hsec hβρ hker t (u 1)]
    have h1 : s ![u 0 + t * u 1, u 1] ∈ s.range :=
      AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h2 : gV ρ β s hsec hβρ hker (t * (u 1) ^ 2) ∈
        (gV ρ β s hsec hβρ hker).range :=
      AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left h1) (AddSubgroup.mem_sup_right h2)
  · intro a
    have hmem : gV ρ β s hsec hβρ hker a ∈ β.ker := by
      rw [AddMonoidHom.mem_ker]
      exact beta_gV ρ β s hsec hβρ hker a
    rw [hker (sl2Upper F t) _ hmem]
    exact AddSubgroup.mem_sup_right (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)

private lemma Wsub_diag (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (l : Fˣ) :
    Wsub ρ β s hsec hβρ hker ≤
      AddSubgroup.comap (endHom ρ (sl2Diag F l)) (Wsub ρ β s hsec hβρ hker) := by
  refine Wsub_le_comap ρ β s hsec hβρ hker (sl2Diag F l) ?_ ?_
  · intro u
    rw [← hsec.diag l u]
    exact AddSubgroup.mem_sup_left (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
  · intro a
    have hmem : gV ρ β s hsec hβρ hker a ∈ β.ker := by
      rw [AddMonoidHom.mem_ker]
      exact beta_gV ρ β s hsec hβρ hker a
    rw [hker (sl2Diag F l) _ hmem]
    exact AddSubgroup.mem_sup_right (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)

private lemma Wsub_weyl (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) :
    Wsub ρ β s hsec hβρ hker ≤
      AddSubgroup.comap (endHom ρ (sl2Weyl F 1)) (Wsub ρ β s hsec hβρ hker) := by
  refine Wsub_le_comap ρ β s hsec hβρ hker (sl2Weyl F 1) ?_ ?_
  · intro u
    have hu : u = ![u 0, u 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hu, weyl_action ρ β s hsec hβρ hker hF (u 0) (u 1)]
    exact AddSubgroup.mem_sup_left (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)
  · intro a
    have hmem : gV ρ β s hsec hβρ hker a ∈ β.ker := by
      rw [AddMonoidHom.mem_ker]
      exact beta_gV ρ β s hsec hβρ hker a
    rw [hker (sl2Weyl F 1) _ hmem]
    exact AddSubgroup.mem_sup_right (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)

private def stableSub (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) :
    Subgroup (SL(2, F)) where
  carrier := {k | AddSubgroup.map (endHom ρ k) (Wsub ρ β s hsec hβρ hker) ≤
        Wsub ρ β s hsec hβρ hker ∧
      AddSubgroup.map (endHom ρ (k⁻¹)) (Wsub ρ β s hsec hβρ hker) ≤
        Wsub ρ β s hsec hβρ hker}
  one_mem' := by
    constructor
    · rw [endHom_one, AddSubgroup.map_id]
    · rw [inv_one, endHom_one, AddSubgroup.map_id]
  mul_mem' := by
    intro k l hk hl
    constructor
    · rw [endHom_mul, ← AddSubgroup.map_map]
      exact (AddSubgroup.map_mono hl.1).trans hk.1
    · rw [_root_.mul_inv_rev, endHom_mul, ← AddSubgroup.map_map]
      exact (AddSubgroup.map_mono hk.2).trans hl.2
  inv_mem' := by
    intro k hk
    exact ⟨hk.2, by simpa using hk.1⟩

private lemma upper_mem_stableSub (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (t : F) :
    sl2Upper F t ∈ stableSub ρ β s hsec hβρ hker := by
  constructor
  · exact AddSubgroup.map_le_iff_le_comap.mpr (Wsub_upper ρ β s hsec hβρ hker t)
  · rw [show (sl2Upper F t)⁻¹ = sl2Upper F (-t) from (sl2Upper_neg t).symm]
    exact AddSubgroup.map_le_iff_le_comap.mpr (Wsub_upper ρ β s hsec hβρ hker (-t))

private lemma diag_mem_stableSub (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v) (l : Fˣ) :
    sl2Diag F l ∈ stableSub ρ β s hsec hβρ hker := by
  constructor
  · exact AddSubgroup.map_le_iff_le_comap.mpr (Wsub_diag ρ β s hsec hβρ hker l)
  · rw [diag_inv]
    exact AddSubgroup.map_le_iff_le_comap.mpr (Wsub_diag ρ β s hsec hβρ hker l⁻¹)

private lemma weyl_mem_stableSub (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) :
    sl2Weyl F 1 ∈ stableSub ρ β s hsec hβρ hker := by
  constructor
  · exact AddSubgroup.map_le_iff_le_comap.mpr (Wsub_weyl ρ β s hsec hβρ hker hF)
  · rw [show (sl2Weyl F 1)⁻¹ = sl2Weyl F 1 from inv_eq_of_mul_eq_one_right weyl_mul_self]
    exact AddSubgroup.map_le_iff_le_comap.mpr (Wsub_weyl ρ β s hsec hβρ hker hF)

private lemma closure_upper_diag_weyl :
    Subgroup.closure (Set.range (sl2Upper F) ∪ Set.range (sl2Diag F) ∪ {sl2Weyl F 1}) = ⊤ := by
  set K := Subgroup.closure (Set.range (sl2Upper F) ∪ Set.range (sl2Diag F) ∪ {sl2Weyl F 1})
  have hU : ∀ t, sl2Upper F t ∈ K := fun t =>
    Subgroup.subset_closure (Or.inl (Or.inl ⟨t, rfl⟩))
  have hD : ∀ l, sl2Diag F l ∈ K := fun l =>
    Subgroup.subset_closure (Or.inl (Or.inr ⟨l, rfl⟩))
  have hW : sl2Weyl F 1 ∈ K := Subgroup.subset_closure (Or.inr rfl)
  have hL : ∀ t, sl2Lower F t ∈ K := by
    intro t
    rw [← weyl_mul_upper_weyl t]
    exact mul_mem (mul_mem hW (hU t)) hW
  rw [eq_top_iff, ← sl2_closure_upper_lower (K := F)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (hx | hx)
  · obtain ⟨t, rfl⟩ := hx
    exact hU t
  · obtain ⟨t, rfl⟩ := hx
    exact hL t

private lemma stableSub_eq_top (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F) :
    stableSub ρ β s hsec hβρ hker = ⊤ := by
  rw [eq_top_iff, ← closure_upper_diag_weyl (F := F)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ((⟨t, rfl⟩ | ⟨l, rfl⟩) | rfl)
  · exact upper_mem_stableSub ρ β s hsec hβρ hker t
  · exact diag_mem_stableSub ρ β s hsec hβρ hker l
  · exact weyl_mem_stableSub ρ β s hsec hβρ hker hF

private theorem Wsub_eq_top (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤) :
    Wsub ρ β s hsec hβρ hker = ⊤ := by
  refine hgen (Wsub ρ β s hsec hβρ hker) ?_
  intro k v
  have hz : v - s (β v) ∈ β.ker := by
    show β (v - s (β v)) = 0
    rw [map_sub, hsec.beta_s]
    simp
  have hv : v = s (β v) + (v - s (β v)) := by abel
  have hk : k ∈ stableSub ρ β s hsec hβρ hker := by
    rw [stableSub_eq_top ρ β s hsec hβρ hker hF]
    exact Subgroup.mem_top k
  have hmap := hk.1
  have hsk : s (β v) ∈ Wsub ρ β s hsec hβρ hker :=
    AddSubgroup.mem_sup_left (AddMonoidHom.mem_range.mpr ⟨β v, rfl⟩)
  have hks : ρ k (s (β v)) ∈ Wsub ρ β s hsec hβρ hker :=
    hmap (AddSubgroup.mem_map.mpr ⟨s (β v), hsk, rfl⟩)
  have hgoal : ρ k v - v = ρ k (s (β v)) - s (β v) := by
    rw [hv, map_add, hker k (v - s (β v)) hz]
    abel_nf
  rw [hgoal]
  exact AddSubgroup.sub_mem _ hks hsk

private lemma gV_range_eq (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤) :
    (gV ρ β s hsec hβρ hker).range = β.ker := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact (gHom ρ β s hsec hβρ hker a).2
  · intro z hz
    have hzW : z ∈ Wsub ρ β s hsec hβρ hker := by
      rw [Wsub_eq_top ρ β s hsec hβρ hker hF hgen]
      exact AddSubgroup.mem_top z
    rw [Wsub, AddSubgroup.mem_sup] at hzW
    obtain ⟨x, hx, y, hy, hxy⟩ := hzW
    obtain ⟨u, rfl⟩ := AddMonoidHom.mem_range.mp hx
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hy
    have hsum : β (s u + gV ρ β s hsec hβρ hker a) = u := by
      rw [map_add, hsec.beta_s, beta_gV ρ β s hsec hβρ hker a, add_zero]
    have hu : u = 0 := by
      rw [hsum.symm, hxy, hz]
    subst hu
    rw [map_zero, zero_add] at hxy
    rw [← hxy]
    exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩

private lemma gHom_surjective (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F))
    (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤) :
    Function.Surjective (gHom ρ β s hsec hβρ hker) := by
  intro z
  have hz : (z : V) ∈ (gV ρ β s hsec hβρ hker).range := by
    rw [gV_range_eq ρ β s hsec hβρ hker hF hgen]
    exact z.2
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hz
  exact ⟨a, Subtype.ext ha⟩

private noncomputable def gEquiv (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) :
    F ≃+ β.ker := by
  classical
  letI : Fintype β.ker := Fintype.ofFinite _
  have hβ : Function.Surjective β := fun u => ⟨s u, hsec.beta_s u⟩
  refine AddEquiv.ofBijective (gHom ρ β s hsec hβρ hker) ?_
  refine (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨gHom_surjective ρ β s hsec hβρ hker hF hgen, ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, card_ker hcard β hβ]
end Global

section Gamma

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {V : Type*} [AddCommGroup V]

private noncomputable def sqrt (F : Type*) [Field F] [Finite F] [CharP F 2] (x : F) : F :=
  (frobeniusEquiv F 2).symm x

private lemma sqrt_sq (x : F) : (sqrt F x) ^ 2 = x := by
  rw [sqrt, ← frobeniusEquiv_def]
  simp

private lemma sq_sqrt (x : F) : sqrt F (x ^ 2) = x := by
  exact (frobeniusEquiv F 2).injective (by simp [sqrt, frobeniusEquiv_def])

private lemma beta_sub_s (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (v : V) : v - s (β v) ∈ β.ker := by
  show β (v - s (β v)) = 0
  rw [map_sub, hs]
  simp

private noncomputable def gammaHom (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) : V →+ (Fin 3 → F) where
  toFun v :=
    ![g.symm ⟨v - s (β v), beta_sub_s β s hs v⟩,
      (β v 0) ^ 2, (β v 1) ^ 2]
  map_zero' := by
    ext i
    fin_cases i
    · show g.symm ⟨0 - s (β 0), _⟩ = 0
      have h0 : (⟨0 - s (β 0), beta_sub_s β s hs 0⟩ : β.ker) = 0 := by
        apply Subtype.ext
        simp
      rw [h0, map_zero]
    · simp
    · simp
  map_add' := by
    intro v w
    ext i
    fin_cases i
    · show g.symm ⟨(v + w) - s (β (v + w)), _⟩ =
        g.symm ⟨v - s (β v), _⟩ + g.symm ⟨w - s (β w), _⟩
      rw [← map_add]
      congr 1
      apply Subtype.ext
      show (v + w) - s (β (v + w)) = (v - s (β v)) + (w - s (β w))
      simp only [map_add]
      abel
    · show (β (v + w) 0) ^ 2 = (β v 0) ^ 2 + (β w 0) ^ 2
      rw [map_add]
      simpa using (add_pow_char (p := 2) (x := β v 0) (y := β w 0))
    · show (β (v + w) 1) ^ 2 = (β v 1) ^ 2 + (β w 1) ^ 2
      rw [map_add]
      simpa using (add_pow_char (p := 2) (x := β v 1) (y := β w 1))

private lemma gammaHom_apply_zero (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (v : V) :
    gammaHom β s hs g v 0 = g.symm ⟨v - s (β v), beta_sub_s β s hs v⟩ := rfl

private lemma gammaHom_apply_one (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (v : V) :
    gammaHom β s hs g v 1 = (β v 0) ^ 2 := rfl

private lemma gammaHom_apply_two (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (v : V) :
    gammaHom β s hs g v 2 = (β v 1) ^ 2 := rfl

private noncomputable def gammaInv (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (g : F ≃+ β.ker) (x : Fin 3 → F) : V :=
  s ![sqrt F (x 1), sqrt F (x 2)] + (g (x 0) : β.ker)

private lemma gammaHom_gammaInv (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (x : Fin 3 → F) :
    gammaHom β s hs g (gammaInv β s g x) = x := by
  have hbeta : β (gammaInv β s g x) = ![sqrt F (x 1), sqrt F (x 2)] := by
    rw [gammaInv, map_add, hs]
    show ![sqrt F (x 1), sqrt F (x 2)] + β (g (x 0) : β.ker) = _
    rw [show β (g (x 0) : β.ker) = 0 from (g (x 0)).2, add_zero]
  ext i
  fin_cases i
  · change gammaHom β s hs g (gammaInv β s g x) 0 = x 0
    rw [gammaHom_apply_zero]
    have hdiff : gammaInv β s g x - s (β (gammaInv β s g x)) = (g (x 0) : β.ker) := by
      rw [hbeta, gammaInv]
      abel
    have hsub : (⟨gammaInv β s g x - s (β (gammaInv β s g x)),
        beta_sub_s β s hs (gammaInv β s g x)⟩ : β.ker) = g (x 0) := by
      apply Subtype.ext
      exact hdiff
    rw [hsub, g.symm_apply_apply]
  · change gammaHom β s hs g (gammaInv β s g x) 1 = x 1
    rw [gammaHom_apply_one, hbeta]
    exact sqrt_sq (x 1)
  · change gammaHom β s hs g (gammaInv β s g x) 2 = x 2
    rw [gammaHom_apply_two, hbeta]
    exact sqrt_sq (x 2)

private lemma gammaInv_gammaHom (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (v : V) :
    gammaInv β s g (gammaHom β s hs g v) = v := by
  have hu : (![β v 0, β v 1] : Fin 2 → F) = β v := by
    ext i
    fin_cases i <;> rfl
  simp only [gammaInv]
  rw [gammaHom_apply_one, gammaHom_apply_two, sq_sqrt, sq_sqrt,
    gammaHom_apply_zero, g.apply_symm_apply, hu]
  simp only [neg_smul, one_smul]
  abel

private noncomputable def gammaEquiv (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) : V ≃+ (Fin 3 → F) :=
  AddEquiv.ofBijective (gammaHom β s hs g)
    ⟨fun x y h => by
        have h' := congrArg (gammaInv β s g) h
        rwa [gammaInv_gammaHom, gammaInv_gammaHom] at h',
      fun x => ⟨gammaInv β s g x, gammaHom_gammaInv β s hs g x⟩⟩

private lemma gammaEquiv_apply_one (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (v : V) :
    gammaEquiv β s hs g v 1 = (β v 0) ^ 2 := rfl

private lemma gammaEquiv_apply_two (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V)
    (hs : ∀ u, β (s u) = u) (g : F ≃+ β.ker) (v : V) :
    gammaEquiv β s hs g v 2 = (β v 1) ^ 2 := rfl

end Gamma

section Orth

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Fintype F] [DecidableEq F]
variable {V : Type*} [AddCommGroup V] [Finite V]

private noncomputable def gammaOf (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) : V ≃+ (Fin 3 → F) :=
  gammaEquiv β s hsec.beta_s (gEquiv ρ β s hsec hβρ hker hF hgen hcard)

private lemma gammaOf_s_add_g (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (a b u : F) :
    gammaOf ρ β s hsec hβρ hker hF hgen hcard
        (s ![a, b] + gV ρ β s hsec hβρ hker u) = ![u, a ^ 2, b ^ 2] := by
  change gammaHom β s hsec.beta_s
    (gEquiv ρ β s hsec hβρ hker hF hgen hcard)
    (s ![a, b] + gV ρ β s hsec hβρ hker u) = ![u, a ^ 2, b ^ 2]
  have hβ : β (s ![a, b] + gV ρ β s hsec hβρ hker u) = ![a, b] := by
    rw [map_add, hsec.beta_s, beta_gV ρ β s hsec hβρ hker, add_zero]
  have hdiff : (s ![a, b] + gV ρ β s hsec hβρ hker u) -
      s (β (s ![a, b] + gV ρ β s hsec hβρ hker u)) =
      ((gEquiv ρ β s hsec hβρ hker hF hgen hcard) u : V) := by
    rw [hβ]
    abel
  ext i
  fin_cases i
  · change gammaHom β s hsec.beta_s
      (gEquiv ρ β s hsec hβρ hker hF hgen hcard)
      (s ![a, b] + gV ρ β s hsec hβρ hker u) 0 = u
    rw [gammaHom_apply_zero]
    have hsub : (⟨(s ![a, b] + gV ρ β s hsec hβρ hker u) -
        s (β (s ![a, b] + gV ρ β s hsec hβρ hker u)),
        beta_sub_s β s hsec.beta_s _⟩ : β.ker) =
        (gEquiv ρ β s hsec hβρ hker hF hgen hcard) u := by
      apply Subtype.ext
      exact hdiff
    rw [hsub, (gEquiv ρ β s hsec hβρ hker hF hgen hcard).symm_apply_apply]
  · change gammaHom β s hsec.beta_s
      (gEquiv ρ β s hsec hβρ hker hF hgen hcard)
      (s ![a, b] + gV ρ β s hsec hβρ hker u) 1 = a ^ 2
    rw [gammaHom_apply_one, hβ]
    rfl
  · change gammaHom β s hsec.beta_s
      (gEquiv ρ β s hsec hβρ hker hF hgen hcard)
      (s ![a, b] + gV ρ β s hsec hβρ hker u) 2 = b ^ 2
    rw [gammaHom_apply_two, hβ]
    rfl

private lemma exists_decomp (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (v : V) : ∃ u : F, v = s ![β v 0, β v 1] + gV ρ β s hsec hβρ hker u := by
  have hz : v - s (β v) ∈ β.ker := beta_sub_s β s hsec.beta_s v
  have hz' : v - s (β v) ∈ (gV ρ β s hsec hβρ hker).range := by
    rw [gV_range_eq ρ β s hsec hβρ hker hF hgen]
    exact hz
  obtain ⟨u, hu⟩ := AddMonoidHom.mem_range.mp hz'
  have hβ : β v = ![β v 0, β v 1] := by
    ext i
    fin_cases i <;> rfl
  refine ⟨u, ?_⟩
  have hβ' : (![β v 0, β v 1] : Fin 2 → F) = β v := by
    ext i
    fin_cases i <;> rfl
  rw [hu]
  rw [hβ']
  abel

private lemma gammaOf_upper (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (t : F) (v : V) :
    gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ (sl2Upper F t) v) =
      (sp4RadMat (sl2Upper F t)).mulVec
        (gammaOf ρ β s hsec hβρ hker hF hgen hcard v) := by
  obtain ⟨u, hu⟩ := exists_decomp ρ β s hsec hβρ hker hF hgen v
  set a : F := β v 0
  set b : F := β v 1
  have hβv : β v = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  have hv : v = s ![a, b] + gV ρ β s hsec hβρ hker u := hu
  rw [hv]
  have hgfix : ρ (sl2Upper F t) (gV ρ β s hsec hβρ hker u) =
      gV ρ β s hsec hβρ hker u :=
    hker _ _ (beta_gV ρ β s hsec hβρ hker u)
  have hstep : ρ (sl2Upper F t) (s ![a, b] + gV ρ β s hsec hβρ hker u) =
      s ![a + t * b, b] + gV ρ β s hsec hβρ hker (t * b ^ 2 + u) := by
    rw [map_add, hgfix, upper_action ρ β s hsec t a b,
      zetaV_eq_g ρ β s hsec hβρ hker t b]
    rw [map_add]
    simp [add_comm, add_left_comm, add_assoc]
    rfl
  rw [hstep, gammaOf_s_add_g, gammaOf_s_add_g, sp4_upper_mulVec]
  ext i
  fin_cases i <;> simp [add_pow_char (p := 2), mul_pow, add_comm]

private lemma gammaOf_diag (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (l : Fˣ) (v : V) :
    gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ (sl2Diag F l) v) =
      (sp4RadMat (sl2Diag F l)).mulVec
        (gammaOf ρ β s hsec hβρ hker hF hgen hcard v) := by
  obtain ⟨u, hu⟩ := exists_decomp ρ β s hsec hβρ hker hF hgen v
  set a : F := β v 0
  set b : F := β v 1
  have hβv : β v = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  have hv : v = s ![a, b] + gV ρ β s hsec hβρ hker u := hu
  rw [hv]
  have hgfix : ρ (sl2Diag F l) (gV ρ β s hsec hβρ hker u) =
      gV ρ β s hsec hβρ hker u :=
    hker _ _ (beta_gV ρ β s hsec hβρ hker u)
  have hstep : ρ (sl2Diag F l) (s ![a, b] + gV ρ β s hsec hβρ hker u) =
      s ![((l : F)) * a, ((l⁻¹ : Fˣ) : F) * b] + gV ρ β s hsec hβρ hker u := by
    rw [map_add, hgfix, ← hsec.diag l ![a, b], l2Act, diag_mulVec]
    simp
  rw [hstep, gammaOf_s_add_g, gammaOf_s_add_g, sp4_diag_mulVec]
  ext i
  fin_cases i <;> simp [mul_pow]

private lemma gammaOf_weyl (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (v : V) :
    gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ (sl2Weyl F 1) v) =
      (sp4RadMat (sl2Weyl F 1)).mulVec
        (gammaOf ρ β s hsec hβρ hker hF hgen hcard v) := by
  obtain ⟨u, hu⟩ := exists_decomp ρ β s hsec hβρ hker hF hgen v
  set a : F := β v 0
  set b : F := β v 1
  have hβv : β v = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  have hv : v = s ![a, b] + gV ρ β s hsec hβρ hker u := hu
  rw [hv]
  have hgfix : ρ (sl2Weyl F 1) (gV ρ β s hsec hβρ hker u) =
      gV ρ β s hsec hβρ hker u :=
    hker _ _ (beta_gV ρ β s hsec hβρ hker u)
  have hstep : ρ (sl2Weyl F 1) (s ![a, b] + gV ρ β s hsec hβρ hker u) =
      s ![b, a] + gV ρ β s hsec hβρ hker u := by
    rw [map_add, hgfix, weyl_action ρ β s hsec hβρ hker hF a b]
  rw [hstep, gammaOf_s_add_g, gammaOf_s_add_g, sp4_weyl_mulVec]
  rfl

private def Kgood (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) : Subgroup (SL(2, F)) where
  carrier := {k | ∀ v, gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ k v) =
    (sp4RadMat k).mulVec (gammaOf ρ β s hsec hβρ hker hF hgen hcard v)}
  one_mem' := by
    intro v
    change gammaOf ρ β s hsec hβρ hker hF hgen hcard ((endHom ρ 1) v) =
      (sp4RadMat (1 : SL(2, F))).mulVec
        (gammaOf ρ β s hsec hβρ hker hF hgen hcard v)
    rw [endHom_one, sp4RadMat_one]
    simp
  mul_mem' := by
    intro k l hk hl v
    change gammaOf ρ β s hsec hβρ hker hF hgen hcard ((endHom ρ (k * l)) v) =
      (sp4RadMat (k * l)).mulVec
        (gammaOf ρ β s hsec hβρ hker hF hgen hcard v)
    rw [endHom_mul, sp4RadMat_mul]
    change gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ k (ρ l v)) =
      (sp4RadMat k * sp4RadMat l).mulVec
        (gammaOf ρ β s hsec hβρ hker hF hgen hcard v)
    rw [hk (ρ l v), hl v, Matrix.mulVec_mulVec]
  inv_mem' := by
    intro k hk v
    have hv : v = ρ k (ρ (k⁻¹) v) := by
      change v = ((endHom ρ k).comp (endHom ρ (k⁻¹))) v
      rw [← endHom_mul, mul_inv_cancel, endHom_one]
      rfl
    have h1 : gammaOf ρ β s hsec hβρ hker hF hgen hcard v =
        (sp4RadMat k).mulVec
          (gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ (k⁻¹) v)) := by
      conv_lhs => rw [hv]
      exact hk (ρ (k⁻¹) v)
    have h2 := congrArg
      (fun w => (sp4RadMat (k⁻¹)).mulVec w) h1
    rw [Matrix.mulVec_mulVec, ← sp4RadMat_mul, inv_mul_cancel, sp4RadMat_one,
      Matrix.one_mulVec] at h2
    exact h2.symm

private lemma upper_mem_Kgood (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (t : F) :
    sl2Upper F t ∈ Kgood ρ β s hsec hβρ hker hF hgen hcard :=
  gammaOf_upper ρ β s hsec hβρ hker hF hgen hcard t

private lemma diag_mem_Kgood (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (l : Fˣ) :
    sl2Diag F l ∈ Kgood ρ β s hsec hβρ hker hF hgen hcard :=
  gammaOf_diag ρ β s hsec hβρ hker hF hgen hcard l

private lemma weyl_mem_Kgood (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) :
    sl2Weyl F 1 ∈ Kgood ρ β s hsec hβρ hker hF hgen hcard :=
  gammaOf_weyl ρ β s hsec hβρ hker hF hgen hcard

private lemma Kgood_eq_top (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) :
    Kgood ρ β s hsec hβρ hker hF hgen hcard = ⊤ := by
  rw [eq_top_iff, ← closure_upper_diag_weyl (F := F)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ((⟨t, rfl⟩ | ⟨l, rfl⟩) | rfl)
  · exact upper_mem_Kgood ρ β s hsec hβρ hker hF hgen hcard t
  · exact diag_mem_Kgood ρ β s hsec hβρ hker hF hgen hcard l
  · exact weyl_mem_Kgood ρ β s hsec hβρ hker hF hgen hcard

private lemma gammaOf_equivariant (ρ : SL(2, F) →* AddMonoid.End V)
    (β : V →+ (Fin 2 → F)) (s : (Fin 2 → F) →+ V) (hsec : SectionData ρ β s)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = ((k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hF : 4 ≤ Nat.card F)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hcard : Nat.card V = Nat.card F ^ 3) (k : SL(2, F)) (v : V) :
    gammaOf ρ β s hsec hβρ hker hF hgen hcard (ρ k v) =
      (sp4RadMat k).mulVec (gammaOf ρ β s hsec hβρ hker hF hgen hcard v) := by
  have hk : k ∈ Kgood ρ β s hsec hβρ hker hF hgen hcard := by
    rw [Kgood_eq_top ρ β s hsec hβρ hker hF hgen hcard]
    exact Subgroup.mem_top k
  exact hk v

end Orth

theorem exists_o3Coord {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {V : Type*} [AddCommGroup V] [Finite V] (h2 : ∀ v : V, v + v = 0)
    (hcard : Nat.card V = Nat.card F ^ 3)
    (ρ : SL(2, F) →* AddMonoid.End V) (β : V →+ (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβρ : ∀ (k : SL(2, F)) (v : V),
      β (ρ k v) = (k : Matrix (Fin 2) (Fin 2) F).mulVec (β v))
    (hker : ∀ (k : SL(2, F)) (v : V), β v = 0 → ρ k v = v)
    (hgen : ∀ W : AddSubgroup V, (∀ (k : SL(2, F)) (v : V), ρ k v - v ∈ W) → W = ⊤)
    (hC : Nat.card F ^ 2 ≤ Nat.card {v : V // ∀ k : SL(2, F),
      (∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) → ρ k v = v}) :
    ∃ γ : V ≃+ (Fin 3 → F),
      (∀ (k : SL(2, F)) (v : V), γ (ρ k v) = (sp4RadMat k).mulVec (γ v)) ∧
      ∀ v : V, γ v 1 = β v 0 ^ 2 ∧ γ v 2 = β v 1 ^ 2 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let s₀ : (Fin 2 → F) →+ V := addSection h2 β hβ
  have hβs₀ : ∀ u, β (s₀ u) = u := addSection_spec h2 β hβ
  let s : (Fin 2 → F) →+ V := sectionAve ρ s₀
  have hUpperEq := upperFixed_eq_kerCoordOne hcard ρ β hβ hβρ hC
  have hupper : ∀ (t a : F), ρ (sl2Upper F t) (s ![a, 0]) = s ![a, 0] := by
    intro t a
    have hmem : s ![a, 0] ∈ upperFixed ρ := by
      rw [hUpperEq]
      show β (s ![a, 0]) 1 = 0
      rw [sectionAve_beta ρ s₀ β hβs₀ hβρ]
      simp
    exact hmem (sl2Upper F t) ⟨t, rfl⟩
  have hsec : SectionData ρ β s :=
    { beta_s := sectionAve_beta ρ s₀ β hβs₀ hβρ
      diag := sectionAve_diag ρ s₀
      upper := hupper }
  let g : F ≃+ β.ker := gEquiv ρ β s hsec hβρ hker hF hgen hcard
  let γ : V ≃+ (Fin 3 → F) := gammaOf ρ β s hsec hβρ hker hF hgen hcard
  have hγ : γ = gammaEquiv β s hsec.beta_s g := rfl
  refine ⟨γ, ?_, ?_⟩
  · intro k v
    exact gammaOf_equivariant ρ β s hsec hβρ hker hF hgen hcard k v
  · intro v
    constructor
    · rw [hγ]
      exact gammaEquiv_apply_one β s hsec.beta_s g v
    · rw [hγ]
      exact gammaEquiv_apply_two β s hsec.beta_s g v

end CFSG.Quasithin.F112R.St84
