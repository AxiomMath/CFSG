module

public import CFSG.Timmesfeld.RankTwo.LevisBMinus
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne
public import CFSG.Timmesfeld.RankTwo.LevisExtras
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.Timmesfeld.RankTwo.LevisBCone
public import CFSG.Timmesfeld.RankTwo.LevisBWords
public import CFSG.Timmesfeld.RankTwo.ModelG2

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.Timmesfeld.GradedPresentation
open scoped commutatorElement MatrixGroups

theorem injective_of_sl2_charTwo {E : Type} [Field E] [CharP E 2] (hE : 4 ≤ Nat.card E)
    {H : Type*} [Group H] (Θ : Matrix.SpecialLinearGroup (Fin 2) E →* H)
    (hΘ : Θ (sl2Upper 1) ≠ 1) : Function.Injective Θ := by
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) = ⊥ :=
    eq_bot_iff.2 fun g hg => (Subgroup.mem_bot).2 (LevisExtras.eq_one_of_mem_center_sl2 hg)
  have hs : IsSimpleGroup PSL(2, E) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) with hπdef
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  rw [← MonoidHom.ker_eq_bot_iff]
  have hN : (Θ.ker.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases (haveI := hN; hs.eq_bot_or_eq_top_of_normal (Θ.ker.map π)) with h | h
  · exact (Subgroup.map_eq_bot_iff_of_injective _ hπ).1 h
  · exfalso
    have hmem : π (sl2Upper 1) ∈ Θ.ker.map π := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, hgx⟩ := hmem
    exact hΘ (by rw [← hπ hgx]; exact hg)

theorem extendsToHom_pair_of_hom {ι K : Type*} [Group K] {X : (ι → ℤ) → Subgroup K}
    {G : Type*} [Group G] {φ : ∀ γ, X γ → G} {k : Type*} [Field k]
    {φK : Matrix.SpecialLinearGroup (Fin 2) k →* K} (hinj : Function.Injective φK)
    (Θ : Matrix.SpecialLinearGroup (Fin 2) k →* G) {α β : ι → ℤ}
    (hα : ∀ z : X α, ∃ t, φK (sl2Upper t) = z ∧ φ α z = Θ (sl2Upper t))
    (hβ : ∀ z : X β, ∃ t, φK (sl2Lower t) = z ∧ φ β z = Θ (sl2Lower t)) :
    ExtendsToHom X {α, β} φ := by
  set e := MonoidHom.ofInjective hinj
  refine ⟨φK.range, Θ.comp e.symm.toMonoidHom, fun γ hγ z => ?_⟩
  rcases hγ with rfl | hγ
  · obtain ⟨t, ht, hφ⟩ := hα z
    refine ⟨⟨sl2Upper t, ht⟩, ?_⟩
    have h1 : e.symm ⟨z, ⟨sl2Upper t, ht⟩⟩ = sl2Upper t :=
      e.symm_apply_eq.2 (Subtype.ext ht.symm)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    exact hφ.symm
  · rw [Set.mem_singleton_iff] at hγ
    subst hγ
    obtain ⟨t, ht, hφ⟩ := hβ z
    refine ⟨⟨sl2Lower t, ht⟩, ?_⟩
    have h1 : e.symm ⟨z, ⟨sl2Lower t, ht⟩⟩ = sl2Lower t :=
      e.symm_apply_eq.2 (Subtype.ext ht.symm)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    exact hφ.symm

section Weyl

variable {F : Type} [Field F] {b c : F}

variable (b c) in
@[expose] noncomputable def mnA : spinGroup (quadMinus 4 F b c) :=
  (minusFrame 4 b c).longWeyl (i := (0 : Fin 3)) (j := 1) (by decide) true false

variable (b c) in
@[expose] noncomputable def mnB : spinGroup (quadMinus 4 F b c) :=
  (minusFrame 4 b c).longWeyl (i := (1 : Fin 3)) (j := 2) (by decide) true false

variable (b c) in
@[expose] noncomputable def mnC : spinGroup (quadMinus 4 F b c) :=
  (minusFrame 4 b c).longWeyl (i := (0 : Fin 3)) (j := 2) (by decide) true false *
    (minusFrame 4 b c).longWeyl (i := (0 : Fin 3)) (j := 2) (by decide) true true

noncomputable abbrev mnD (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    spinGroup (quadMinus 4 F b c) :=
  shortWeyl 4 hirr (2 : Fin 3)

theorem conj_mul_conj {G : Type*} [Group G] (a b' y : G) :
    a * b' * y * (a * b')⁻¹ = a * (b' * y * b'⁻¹) * a⁻¹ := by
  group

variable [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

section A

omit hirr

theorem mnA_L0 (x : F) : mnA b c * b3xL b c 0 x * (mnA b c)⁻¹ = b3xL b c 1 x := by
  simp only [mnA, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnA_L1 (x : F) : mnA b c * b3xL b c 1 x * (mnA b c)⁻¹ = b3xL b c 0 x := by
  simp only [mnA, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnA_L2 (x : F) : mnA b c * b3xL b c 2 x * (mnA b c)⁻¹ = b3xL b c 6 x := by
  simp only [mnA, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnA_L3 (x : F) : mnA b c * b3xL b c 3 x * (mnA b c)⁻¹ = b3xL b c 7 x := by
  simp only [mnA, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnA_L6 (x : F) : mnA b c * b3xL b c 6 x * (mnA b c)⁻¹ = b3xL b c 2 x := by
  simp only [mnA, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnA_L7 (x : F) : mnA b c * b3xL b c 7 x * (mnA b c)⁻¹ = b3xL b c 3 x := by
  simp only [mnA, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L0 (x : F) : mnB b c * b3xL b c 0 x * (mnB b c)⁻¹ = b3xL b c 6 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L1 (x : F) : mnB b c * b3xL b c 1 x * (mnB b c)⁻¹ = b3xL b c 7 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L2 (x : F) : mnB b c * b3xL b c 2 x * (mnB b c)⁻¹ = b3xL b c 3 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L3 (x : F) : mnB b c * b3xL b c 3 x * (mnB b c)⁻¹ = b3xL b c 2 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L6 (x : F) : mnB b c * b3xL b c 6 x * (mnB b c)⁻¹ = b3xL b c 0 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L7 (x : F) : mnB b c * b3xL b c 7 x * (mnB b c)⁻¹ = b3xL b c 1 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr]; · congr 1
  · decide

theorem mnB_L10 (x : F) : mnB b c * b3xL b c 10 x * (mnB b c)⁻¹ = b3xL b c 10 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr, mlr_swap]; · congr 1
  · decide

theorem mnB_L11 (x : F) : mnB b c * b3xL b c 11 x * (mnB b c)⁻¹ = b3xL b c 11 x := by
  simp only [mnB, b3xL]; rw [longWeyl_conj_mlr, mlr_swap]; · congr 1
  · decide

theorem mnC_L2 (x : F) : mnC b c * b3xL b c 2 x * (mnC b c)⁻¹ = b3xL b c 10 x := by
  simp only [mnC, conj_mul_conj, b3xL]; rw [longWeyl_conj_mlr, longWeyl_conj_mlr]
  · congr 1
  all_goals decide

theorem mnC_L3 (x : F) : mnC b c * b3xL b c 3 x * (mnC b c)⁻¹ = b3xL b c 11 x := by
  simp only [mnC, conj_mul_conj, b3xL]; rw [longWeyl_conj_mlr, longWeyl_conj_mlr, mlr_swap]
  · congr 1
  all_goals decide

theorem mnC_L10 (x : F) : mnC b c * b3xL b c 10 x * (mnC b c)⁻¹ = b3xL b c 2 x := by
  simp only [mnC, conj_mul_conj, b3xL]; rw [longWeyl_conj_mlr, longWeyl_conj_mlr]
  · congr 1
  all_goals decide

theorem mnC_L11 (x : F) : mnC b c * b3xL b c 11 x * (mnC b c)⁻¹ = b3xL b c 3 x := by
  simp only [mnC, conj_mul_conj, b3xL]; rw [longWeyl_conj_mlr, longWeyl_conj_mlr, mlr_swap]
  · congr 1
  all_goals decide

end A

theorem mnA_S4 (p : Fin 2 → F) : mnA b c * b3xS hirr 4 p * (mnA b c)⁻¹ = b3xS hirr 4 p := by
  simp only [mnA, b3xS]; rw [longWeyl_conj_msr]; congr 1

theorem mnA_S5 (p : Fin 2 → F) : mnA b c * b3xS hirr 5 p * (mnA b c)⁻¹ = b3xS hirr 5 p := by
  simp only [mnA, b3xS]; rw [longWeyl_conj_msr]; congr 1

theorem mnB_S4 (p : Fin 2 → F) : mnB b c * b3xS hirr 4 p * (mnB b c)⁻¹ = b3xS hirr 8 p := by
  simp only [mnB, b3xS]; rw [longWeyl_conj_msr]; congr 1

theorem mnB_S5 (p : Fin 2 → F) : mnB b c * b3xS hirr 5 p * (mnB b c)⁻¹ = b3xS hirr 9 p := by
  simp only [mnB, b3xS]; rw [longWeyl_conj_msr]; congr 1

theorem mnB_S8 (p : Fin 2 → F) : mnB b c * b3xS hirr 8 p * (mnB b c)⁻¹ = b3xS hirr 4 p := by
  simp only [mnB, b3xS]; rw [longWeyl_conj_msr]; congr 1

theorem mnB_S9 (p : Fin 2 → F) : mnB b c * b3xS hirr 9 p * (mnB b c)⁻¹ = b3xS hirr 5 p := by
  simp only [mnB, b3xS]; rw [longWeyl_conj_msr]; congr 1

theorem mnC_S4 (p : Fin 2 → F) : mnC b c * b3xS hirr 4 p * (mnC b c)⁻¹ = b3xS hirr 5 p := by
  simp only [mnC, conj_mul_conj, b3xS]; rw [longWeyl_conj_msr, longWeyl_conj_msr]; congr 1

theorem mnC_S5 (p : Fin 2 → F) : mnC b c * b3xS hirr 5 p * (mnC b c)⁻¹ = b3xS hirr 4 p := by
  simp only [mnC, conj_mul_conj, b3xS]; rw [longWeyl_conj_msr, longWeyl_conj_msr]; congr 1

theorem mnC_S8 (p : Fin 2 → F) : mnC b c * b3xS hirr 8 p * (mnC b c)⁻¹ = b3xS hirr 8 p := by
  simp only [mnC, conj_mul_conj, b3xS]; rw [longWeyl_conj_msr, longWeyl_conj_msr]; congr 1

theorem mnC_S9 (p : Fin 2 → F) : mnC b c * b3xS hirr 9 p * (mnC b c)⁻¹ = b3xS hirr 9 p := by
  simp only [mnC, conj_mul_conj, b3xS]; rw [longWeyl_conj_msr, longWeyl_conj_msr]; congr 1

theorem mnD_L0 (x : F) : mnD hirr * b3xL b c 0 x * (mnD hirr)⁻¹ = b3xL b c 0 x := by
  simp only [mnD, b3xL]; rw [shortWeyl_conj_mlr]; · congr 1
  · decide

theorem mnD_L1 (x : F) : mnD hirr * b3xL b c 1 x * (mnD hirr)⁻¹ = b3xL b c 1 x := by
  simp only [mnD, b3xL]; rw [shortWeyl_conj_mlr]; · congr 1
  · decide

theorem mnD_S4 (p : Fin 2 → F) :
    mnD hirr * b3xS hirr 4 p * (mnD hirr)⁻¹ = b3xS hirr 5 (planeRefl b c planeOne p) := by
  simp only [mnD, b3xS]; rw [shortWeyl_conj_msr]; congr 1

theorem mnD_S5 (p : Fin 2 → F) :
    mnD hirr * b3xS hirr 5 p * (mnD hirr)⁻¹ = b3xS hirr 4 (planeRefl b c planeOne p) := by
  simp only [mnD, b3xS]; rw [shortWeyl_conj_msr]; congr 1

end Weyl

section Rels

variable {F : Type} [Field F] [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

section Long

omit [CharP F 2] hirr

theorem b3_comm_0_2 (s t : F) : ⁅b3xL b c 0 s, b3xL b c 2 t⁆ = b3xL b c 6 (s * t) := by
  simp only [b3xL]
  rw [mlr_of_ne (by decide), mlr_of_ne (by decide), mlr_of_ne (by decide)]
  exact HypFrame.commutator_longRoot_longRoot _ (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide)
    (by decide) (by decide) true false false s t

theorem b3_commute_0_6 (s t : F) : Commute (b3xL b c 0 s) (b3xL b c 6 t) := by
  simp only [b3xL]
  rw [mlr_of_ne (by decide), mlr_of_ne (by decide)]
  exact HypFrame.commute_longRoot_longRoot_left _ (i := (0 : Fin 3)) (j := 1) (l := 2)
    (by decide) (by decide) true false false s t

theorem b3_commute_6_2 (s t : F) : Commute (b3xL b c 6 s) (b3xL b c 2 t) := by
  simp only [b3xL]
  rw [mlr_of_ne (by decide), mlr_of_ne (by decide)]
  exact HypFrame.commute_longRoot_longRoot_right _ (i := (0 : Fin 3)) (j := 2) (k := 1)
    (by decide) (by decide) true false true s t

theorem b3_commute_10_2 (s t : F) : Commute (b3xL b c 10 s) (b3xL b c 2 t) := by
  simp only [b3xL]
  rw [mlr_of_ne (by decide), mlr_of_ne (by decide)]
  exact HypFrame.commute_longRoot_longRoot_left _ (i := (1 : Fin 3)) (j := 2) (l := 2)
    (by decide) (by decide) true true false s t

end Long

omit hirr in
theorem mlr_inv' (i j : Fin 3) (u v : Bool) (a : F) :
    (mlr 4 b c i j u v a)⁻¹ = mlr 4 b c i j u v a := by
  by_cases h : i = j
  · subst h
    simp [mlr]
  · rw [mlr_of_ne h, ← map_inv, ← ofAdd_neg, CharTwo.neg_eq]

theorem msr_inv' (i : Fin 3) (u : Bool) (p : Fin 2 → F) :
    (msr 4 hirr i u p)⁻¹ = msr 4 hirr i u p := by
  rw [msr, ← map_inv, ← ofAdd_neg]
  congr 2
  funext k
  exact CharTwo.neg_eq _

theorem b3_comm_4_2 (p : Fin 2 → F) (s : F) :
    ⁅b3xS hirr 4 p, b3xL b c 2 s⁆ = b3xS hirr 8 (s • p) * b3xL b c 10 (s * planeNorm b c p) := by
  have e : ⁅b3xL b c 2 s, b3xS hirr 4 p⁆ =
      b3xS hirr 8 (s • p) * b3xL b c 10 (s * planeNorm b c p) := by
    simp only [b3xL, b3xS]
    rw [mlr_of_ne (by decide), mlr_of_ne (by decide)]
    exact commutator_longRoot_twShortRoot 4 hirr (i := (1 : Fin 3)) (j := 2) (by decide) true
      false s p
  have hc : Commute (b3xL b c 10 (s * planeNorm b c p)) (b3xS hirr 8 (s • p)) := by
    simp only [b3xL, b3xS]
    rw [mlr_of_ne (by decide)]
    exact commute_longRoot_twShortRoot_left 4 hirr (i := (1 : Fin 3)) (j := 2) (by decide)
      true true (s * planeNorm b c p) (s • p)
  rw [← commutatorElement_inv, e, _root_.mul_inv_rev, b3xL, b3xS, mlr_inv', msr_inv', ← b3xL,
    ← b3xS]
  exact hc.eq

theorem b3_comm_4_8 (p q : Fin 2 → F) :
    ⁅b3xS hirr 4 p, b3xS hirr 8 q⁆ = b3xL b c 10 (polarPlane b c p q) := by
  have e : ⁅b3xS hirr 4 p, b3xS hirr 8 q⁆ = mlr 4 b c 2 1 true true (-polarPlane b c p q) := by
    rw [mlr_of_ne (by decide)]
    exact commutator_twShortRoot_twShortRoot 4 hirr (i := (2 : Fin 3)) (j := 1) (by decide)
      true true p q
  rw [e, mlr_swap, CharTwo.neg_eq]
  rfl

omit [CharP F 2] in
theorem b3_commute_4_10 (p : Fin 2 → F) (s : F) :
    Commute (b3xS hirr 4 p) (b3xL b c 10 s) := by
  simp only [b3xL, b3xS, msr]
  rw [mlr_of_ne (by decide)]
  exact (commute_longRoot_twShortRoot_right 4 hirr (i := (1 : Fin 3)) (j := 2) (by decide)
    true true s p).symm

omit [CharP F 2] in
theorem b3_commute_8_10 (p : Fin 2 → F) (s : F) :
    Commute (b3xS hirr 8 p) (b3xL b c 10 s) := by
  simp only [b3xL, b3xS, msr]
  rw [mlr_of_ne (by decide)]
  exact (commute_longRoot_twShortRoot_left 4 hirr (i := (1 : Fin 3)) (j := 2) (by decide)
    true true s p).symm

omit [CharP F 2] in
theorem b3_commute_8_2 (p : Fin 2 → F) (s : F) : Commute (b3xS hirr 8 p) (b3xL b c 2 s) := by
  simp only [b3xL, b3xS, msr]
  rw [mlr_of_ne (by decide)]
  exact (commute_longRoot_twShortRoot_left 4 hirr (i := (1 : Fin 3)) (j := 2) (by decide)
    true false s p).symm

omit [CharP F 2] in
theorem b3_commute_0_4 (s : F) (p : Fin 2 → F) : Commute (b3xL b c 0 s) (b3xS hirr 4 p) := by
  simp only [b3xL, b3xS, msr]
  rw [mlr_of_ne (by decide)]
  exact commute_longRoot_twShortRoot_of_ne 4 hirr (i := (0 : Fin 3)) (j := 1) (k := 2)
    (by decide) (by decide) (by decide) true false true s p

end Rels

section RankOne

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem exists_sl2_b3_0 :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup (quadMinus 4 F b c),
      Function.Injective φ ∧ (∀ x, φ (sl2Upper x) = b3xL b c 0 x) ∧
        ∀ x, φ (sl2Lower x) = b3xL b c 1 x := by
  refine ⟨(minusFrame 4 b c).longSL2 (i := (0 : Fin 3)) (j := 1) (by decide) true false,
    SpinFrame.longSL2_injective _ _ _ _, fun x => ?_, fun x => ?_⟩
  · simp only [b3xL]
    rw [mlr_of_ne (by decide)]
    exact HypFrame.longSL2_upperSL2 _ _ _ _ x
  · simp only [b3xL]
    rw [mlr_of_ne (by decide)]
    exact HypFrame.longSL2_lowerSL2 _ _ _ _ x

theorem exists_sl2_b3_1 :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup (quadMinus 4 F b c),
      Function.Injective φ ∧ (∀ x, φ (sl2Upper x) = b3xL b c 2 x) ∧
        ∀ x, φ (sl2Lower x) = b3xL b c 3 x := by
  refine ⟨(minusFrame 4 b c).longSL2 (i := (1 : Fin 3)) (j := 2) (by decide) true false,
    SpinFrame.longSL2_injective _ _ _ _, fun x => ?_, fun x => ?_⟩
  · simp only [b3xL]
    rw [mlr_of_ne (by decide)]
    exact HypFrame.longSL2_upperSL2 _ _ _ _ x
  · simp only [b3xL]
    rw [mlr_of_ne (by decide)]
    exact HypFrame.longSL2_lowerSL2 _ _ _ _ x

theorem four_le_card_shortField [Finite F] : 4 ≤ Nat.card (ShortField b c) := by
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod]
  nlinarith

theorem exists_sl2_b3_2 [CharP F 2] [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] :
    ∃ φ : SL2E b c →* spinGroup (quadMinus 4 F b c),
      Function.Injective φ ∧ (∀ t, φ (sl2Upper t) = b3xS hirr 4 (fieldCoord t)) ∧
        ∀ t, φ (sl2Lower t) = b3xS hirr 5 (starCoord t) := by
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective 2
  obtain ⟨Θ, hU, hL⟩ := exists_hom_of_rankOneRels (shortRels 4 hirr (2 : Fin 3))
  have ex : ∀ t, (shortRels 4 hirr (2 : Fin 3)).x t = b3xS hirr 4 (fieldCoord t) := fun t => by
    rw [shortRels_x, b3xS, msr]
    rfl
  have ey : ∀ t, (shortRels 4 hirr (2 : Fin 3)).y t = b3xS hirr 5 (starCoord t) := fun t => by
    rw [shortRels_y, b3xS, msr]
    rfl
  refine ⟨Θ, injective_of_sl2_charTwo four_le_card_shortField Θ ?_, fun t => (hU t).trans (ex t),
    fun t => (hL t).trans (ey t)⟩
  rw [hU, shortRels_x]
  intro h1
  have h2 := congrArg Multiplicative.toAdd (shortPosHom_injective 4 hirr (2 : Fin 3)
    (h1.trans (map_one _).symm))
  rw [toAdd_ofAdd, toAdd_one, fieldCoord_one] at h2
  exact planeOne_ne_zero h2

end RankOne

section Pairs

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

noncomputable abbrev Φm : Steinberg.RootSystem (Fin (4 - 1)) :=
  Steinberg.RootSystem.ofCartan (minusDatum 4 hirr).isFiniteType (minusDatum 4 hirr).divisible

theorem b3_pair01 {γ : Fin 3 → ℤ}
    (hγ : γ ∈ pairRoots (minusDatum 4 hirr) (0 : Fin 3) (1 : Fin 3)) :
    γ = b3r 0 ∨ γ = b3r 1 ∨ γ = b3r 2 ∨ γ = b3r 3 ∨ γ = b3r 6 ∨ γ = b3r 7 := by
  have key : ∀ v ∈ b3Roots, v 2 = 0 →
      v = b3r 0 ∨ v = b3r 1 ∨ v = b3r 2 ∨ v = b3r 3 ∨ v = b3r 6 ∨ v = b3r 7 := by
    decide
  exact key γ (mem_b3Roots hγ.1)
    (hγ.2 (2 : Fin 3) (show (2 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 1 by decide))

theorem b3_pair12 {γ : Fin 3 → ℤ}
    (hγ : γ ∈ pairRoots (minusDatum 4 hirr) (1 : Fin 3) (2 : Fin 3)) :
    γ = b3r 2 ∨ γ = b3r 3 ∨ γ = b3r 4 ∨ γ = b3r 5 ∨ γ = b3r 8 ∨ γ = b3r 9 ∨ γ = b3r 10 ∨
      γ = b3r 11 := by
  have key : ∀ v ∈ b3Roots, v 0 = 0 →
      v = b3r 2 ∨ v = b3r 3 ∨ v = b3r 4 ∨ v = b3r 5 ∨ v = b3r 8 ∨ v = b3r 9 ∨ v = b3r 10 ∨
        v = b3r 11 := by
    decide
  exact key γ (mem_b3Roots hγ.1)
    (hγ.2 (0 : Fin 3) (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide))

theorem b3_pair02 {γ : Fin 3 → ℤ}
    (hγ : γ ∈ pairRoots (minusDatum 4 hirr) (0 : Fin 3) (2 : Fin 3)) :
    γ = b3r 0 ∨ γ = b3r 1 ∨ γ = b3r 4 ∨ γ = b3r 5 := by
  have key : ∀ v ∈ b3Roots, v 1 = 0 → v = b3r 0 ∨ v = b3r 1 ∨ v = b3r 4 ∨ v = b3r 5 := by
    decide
  exact key γ (mem_b3Roots hγ.1)
    (hγ.2 (1 : Fin 3) (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide))

theorem b3_pair_self {k : Fin 3} {γ : Fin 3 → ℤ}
    (hγ : γ ∈ pairRoots (minusDatum 4 hirr) k k) : γ = Pi.single k 1 ∨ γ = -Pi.single k 1 := by
  have key : ∀ k : Fin 3, ∀ v ∈ b3Roots, (∀ l, l ≠ k → v l = 0) →
      v = Pi.single k 1 ∨ v = -Pi.single k 1 := by
    decide
  exact key k γ (mem_b3Roots hγ.1) fun l hl => hγ.2 l hl hl

theorem pairRoots_comm_minus {i j : Fin 3} :
    pairRoots (minusDatum 4 hirr) i j = pairRoots (minusDatum 4 hirr) j i := by
  ext γ
  exact ⟨fun h => ⟨h.1, fun k hj hi => h.2 k hi hj⟩, fun h => ⟨h.1, fun k hi hj => h.2 k hj hi⟩⟩

theorem ht_b3r_neg {a : Fin 12} (ha : a ∈ ({1, 3, 5, 7, 9, 11} : Finset (Fin 12))) :
    ¬ 0 < Steinberg.ht (b3r a) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Pairs

section Frame

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {G : Type*} [Group G]

structure IsB3Frame [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (fL : Fin 12 → F → G)
    (fS : Fin 12 → (Fin 2 → F) → G) (w01 w12 w02 : Fin 3 → G) : Prop where
  addL0 : ∀ x y, fL 0 (x + y) = fL 0 x * fL 0 y
  addL2 : ∀ x y, fL 2 (x + y) = fL 2 x * fL 2 y
  addL6 : ∀ x y, fL 6 (x + y) = fL 6 x * fL 6 y
  addL10 : ∀ x y, fL 10 (x + y) = fL 10 x * fL 10 y
  addS4 : ∀ p q, fS 4 (p + q) = fS 4 p * fS 4 q
  addS8 : ∀ p q, fS 8 (p + q) = fS 8 p * fS 8 q
  comm_0_2 : ∀ s t, ⁅fL 0 s, fL 2 t⁆ = fL 6 (s * t)
  commute_0_6 : ∀ s t, Commute (fL 0 s) (fL 6 t)
  commute_6_2 : ∀ s t, Commute (fL 6 s) (fL 2 t)
  comm_4_2 : ∀ p s, ⁅fS 4 p, fL 2 s⁆ = fS 8 (s • p) * fL 10 (s * planeNorm b c p)
  comm_4_8 : ∀ p q, ⁅fS 4 p, fS 8 q⁆ = fL 10 (polarPlane b c p q)
  commute_4_10 : ∀ p s, Commute (fS 4 p) (fL 10 s)
  commute_8_10 : ∀ p s, Commute (fS 8 p) (fL 10 s)
  commute_8_2 : ∀ p s, Commute (fS 8 p) (fL 2 s)
  commute_10_2 : ∀ s t, Commute (fL 10 s) (fL 2 t)
  commute_0_4 : ∀ s p, Commute (fL 0 s) (fS 4 p)
  w01_0_0 : ∀ x, w01 0 * fL 0 x * (w01 0)⁻¹ = fL 1 x
  w01_0_1 : ∀ x, w01 0 * fL 1 x * (w01 0)⁻¹ = fL 0 x
  w01_0_2 : ∀ x, w01 0 * fL 2 x * (w01 0)⁻¹ = fL 6 x
  w01_0_3 : ∀ x, w01 0 * fL 3 x * (w01 0)⁻¹ = fL 7 x
  w01_0_6 : ∀ x, w01 0 * fL 6 x * (w01 0)⁻¹ = fL 2 x
  w01_0_7 : ∀ x, w01 0 * fL 7 x * (w01 0)⁻¹ = fL 3 x
  w01_1_0 : ∀ x, w01 1 * fL 0 x * (w01 1)⁻¹ = fL 6 x
  w01_1_1 : ∀ x, w01 1 * fL 1 x * (w01 1)⁻¹ = fL 7 x
  w01_1_2 : ∀ x, w01 1 * fL 2 x * (w01 1)⁻¹ = fL 3 x
  w01_1_3 : ∀ x, w01 1 * fL 3 x * (w01 1)⁻¹ = fL 2 x
  w01_1_6 : ∀ x, w01 1 * fL 6 x * (w01 1)⁻¹ = fL 0 x
  w01_1_7 : ∀ x, w01 1 * fL 7 x * (w01 1)⁻¹ = fL 1 x
  w12_1_2 : ∀ x, w12 1 * fL 2 x * (w12 1)⁻¹ = fL 3 x
  w12_1_3 : ∀ x, w12 1 * fL 3 x * (w12 1)⁻¹ = fL 2 x
  w12_1_4 : ∀ p, w12 1 * fS 4 p * (w12 1)⁻¹ = fS 8 p
  w12_1_5 : ∀ p, w12 1 * fS 5 p * (w12 1)⁻¹ = fS 9 p
  w12_1_8 : ∀ p, w12 1 * fS 8 p * (w12 1)⁻¹ = fS 4 p
  w12_1_9 : ∀ p, w12 1 * fS 9 p * (w12 1)⁻¹ = fS 5 p
  w12_1_10 : ∀ x, w12 1 * fL 10 x * (w12 1)⁻¹ = fL 10 x
  w12_1_11 : ∀ x, w12 1 * fL 11 x * (w12 1)⁻¹ = fL 11 x
  w12_2_2 : ∀ x, w12 2 * fL 2 x * (w12 2)⁻¹ = fL 10 x
  w12_2_3 : ∀ x, w12 2 * fL 3 x * (w12 2)⁻¹ = fL 11 x
  w12_2_4 : ∀ p, w12 2 * fS 4 p * (w12 2)⁻¹ = fS 5 p
  w12_2_5 : ∀ p, w12 2 * fS 5 p * (w12 2)⁻¹ = fS 4 p
  w12_2_8 : ∀ p, w12 2 * fS 8 p * (w12 2)⁻¹ = fS 8 p
  w12_2_9 : ∀ p, w12 2 * fS 9 p * (w12 2)⁻¹ = fS 9 p
  w12_2_10 : ∀ x, w12 2 * fL 10 x * (w12 2)⁻¹ = fL 2 x
  w12_2_11 : ∀ x, w12 2 * fL 11 x * (w12 2)⁻¹ = fL 3 x
  w02_0_0 : ∀ x, w02 0 * fL 0 x * (w02 0)⁻¹ = fL 1 x
  w02_0_1 : ∀ x, w02 0 * fL 1 x * (w02 0)⁻¹ = fL 0 x
  w02_0_4 : ∀ p, w02 0 * fS 4 p * (w02 0)⁻¹ = fS 4 p
  w02_0_5 : ∀ p, w02 0 * fS 5 p * (w02 0)⁻¹ = fS 5 p
  w02_2_0 : ∀ x, w02 2 * fL 0 x * (w02 2)⁻¹ = fL 0 x
  w02_2_1 : ∀ x, w02 2 * fL 1 x * (w02 2)⁻¹ = fL 1 x
  w02_2_4 : ∀ p, w02 2 * fS 4 p * (w02 2)⁻¹ = fS 5 (planeRefl b c planeOne p)
  w02_2_5 : ∀ p, w02 2 * fS 5 p * (w02 2)⁻¹ = fS 4 (planeRefl b c planeOne p)
  rank0 : ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ x, Θ (sl2Upper x) = fL 0 x) ∧ ∀ x, Θ (sl2Lower x) = fL 1 x
  rank1 : ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ x, Θ (sl2Upper x) = fL 2 x) ∧ ∀ x, Θ (sl2Lower x) = fL 3 x
  rank2 : ∃ Θ : SL2E b c →* G,
    (∀ t, Θ (sl2Upper t) = fS 4 (fieldCoord t)) ∧ ∀ t, Θ (sl2Lower t) = fS 5 (starCoord t)
  gen : Subgroup.closure (Set.range (fL 0) ∪ Set.range (fL 1) ∪ Set.range (fL 2) ∪
    Set.range (fL 3) ∪ Set.range (fS 4) ∪ Set.range (fS 5)) = ⊤
  nt : ∃ x, fL 0 x ≠ 1

theorem b3_weyl_long (fL : Fin 12 → F → G) (fS : Fin 12 → (Fin 2 → F) → G) {k : Fin 3}
    {a a' : Fin 12} (ha : b3Short a = false) (ha' : b3Short a' = false)
    (hr : CFSG.LieType.RootSystem.reflection (cartanB 3) k (b3r a) = b3r a')
    {n : spinGroup (quadMinus 4 F b c)} (hK : ∀ x, n * b3xL b c a x * n⁻¹ = b3xL b c a' x)
    {w : G} (hG : ∀ x, w * fL a x * w⁻¹ = fL a' x) :
    (∀ y ∈ (minusDatum 4 hirr).rootGroup (b3r a),
      n * y * n⁻¹ ∈ (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k (b3r a))) ∧
    ∀ (z : (minusDatum 4 hirr).rootGroup (b3r a))
      (y : (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k (b3r a))),
      (y : spinGroup (quadMinus 4 F b c)) = n * z * n⁻¹ →
        w * b3PhiOf hirr fL fS (b3r a) z * w⁻¹ =
          b3PhiOf hirr fL fS ((Φm hirr).refl k (b3r a)) y := by
  have hr' : (Φm hirr).refl k (b3r a) = b3r a' := hr
  refine ⟨fun y hy => ?_, fun z y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_b3xL_eq hirr ha hy
    rw [hK, hr']
    exact b3xL_mem hirr ha' x
  · obtain ⟨⟨z, hz⟩, rfl⟩ : ∃ z', z' = z := ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := exists_b3xL_eq hirr ha hz
    rw [b3PhiOf_long hirr fL fS ha x hz,
      apply_eq_of_index_eq (b3PhiOf hirr fL fS) hr' y ⟨b3xL b c a' x, b3xL_mem hirr ha' x⟩
        (hy.trans (hK x)), b3PhiOf_long hirr fL fS ha' x]
    exact hG x

theorem b3_weyl_short (fL : Fin 12 → F → G) (fS : Fin 12 → (Fin 2 → F) → G) {k : Fin 3}
    {a a' : Fin 12} (ha : b3Short a = true) (ha' : b3Short a' = true)
    (hr : CFSG.LieType.RootSystem.reflection (cartanB 3) k (b3r a) = b3r a')
    (σ : (Fin 2 → F) → (Fin 2 → F)) {n : spinGroup (quadMinus 4 F b c)}
    (hK : ∀ p, n * b3xS hirr a p * n⁻¹ = b3xS hirr a' (σ p)) {w : G}
    (hG : ∀ p, w * fS a p * w⁻¹ = fS a' (σ p)) :
    (∀ y ∈ (minusDatum 4 hirr).rootGroup (b3r a),
      n * y * n⁻¹ ∈ (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k (b3r a))) ∧
    ∀ (z : (minusDatum 4 hirr).rootGroup (b3r a))
      (y : (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k (b3r a))),
      (y : spinGroup (quadMinus 4 F b c)) = n * z * n⁻¹ →
        w * b3PhiOf hirr fL fS (b3r a) z * w⁻¹ =
          b3PhiOf hirr fL fS ((Φm hirr).refl k (b3r a)) y := by
  have hr' : (Φm hirr).refl k (b3r a) = b3r a' := hr
  refine ⟨fun y hy => ?_, fun z y hy => ?_⟩
  · obtain ⟨p, rfl⟩ := exists_b3xS_eq hirr ha hy
    rw [hK, hr']
    exact b3xS_mem hirr ha' _
  · obtain ⟨⟨z, hz⟩, rfl⟩ : ∃ z', z' = z := ⟨z, rfl⟩
    obtain ⟨p, rfl⟩ := exists_b3xS_eq hirr ha hz
    rw [b3PhiOf_short hirr fL fS ha p hz,
      apply_eq_of_index_eq (b3PhiOf hirr fL fS) hr' y ⟨b3xS hirr a' (σ p), b3xS_mem hirr ha' _⟩
        (hy.trans (hK p)), b3PhiOf_short hirr fL fS ha' (σ p)]
    exact hG p

noncomputable abbrev n01 (b c : F) : Fin 3 → spinGroup (quadMinus 4 F b c) := ![mnA b c, mnB b c, 1]

noncomputable abbrev n12 (b c : F) : Fin 3 → spinGroup (quadMinus 4 F b c) := ![1, mnB b c, mnC b c]

noncomputable abbrev n02 : Fin 3 → spinGroup (quadMinus 4 F b c) := ![mnA b c, 1, mnD hirr]

@[expose] def b3i01 : Fin 3 → Fin 12 := ![0, 6, 2]

@[expose] noncomputable def b3x12 : ∀ i, tb2Par F i → spinGroup (quadMinus 4 F b c)
  | 0 => b3xS hirr 4
  | 1 => b3xS hirr 8
  | 2 => b3xL b c 10
  | 3 => b3xL b c 2

@[expose] def b3r12 : Fin 4 → Fin 3 → ℤ := ![b3r 4, b3r 8, b3r 10, b3r 2]

@[expose] noncomputable def b3x02 : ∀ i, ma1Par F i → spinGroup (quadMinus 4 F b c)
  | 0 => b3xL b c 0
  | 1 => b3xS hirr 4

@[expose] def b3r02 : Fin 2 → Fin 3 → ℤ := ![b3r 0, b3r 4]

theorem b3x12_mem (i : Fin 4) (c' : tb2Par F i) :
    b3x12 hirr i c' ∈ (minusDatum 4 hirr).rootGroup (b3r12 i) :=
  match i, c' with
  | 0, p => b3xS_mem hirr (a := 4) rfl p
  | 1, p => b3xS_mem hirr (a := 8) rfl p
  | 2, x => b3xL_mem hirr (a := 10) rfl x
  | 3, x => b3xL_mem hirr (a := 2) rfl x

theorem b3x02_mem (i : Fin 2) (c' : ma1Par F i) :
    b3x02 hirr i c' ∈ (minusDatum 4 hirr).rootGroup (b3r02 i) :=
  match i, c' with
  | 0, x => b3xL_mem hirr (a := 0) rfl x
  | 1, p => b3xS_mem hirr (a := 4) rfl p

theorem b3r12_injective : Function.Injective b3r12 := by decide

theorem b3r02_injective : Function.Injective b3r02 := by decide

theorem b3i01_injective : Function.Injective (fun i => b3r (b3i01 i)) := by decide

theorem b3_list01 : (List.map (fun i => b3r (b3i01 i)) [0, 2, 1]).Nodup ∧
    (∀ γ ∈ List.map (fun i => b3r (b3i01 i)) [0, 2, 1], 0 < 1 * Steinberg.ht γ) ∧
    (List.map (fun i => b3r (b3i01 i)) [0, 2, 1]).Pairwise
      (fun γ δ => 1 * Steinberg.ht γ ≤ 1 * Steinberg.ht δ) := by
  decide

theorem b3_list12 : (List.map b3r12 [0, 3, 1, 2]).Nodup ∧
    (∀ γ ∈ List.map b3r12 [0, 3, 1, 2], 0 < 1 * Steinberg.ht γ) ∧
    (List.map b3r12 [0, 3, 1, 2]).Pairwise
      (fun γ δ => 1 * Steinberg.ht γ ≤ 1 * Steinberg.ht δ) := by
  decide

theorem b3_list02 : (List.map b3r02 [0, 1]).Nodup ∧
    (∀ γ ∈ List.map b3r02 [0, 1], 0 < 1 * Steinberg.ht γ) ∧
    (List.map b3r02 [0, 1]).Pairwise (fun γ δ => 1 * Steinberg.ht γ ≤ 1 * Steinberg.ht δ) := by
  decide

theorem b3r12_mem (i : Fin 4) : b3r12 i ∈ CFSG.LieType.RootSystem.roots
    (isFiniteType_cartanB 3) ∅ := by
  fin_cases i
  exacts [b3r_mem_roots 4, b3r_mem_roots 8, b3r_mem_roots 10, b3r_mem_roots 2]

theorem b3r02_mem (i : Fin 2) : b3r02 i ∈ CFSG.LieType.RootSystem.roots
    (isFiniteType_cartanB 3) ∅ := by
  fin_cases i
  exacts [b3r_mem_roots 0, b3r_mem_roots 4]

@[expose] def b3psi12 (fL : Fin 12 → F → G) (fS : Fin 12 → (Fin 2 → F) → G) :
    (Σ i, tb2Par F i) → G
  | ⟨0, p⟩ => fS 4 p
  | ⟨1, p⟩ => fS 8 p
  | ⟨2, x⟩ => fL 10 x
  | ⟨3, x⟩ => fL 2 x

@[expose] def b3psi02 (fL : Fin 12 → F → G) (fS : Fin 12 → (Fin 2 → F) → G) :
    (Σ i, ma1Par F i) → G
  | ⟨0, x⟩ => fL 0 x
  | ⟨1, p⟩ => fS 4 p

namespace IsB3Frame

variable [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] {fL : Fin 12 → F → G}
  {fS : Fin 12 → (Fin 2 → F) → G} {w01 w12 w02 : Fin 3 → G}
  (h : IsB3Frame (b := b) (c := c) fL fS w01 w12 w02)
include h

theorem weyl01 : ∀ k : Fin 3, (k = 0 ∨ k = 1) →
    ∀ γ ∈ pairRoots (minusDatum 4 hirr) (0 : Fin 3) (1 : Fin 3),
      (∀ y ∈ (minusDatum 4 hirr).rootGroup γ,
        n01 b c k * y * (n01 b c k)⁻¹ ∈ (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k γ)) ∧
      ∀ (z : (minusDatum 4 hirr).rootGroup γ)
        (y : (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k γ)),
        (y : spinGroup (quadMinus 4 F b c)) = n01 b c k * z * (n01 b c k)⁻¹ →
          w01 k * b3PhiOf hirr fL fS γ z * (w01 k)⁻¹ =
            b3PhiOf hirr fL fS ((Φm hirr).refl k γ) y := by
  rintro k (rfl | rfl) γ hγ <;> rcases b3_pair01 hirr hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L0 h.w01_0_0
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L1 h.w01_0_1
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L2 h.w01_0_2
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L3 h.w01_0_3
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L6 h.w01_0_6
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L7 h.w01_0_7
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L0 h.w01_1_0
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L1 h.w01_1_1
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L2 h.w01_1_2
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L3 h.w01_1_3
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L6 h.w01_1_6
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L7 h.w01_1_7

theorem weyl12 : ∀ k : Fin 3, (k = 1 ∨ k = 2) →
    ∀ γ ∈ pairRoots (minusDatum 4 hirr) (1 : Fin 3) (2 : Fin 3),
      (∀ y ∈ (minusDatum 4 hirr).rootGroup γ,
        n12 b c k * y * (n12 b c k)⁻¹ ∈ (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k γ)) ∧
      ∀ (z : (minusDatum 4 hirr).rootGroup γ)
        (y : (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k γ)),
        (y : spinGroup (quadMinus 4 F b c)) = n12 b c k * z * (n12 b c k)⁻¹ →
          w12 k * b3PhiOf hirr fL fS γ z * (w12 k)⁻¹ =
            b3PhiOf hirr fL fS ((Φm hirr).refl k γ) y := by
  rintro k (rfl | rfl) γ hγ <;>
    rcases b3_pair12 hirr hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L2 h.w12_1_2
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L3 h.w12_1_3
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnB_S4 hirr) h.w12_1_4
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnB_S5 hirr) h.w12_1_5
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnB_S8 hirr) h.w12_1_8
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnB_S9 hirr) h.w12_1_9
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L10 h.w12_1_10
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnB_L11 h.w12_1_11
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnC_L2 h.w12_2_2
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnC_L3 h.w12_2_3
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnC_S4 hirr) h.w12_2_4
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnC_S5 hirr) h.w12_2_5
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnC_S8 hirr) h.w12_2_8
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnC_S9 hirr) h.w12_2_9
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnC_L10 h.w12_2_10
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnC_L11 h.w12_2_11

theorem weyl02 : ∀ k : Fin 3, (k = 0 ∨ k = 2) →
    ∀ γ ∈ pairRoots (minusDatum 4 hirr) (0 : Fin 3) (2 : Fin 3),
      (∀ y ∈ (minusDatum 4 hirr).rootGroup γ,
        n02 hirr k * y * (n02 hirr k)⁻¹ ∈ (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k γ)) ∧
      ∀ (z : (minusDatum 4 hirr).rootGroup γ)
        (y : (minusDatum 4 hirr).rootGroup ((Φm hirr).refl k γ)),
        (y : spinGroup (quadMinus 4 F b c)) = n02 hirr k * z * (n02 hirr k)⁻¹ →
          w02 k * b3PhiOf hirr fL fS γ z * (w02 k)⁻¹ =
            b3PhiOf hirr fL fS ((Φm hirr).refl k γ) y := by
  rintro k (rfl | rfl) γ hγ <;> rcases b3_pair02 hirr hγ with rfl | rfl | rfl | rfl
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L0 h.w02_0_0
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) mnA_L1 h.w02_0_1
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnA_S4 hirr) h.w02_0_4
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) id (mnA_S5 hirr) h.w02_0_5
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) (mnD_L0 hirr) h.w02_2_0
  · exact b3_weyl_long hirr fL fS rfl rfl (by decide) (mnD_L1 hirr) h.w02_2_1
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) _ (mnD_S4 hirr) h.w02_2_4
  · exact b3_weyl_short hirr fL fS rfl rfl (by decide) _ (mnD_S5 hirr) h.w02_2_5

omit [CharP F 2] in
theorem pos01 [Finite F] :
    ExtendsToHom (minusDatum 4 hirr).rootGroup
      (pairRoots (minusDatum 4 hirr) (0 : Fin 3) (1 : Fin 3) ∩ (Φm hirr).pos)
      (b3PhiOf hirr fL fS) := by
  have := Fintype.ofFinite F
  have hsh : ∀ i, b3Short (b3i01 i) = false := by decide
  refine extendsToHom_of_rels (F := fun _ => F) (cm := a2Cm (K := F)) (ht := a2Ht)
    (fun α s β t => a2Cm_mem_above α s β t) (fun i => b3r (b3i01 i))
    (fun i c' => b3xL b c (b3i01 i) c') (fun i c' => b3xL_mem hirr (hsh i) c') ?_ [0, 2, 1]
    ?_ (fun γ hγ => ?_) (fun i y hy => exists_b3xL_eq hirr (hsh i) hy)
    (fun g => fL (b3i01 g.1) g.2) ?_ (fun i c' => b3PhiOf_long hirr fL fS (hsh i) c' _)
  · exact rels_a2Cm_of (fun i c' d => b3xL_add _ c' d) (fun s t => b3_comm_0_2 s t)
      (fun s t => b3_commute_0_6 s t) (fun s t => b3_commute_6_2 s t)
  · refine injective_prod_of_prodInjectiveFor (F := fun _ => F)
      (X := (minusDatum 4 hirr).rootGroup) _ b3i01_injective _
      (fun i c' => b3xL_mem hirr (hsh i) c') (fun i => b3xL_injective (F := F) _) _
      (by decide) ?_
    exact minusDatum_prodInjective 4 hirr 1 _ b3_list01.1
      (fun γ hγ => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hγ
        exact b3r_mem_roots _) b3_list01.2.1 b3_list01.2.2
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases b3_pair01 hirr hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
    · exact ⟨2, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
    · exact ⟨1, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
  · refine rels_a2Cm_of (fun i c' d => ?_) h.comm_0_2 h.commute_0_6 h.commute_6_2
    fin_cases i
    exacts [h.addL0 c' d, h.addL6 c' d, h.addL2 c' d]

theorem pos12 [Finite F] :
    ExtendsToHom (minusDatum 4 hirr).rootGroup
      (pairRoots (minusDatum 4 hirr) (1 : Fin 3) (2 : Fin 3) ∩ (Φm hirr).pos)
      (b3PhiOf hirr fL fS) := by
  have := Fintype.ofFinite F
  have hfin : ∀ i, Fintype (tb2Par F i) := fun i =>
    match i with
    | 0 => (inferInstance : Fintype (Fin 2 → F))
    | 1 => (inferInstance : Fintype (Fin 2 → F))
    | 2 => (inferInstance : Fintype F)
    | 3 => (inferInstance : Fintype F)
  refine extendsToHom_of_rels (F := tb2Par F) (cm := tb2Cm (planeNorm b c) (polarPlane b c))
    (ht := b2Ht) (fun α s β t => tb2Cm_mem_above _ _ α s β t) b3r12 (b3x12 hirr)
    (b3x12_mem hirr) ?_ [0, 3, 1, 2] ?_ (fun γ hγ => ?_) (fun i y hy => ?_)
    (b3psi12 fL fS) ?_ (fun i c' => ?_)
  · refine rels_tb2Cm_of (φ := fun g => b3x12 hirr g.1 g.2) _ _
      (tb2_add_of (φ := fun g => b3x12 hirr g.1 g.2) (fun p q => b3xS_add hirr 4 p q)
        (fun p q => b3xS_add hirr 8 p q) (fun x y => b3xL_add 10 x y)
        (fun x y => b3xL_add 2 x y))
      (fun p q => b3_comm_4_8 hirr p q) (fun p s => b3_comm_4_2 hirr p s)
      (fun p s => b3_commute_4_10 hirr p s) (fun p s => b3_commute_8_10 hirr p s)
      (fun p s => b3_commute_8_2 hirr p s) (fun s t => b3_commute_10_2 s t)
  · refine injective_prod_of_prodInjectiveFor (F := tb2Par F)
      (X := (minusDatum 4 hirr).rootGroup) b3r12 b3r12_injective (b3x12 hirr) (b3x12_mem hirr)
      (fun i => ?_) _ (by decide) ?_
    · match i with
      | 0 => exact b3xS_injective hirr 4
      | 1 => exact b3xS_injective hirr 8
      | 2 => exact b3xL_injective (F := F) 10
      | 3 => exact b3xL_injective (F := F) 2
    · exact minusDatum_prodInjective 4 hirr 1 _ b3_list12.1
        (fun γ hγ => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hγ
          exact b3r12_mem i) b3_list12.2.1 b3_list12.2.2
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases b3_pair12 hirr hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
    · exact ⟨0, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
    · exact ⟨1, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
    · exact ⟨2, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
  · match i, y, hy with
    | 0, y, hy => exact exists_b3xS_eq hirr (a := 4) rfl hy
    | 1, y, hy => exact exists_b3xS_eq hirr (a := 8) rfl hy
    | 2, y, hy => exact exists_b3xL_eq hirr (a := 10) rfl hy
    | 3, y, hy => exact exists_b3xL_eq hirr (a := 2) rfl hy
  · exact rels_tb2Cm_of (φ := b3psi12 fL fS) _ _
      (tb2_add_of (φ := b3psi12 fL fS) h.addS4 h.addS8 h.addL10 h.addL2) h.comm_4_8 h.comm_4_2
      h.commute_4_10 h.commute_8_10 h.commute_8_2 h.commute_10_2
  · match i, c' with
    | 0, p => exact b3PhiOf_short hirr fL fS (a := 4) rfl p _
    | 1, p => exact b3PhiOf_short hirr fL fS (a := 8) rfl p _
    | 2, x => exact b3PhiOf_long hirr fL fS (a := 10) rfl x _
    | 3, x => exact b3PhiOf_long hirr fL fS (a := 2) rfl x _

omit [CharP F 2] in
theorem pos02 [Finite F] :
    ExtendsToHom (minusDatum 4 hirr).rootGroup
      (pairRoots (minusDatum 4 hirr) (0 : Fin 3) (2 : Fin 3) ∩ (Φm hirr).pos)
      (b3PhiOf hirr fL fS) := by
  have := Fintype.ofFinite F
  have hfin : ∀ i, Fintype (ma1Par F i) := fun i =>
    match i with
    | 0 => (inferInstance : Fintype F)
    | 1 => (inferInstance : Fintype (Fin 2 → F))
  refine extendsToHom_of_rels (F := ma1Par F) (cm := ma1Cm F) (ht := a1a1Ht)
    (fun α s β t => ma1Cm_mem_above α s β t) b3r02 (b3x02 hirr) (b3x02_mem hirr) ?_ [0, 1] ?_
    (fun γ hγ => ?_) (fun i y hy => ?_) (b3psi02 fL fS) ?_ (fun i c' => ?_)
  · exact rels_ma1Cm_of (φ := fun g => b3x02 hirr g.1 g.2) (fun x y => b3xL_add 0 x y)
      (fun p q => b3xS_add hirr 4 p q) (fun s p => b3_commute_0_4 hirr s p)
  · refine injective_prod_of_prodInjectiveFor (F := ma1Par F)
      (X := (minusDatum 4 hirr).rootGroup) b3r02 b3r02_injective (b3x02 hirr) (b3x02_mem hirr)
      (fun i => ?_) _ (by decide) ?_
    · match i with
      | 0 => exact b3xL_injective (F := F) 0
      | 1 => exact b3xS_injective hirr 4
    · exact minusDatum_prodInjective 4 hirr 1 _ b3_list02.1
        (fun γ hγ => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hγ
          exact b3r02_mem i) b3_list02.2.1 b3_list02.2.2
  · obtain ⟨hγ, hpos⟩ := hγ
    rcases b3_pair02 hirr hγ with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
    · exact ⟨1, rfl⟩
    · exact absurd hpos.2 (ht_b3r_neg (by decide))
  · match i, y, hy with
    | 0, y, hy => exact exists_b3xL_eq hirr (a := 0) rfl hy
    | 1, y, hy => exact exists_b3xS_eq hirr (a := 4) rfl hy
  · exact rels_ma1Cm_of (φ := b3psi02 fL fS) h.addL0 h.addS4 h.commute_0_4
  · match i, c' with
    | 0, x => exact b3PhiOf_long hirr fL fS (a := 0) rfl x _
    | 1, p => exact b3PhiOf_short hirr fL fS (a := 4) rfl p _

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h in
theorem rank_long {a a' : Fin 12} (ha : b3Short a = false) (ha' : b3Short a' = false)
    {φK : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup (quadMinus 4 F b c)}
    (hinj : Function.Injective φK) (hU : ∀ x, φK (sl2Upper x) = b3xL b c a x)
    (hL : ∀ x, φK (sl2Lower x) = b3xL b c a' x) {Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G}
    (hΘU : ∀ x, Θ (sl2Upper x) = fL a x) (hΘL : ∀ x, Θ (sl2Lower x) = fL a' x) :
    ∀ α β : Fin 3 → ℤ, b3r a = α → b3r a' = β →
      ExtendsToHom (minusDatum 4 hirr).rootGroup {α, β} (b3PhiOf hirr fL fS) := by
  rintro α β rfl rfl
  refine extendsToHom_pair_of_hom hinj Θ (fun z => ?_) (fun z => ?_)
  · obtain ⟨z, hz⟩ := z
    obtain ⟨x, rfl⟩ := exists_b3xL_eq hirr ha hz
    exact ⟨x, hU x, (b3PhiOf_long hirr fL fS ha x hz).trans (hΘU x).symm⟩
  · obtain ⟨z, hz⟩ := z
    obtain ⟨x, rfl⟩ := exists_b3xL_eq hirr ha' hz
    exact ⟨x, hL x, (b3PhiOf_long hirr fL fS ha' x hz).trans (hΘL x).symm⟩

theorem hrank [Finite F] (k : Fin 3) :
    ExtendsToHom (minusDatum 4 hirr).rootGroup {Pi.single k 1, -Pi.single k 1}
      (b3PhiOf hirr fL fS) := by
  fin_cases k
  · obtain ⟨φK, hinj, hU, hL⟩ := exists_sl2_b3_0 (b := b) (c := c)
    obtain ⟨Θ, hΘU, hΘL⟩ := h.rank0
    exact rank_long hirr rfl rfl hinj hU hL hΘU hΘL _ _ (by decide) (by decide)
  · obtain ⟨φK, hinj, hU, hL⟩ := exists_sl2_b3_1 (b := b) (c := c)
    obtain ⟨Θ, hΘU, hΘL⟩ := h.rank1
    exact rank_long hirr rfl rfl hinj hU hL hΘU hΘL _ _ (by decide) (by decide)
  · obtain ⟨φK, hinj, hU, hL⟩ := exists_sl2_b3_2 hirr
    obtain ⟨Θ, hΘU, hΘL⟩ := h.rank2
    have key : ∀ α β : Fin 3 → ℤ, b3r 4 = α → b3r 5 = β →
        ExtendsToHom (minusDatum 4 hirr).rootGroup {α, β} (b3PhiOf hirr fL fS) := by
      rintro α β rfl rfl
      refine extendsToHom_pair_of_hom hinj Θ (fun z => ?_) (fun z => ?_)
      · obtain ⟨z, hz⟩ := z
        obtain ⟨p, rfl⟩ := exists_b3xS_eq hirr (a := 4) rfl hz
        obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) p
        exact ⟨t, hU t, (b3PhiOf_short hirr fL fS rfl _ hz).trans (hΘU t).symm⟩
      · obtain ⟨z, hz⟩ := z
        obtain ⟨p, rfl⟩ := exists_b3xS_eq hirr (a := 5) rfl hz
        obtain ⟨t, rfl⟩ := exists_starCoord_eq (b := b) (c := c) p
        exact ⟨t, hL t, (b3PhiOf_short hirr fL fS rfl _ hz).trans (hΘL t).symm⟩
    exact key _ _ (by decide) (by decide)

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h in
theorem cone_swap {i j : Fin 3}
    (hc : ∀ α ∈ pairRoots (minusDatum 4 hirr) i j, ∀ β ∈ pairRoots (minusDatum 4 hirr) i j,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (minusDatum 4 hirr).rootGroup
          ((minusDatum 4 hirr).cone α β ∩ pairRoots (minusDatum 4 hirr) i j)
          (b3PhiOf hirr fL fS)) :
    ∀ α ∈ pairRoots (minusDatum 4 hirr) j i, ∀ β ∈ pairRoots (minusDatum 4 hirr) j i,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (minusDatum 4 hirr).rootGroup
          ((minusDatum 4 hirr).cone α β ∩ pairRoots (minusDatum 4 hirr) j i)
          (b3PhiOf hirr fL fS) := by
  rw [pairRoots_comm_minus hirr]
  exact hc

theorem hcone [Finite F] : ∀ i j : Fin 3, ∀ α ∈ pairRoots (minusDatum 4 hirr) i j,
    ∀ β ∈ pairRoots (minusDatum 4 hirr) i j, ¬ Universal.IsNegMultiple α β →
      ExtendsToHom (minusDatum 4 hirr).rootGroup
        ((minusDatum 4 hirr).cone α β ∩ pairRoots (minusDatum 4 hirr) i j)
        (b3PhiOf hirr fL fS) := by
  have h01 := extendsToHom_cone_pairRoots (D := minusDatum 4 hirr) (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (n01 b c) (fun k hk γ hγ y hy => (h.weyl01 hirr k hk γ hγ).1 y hy) w01
    (fun k hk γ hγ => (h.weyl01 hirr k hk γ hγ).2) (h.pos01 hirr) (fun k _ => h.hrank hirr k)
  have h12 := extendsToHom_cone_pairRoots (D := minusDatum 4 hirr) (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (n12 b c) (fun k hk γ hγ y hy => (h.weyl12 hirr k hk γ hγ).1 y hy) w12
    (fun k hk γ hγ => (h.weyl12 hirr k hk γ hγ).2) (h.pos12 hirr) (fun k _ => h.hrank hirr k)
  have h02 := extendsToHom_cone_pairRoots (D := minusDatum 4 hirr) (i := (0 : Fin 3))
    (j := (2 : Fin 3)) (n02 hirr) (fun k hk γ hγ y hy => (h.weyl02 hirr k hk γ hγ).1 y hy) w02
    (fun k hk γ hγ => (h.weyl02 hirr k hk γ hγ).2) (h.pos02 hirr) (fun k _ => h.hrank hirr k)
  have hself : ∀ k : Fin 3, ∀ α ∈ pairRoots (minusDatum 4 hirr) k k,
      ∀ β ∈ pairRoots (minusDatum 4 hirr) k k, ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (minusDatum 4 hirr).rootGroup
          ((minusDatum 4 hirr).cone α β ∩ pairRoots (minusDatum 4 hirr) k k)
          (b3PhiOf hirr fL fS) := by
    intro k α _ β _ _
    refine (h.hrank hirr k).mono fun γ hγ => ?_
    rcases b3_pair_self hirr hγ.2 with e | e
    · exact Or.inl e
    · exact Or.inr e
  intro i j
  fin_cases i <;> fin_cases j
  · exact hself 0
  · exact h01
  · exact h02
  · exact cone_swap hirr h01
  · exact hself 1
  · exact h12
  · exact cone_swap hirr h02
  · exact cone_swap hirr h12
  · exact hself 2

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h in
theorem mem_range_long (γ : Fin 3 → ℤ) {a : Fin 12} (ha : b3Short a = false)
    (hγ : b3r a = γ) (x : G) (hx : x ∈ Set.range (fL a)) :
    x ∈ Set.range (b3PhiOf hirr fL fS γ) := by
  subst hγ
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨b3xL b c a y, b3xL_mem hirr ha y⟩, b3PhiOf_long hirr fL fS ha y _⟩

omit [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] h in
theorem mem_range_short (γ : Fin 3 → ℤ) {a : Fin 12} (ha : b3Short a = true)
    (hγ : b3r a = γ) (x : G) (hx : x ∈ Set.range (fS a)) :
    x ∈ Set.range (b3PhiOf hirr fL fS γ) := by
  subst hγ
  obtain ⟨p, rfl⟩ := hx
  exact ⟨⟨b3xS hirr a p, b3xS_mem hirr ha p⟩, b3PhiOf_short hirr fL fS ha p _⟩

omit [CharP F 2] in
theorem hgen : Subgroup.closure (⋃ k : Fin 3,
    Set.range (b3PhiOf hirr fL fS (Pi.single k 1)) ∪
      Set.range (b3PhiOf hirr fL fS (-Pi.single k 1))) = ⊤ := by
  rw [eq_top_iff, ← h.gen]
  refine Subgroup.closure_mono ?_
  rintro x (((((hx | hx) | hx) | hx) | hx) | hx)
  · exact Set.mem_iUnion.2 ⟨0, Or.inl (mem_range_long hirr (Pi.single 0 1) (a := 0) rfl
      (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨0, Or.inr (mem_range_long hirr (-Pi.single 0 1) (a := 1) rfl
      (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨1, Or.inl (mem_range_long hirr (Pi.single 1 1) (a := 2) rfl
      (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨1, Or.inr (mem_range_long hirr (-Pi.single 1 1) (a := 3) rfl
      (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨2, Or.inl (mem_range_short hirr (Pi.single 2 1) (a := 4) rfl
      (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨2, Or.inr (mem_range_short hirr (-Pi.single 2 1) (a := 5) rfl
      (by decide) x hx)⟩

omit [CharP F 2] in
theorem hnt : ∃ k : Fin 3, ∃ x, b3PhiOf hirr fL fS (Pi.single k 1) x ≠ 1 := by
  obtain ⟨y, hy⟩ := h.nt
  have key : ∀ γ : Fin 3 → ℤ, b3r 0 = γ → ∃ x, b3PhiOf hirr fL fS γ x ≠ 1 := by
    rintro γ rfl
    exact ⟨⟨b3xL b c 0 y, b3xL_mem hirr (a := 0) rfl y⟩, fun h1 =>
      hy ((b3PhiOf_long hirr fL fS (a := 0) rfl y _).symm.trans h1)⟩
  exact ⟨0, key (Pi.single 0 1) (by decide)⟩

end IsB3Frame

theorem b3_isPGroup [CharP F 2] :
    ∀ γ ∈ (minusDatum 4 hirr).roots, IsPGroup 2 ((minusDatum 4 hirr).rootGroup γ) :=
  fun _ hγ => isPGroup_minusRootGroup hirr hγ

theorem minusDatum_cartan_ne :
    (minusDatum 4 hirr).cartan ≠ Symplectic.cartanC (minusDatum 4 hirr).rank := by
  intro hC
  have e := congrFun (congrFun hC (2 : Fin 3)) (1 : Fin 3)
  change cartanB 3 2 1 = Symplectic.cartanC 3 2 1 at e
  exact absurd e (by decide)

end Frame

end CFSG.Timmesfeld.RankTwo
