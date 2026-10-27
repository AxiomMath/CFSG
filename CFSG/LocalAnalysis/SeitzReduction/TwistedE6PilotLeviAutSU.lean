module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.E6Pilot (IsAutConj IsAutConjIn)

local instance twistedE6PilotLeviAutSUNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotLeviAutSUNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank :=
  ⟨by decide⟩

section Bridge

variable {f : ℕ} {K : Type} [Field K]

theorem unitaryFieldData_of_card (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem bar_apply_eq (h : UnitaryFieldData 2 f K) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (c : K) : h.bar c = σ c := by
  rw [UnitaryFieldData.bar_apply, hσ]

theorem two_eq_zero_of_unitaryFieldData (h : UnitaryFieldData 2 f K) : (2 : K) = 0 := by
  have := h.charP
  exact CharP.cast_eq_zero K 2

variable (h : UnitaryFieldData 2 f K)

@[expose] def gramToSL :
    gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) →*
      SpecialLinearGroup (Fin 6) K where
  toFun g := ⟨((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), (mem_gramSU.1 g.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_gramToSL (g : gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    ((gramToSL h g : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
  rfl

theorem gramToSL_mem_unitarySL {σ : K →+* K} (hσ : ∀ c, h.bar c = σ c)
    (g : gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    gramToSL h g ∈ E6GraphLevi.unitarySL σ := by
  rw [E6GraphLevi.mem_unitarySL_iff, coe_gramToSL]
  have e : (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ) =
      ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map h.bar := by
    ext i j
    simp [hσ]
  rw [e]
  exact (mem_gramSU.1 g.2).1

theorem toGL_mem_gramSU {σ : K →+* K} (hσ : ∀ c, h.bar c = σ c)
    {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ E6GraphLevi.unitarySL σ) :
    Matrix.SpecialLinearGroup.toGL B ∈
      gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · have e : ((B : Matrix (Fin 6) (Fin 6) K).map h.bar) =
        (B : Matrix (Fin 6) (Fin 6) K).map σ := by
      ext i j
      simp [hσ]
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, e]
    exact E6GraphLevi.mem_unitarySL_iff.1 hB
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact B.2

theorem range_gramToSL {σ : K →+* K} (hσ : ∀ c, h.bar c = σ c) :
    (gramToSL h).range = E6GraphLevi.unitarySL σ := by
  refine le_antisymm ?_ fun B hB => ⟨⟨_, toGL_mem_gramSU h hσ hB⟩, rfl⟩
  rintro _ ⟨g, rfl⟩
  exact gramToSL_mem_unitarySL h hσ g

end Bridge

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def gramRealize :
    gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) →*
      ModGL TwistTag.E6.tag K :=
  (E6GraphLevi.realize (two_eq_zero_of_unitaryFieldData h)).comp (gramToSL h)

theorem gramRealize_apply
    (g : gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    gramRealize h g = E6GraphLevi.realize (two_eq_zero_of_unitaryFieldData h) (gramToSL h g) :=
  rfl

theorem ker_gramRealize :
    (gramRealize h).ker = normOneScalars h
      (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6 := by
  have h2 := two_eq_zero_of_unitaryFieldData h
  ext g
  rw [gramRealize, ← MonoidHom.comap_ker, mem_comap, E6GraphLevi.mem_ker_realize,
    mem_normOneScalars, coe_gramToSL]
  constructor
  · rintro ⟨l, hl3, hl⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl3
    refine ⟨Units.mk0 l hl0, ?_, ?_, ?_⟩
    · have hsc : Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 l hl0) ∈
          primeFormUnitary h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
        have e : Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 l hl0) =
            (g : GL (Fin 6) K) := Units.ext (by
          rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hl])
        rw [e]
        exact ((mem_gramSU_iff_unitary h).1 g.2).1
      exact norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num) (antiIdGL K) hsc
    · ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
        show (6 : ℕ) = 3 * 2 by rfl, pow_mul, hl3, one_pow]
    · exact Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hl])
  · rintro ⟨c, -, hc6, hc⟩
    refine ⟨c, ?_, ?_⟩
    · have h6 : (c : K) ^ 6 = 1 := by rw [← Units.val_pow_eq_pow_val, hc6, Units.val_one]
      exact E6GraphLevi.pow_three_eq_one_of_pow_six h2 h6
    · rw [hc, Matrix.GeneralLinearGroup.coe_scalar]

variable [Finite K]

theorem range_gramRealize {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (gramRealize h).range = su6Levi σ := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rw [gramRealize, MonoidHom.range_comp, range_gramToSL h (bar_apply_eq h hσ), su6Levi,
    (E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ (two_eq_zero_of_unitaryFieldData h)).1]

@[expose] noncomputable def su6LeviEquiv {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    primeFormP h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ≃* su6Levi σ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gramRealize h).symm).trans
    ((QuotientGroup.quotientKerEquivRange (gramRealize h)).trans
      (MulEquiv.subgroupCongr (range_gramRealize h hσ)))

theorem coe_su6LeviEquiv_mk {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (g : gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    ((su6LeviEquiv h hσ (QuotientGroup.mk' _ g) : su6Levi σ) : ModGL TwistTag.E6.tag K) =
      gramRealize h g :=
  rfl

end Model

section Transvections

variable {K : Type} [Field K]

theorem unitaryTwist_transvection {σ : K →+* K} (h2 : (2 : K) = 0) {a b : Fin 6} (hab : a ≠ b)
    {c : K} (hc : σ c = c) :
    E6GraphLevi.unitaryTwist σ (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection (fun h' => hab (Fin.rev_injective h').symm) c := by
  change E6GraphLevi.graphSL K (Matrix.SpecialLinearGroup.map σ
    (SpecialLinearGroup.transvection hab c)) = _
  rw [E6GraphLevi.map_transvection, E6GraphLevi.graphSL_transvection h2, hc]

theorem transvection_mem_unitarySL {σ : K →+* K} (h2 : (2 : K) = 0) {a b : Fin 6} (hab : a ≠ b)
    (hba : Fin.rev b = a) {c : K} (hc : σ c = c) :
    SpecialLinearGroup.transvection hab c ∈ E6GraphLevi.unitarySL σ := by
  rw [E6GraphLevi.mem_unitarySL_iff_unitaryTwist, unitaryTwist_transvection h2 hab hc]
  have hab' : Fin.rev a = b := by rw [← hba, Fin.rev_rev]
  apply Subtype.ext
  change 1 + Matrix.single (Fin.rev b) (Fin.rev a) c = 1 + Matrix.single a b c
  rw [hba, hab']

theorem one_add_single_mul_comm {a b d e : Fin 6} (hbd : b ≠ d) (hea : e ≠ a) (c c' : K) :
    (1 + Matrix.single a b c) * (1 + Matrix.single d e c') =
      (1 + Matrix.single d e c') * (1 + Matrix.single a b c) := by
  have h1 : Matrix.single a b c * Matrix.single d e c' = 0 :=
    Matrix.single_mul_single_of_ne c a b d hbd c'
  have h2 : Matrix.single d e c' * Matrix.single a b c = 0 :=
    Matrix.single_mul_single_of_ne c' d e a hea c
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2]
  abel

theorem transvection_mul_mem_unitarySL {σ : K →+* K} (h2 : (2 : K) = 0) {a b d e : Fin 6}
    (hab : a ≠ b) (hde : d ≠ e) (hd : Fin.rev b = d) (he : Fin.rev a = e) (hbd : b ≠ d)
    (hea : e ≠ a) {c : K} (hc : σ c = c) :
    SpecialLinearGroup.transvection hab c * SpecialLinearGroup.transvection hde c ∈
      E6GraphLevi.unitarySL σ := by
  rw [E6GraphLevi.mem_unitarySL_iff_unitaryTwist, map_mul, unitaryTwist_transvection h2 hab hc,
    unitaryTwist_transvection h2 hde hc]
  have hb : Fin.rev d = b := by rw [← hd, Fin.rev_rev]
  have ha : Fin.rev e = a := by rw [← he, Fin.rev_rev]
  apply Subtype.ext
  change (1 + Matrix.single (Fin.rev b) (Fin.rev a) c) *
      (1 + Matrix.single (Fin.rev e) (Fin.rev d) c) =
    (1 + Matrix.single a b c) * (1 + Matrix.single d e c)
  rw [hd, he, hb, ha]
  exact one_add_single_mul_comm hea hbd c c

theorem jPairDiag_mul_transvection {i a b : Fin 6} (hab : a ≠ b) (ha : ¬(a = i ∨ a = Fin.rev i))
    (hb : ¬(b = i ∨ b = Fin.rev i)) (s : Kˣ) (c : K) :
    jPairDiag i s * Matrix.SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hab c) =
      Matrix.SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hab c) * jPairDiag i s := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_jPairDiag, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change _ * (1 + Matrix.single a b c) = (1 + Matrix.single a b c) * _
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hxy : x = y
  · subst hxy
    have : ¬(a = x ∧ b = x) := fun h' => hab (h'.1.trans h'.2.symm)
    simp [this]
  · by_cases h' : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := h'
      simp [ha, hb, hxy]
    · simp [hxy, h']

end Transvections

section Gens

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def jA4Gens :
    Set (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
  {g | ∃ c : K, h.bar c = c ∧
    (gramToSL h g = SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) c ∨
      gramToSL h g = SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 2 by decide) c)}

@[expose] noncomputable def jA4Mat :
    Subgroup (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
  closure (jA4Gens h)

@[expose] def jA1Gens :
    Set (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
  {g | ∃ c : K, h.bar c = c ∧
    (gramToSL h g = SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) c ∨
      gramToSL h g = SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) c *
        SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) c)}

@[expose] noncomputable def jA1Mat :
    Subgroup (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
  closure (jA1Gens h)

theorem coe_eq_toGL_gramToSL
    (g : gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    (g : GL (Fin 6) K) = Matrix.SpecialLinearGroup.toGL (gramToSL h g) :=
  Units.ext rfl

theorem jPairDiag_mul_of_mem_closure
    {S : Set (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))} (i : Fin 6)
    (s : Kˣ) (hS : ∀ g ∈ S, jPairDiag i s * (g : GL (Fin 6) K) = g * jPairDiag i s) :
    ∀ g ∈ closure S, jPairDiag i s * (g : GL (Fin 6) K) = g * jPairDiag i s := by
  intro g hg
  have hle : closure S ≤ (centralizer ({jPairDiag i s} : Set (GL (Fin 6) K))).comap
      (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).subtype := by
    rw [closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff]
    exact (hS x hx).symm
  have h1 := hle hg
  rw [mem_comap, mem_centralizer_singleton_iff] at h1
  exact h1.symm

theorem gramToSL_primeFormFieldSU (φ : K ≃+* K)
    (g : gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    gramToSL h (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g) =
      Matrix.SpecialLinearGroup.map (φ : K →+* K) (gramToSL h g) :=
  Subtype.ext rfl

theorem primeFormFieldSU_mem_closure
    {S : Set (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))}
    (φ : K ≃+* K) (hS : ∀ g ∈ S, primeFormFieldSU h isPrimeFormGram_antiIdGL φ g ∈ S) :
    ∀ g ∈ closure S, primeFormFieldSU h isPrimeFormGram_antiIdGL φ g ∈ closure S := by
  intro g hg
  have hle : closure S ≤ (closure S).comap
      (primeFormFieldSU h isPrimeFormGram_antiIdGL φ).toMonoidHom := by
    rw [closure_le]
    intro x hx
    exact subset_closure (hS x hx)
  exact hle hg

theorem bar_apply_ringEquiv_of_bar {c : K} (hc : h.bar c = c) (φ : K ≃+* K) :
    h.bar (φ c) = φ c := by
  rw [← map_bar_comm h φ c, hc]

theorem isAutConj_jA4Mat :
    IsAutConj ((jA4Mat h).map (QuotientGroup.mk' (normOneScalars h
      (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6))) := by
  refine isAutConj_map_mk_of_commute h 1 (fun s => jPairDiag_mul_of_mem_closure h 1 s ?_)
    (fun φ => primeFormFieldSU_mem_closure h φ ?_)
  · rintro g ⟨c, -, hg | hg⟩ <;> rw [coe_eq_toGL_gramToSL, hg]
    · exact jPairDiag_mul_transvection _ (by decide) (by decide) s c
    · exact jPairDiag_mul_transvection _ (by decide) (by decide) s c
  · rintro g ⟨c, hc, hg | hg⟩
    · refine ⟨φ c, bar_apply_ringEquiv_of_bar h hc φ, Or.inl ?_⟩
      rw [gramToSL_primeFormFieldSU, hg, E6GraphLevi.map_transvection]
      rfl
    · refine ⟨φ c, bar_apply_ringEquiv_of_bar h hc φ, Or.inr ?_⟩
      rw [gramToSL_primeFormFieldSU, hg, E6GraphLevi.map_transvection]
      rfl

theorem isAutConj_jA1Mat :
    IsAutConj ((jA1Mat h).map (QuotientGroup.mk' (normOneScalars h
      (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6))) := by
  refine isAutConj_map_mk_of_commute h 2 (fun s => jPairDiag_mul_of_mem_closure h 2 s ?_)
    (fun φ => primeFormFieldSU_mem_closure h φ ?_)
  · rintro g ⟨c, -, hg | hg⟩ <;> rw [coe_eq_toGL_gramToSL, hg, map_mul, ← mul_assoc]
    · rw [jPairDiag_mul_transvection _ (by decide) (by decide) s c, mul_assoc,
        jPairDiag_mul_transvection _ (by decide) (by decide) s c, mul_assoc]
    · rw [jPairDiag_mul_transvection _ (by decide) (by decide) s c, mul_assoc,
        jPairDiag_mul_transvection _ (by decide) (by decide) s c, mul_assoc]
  · rintro g ⟨c, hc, hg | hg⟩
    · refine ⟨φ c, bar_apply_ringEquiv_of_bar h hc φ, Or.inl ?_⟩
      rw [gramToSL_primeFormFieldSU, hg, map_mul, E6GraphLevi.map_transvection,
        E6GraphLevi.map_transvection]
      rfl
    · refine ⟨φ c, bar_apply_ringEquiv_of_bar h hc φ, Or.inr ?_⟩
      rw [gramToSL_primeFormFieldSU, hg, map_mul, E6GraphLevi.map_transvection,
        E6GraphLevi.map_transvection]
      rfl

end Gens

section Images

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem realize_transvection_up (h2 : (2 : K) = 0) {a b : Fin 6} (hab : a ≠ b) (t : Fin 5)
    (ha : a = t.castSucc) (hb : b = t.succ) (c : K) :
    E6GraphLevi.realize h2 (SpecialLinearGroup.transvection hab c) =
      xUnit TwistTag.E6.tag K (E6GraphLevi.pathIdx t) c := by
  subst ha hb
  exact E6GraphLevi.realize_x h2 t c

theorem realize_transvection_down (h2 : (2 : K) = 0) {a b : Fin 6} (hab : a ≠ b) (t : Fin 5)
    (ha : a = t.succ) (hb : b = t.castSucc) (c : K) :
    E6GraphLevi.realize h2 (SpecialLinearGroup.transvection hab c) =
      yUnit TwistTag.E6.tag K (E6GraphLevi.pathIdx t) c := by
  subst ha hb
  exact E6GraphLevi.realize_y h2 t c

theorem map_gramRealize_jA4Mat :
    (jA4Mat h).map (gramRealize h) =
      closure {g | ∃ c : K, h.bar c = c ∧
        (g = pinnedX TwistTag.E6.tag K (Pi.single 3 1) c ∨
          g = pinnedX TwistTag.E6.tag K (-Pi.single 3 1) c)} := by
  have h2 := two_eq_zero_of_unitaryFieldData h
  have hbar : ∀ c, h.bar c = h.bar c := fun _ => rfl
  rw [jA4Mat, MonoidHom.map_closure]
  apply le_antisymm
  · refine closure_mono ?_
    rintro _ ⟨g, ⟨c, hc, hg | hg⟩, rfl⟩
    · refine ⟨c, hc, Or.inl ?_⟩
      rw [gramRealize_apply, hg, pinnedX_single]
      exact realize_transvection_up h2 _ 2 rfl rfl c
    · refine ⟨c, hc, Or.inr ?_⟩
      rw [gramRealize_apply, hg, pinnedX_neg_single]
      exact realize_transvection_down h2 _ 2 rfl rfl c
  · rw [closure_le]
    rintro _ ⟨c, hc, rfl | rfl⟩
    · refine subset_closure ⟨⟨_, toGL_mem_gramSU h hbar (transvection_mem_unitarySL h2
        (show (2 : Fin 6) ≠ 3 by decide) (by decide) hc)⟩, ⟨c, hc, Or.inl rfl⟩, ?_⟩
      change E6GraphLevi.realize h2
        (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) c) = _
      rw [pinnedX_single]
      exact realize_transvection_up h2 _ 2 rfl rfl c
    · refine subset_closure ⟨⟨_, toGL_mem_gramSU h hbar (transvection_mem_unitarySL h2
        (show (3 : Fin 6) ≠ 2 by decide) (by decide) hc)⟩, ⟨c, hc, Or.inr rfl⟩, ?_⟩
      change E6GraphLevi.realize h2
        (SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 2 by decide) c) = _
      rw [pinnedX_neg_single]
      exact realize_transvection_down h2 _ 2 rfl rfl c

theorem map_gramRealize_jA1Mat :
    (jA1Mat h).map (gramRealize h) =
      closure {g | ∃ c : K, h.bar c = c ∧
        (g = pinnedX TwistTag.E6.tag K (Pi.single 0 1) c *
            pinnedX TwistTag.E6.tag K (Pi.single 5 1) c ∨
          g = pinnedX TwistTag.E6.tag K (-Pi.single 0 1) c *
            pinnedX TwistTag.E6.tag K (-Pi.single 5 1) c)} := by
  have h2 := two_eq_zero_of_unitaryFieldData h
  have hbar : ∀ c, h.bar c = h.bar c := fun _ => rfl
  rw [jA1Mat, MonoidHom.map_closure]
  apply le_antisymm
  · refine closure_mono ?_
    rintro _ ⟨g, ⟨c, hc, hg | hg⟩, rfl⟩
    · refine ⟨c, hc, Or.inl ?_⟩
      rw [gramRealize_apply, hg, map_mul, pinnedX_single, pinnedX_single,
        realize_transvection_up h2 _ 0 rfl rfl c, realize_transvection_up h2 _ 4 rfl rfl c]
      rfl
    · refine ⟨c, hc, Or.inr ?_⟩
      rw [gramRealize_apply, hg, map_mul, pinnedX_neg_single, pinnedX_neg_single,
        realize_transvection_down h2 _ 0 rfl rfl c, realize_transvection_down h2 _ 4 rfl rfl c]
      rfl
  · rw [closure_le]
    rintro _ ⟨c, hc, rfl | rfl⟩
    · refine subset_closure ⟨⟨_, toGL_mem_gramSU h hbar (transvection_mul_mem_unitarySL h2
        (show (0 : Fin 6) ≠ 1 by decide) (show (4 : Fin 6) ≠ 5 by decide) (by decide)
        (by decide) (by decide) (by decide) hc)⟩, ⟨c, hc, Or.inl rfl⟩, ?_⟩
      change E6GraphLevi.realize h2
        (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
          SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) c) = _
      rw [map_mul, pinnedX_single, pinnedX_single,
        realize_transvection_up h2 _ 0 rfl rfl c, realize_transvection_up h2 _ 4 rfl rfl c]
      rfl
    · refine subset_closure ⟨⟨_, toGL_mem_gramSU h hbar (transvection_mul_mem_unitarySL h2
        (show (1 : Fin 6) ≠ 0 by decide) (show (5 : Fin 6) ≠ 4 by decide) (by decide)
        (by decide) (by decide) (by decide) hc)⟩, ⟨c, hc, Or.inr rfl⟩, ?_⟩
      change E6GraphLevi.realize h2
        (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) c *
          SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) c) = _
      rw [map_mul, pinnedX_neg_single, pinnedX_neg_single,
        realize_transvection_down h2 _ 0 rfl rfl c, realize_transvection_down h2 _ 4 rfl rfl c]
      rfl

end Images

section Standard

variable {K : Type} [Field K]

@[expose] noncomputable def rootSL2A4
    {k : Type} [Field k] (ι : k →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  closure {g | ∃ c : k, g = pinnedX TwistTag.E6.tag K (Pi.single 3 1) (ι c) ∨
    g = pinnedX TwistTag.E6.tag K (-Pi.single 3 1) (ι c)}

@[expose] noncomputable def pairSL2A1
    {k : Type} [Field k] (ι : k →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  closure {g | ∃ c : k, g = pinnedX TwistTag.E6.tag K (Pi.single 0 1) (ι c) *
      pinnedX TwistTag.E6.tag K (Pi.single 5 1) (ι c) ∨
    g = pinnedX TwistTag.E6.tag K (-Pi.single 0 1) (ι c) *
      pinnedX TwistTag.E6.tag K (-Pi.single 5 1) (ι c)}

variable {f : ℕ}

@[expose] noncomputable def su6LeviEquivC0 (h : UnitaryFieldData 2 f K) [Finite K]
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    primeFormP h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ≃*
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
  (su6LeviEquiv h hσ).trans (subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm

theorem map_map_mk_su6LeviEquivC0 (h : UnitaryFieldData 2 f K) [Finite K] {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (H : Subgroup (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) :
    ((H.map (QuotientGroup.mk' _)).map (su6LeviEquivC0 h hσ).toMonoidHom).map
        ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).subtype =
      (H.map (gramRealize h)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨su6LeviEquivC0 h hσ (QuotientGroup.mk' _ g), ⟨_, ⟨g, hg, rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hgx

theorem setOf_bar_eq_setOf {k : Type} [Field k] {ι : k →+* K} {P : K → Prop}
    (hfix : ∀ c : K, P c ↔ c ∈ Set.range ι) (Q : K → ModGL TwistTag.E6.tag K → Prop) :
    {g | ∃ c : K, P c ∧ Q c g} = {g | ∃ c : k, Q (ι c) g} := by
  ext g
  constructor
  · rintro ⟨c, hc, hg⟩
    obtain ⟨c', rfl⟩ := (hfix c).1 hc
    exact ⟨c', hg⟩
  · rintro ⟨c', hg⟩
    exact ⟨ι c', (hfix _).2 ⟨c', rfl⟩, hg⟩

theorem isAutConjIn_su6Levi_rootSL2A4 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type} [Field k] {ι : k →+* K}
    (hfix : ∀ c : K, σ c = c ↔ c ∈ Set.range ι) :
    IsAutConjIn ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((rootSL2A4 ι).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have h := unitaryFieldData_of_card hf hK
  have := h.finite
  have hfix' : ∀ c, h.bar c = c ↔ c ∈ Set.range ι := fun c => by
    rw [bar_apply_eq h hσ]
    exact hfix c
  have h1 := (isAutConj_jA4Mat h).isAutConjIn_map (su6LeviEquivC0 h hσ)
  rwa [map_map_mk_su6LeviEquivC0, map_gramRealize_jA4Mat,
    setOf_bar_eq_setOf hfix' (fun c g => g = pinnedX TwistTag.E6.tag K (Pi.single 3 1) c ∨
      g = pinnedX TwistTag.E6.tag K (-Pi.single 3 1) c)] at h1

theorem isAutConjIn_su6Levi_pairSL2A1 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type} [Field k] {ι : k →+* K}
    (hfix : ∀ c : K, σ c = c ↔ c ∈ Set.range ι) :
    IsAutConjIn ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((pairSL2A1 ι).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have h := unitaryFieldData_of_card hf hK
  have := h.finite
  have hfix' : ∀ c, h.bar c = c ↔ c ∈ Set.range ι := fun c => by
    rw [bar_apply_eq h hσ]
    exact hfix c
  have h1 := (isAutConj_jA1Mat h).isAutConjIn_map (su6LeviEquivC0 h hσ)
  rwa [map_map_mk_su6LeviEquivC0, map_gramRealize_jA1Mat,
    setOf_bar_eq_setOf hfix' (fun c g => g = pinnedX TwistTag.E6.tag K (Pi.single 0 1) c *
        pinnedX TwistTag.E6.tag K (Pi.single 5 1) c ∨
      g = pinnedX TwistTag.E6.tag K (-Pi.single 0 1) c *
        pinnedX TwistTag.E6.tag K (-Pi.single 5 1) c)] at h1

end Standard

section Transport

theorem leviAutWords_check :
    twistedE6RelAct (relWordTX ++ [0, 1]) (Pi.single 3 1) = e6HighestRoot ∧
      twistedE6RelAct (relWordTX ++ [0, 1]) (-Pi.single 3 1) = -e6HighestRoot ∧
      twistedE6RelAct (relWordTY ++ [1, 2, 1]) (Pi.single 0 1) = twistedE6ClassRootU ∧
      twistedE6RelAct (relWordTY ++ [1, 2, 1]) (Pi.single 5 1) = twistedE6ClassRootU' ∧
      twistedE6RelAct (relWordTY ++ [1, 2, 1]) (-Pi.single 0 1) = -twistedE6ClassRootU ∧
      twistedE6RelAct (relWordTY ++ [1, 2, 1]) (-Pi.single 5 1) = -twistedE6ClassRootU' ∧
      (∀ j ∈ ([0, 1] : List (Fin TwistTag.E6.foldedTag.rank)).flatMap TwistTag.E6.orbitWord,
        j ≠ 1) ∧
      ∀ j ∈ ([1, 2, 1] : List (Fin TwistTag.E6.foldedTag.rank)).flatMap TwistTag.E6.orbitWord,
        j ≠ 1 := by
  decide +kernel

variable {K : Type} [Field K]

theorem twistedE6RelWeyl_append (ω₁ ω₂ : List (Fin TwistTag.E6.foldedTag.rank)) :
    twistedE6RelWeyl K (ω₁ ++ ω₂) = twistedE6RelWeyl K ω₁ * twistedE6RelWeyl K ω₂ := by
  rw [twistedE6RelWeyl, twistedE6RelWeyl, twistedE6RelWeyl, List.flatMap_append, List.map_append,
    List.prod_append]

theorem relWeylC_append (σ : K →+* K) (ω₁ ω₂ : List (Fin TwistTag.E6.foldedTag.rank)) :
    relWeylC σ (ω₁ ++ ω₂) = relWeylC σ ω₁ * relWeylC σ ω₂ :=
  Subtype.ext (twistedE6RelWeyl_append ω₁ ω₂)

theorem twistedE6RelWeyl_mem_subsystemGroup_setA {ω : List (Fin TwistTag.E6.foldedTag.rank)}
    (hω : ∀ j ∈ ω.flatMap TwistTag.E6.orbitWord, j ≠ 1) :
    twistedE6RelWeyl K ω ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_subsystemGroup (show j ∈ E6GraphLevi.setA from hω j hj) 1

theorem map_conj_eq_self_of_mem {G : Type*} [Group G] {M : Subgroup G} {m : G} (hm : m ∈ M) :
    M.map (MulAut.conj m).toMonoidHom = M := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm)
  · intro x hx
    refine ⟨m⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem relWeylC_mem_su6Levi_subgroupOf (σ : K →+* K) {ω : List (Fin TwistTag.E6.foldedTag.rank)}
    (hω : ∀ j ∈ ω.flatMap TwistTag.E6.orbitWord, j ≠ 1) :
    relWeylC σ ω ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
  mem_subgroupOf.2 (mem_inf.2 ⟨twistedE6RelWeyl_mem_subsystemGroup_setA hω,
    twistedE6RelWeyl_mem σ ω⟩)

variable [CharP K 2]

theorem rootSL2A4_le_su6Levi {k : Type} [Field k] {ι : k →+* K} {σ : K →+* K}
    (hσι : ∀ c, σ (ι c) = ι c) : rootSL2A4 ι ≤ su6Levi σ := by
  rw [rootSL2A4, closure_le]
  have h3 : (3 : Fin TwistTag.E6.tag.rank) ∈ E6GraphLevi.setA :=
    show (3 : Fin TwistTag.E6.tag.rank) ≠ E6GraphHighestRoot.e6Idx 1 by decide
  have hp : TwistTag.E6.perm 3 = 3 := by decide
  rintro _ ⟨c, rfl | rfl⟩
  · refine mem_inf.2 ⟨?_, pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_single _ _)
      (by rw [permLattice_single, hp]) (hσι c)⟩
    rw [pinnedX_single]
    exact xUnit_mem_subsystemGroup h3 _
  · refine mem_inf.2 ⟨?_, pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_neg_single _ _)
      (by rw [permLattice_neg_single, hp]) (hσι c)⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_subsystemGroup h3 _

theorem pairSL2A1_le_su6Levi {k : Type} [Field k] {ι : k →+* K} {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) (hσι : ∀ c, σ (ι c) = ι c) : pairSL2A1 ι ≤ su6Levi σ := by
  rw [pairSL2A1, closure_le]
  have h0 : (0 : Fin TwistTag.E6.tag.rank) ∈ E6GraphLevi.setA :=
    show (0 : Fin TwistTag.E6.tag.rank) ≠ E6GraphHighestRoot.e6Idx 1 by decide
  have h5 : (5 : Fin TwistTag.E6.tag.rank) ∈ E6GraphLevi.setA :=
    show (5 : Fin TwistTag.E6.tag.rank) ≠ E6GraphHighestRoot.e6Idx 1 by decide
  have hp : TwistTag.E6.perm 0 = 5 := by decide
  rintro _ ⟨c, rfl | rfl⟩
  · refine mem_inf.2 ⟨?_, ?_⟩
    · rw [pinnedX_single, pinnedX_single]
      exact mul_mem (xUnit_mem_subsystemGroup h0 _) (xUnit_mem_subsystemGroup h5 _)
    · have e : pinnedX TwistTag.E6.tag K (Pi.single 0 1) (ι c) *
          pinnedX TwistTag.E6.tag K (Pi.single 5 1) (ι c) =
            twistedE6PairX σ (Pi.single 0 1) (ι c) := by
        rw [twistedE6PairX, permLattice_single, hp, hσι]
      rw [e]
      exact twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_single _ _) _
  · refine mem_inf.2 ⟨?_, ?_⟩
    · rw [pinnedX_neg_single, pinnedX_neg_single]
      exact mul_mem (yUnit_mem_subsystemGroup h0 _) (yUnit_mem_subsystemGroup h5 _)
    · have e : pinnedX TwistTag.E6.tag K (-Pi.single 0 1) (ι c) *
          pinnedX TwistTag.E6.tag K (-Pi.single 5 1) (ι c) =
            twistedE6PairX σ (-Pi.single 0 1) (ι c) := by
        rw [twistedE6PairX, permLattice_neg_single, hp, hσι]
      rw [e]
      exact twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_neg_single _ _) _

theorem map_conj_rootSL2A4 {k : Type} [Field k] (ι : k →+* K) :
    (rootSL2A4 ι).map (MulAut.conj (twistedE6RelWeyl K (relWordTX ++ [0, 1]))).toMonoidHom =
      E6GraphLevi.thetaRankOneGroup ι := by
  obtain ⟨h1, h2, -⟩ := leviAutWords_check
  rw [rootSL2A4, MonoidHom.map_closure, E6GraphLevi.thetaRankOneGroup,
    E6GraphLevi.thetaRootGroup, E6GraphLevi.thetaNegRootGroup, ← Subgroup.closure_union]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl | rfl⟩, rfl⟩
    · left
      refine ⟨c, ?_⟩
      change _ = twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h1]
    · right
      refine ⟨c, ?_⟩
      change _ = twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h2]
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨_, ⟨c, Or.inl rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹ = _
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h1]
    · refine ⟨_, ⟨c, Or.inr rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹ = _
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h2]

theorem map_conj_pairSL2A1 {k : Type} [Field k] (ι : k →+* K) :
    (pairSL2A1 ι).map (MulAut.conj (twistedE6RelWeyl K (relWordTY ++ [1, 2, 1]))).toMonoidHom =
      shortRankOneGroup ι := by
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := leviAutWords_check
  rw [pairSL2A1, MonoidHom.map_closure, shortRankOneGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl | rfl⟩, rfl⟩
    · refine ⟨c, Or.inl ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h3, h4]
    · refine ⟨c, Or.inr ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h5, h6]
  · rintro ⟨c, rfl | rfl⟩
    · refine ⟨_, ⟨c, Or.inl rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h3, h4]
    · refine ⟨_, ⟨c, Or.inr rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h5, h6]

variable {f : ℕ}

omit [CharP K 2] in
theorem isAutConjIn_levi_tX (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type} [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ f) :
    IsAutConjIn (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom)
      ((E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have : CharP K 2 := charP_two_of_card hf hK
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hfix : ∀ c : K, σ c = c ↔ c ∈ Set.range (algebraMap k K) := sigma_eq_self_iff hk hσ
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => (hfix _).2 ⟨c, rfl⟩
  have hJD : (rootSL2A4 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
    fun x hx => mem_subgroupOf.2 (rootSL2A4_le_su6Levi hσι (mem_subgroupOf.1 hx))
  have h0 := isAutConjIn_map_conj (isAutConjIn_su6Levi_rootSL2A4 hf hK hσ hfix) hJD
    (relWeylC σ (relWordTX ++ [0, 1]))
  have hM : ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordTX ++ [0, 1]))).toMonoidHom =
      ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom := by
    rw [relWeylC_append, ← E6Pilot.map_conj_map_conj_eq_conj_mul,
      map_conj_eq_self_of_mem (relWeylC_mem_su6Levi_subgroupOf σ leviAutWords_check.2.2.2.2.2.2.1)]
  have hJ : ((rootSL2A4 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordTX ++ [0, 1]))).toMonoidHom =
      (E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [← E6Pilot.subgroupOf_map_conj_eq_map_conj_subgroupOf
      ((rootSL2A4_le_su6Levi hσι).trans (su6Levi_le_graphFixedRootGroup σ))]
    exact congrArg (fun H => H.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      (map_conj_rootSL2A4 (algebraMap k K))
  rwa [hM, hJ] at h0

omit [CharP K 2] in
theorem isAutConjIn_levi_tY (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type} [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ f) :
    IsAutConjIn (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTY)).toMonoidHom)
      ((shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have : CharP K 2 := charP_two_of_card hf hK
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hfix : ∀ c : K, σ c = c ↔ c ∈ Set.range (algebraMap k K) := sigma_eq_self_iff hk hσ
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => (hfix _).2 ⟨c, rfl⟩
  have hJD : (pairSL2A1 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
    fun x hx => mem_subgroupOf.2
      (pairSL2A1_le_su6Levi (apply_apply_eq hK hσ) hσι (mem_subgroupOf.1 hx))
  have h0 := isAutConjIn_map_conj (isAutConjIn_su6Levi_pairSL2A1 hf hK hσ hfix) hJD
    (relWeylC σ (relWordTY ++ [1, 2, 1]))
  have hM : ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordTY ++ [1, 2, 1]))).toMonoidHom =
      ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTY)).toMonoidHom := by
    rw [relWeylC_append, ← E6Pilot.map_conj_map_conj_eq_conj_mul,
      map_conj_eq_self_of_mem (relWeylC_mem_su6Levi_subgroupOf σ leviAutWords_check.2.2.2.2.2.2.2)]
  have hJ : ((pairSL2A1 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordTY ++ [1, 2, 1]))).toMonoidHom =
      (shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [← E6Pilot.subgroupOf_map_conj_eq_map_conj_subgroupOf
      ((pairSL2A1_le_su6Levi (apply_apply_eq hK hσ) hσι).trans
        (su6Levi_le_graphFixedRootGroup σ))]
    exact congrArg (fun H => H.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      (map_conj_pairSL2A1 (algebraMap k K))
  rwa [hM, hJ] at h0

end Transport

end CFSG.SeitzReduction.TwistedE6Pilot
