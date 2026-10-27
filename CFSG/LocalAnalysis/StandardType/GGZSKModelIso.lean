module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import Certificates.Certificate709541
public import Certificates.Certificate709542
import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherBound
import CFSG.LocalAnalysis.StandardType.GGZSKModelSound
import CFSG.LocalAnalysis.StandardType.GGWitExcModelTransfer
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.Mathlib.LinearAlgebra.Matrix.ReflectionClass
import CFSG.Timmesfeld.Components
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.ZS

private lemma isConj_of_mul_pow_three {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (h3 : (x * y) ^ 3 = 1) : IsConj x y :=
  isConj_iff.mpr ⟨x * y, CFSG.Timmesfeld.Components.conj_eq_of_pow_three hx hy h3⟩

private lemma mul_self_of_pair_rel {G : Type*} [Group G] {m : ℕ} {e : Fin m → Fin m → ℕ}
    {t : Fin m → G} (h : ∀ i j, (t i * t j) ^ e i j = 1) (he : ∀ i, e i i = 1) (i : Fin m) :
    t i * t i = 1 := by
  have hii := h i i
  rwa [he i, pow_one] at hii

private lemma pow_three_of_pair_rel {G : Type*} [Group G] {m : ℕ} {e : Fin m → Fin m → ℕ}
    {t : Fin m → G} (h : ∀ i j, (t i * t j) ^ e i j = 1) {i j : Fin m} (he : e i j = 3) :
    (t i * t j) ^ 3 = 1 := by
  rw [← he]
  exact h i j

private lemma closure_conj_of_forall_isConj {n m : ℕ} [NeZero m]
    (M : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 13))) (t : Fin m → ↥M)
    (ht : Subgroup.closure (Set.range t) = ⊤) (hconj : ∀ i, IsConj (t 0) (t i)) :
    Subgroup.closure {x | ∃ g ∈ M,
      x = g * (t 0 : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) * g⁻¹} = M := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro x ⟨g, hg, rfl⟩
    exact M.mul_mem (M.mul_mem hg (t 0).2) (M.inv_mem hg)
  · have hM : M = (Subgroup.closure (Set.range t)).map M.subtype := by
      rw [ht, Subgroup.map_top, Subgroup.range_subtype]
    calc M = (Subgroup.closure (Set.range t)).map M.subtype := hM
      _ = Subgroup.closure (M.subtype '' Set.range t) := MonoidHom.map_closure _ _
      _ ≤ Subgroup.closure {x | ∃ g ∈ M,
          x = g * (t 0 : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) * g⁻¹} := by
        apply Subgroup.closure_mono
        rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
        obtain ⟨g, hg⟩ := isConj_iff.mp (hconj i)
        have hmem : (t i : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) ∈ {x | ∃ g ∈ M,
            x = g * (t 0 : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) * g⁻¹} := by
          refine ⟨(g : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)), g.2, ?_⟩
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hg.symm
        exact hmem

private lemma modelIso_of_conj_class {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} {k : ExcRow} (f : ↥(model k) ≃* ↥A)
    (c : ↥(model k)) (hc : IsReflMat (c : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)))
    (hG : (Nat.card (model k) : ZMod 13) ≠ 0)
    (hgen : Subgroup.closure {x | ∃ g ∈ model k,
      x = g * (c : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) * g⁻¹} = model k)
    (hcRefl : IsRefl p (f c : U ≃ₗ[ZMod p] U)) (hone : OneClass p A) : ModelIso p k A := by
  have hfact : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine ⟨f, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    obtain ⟨h, hh, hgh⟩ := Matrix.GeneralLinearGroup.exists_conj_of_closure_conj_eq
      (n := Fin (mdeg k)) (K := ZMod 13) hG hc.1 hc.2 hgen g.2 hg.1 hg.2
    have hg' : g = (⟨h, hh⟩ : ↥(model k)) * c * (⟨h, hh⟩ : ↥(model k))⁻¹ := Subtype.ext hgh
    rw [hg']
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using
      IsRefl.conj hcRefl (f ⟨h, hh⟩ : U ≃ₗ[ZMod p] U)
  · intro hg
    obtain ⟨k', hk', hconj⟩ := hone (f c : U ≃ₗ[ZMod p] U) (f c).2
      (f g : U ≃ₗ[ZMod p] U) (f g).2 hcRefl hg
    let m : ↥(model k) := f.symm ⟨k', hk'⟩
    have hg_eq : g = m * c * m⁻¹ := by
      apply f.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj)
    have hrefl : IsReflMat (g : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) := by
      rw [hg_eq]
      simpa using owEm_isReflMat_conj (c : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13))
        (m : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) hc
    exact hrefl

private lemma exists_subtype_tuple {m p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : Fin m → (U ≃ₗ[ZMod p] U)}
    (hA : Subgroup.closure (Set.range r) = A) :
    ∃ r' : Fin m → ↥A, Subgroup.closure (Set.range r') = ⊤ ∧
      ∀ i, (r' i : U ≃ₗ[ZMod p] U) = r i := by
  let r' : Fin m → ↥A := fun i => ⟨r i, by
    rw [← hA]
    exact Subgroup.subset_closure ⟨i, rfl⟩⟩
  refine ⟨r', ?_, fun i => rfl⟩
  apply (Subgroup.map_subtype_inj (H := A)).mp
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  have himg : A.subtype '' Set.range r' = Set.range r := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨r' i, ⟨i, rfl⟩, rfl⟩
  rw [himg, hA]

private lemma kFive_conj_of_rel {G : Type*} [Group G] {t : Fin 5 → G} (hrel : HSFiveRel t) :
    ∀ i, IsConj (t 0) (t i) := by
  change (∀ i j, (t i * t j) ^ kFiveExp i j = 1) ∧
    (t 2 * t 1 * t 2 * t 3) ^ 3 = 1 at hrel
  obtain ⟨hpair, _⟩ := hrel
  have hsq : ∀ i, t i * t i = 1 :=
    mul_self_of_pair_rel hpair (by decide)
  have h01 : IsConj (t 0) (t 1) :=
    isConj_of_mul_pow_three (hsq 0) (hsq 1) (pow_three_of_pair_rel hpair (by decide))
  have h12 : IsConj (t 1) (t 2) :=
    isConj_of_mul_pow_three (hsq 1) (hsq 2) (pow_three_of_pair_rel hpair (by decide))
  have h13 : IsConj (t 1) (t 3) :=
    isConj_of_mul_pow_three (hsq 1) (hsq 3) (pow_three_of_pair_rel hpair (by decide))
  have h34 : IsConj (t 3) (t 4) :=
    isConj_of_mul_pow_three (hsq 3) (hsq 4) (pow_three_of_pair_rel hpair (by decide))
  intro i
  fin_cases i
  · exact IsConj.refl (t 0)
  · exact h01
  · exact h01.trans h12
  · exact h01.trans h13
  · exact (h01.trans h13).trans h34

private lemma kSix_conj_of_rel {G : Type*} [Group G] {t : Fin 6 → G} (hrel : HSSixRel t) :
    ∀ i, IsConj (t 0) (t i) := by
  change (∀ i j, (t i * t j) ^ kSixExp i j = 1) ∧
    (t 2 * t 1 * t 2 * t 3) ^ 3 = 1 at hrel
  obtain ⟨hpair, _⟩ := hrel
  have hsq : ∀ i, t i * t i = 1 :=
    mul_self_of_pair_rel hpair (by decide)
  have h01 : IsConj (t 0) (t 1) :=
    isConj_of_mul_pow_three (hsq 0) (hsq 1) (pow_three_of_pair_rel hpair (by decide))
  have h12 : IsConj (t 1) (t 2) :=
    isConj_of_mul_pow_three (hsq 1) (hsq 2) (pow_three_of_pair_rel hpair (by decide))
  have h13 : IsConj (t 1) (t 3) :=
    isConj_of_mul_pow_three (hsq 1) (hsq 3) (pow_three_of_pair_rel hpair (by decide))
  have h34 : IsConj (t 3) (t 4) :=
    isConj_of_mul_pow_three (hsq 3) (hsq 4) (pow_three_of_pair_rel hpair (by decide))
  have h45 : IsConj (t 4) (t 5) :=
    isConj_of_mul_pow_three (hsq 4) (hsq 5) (pow_three_of_pair_rel hpair (by decide))
  intro i
  fin_cases i
  · exact IsConj.refl (t 0)
  · exact h01
  · exact h01.trans h12
  · exact h01.trans h13
  · exact (h01.trans h13).trans h34
  · exact ((h01.trans h13).trans h34).trans h45

theorem card_model_kFive :
    Nat.card (model .K5) = ExcRow.K5.ord := by
  obtain ⟨t, ht, htgen, htcard, -⟩ := exists_hsFive_model
  refine le_antisymm ?_ htcard
  have h := card_closure_le_of_hsFiveRel ht
  rw [htgen, Subgroup.card_top] at h
  exact h.trans_eq (by decide)

theorem card_model_kSix :
    Nat.card (model .K6) = ExcRow.K6.ord := by
  obtain ⟨t, ht, htgen, htcard, -⟩ := exists_hsSix_model
  refine le_antisymm ?_ htcard
  have h := card_closure_le_of_hsSixRel ht
  rw [htgen, Subgroup.card_top] at h
  exact h.trans_eq (by decide)

theorem modelIso_kFive {p : ℕ}
    [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {r : Fin 5 → (U ≃ₗ[ZMod p] U)} (hA : Subgroup.closure (Set.range r) = A) (hrel : HSFiveRel r)
    (hcard : ExcRow.K5.ord ≤ Nat.card A) (hr0 : IsRefl p (r 0)) (hone : OneClass p A) :
    ModelIso p .K5 A := by
  classical
  obtain ⟨r', htop, hcoe⟩ := exists_subtype_tuple hA
  change (∀ i j, (r i * r j) ^ kFiveExp i j = 1) ∧
    (r 2 * r 1 * r 2 * r 3) ^ 3 = 1 at hrel
  have hrel' : HSFiveRel r' := by
    show (∀ i j, (r' i * r' j) ^ kFiveExp i j = 1) ∧
      (r' 2 * r' 1 * r' 2 * r' 3) ^ 3 = 1
    constructor
    · intro i j
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, hcoe] using hrel.1 i j
    · apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, hcoe] using hrel.2
  have hK : ExcRow.K5.ord = 51840 := by decide
  have hcardModel : Nat.card (model .K5) = 51840 := card_model_kFive.trans hK
  obtain ⟨t, ht, htgen, -, ht0⟩ := exists_hsFive_model
  obtain ⟨f, hf⟩ := exists_mulEquiv_of_hsFiveRel ht hrel' htgen htop hcardModel.ge
    (hK.symm.trans_le hcard)
  have hG : (Nat.card (model .K5) : ZMod 13) ≠ 0 := by
    rw [hcardModel]
    decide
  have hgen := closure_conj_of_forall_isConj (model .K5) t htgen (kFive_conj_of_rel ht)
  refine modelIso_of_conj_class (k := .K5) f (t 0) ht0 hG hgen ?_ hone
  rw [hf 0, hcoe 0]
  exact hr0

theorem modelIso_kSix {p : ℕ}
    [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {r : Fin 6 → (U ≃ₗ[ZMod p] U)}
    (hA : Subgroup.closure (Set.range r) = A) (hrel : HSSixRel r)
    (hcard : ExcRow.K6.ord ≤ Nat.card A) (hr0 : IsRefl p (r 0)) (hone : OneClass p A) :
    ModelIso p .K6 A := by
  classical
  obtain ⟨r', htop, hcoe⟩ := exists_subtype_tuple hA
  change (∀ i j, (r i * r j) ^ kSixExp i j = 1) ∧
    (r 2 * r 1 * r 2 * r 3) ^ 3 = 1 at hrel
  have hrel' : HSSixRel r' := by
    show (∀ i j, (r' i * r' j) ^ kSixExp i j = 1) ∧
      (r' 2 * r' 1 * r' 2 * r' 3) ^ 3 = 1
    constructor
    · intro i j
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, hcoe] using hrel.1 i j
    · apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, hcoe] using hrel.2
  have hK : ExcRow.K6.ord = 39191040 := by decide
  have hcardModel : Nat.card (model .K6) = 39191040 := card_model_kSix.trans hK
  obtain ⟨t, ht, htgen, -, ht0⟩ := exists_hsSix_model
  obtain ⟨f, hf⟩ := exists_mulEquiv_of_hsSixRel ht hrel' htgen htop hcardModel.ge
    (hK.symm.trans_le hcard)
  have hG : (Nat.card (model .K6) : ZMod 13) ≠ 0 := by
    rw [hcardModel]
    decide
  have hgen := closure_conj_of_forall_isConj (model .K6) t htgen (kSix_conj_of_rel ht)
  refine modelIso_of_conj_class (k := .K6) f (t 0) ht0 hG hgen ?_ hone
  rw [hf 0, hcoe 0]
  exact hr0

end CFSG.StandardType.ZS

end
