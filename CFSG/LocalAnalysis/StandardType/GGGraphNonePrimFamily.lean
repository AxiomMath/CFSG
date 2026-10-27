module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition

@[expose] def PrimFamily {n : ℕ} {K : Type} [Field K] (A : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (P : Finset (Matrix (Fin n) (Fin n) K)) : Prop :=
  (∀ e, e ∈ P ↔ IsPrimIdemIn A e) ∧ (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e * e' = 0) ∧ ∑ e ∈ P, e = 1

private lemma primFamilyAux_primFamily_intro {n : ℕ} {K : Type} [Field K]
    {A : Subalgebra K (Matrix (Fin n) (Fin n) K)} {P : Finset (Matrix (Fin n) (Fin n) K)}
    (h1 : ∀ e, e ∈ P ↔ IsPrimIdemIn A e)
    (h2 : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e * e' = 0) (h3 : ∑ e ∈ P, e = 1) :
    PrimFamily A P := by
  exact ⟨h1, h2, h3⟩
private lemma primFamilyAux_adjoin_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K))),
      ∀ b ∈ Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K))), a * b = b * a := by
  let A : Subalgebra K (Matrix (Fin n) (Fin n) K) :=
    Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K)))
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs
    subst ht
    exact Commute.refl _
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
private lemma primFamilyAux_exists_orthFamily {n : ℕ} {K : Type} [Field K]
    (A : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ P : Finset (Matrix (Fin n) (Fin n) K),
      (∀ p ∈ P, IsPrimIdemIn A p) ∧
        (∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0) ∧ ∑ p ∈ P, p = 1 := by
  obtain ⟨P, hP, horth, hsum⟩ :=
    CFSG.StandardType.ClassicalPosition.Block.exists_finset_isPrimStarIdemIn_sum_eq
      id A hcomm (by intro a _ b _; rfl) A.one_mem (by rw [IsIdempotentElem, one_mul]) rfl
  refine ⟨P, ?_, horth, hsum⟩
  intro p hp
  exact (CFSG.StandardType.ClassicalPosition.Block.isPrimStarIdemIn_id_iff A p).mp (hP p hp).1
private lemma primFamilyAux_prim_mem_of_sum_one {n : ℕ} {K : Type} [Field K]
    (A : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {P : Finset (Matrix (Fin n) (Fin n) K)}
    (hprim : ∀ p ∈ P, IsPrimIdemIn A p)
    (hsum : ∑ p ∈ P, p = 1)
    {e : Matrix (Fin n) (Fin n) K} (he : IsPrimIdemIn A e) : e ∈ P := by
  by_contra hnot
  have heA : e ∈ A := he.1
  have hee : e * e = e := he.2.1
  have he0 : e ≠ 0 := he.2.2.1
  have heprim : ∀ e' ∈ A, IsIdempotentElem e' → e' * e = e' → e' = 0 ∨ e' = e := he.2.2.2
  have hzero : ∀ p ∈ P, e * p = 0 := by
    intro p hp
    have hpA : p ∈ A := (hprim p hp).1
    have hpe : p * e = e * p := hcomm p hpA e heA
    have hpp : p * p = p := (hprim p hp).2.1
    have hidem : IsIdempotentElem (e * p) := by
      rw [IsIdempotentElem]
      calc (e * p) * (e * p) = e * (p * (e * p)) := by rw [mul_assoc e p (e * p)]
        _ = e * ((p * e) * p) := by rw [← mul_assoc p e p]
        _ = e * ((e * p) * p) := by rw [hpe]
        _ = e * (e * (p * p)) := by rw [← mul_assoc e p p]
        _ = e * (e * p) := by rw [hpp]
        _ = (e * e) * p := by rw [← mul_assoc e e p]
        _ = e * p := by rw [hee]
    have hmul : (e * p) * e = e * p := by
      calc (e * p) * e = e * (p * e) := by rw [mul_assoc e p e]
        _ = e * (e * p) := by rw [hpe]
        _ = (e * e) * p := by rw [← mul_assoc e e p]
        _ = e * p := by rw [hee]
    rcases heprim (e * p) (A.mul_mem heA hpA) hidem hmul with h0 | hep
    · exact h0
    · exfalso
      have hmem : e ∈ P := by
        rcases (hprim p hp).2.2.2 e heA hee hep with h | h
        · exact absurd h he0
        · rw [h]; exact hp
      exact hnot hmem
  have hsum_mul : e = ∑ p ∈ P, e * p := by
    calc e = e * 1 := (mul_one e).symm
      _ = e * (∑ p ∈ P, p) := by rw [← hsum]
      _ = ∑ p ∈ P, e * p := by rw [Finset.mul_sum]
  have hzero_sum : ∑ p ∈ P, e * p = 0 := Finset.sum_eq_zero hzero
  exact he0 (by rw [hsum_mul, hzero_sum])
theorem exists_primFamily_adjoin {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∃ P : Finset (Matrix (Fin n) (Fin n) K),
      PrimFamily (Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K)))) P := by
  obtain ⟨P, hprim, horth, hsum⟩ :=
    primFamilyAux_exists_orthFamily (Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K))))
      (primFamilyAux_adjoin_comm B)
  refine ⟨P, primFamilyAux_primFamily_intro ?_ horth hsum⟩
  intro e
  exact ⟨fun he => hprim e he,
    fun he => primFamilyAux_prim_mem_of_sum_one (Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K))))
      (primFamilyAux_adjoin_comm B) hprim hsum he⟩

theorem primFamily_map_mem {n : ℕ} {K : Type} [Field K]
    {A : Subalgebra K (Matrix (Fin n) (Fin n) K)} {P : Finset (Matrix (Fin n) (Fin n) K)}
    (hP : PrimFamily A P) (φ : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hmul : ∀ a b, φ (a * b) = φ b * φ a)
    (hA : ∀ a ∈ A, φ a ∈ A) (hinv : ∀ a ∈ A, φ (φ a) = a)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : ∀ e ∈ P, φ e ∈ P := by
  intro e he
  rcases hP with ⟨hP1, _, _⟩
  have hpe : IsPrimIdemIn A e := (hP1 e).1 he
  have hzero : φ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero (φ 0)).symm)
  have hmem : φ e ∈ A := hA e hpe.1
  have hidem : IsIdempotentElem (φ e) := by
    rw [IsIdempotentElem, ← hmul e e, hpe.2.1.eq]
  have hne : φ e ≠ 0 := by
    intro h0
    have h := congrArg φ h0
    rw [hinv e hpe.1, hzero] at h
    exact hpe.2.2.1 h
  refine (hP1 (φ e)).2 ⟨hmem, hidem, hne, ?_⟩
  intro f hfA hfid hfe
  have hfA' : φ f ∈ A := hA f hfA
  have hidem' : IsIdempotentElem (φ f) := by
    rw [IsIdempotentElem, ← hmul f f, hfid.eq]
  have hkey1 : e * φ f = φ f := by
    have h := congrArg φ hfe
    rw [hmul f (φ e), hinv e hpe.1] at h
    exact h
  have hkey : φ f * e = φ f := (hcomm (φ f) hfA' e hpe.1).trans hkey1
  rcases hpe.2.2.2 (φ f) hfA' hidem' hkey with h0 | hee
  · left
    have h := congrArg φ h0
    rw [hinv f hfA, hzero] at h
    exact h
  · right
    have h := congrArg φ hee
    rw [hinv f hfA] at h
    exact h

end CFSG.StandardType
