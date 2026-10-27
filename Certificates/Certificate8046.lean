module

public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityVocab

public section

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint

namespace CertificateChecks.Batch8046

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint

private def twoTable : Fin 8 → Fin 2 → Fin 11 → Fin 11 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![0, 1, 5, 10, 8, 2, 7, 6, 4, 9, 3]],
    ![![0, 6, 5, 7, 10, 2, 3, 9, 1, 4, 8], ![0, 6, 2, 8, 1, 5, 9, 3, 10, 4, 7]],
    ![![0, 3, 2, 9, 8, 5, 7, 4, 6, 10, 1], ![0, 3, 5, 1, 6, 2, 4, 7, 8, 10, 9]],
    ![![0, 7, 5, 4, 1, 2, 9, 10, 3, 8, 6], ![0, 7, 2, 6, 3, 5, 10, 9, 1, 8, 4]],
    ![![0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3], ![0, 9, 5, 3, 7, 2, 8, 4, 6, 1, 10]],
    ![![0, 4, 5, 8, 3, 2, 10, 1, 9, 6, 7], ![0, 4, 2, 7, 9, 5, 1, 10, 3, 6, 8]],
    ![![0, 10, 2, 1, 7, 5, 8, 6, 4, 3, 9], ![0, 10, 5, 9, 4, 2, 6, 8, 7, 3, 1]],
    ![![0, 8, 5, 6, 9, 2, 1, 3, 10, 7, 4], ![0, 8, 2, 4, 10, 5, 3, 1, 9, 7, 6]]]

private def twoT (x : Fin 8 × Fin 2) : Fin 11 → Fin 11 := twoTable x.1 x.2

private def threeT : Fin 11 → Fin 11 := ![2, 6, 5, 9, 3, 0, 10, 7, 8, 4, 1]

private def aT : Fin 11 → Fin 11 := ![0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]

private def conjT : Fin 5 → Fin 11 → Fin 11 :=
  ![![2, 5, 8, 10, 6, 7, 9, 1, 4, 0, 3], ![0, 1, 7, 9, 6, 8, 4, 2, 5, 3, 10],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![5, 8, 9, 2, 4, 1, 3, 6, 10, 7, 0],
    ![0, 1, 8, 10, 5, 7, 2, 4, 6, 3, 9]]

private def centT (x : (Fin 8 × Fin 2) × Fin 3) (p : Fin 11) : Fin 11 :=
  twoT x.1 (threeT^[x.2.val] p)

private theorem two_apply :
    ∀ x p, (m11TwoCoordinates x : Equiv.Perm (Fin 11)) p = twoT x p := by
  decide +kernel

private theorem three_apply : ∀ p, (m11LocalThree : Equiv.Perm (Fin 11)) p = threeT p := by
  decide +kernel

private theorem a_apply : ∀ p, (m11a : Equiv.Perm (Fin 11)) p = aT p := by
  decide +kernel

private theorem conj_apply :
    ∀ i p, (m11InvolutionConjugator i : Equiv.Perm (Fin 11)) p = conjT i p := by
  decide +kernel

private theorem cent_apply (x : (Fin 8 × Fin 2) × Fin 3) (p : Fin 11) :
    (m11CentralizerCoordinates x : Equiv.Perm (Fin 11)) p = centT x p := by
  have h3 : ⇑(m11LocalThree : Equiv.Perm (Fin 11)) = threeT := funext three_apply
  simp only [m11CentralizerCoordinates, Subgroup.coe_mul, Subgroup.coe_pow, Equiv.Perm.mul_apply,
    Equiv.Perm.coe_pow, h3, two_apply, centT]

private theorem m11_ext_iff {g h : NativeSporadic.M11} :
    g = h ↔ ∀ p, (g : Equiv.Perm (Fin 11)) p = (h : Equiv.Perm (Fin 11)) p := by
  rw [Subtype.ext_iff, Equiv.ext_iff]

private theorem eq_one_of_table {g : NativeSporadic.M11} {G : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (hG : ∀ p, G p = p) : g = 1 :=
  m11_ext_iff.2 fun p => by simp only [hg, hG, OneMemClass.coe_one, Equiv.Perm.one_apply]

private theorem mul_eq_of_table {g h k : NativeSporadic.M11} {G H K : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (hh : ∀ p, (h : Equiv.Perm (Fin 11)) p = H p)
    (hk : ∀ p, (k : Equiv.Perm (Fin 11)) p = K p) (hGHK : ∀ p, G (H p) = K p) : g * h = k :=
  m11_ext_iff.2 fun p => by simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, hh, hk, hGHK]

private theorem inv_eq_of_table {g h : NativeSporadic.M11} {G H : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (hh : ∀ p, (h : Equiv.Perm (Fin 11)) p = H p)
    (hGH : ∀ p, G (H p) = p) : g⁻¹ = h :=
  inv_eq_iff_mul_eq_one.2 <| m11_ext_iff.2 fun p => by
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, hh, hGH, OneMemClass.coe_one,
      Equiv.Perm.one_apply]

private theorem conj_eq_of_table {c g k : NativeSporadic.M11} {C G K : Fin 11 → Fin 11}
    (hc : ∀ p, (c : Equiv.Perm (Fin 11)) p = C p) (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p)
    (hk : ∀ p, (k : Equiv.Perm (Fin 11)) p = K p) (hCGK : ∀ p, C (G p) = K (C p)) :
    c * g * c⁻¹ = k :=
  mul_inv_eq_iff_eq_mul.2 <| m11_ext_iff.2 fun p => by
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hc, hg, hk, hCGK]

private theorem table_eq_of_eq {g h : NativeSporadic.M11} {G H : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (hh : ∀ p, (h : Equiv.Perm (Fin 11)) p = H p)
    (hgh : g = h) (p : Fin 11) : G p = H p := by
  rw [← hg, ← hh, hgh]

private theorem table_ne_id {g : NativeSporadic.M11} {G : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (h1 : g ≠ 1) : ¬ ∀ p, G p = p :=
  fun hG => h1 (eq_one_of_table hg hG)

private theorem table_sq {g : NativeSporadic.M11} {G : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (h2 : g ^ 2 = 1) (p : Fin 11) :
    G (G p) = p := by
  have h := congrArg (fun g : NativeSporadic.M11 => (g : Equiv.Perm (Fin 11)) p) h2
  simpa only [sq, Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, OneMemClass.coe_one,
    Equiv.Perm.one_apply] using h

private theorem table_cube {g : NativeSporadic.M11} {G : Fin 11 → Fin 11}
    (hg : ∀ p, (g : Equiv.Perm (Fin 11)) p = G p) (h3 : g ^ 3 = 1) (p : Fin 11) :
    G (G (G p)) = p := by
  have h := congrArg (fun g : NativeSporadic.M11 => (g : Equiv.Perm (Fin 11)) p) h3
  simpa only [pow_three, Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, OneMemClass.coe_one,
    Equiv.Perm.one_apply] using h

private theorem two_closed_table :
    (∃ x, ∀ p, twoT x p = p) ∧ (∀ x y, ∃ z, ∀ p, twoT x (twoT y p) = twoT z p) ∧
      ∀ x, ∃ y, ∀ p, twoT x (twoT y p) = p := by
  decide +kernel

private theorem two_injective_table : ∀ x y, (∀ p, twoT x p = twoT y p) → x = y := by
  decide +kernel

private theorem two_fusion_table :
    ∀ x, (¬ ∀ p, twoT x p = p) → (∀ p, twoT x (twoT x p) = p) →
      ∃ i : Fin 5, ∀ p, conjT i (twoT x p) = aT (conjT i p) := by
  decide +kernel

private theorem cent_injective_table : ∀ x y, (∀ p, centT x p = centT y p) → x = y := by
  decide +kernel

private theorem cent_fusion_table :
    ∀ x, (¬ ∀ p, centT x p = p) → (∀ p, centT x (centT x (centT x p)) = p) →
      ∃ y, ∀ p, centT y (centT x p) = threeT (centT y p) := by
  decide +kernel

private def tupleEquiv : (Fin 4 → Fin 11) ≃ Fin 11 × Fin 11 × Fin 11 × Fin 11 where
  toFun a := (a 0, a 1, a 2, a 3)
  invFun v := ![v.1, v.2.1, v.2.2.1, v.2.2.2]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv _ := rfl

private theorem card_images_table :
    Fintype.card {v : Fin 11 × Fin 11 × Fin 11 × Fin 11 //
      aT v.1 = v.1 ∧ aT v.2.1 = v.2.1 ∧ aT v.2.2.1 = v.2.2.1 ∧ aT v.2.2.2 ≠ v.2.2.2 ∧
        Function.Injective (tupleEquiv.symm v)} = 48 := by
  decide +kernel

private theorem m11_two_coordinates_closed_0 :
    (∃ x, m11TwoCoordinates x = 1) ∧
      (∀ x y, ∃ z, m11TwoCoordinates x * m11TwoCoordinates y = m11TwoCoordinates z) ∧
      (∀ x, ∃ y, (m11TwoCoordinates x)⁻¹ = m11TwoCoordinates y) := by
  obtain ⟨⟨e, he⟩, hmul, hinv⟩ := two_closed_table
  refine ⟨⟨e, eq_one_of_table (two_apply e) he⟩, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨z, hz⟩ := hmul x y
    exact ⟨z, mul_eq_of_table (two_apply x) (two_apply y) (two_apply z) hz⟩
  · obtain ⟨y, hy⟩ := hinv x
    exact ⟨y, inv_eq_of_table (two_apply x) (two_apply y) hy⟩

private theorem m11_two_coordinates_injective_1 : Function.Injective m11TwoCoordinates :=
  fun x y h => two_injective_table x y (table_eq_of_eq (two_apply x) (two_apply y) h)

private theorem m11_two_coordinates_involution_fusion_2 :
    ∀ x, m11TwoCoordinates x ≠ 1 → m11TwoCoordinates x ^ 2 = 1 →
      ∃ i : Fin 5, m11InvolutionConjugator i * m11TwoCoordinates x *
        (m11InvolutionConjugator i)⁻¹ = m11a := by
  intro x hx hx2
  obtain ⟨i, hi⟩ :=
    two_fusion_table x (table_ne_id (two_apply x) hx) (table_sq (two_apply x) hx2)
  exact ⟨i, conj_eq_of_table (conj_apply i) (two_apply x) a_apply hi⟩

private theorem m11_centralizer_coordinates_injective_3 :
    Function.Injective m11CentralizerCoordinates :=
  fun x y h => cent_injective_table x y (table_eq_of_eq (cent_apply x) (cent_apply y) h)

private theorem m11_centralizer_base_facts_4 : Function.Injective m11CentralizerBase ∧
    (∀ i : Fin 3, m11gA (m11CentralizerBase i.castSucc) = m11CentralizerBase i.castSucc) ∧
    m11gA (m11CentralizerBase 3) ≠ m11CentralizerBase 3 := by
  decide +kernel

private theorem m11_centralizer_three_fusion_6 :
    ∀ x, m11CentralizerCoordinates x ≠ 1 → m11CentralizerCoordinates x ^ 3 = 1 →
      ∃ y, m11CentralizerCoordinates y * m11CentralizerCoordinates x *
        (m11CentralizerCoordinates y)⁻¹ = m11LocalThree := by
  intro x hx hx3
  obtain ⟨y, hy⟩ :=
    cent_fusion_table x (table_ne_id (cent_apply x) hx) (table_cube (cent_apply x) hx3)
  exact ⟨y, conj_eq_of_table (cent_apply y) (cent_apply x) three_apply hy⟩

private theorem card_M11CentralizerImages_7 : Nat.card M11CentralizerImages = 48 := by
  have hA : ∀ q, m11gA q = aT q := a_apply
  rw [← card_images_table, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (tupleEquiv.subtypeEquiv fun a => ?_)
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hinj, hfix, hmov⟩
    exact ⟨(hA _).symm.trans (hfix 0), (hA _).symm.trans (hfix 1), (hA _).symm.trans (hfix 2),
      fun h => hmov ((hA _).trans h), hinj⟩
  · rintro ⟨h0, h1, h2, h3, hinj⟩
    refine ⟨hinj, fun i => ?_, fun h => h3 ((hA _).symm.trans h)⟩
    fin_cases i
    exacts [(hA _).trans h0, (hA _).trans h1, (hA _).trans h2]

end CertificateChecks.Batch8046

namespace Certificates

open CertificateChecks

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate8046 : ((∃ x, m11TwoCoordinates x = 1) ∧
      (∀ x y, ∃ z, m11TwoCoordinates x * m11TwoCoordinates y = m11TwoCoordinates z) ∧
      (∀ x, ∃ y, (m11TwoCoordinates x)⁻¹ = m11TwoCoordinates y))
    ∧ (Function.Injective m11TwoCoordinates)
    ∧ (∀ x, m11TwoCoordinates x ≠ 1 → m11TwoCoordinates x ^ 2 = 1 →
      ∃ i : Fin 5, m11InvolutionConjugator i * m11TwoCoordinates x *
        (m11InvolutionConjugator i)⁻¹ = m11a)
    ∧ (Function.Injective m11CentralizerCoordinates)
    ∧ (Function.Injective m11CentralizerBase ∧
    (∀ i : Fin 3, m11gA (m11CentralizerBase i.castSucc) = m11CentralizerBase i.castSucc) ∧
    m11gA (m11CentralizerBase 3) ≠ m11CentralizerBase 3)
    ∧ (∀ x, m11CentralizerCoordinates x ≠ 1 → m11CentralizerCoordinates x ^ 3 = 1 →
      ∃ y, m11CentralizerCoordinates y * m11CentralizerCoordinates x *
        (m11CentralizerCoordinates y)⁻¹ = m11LocalThree)
    ∧ (Nat.card M11CentralizerImages = 48) := by
  exact ⟨CertificateChecks.Batch8046.m11_two_coordinates_closed_0, CertificateChecks.Batch8046.m11_two_coordinates_injective_1,
      CertificateChecks.Batch8046.m11_two_coordinates_involution_fusion_2,
      CertificateChecks.Batch8046.m11_centralizer_coordinates_injective_3, CertificateChecks.Batch8046.m11_centralizer_base_facts_4,
      CertificateChecks.Batch8046.m11_centralizer_three_fusion_6,
      CertificateChecks.Batch8046.card_M11CentralizerImages_7⟩

end Certificates
