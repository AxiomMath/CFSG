module

public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KA5L.Roots

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section Conj

variable {L : Type} [Field L]

theorem conjSLn_diag_transvection {n : ℕ} (d : Fin n → Lˣ) {i j : Fin n} (hij : i ≠ j) (s : L) :
    conjSLn (diagHom n d) (Matrix.SpecialLinearGroup.transvection hij s) =
      Matrix.SpecialLinearGroup.transvection hij ((d i : L) * s * ((d j)⁻¹ : Lˣ)) := by
  apply Subtype.ext
  rw [coe_conjSLn, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  exact diagHom_mul_one_add_single_mul d hij s

theorem conjSLn_perm_transvection {n : ℕ} (π : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (s : L) : conjSLn (permGL π : GL (Fin n) L) (Matrix.SpecialLinearGroup.transvection hij s) =
      Matrix.SpecialLinearGroup.transvection (π.injective.ne hij) s := by
  apply Subtype.ext
  rw [coe_conjSLn, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  set P : GL (Fin n) L := permGL π with hP
  have h : (↑P⁻¹ : Matrix (Fin n) (Fin n) L) * single (π i) (π j) s *
      (P : Matrix (Fin n) (Fin n) L) = single i j s := permGL_inv_mul_single_mul (K := L) π i j s
  have e : (P : Matrix (Fin n) (Fin n) L) * single i j s * (↑P⁻¹ : Matrix (Fin n) (Fin n) L) =
      single (π i) (π j) s := by
    calc (P : Matrix (Fin n) (Fin n) L) * single i j s * (↑P⁻¹ : Matrix (Fin n) (Fin n) L)
        = (P : Matrix (Fin n) (Fin n) L) * ((↑P⁻¹ : Matrix (Fin n) (Fin n) L) *
            single (π i) (π j) s * (P : Matrix (Fin n) (Fin n) L)) *
              (↑P⁻¹ : Matrix (Fin n) (Fin n) L) := by rw [h]
      _ = ((P : Matrix (Fin n) (Fin n) L) * (↑P⁻¹ : Matrix (Fin n) (Fin n) L)) *
            single (π i) (π j) s * ((P : Matrix (Fin n) (Fin n) L) *
              (↑P⁻¹ : Matrix (Fin n) (Fin n) L)) := by simp only [Matrix.mul_assoc]
      _ = single (π i) (π j) s := by rw [P.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, P.mul_inv, e]

theorem conjSLn_bijective {n : ℕ} (M : GL (Fin n) L) : Function.Bijective (conjSLn M) := by
  have hl : Function.LeftInverse (conjSLn M⁻¹) (conjSLn M) := fun A => by
    apply Subtype.ext
    rw [coe_conjSLn, coe_conjSLn]
    calc _ = ((↑M⁻¹ : Matrix (Fin n) (Fin n) L) * (M : Matrix (Fin n) (Fin n) L)) *
          (A : Matrix (Fin n) (Fin n) L) * ((↑M⁻¹ : Matrix (Fin n) (Fin n) L) *
            (M : Matrix (Fin n) (Fin n) L)) := by simp only [inv_inv, Matrix.mul_assoc]
      _ = A := by rw [M.inv_mul, Matrix.one_mul, Matrix.mul_one]
  have hr : Function.RightInverse (conjSLn M⁻¹) (conjSLn M) := fun A => by
    apply Subtype.ext
    rw [coe_conjSLn, coe_conjSLn]
    calc _ = ((M : Matrix (Fin n) (Fin n) L) * (↑M⁻¹ : Matrix (Fin n) (Fin n) L)) *
          (A : Matrix (Fin n) (Fin n) L) * ((M : Matrix (Fin n) (Fin n) L) *
            (↑M⁻¹ : Matrix (Fin n) (Fin n) L)) := by simp only [inv_inv, Matrix.mul_assoc]
      _ = A := by rw [M.mul_inv, Matrix.one_mul, Matrix.mul_one]
  exact ⟨hl.injective, hr.surjective⟩

end Conj

section Coboundary

variable {L : Type} [Field L]

theorem exists_coboundary (c : Fin 6 → Fin 6 → Lˣ)
    (hmul : ∀ i j l : Fin 6, i ≠ j → j ≠ l → i ≠ l → c i l = c i j * c j l) :
    ∃ d : Fin 6 → Lˣ, ∀ i j : Fin 6, i ≠ j → c i j = d i * (d j)⁻¹ := by
  have hrec : ∀ i j : Fin 6, i ≠ j → c i j * c j i = 1 := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := exists_ne_and_ne (by norm_num : 3 ≤ 6) i j
    have h1 := hmul i j k hij (Ne.symm hkj) (Ne.symm hki)
    have h2 := hmul j i k hij.symm (Ne.symm hki) (Ne.symm hkj)
    have h3 : c j k = c j i * (c i j * c j k) := by rw [← h1]; exact h2
    have h4 : (c j i * c i j) * c j k = 1 * c j k := by
      calc (c j i * c i j) * c j k = c j i * (c i j * c j k) := mul_assoc _ _ _
        _ = c j k := h3.symm
        _ = 1 * c j k := (one_mul _).symm
    rw [mul_comm]
    exact mul_right_cancel h4
  have hinv : ∀ i j : Fin 6, i ≠ j → c j i = (c i j)⁻¹ := fun i j hij =>
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hrec i j hij)
  refine ⟨fun i => if i = 5 then 1 else c i 5, fun i j hij => ?_⟩
  by_cases hi : i = 5
  · subst hi
    have hj : j ≠ 5 := fun h => hij h.symm
    simp only [hj, ite_true, ite_false, one_mul]
    exact hinv j 5 hj
  by_cases hj : j = 5
  · subst hj
    simp [hi]
  simp only [hi, hj, ite_false]
  rw [hmul i 5 j hi (Ne.symm hj) hij, hinv j 5 hj]

end Coboundary

section Lift

variable {L : Type} [Field L]

theorem map_surjective_of_bijective (Fr : L →+* L) (hFr : Function.Bijective Fr) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 6) Fr) := by
  intro Y
  let e : L ≃+* L := RingEquiv.ofBijective Fr hFr
  refine ⟨Matrix.SpecialLinearGroup.map (n := Fin 6) (e.symm : L →+* L) Y, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply]
  exact e.apply_symm_apply _

@[expose] def splitHom (Fr : L →+* L) (d : Fin 6 → Lˣ) (π : Equiv.Perm (Fin 6)) :
    SL(6, L) →* SL(6, L) :=
  (conjSLn (permGL π : GL (Fin 6) L)).comp ((conjSLn (diagHom 6 d)).comp
    (Matrix.SpecialLinearGroup.map (n := Fin 6) Fr))

theorem splitHom_transvection (Fr : L →+* L) (d : Fin 6 → Lˣ) (π : Equiv.Perm (Fin 6))
    {i j : Fin 6} (hij : i ≠ j) (t : L) :
    splitHom Fr d π (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection (π.injective.ne hij)
        ((d i : L) * Fr t * ((d j)⁻¹ : Lˣ)) := by
  rw [splitHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Matrix.SpecialLinearGroup.map_transvection, conjSLn_diag_transvection,
    conjSLn_perm_transvection]

theorem splitHom_bijective (Fr : L →+* L) (hFr : Function.Bijective Fr) (d : Fin 6 → Lˣ)
    (π : Equiv.Perm (Fin 6)) : Function.Bijective (splitHom Fr d π) := by
  have h1 := conjSLn_bijective (L := L) (permGL π : GL (Fin 6) L)
  have h2 := conjSLn_bijective (L := L) (diagHom 6 d)
  have h3 : Function.Bijective (Matrix.SpecialLinearGroup.map (n := Fin 6) Fr) :=
    ⟨specialLinearGroup_map_injective hFr.1, map_surjective_of_bijective Fr hFr⟩
  unfold splitHom
  rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact h1.comp (h2.comp h3)


theorem cocycle_of_hom (Fr : L →+* L) (ψ : SL(6, L) →* ModGL Tag.E7 L) (π : Equiv.Perm (Fin 6))
    (ν : Fin 6 → Fin 6 → Lˣ)
    (hν : ∀ (a b : Fin 6) (hab : a ≠ b) (t : L),
      ψ (Matrix.SpecialLinearGroup.transvection hab t) =
        a5Frame L (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((ν a b : L) * Fr t)))
    (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (ν a c : Lˣ) = ν a b * ν b c := by
  have hpab := π.injective.ne hab
  have hpbc := π.injective.ne hbc
  have hpac := π.injective.ne hac
  have e1 : ψ ⁅Matrix.SpecialLinearGroup.transvection hab (1 : L),
      Matrix.SpecialLinearGroup.transvection hbc (1 : L)⁆ =
      ψ (Matrix.SpecialLinearGroup.transvection hac ((1 : L) * 1)) := by
    rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac]
  rw [map_commutatorElement, hν a b hab 1, hν b c hbc 1, hν a c hac (1 * 1)] at e1
  have e2 : ⁅a5Frame L (Matrix.SpecialLinearGroup.transvection hpab ((ν a b : L) * Fr 1)),
      a5Frame L (Matrix.SpecialLinearGroup.transvection hpbc ((ν b c : L) * Fr 1))⁆ =
      a5Frame L (Matrix.SpecialLinearGroup.transvection hpac
        (((ν a b : L) * Fr 1) * ((ν b c : L) * Fr 1))) := by
    rw [← map_commutatorElement,
      Matrix.SpecialLinearGroup.commutatorElement_transvection hpab hpbc hpac]
  rw [e1] at e2
  obtain ⟨ε, hε⟩ := a5Frame_transv (L := L) (π a) (π c) hpac
  rw [hε, hε] at e2
  have h1 := pinnedX_injective Tag.E7 L _ e2
  simp only [map_one, mul_one] at h1
  have h2 : (ε : L) * ν a c = ε * (ν a b * ν b c : Lˣ) := by
    rw [Units.val_mul]
    linear_combination h1
  exact Units.ext (mul_left_cancel₀ ε.ne_zero h2)

theorem exists_aut_of_hom_split (Fr : L →+* L) (hFr : Function.Bijective Fr)
    (ψ : SL(6, L) →* ModGL Tag.E7 L) (π : Equiv.Perm (Fin 6))
    (h : ∀ a b : Fin 6, ∃ ν : Lˣ, ∀ (hab : a ≠ b) (t : L),
      ψ (Matrix.SpecialLinearGroup.transvection hab t) =
        a5Frame L (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((ν : L) * Fr t))) :
    ∃ Φ' : SL(6, L) ≃* SL(6, L), (∀ X, ψ X = a5Frame L (Φ' X)) ∧
      ∃ b : Fin 6 → Fin 6 → Lˣ, ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
          Matrix (Fin 6) (Fin 6) L) = 1 + single (π i) (π j) ((b i j : L) * Fr t) := by
  choose ν hν using h
  obtain ⟨d, hd⟩ := exists_coboundary ν (cocycle_of_hom Fr ψ π ν hν)
  have hψ : ψ = (a5Frame L).comp (splitHom Fr d π) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    have hpar : (ν i j : L) * Fr t = (d i : L) * Fr t * ((d j)⁻¹ : Lˣ) := by
      rw [hd i j hij, Units.val_mul]
      ring
    rw [hν i j hij t, MonoidHom.comp_apply, splitHom_transvection, hpar]
  refine ⟨MulEquiv.ofBijective (splitHom Fr d π) (splitHom_bijective Fr hFr d π),
    fun X => DFunLike.congr_fun hψ X, fun i j => d i * (d j)⁻¹, fun i j hij t => ?_⟩
  change ((splitHom Fr d π (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
    Matrix (Fin 6) (Fin 6) L) = _
  rw [splitHom_transvection, Matrix.SpecialLinearGroup.transvection_coe, Units.val_mul]
  congr 2
  ring

theorem exists_aut_of_hom_unitary (Fr : L →+* L) (hFr : Function.Bijective Fr)
    (ψ : SL(6, L) →* ModGL Tag.E7 L) (π : Equiv.Perm (Fin 6))
    (h : ∀ a b : Fin 6, ∃ ν : Lˣ, ∀ (hab : a ≠ b) (t : L),
      ψ (Matrix.SpecialLinearGroup.transvection hab t) =
        a5Frame L (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
          ((ν : L) * Fr t))) :
    ∃ Φ' : SL(6, L) ≃* SL(6, L), (∀ X, ψ X = a5Frame L (Φ' X)) ∧
      ∃ b : Fin 6 → Fin 6 → Lˣ, ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
          Matrix (Fin 6) (Fin 6) L) = 1 + single (π j) (π i) ((b i j : L) * Fr t) := by
  choose ν hν using h
  set ψ' : SL(6, L) →* ModGL Tag.E7 L := ψ.comp invTransposeSL with hψ'
  have hψ'gen : ∀ (a b : Fin 6), ∃ μ : Lˣ, ∀ (hab : a ≠ b) (t : L),
      ψ' (Matrix.SpecialLinearGroup.transvection hab t) =
        a5Frame L (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((μ : L) * Fr t)) := by
    intro a b
    refine ⟨-ν b a, fun hab t => ?_⟩
    have hpar : (ν b a : L) * Fr (-t) = ((-ν b a : Lˣ) : L) * Fr t := by
      rw [map_neg, Units.val_neg]
      ring
    rw [hψ', MonoidHom.comp_apply, show Matrix.SpecialLinearGroup.transvection hab t =
      Matrix.SpecialLinearGroup.transvection (show b ≠ a from hab.symm).symm t from rfl,
      invTransposeSL_transvection (show b ≠ a from hab.symm), hν b a hab.symm (-t), hpar]
  obtain ⟨Φs, hΦs, b, hb⟩ := exists_aut_of_hom_split Fr hFr ψ' π hψ'gen
  have hinv : Function.Bijective (invTransposeSL (n := 6) (K := L)) :=
    Function.Involutive.bijective invTransposeSL_invTransposeSL
  refine ⟨(MulEquiv.ofBijective invTransposeSL hinv).trans Φs, fun X => ?_, fun i j => -b j i,
    fun i j hij t => ?_⟩
  · have := hΦs (invTransposeSL X)
    rw [hψ', MonoidHom.comp_apply, invTransposeSL_invTransposeSL] at this
    exact this
  · change ((Φs (invTransposeSL (Matrix.SpecialLinearGroup.transvection hij t)) : SL(6, L)) :
      Matrix (Fin 6) (Fin 6) L) = _
    have hpar : ((b j i : Lˣ) : L) * Fr (-t) = ((-b j i : Lˣ) : L) * Fr t := by
      rw [map_neg, Units.val_neg]
      ring
    rw [show Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection (show j ≠ i from hij.symm).symm t from rfl,
      invTransposeSL_transvection (show j ≠ i from hij.symm), hb j i hij.symm (-t), hpar]

@[expose] def twistHom (n : ModGL Tag.E7 L) (Fr : L →+* L) : SL(6, L) →* ModGL Tag.E7 L :=
  (MulAut.conj n).toMonoidHom.comp ((Units.map (entrywiseHom Fr)).comp (a5Frame L))

theorem twistHom_apply (n : ModGL Tag.E7 L) (Fr : L →+* L) (X : SL(6, L)) :
    twistHom n Fr X = n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ := by
  simp [twistHom, MulAut.conj_apply]

theorem twistHom_shape_split (Fr : L →+* L) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L)
    (π : Equiv.Perm (Fin 6))
    (hπ : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
      a5Root (π a) (π b)) (a b : Fin 6) :
    ∃ ν : Lˣ, ∀ (hab : a ≠ b) (t : L),
      twistHom n Fr (Matrix.SpecialLinearGroup.transvection hab t) =
      a5Frame L (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab) ((ν : L) * Fr t)) := by
  by_cases hab : a = b
  · exact ⟨1, fun h => absurd hab h⟩
  obtain ⟨ε, hε⟩ := a5Frame_transv (L := L) a b hab
  obtain ⟨ε', hε'⟩ := a5Frame_transv (L := L) (π a) (π b) (π.injective.ne hab)
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (isRoot_a5Root hab)
  refine ⟨μ * Units.map (Fr : L →* L) ε * ε'⁻¹, fun hab' t => ?_⟩
  rw [twistHom_apply, hε t, units_map_entrywiseHom_pinnedX, hμ, hπ a b hab, hε']
  congr 1
  simp only [Units.val_mul, Units.coe_map, Units.val_inv_eq_inv_val, map_mul, MonoidHom.coe_ofClass]
  field_simp [ε'.ne_zero]

theorem twistHom_shape_unitary (Fr : L →+* L) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L) (π : Equiv.Perm (Fin 6))
    (hπ : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
      a5Root (π b) (π a)) (a b : Fin 6) :
    ∃ ν : Lˣ, ∀ (hab : a ≠ b) (t : L),
      twistHom n Fr (Matrix.SpecialLinearGroup.transvection hab t) =
      a5Frame L (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
        ((ν : L) * Fr t)) := by
  by_cases hab : a = b
  · exact ⟨1, fun h => absurd hab h⟩
  obtain ⟨ε, hε⟩ := a5Frame_transv (L := L) a b hab
  obtain ⟨ε', hε'⟩ := a5Frame_transv (L := L) (π b) (π a) (π.injective.ne hab).symm
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (isRoot_a5Root hab)
  refine ⟨μ * Units.map (Fr : L →* L) ε * ε'⁻¹, fun hab' t => ?_⟩
  rw [twistHom_apply, hε t, units_map_entrywiseHom_pinnedX, hμ, hπ a b hab, hε']
  congr 1
  simp only [Units.val_mul, Units.coe_map, Units.val_inv_eq_inv_val, map_mul, MonoidHom.coe_ofClass]
  field_simp [ε'.ne_zero]

theorem exists_aut_split (Fr : L →+* L) (hFr : Function.Bijective Fr) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L) (π : Equiv.Perm (Fin 6))
    (hπ : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
      a5Root (π a) (π b)) :
    ∃ Φ' : SL(6, L) ≃* SL(6, L),
      (∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X)) ∧
      ∃ b : Fin 6 → Fin 6 → Lˣ, ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
          Matrix (Fin 6) (Fin 6) L) = 1 + single (π i) (π j) ((b i j : L) * Fr t) := by
  obtain ⟨Φ', h1, h2⟩ := exists_aut_of_hom_split Fr hFr (twistHom n Fr) π
    (twistHom_shape_split Fr n hn π hπ)
  exact ⟨Φ', fun X => by rw [← twistHom_apply]; exact h1 X, h2⟩

theorem exists_aut_unitary (Fr : L →+* L) (hFr : Function.Bijective Fr) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L) (π : Equiv.Perm (Fin 6))
    (hπ : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
      a5Root (π b) (π a)) :
    ∃ Φ' : SL(6, L) ≃* SL(6, L),
      (∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X)) ∧
      ∃ b : Fin 6 → Fin 6 → Lˣ, ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
          Matrix (Fin 6) (Fin 6) L) = 1 + single (π j) (π i) ((b i j : L) * Fr t) := by
  obtain ⟨Φ', h1, h2⟩ := exists_aut_of_hom_unitary Fr hFr (twistHom n Fr) π
    (twistHom_shape_unitary Fr n hn π hπ)
  exact ⟨Φ', fun X => by rw [← twistHom_apply]; exact h1 X, h2⟩

end Lift

end CFSG.RankThree.PartOne.KA5L
