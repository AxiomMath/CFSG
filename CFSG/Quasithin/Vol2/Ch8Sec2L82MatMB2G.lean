module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TQMod
public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Quasithin.H13.L828T

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem map_subgroupOf_eq_mb2g (e : V ≃* W) (B U : Subgroup V) :
    (U.subgroupOf B).map (e.subgroupMap B).toMonoidHom =
      (U.map e.toMonoidHom).subgroupOf (B.map e.toMonoidHom) := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨b, hb⟩, hbU, hxb⟩
    exact ⟨b, hbU, congrArg Subtype.val hxb⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨b, hb, hbu⟩ := Subgroup.mem_map.mp hx
    have : b = u := e.injective hbu
    subst this
    exact ⟨⟨b, hb⟩, hu, Subtype.ext hbu⟩

@[expose] def qmodEquiv_mb2g (e : V ≃* W) (B U : Subgroup V) :
    QMod B U ≃+ QMod (B.map e.toMonoidHom) (U.map e.toMonoidHom) :=
  MulEquiv.toAdditive (QuotientGroup.congr (U.subgroupOf B)
    ((U.map e.toMonoidHom).subgroupOf (B.map e.toMonoidHom)) (e.subgroupMap B)
    (map_subgroupOf_eq_mb2g e B U))

@[expose] def endConjHom_mb2g {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (ε : A ≃+ A')
    (φ : AddMonoid.End A) : AddMonoid.End A' :=
  show A' →+ A' from
    { toFun := fun x => ε (φ (ε.symm x))
      map_zero' := by simp
      map_add' := fun x y => by simp }

theorem endConjHom_apply_mb2g {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (ε : A ≃+ A')
    (φ : AddMonoid.End A) (x : A') : endConjHom_mb2g ε φ x = ε (φ (ε.symm x)) :=
  rfl

@[expose] def endConj_mb2g {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (ε : A ≃+ A') :
    AddMonoid.End A ≃+* AddMonoid.End A' where
  toFun := endConjHom_mb2g ε
  invFun := endConjHom_mb2g ε.symm
  left_inv φ := AddMonoid.End.ext _ fun x => by simp [endConjHom_apply_mb2g]
  right_inv ψ := AddMonoid.End.ext _ fun x => by simp [endConjHom_apply_mb2g]
  map_mul' φ ψ := AddMonoid.End.ext _ fun x => by simp [endConjHom_apply_mb2g]
  map_add' φ ψ := AddMonoid.End.ext _ fun x => by
    show ε (φ (ε.symm x) + ψ (ε.symm x)) = ε (φ (ε.symm x)) + ε (ψ (ε.symm x))
    rw [map_add]

theorem endConj_apply_mb2g {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (ε : A ≃+ A')
    (γ : AddMonoid.End A) (x : A') : endConj_mb2g ε γ x = ε (γ (ε.symm x)) :=
  rfl

theorem induces_endConj_mb2g (e : V ≃* W) (B U : Subgroup V) (γ : AddMonoid.End (QMod B U))
    (g : MulAut V) :
    Induces γ ⇑g ↔
      Induces (endConj_mb2g (qmodEquiv_mb2g e B U) γ) ⇑(CFSG.Quasithin.H.congrHom e g) := by
  constructor
  · intro h ⟨x, hx⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b', hb', hγ⟩ := h ⟨b, hb⟩
    refine ⟨⟨e b', Subgroup.mem_map_of_mem _ b'.2⟩, ?_, ?_⟩
    · show e b' = CFSG.Quasithin.H.congrHom e g (e b)
      rw [CFSG.Quasithin.H.congrHom_apply, e.symm_apply_apply]
      exact congrArg e hb'
    · have h1 : QMod.mk (B.map e.toMonoidHom) (U.map e.toMonoidHom) ⟨e.toMonoidHom b, hx⟩ =
          qmodEquiv_mb2g e B U (QMod.mk B U ⟨b, hb⟩) := rfl
      rw [h1, endConj_apply_mb2g, AddEquiv.symm_apply_apply, hγ]
      rfl
  · intro h b
    obtain ⟨⟨c, hc⟩, hc1, hc2⟩ := h ⟨e b, Subgroup.mem_map_of_mem _ b.2⟩
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hc
    refine ⟨⟨b', hb'⟩, ?_, ?_⟩
    · apply e.injective
      have h1 : e b' = CFSG.Quasithin.H.congrHom e g (e b) := hc1
      rw [CFSG.Quasithin.H.congrHom_apply, e.symm_apply_apply] at h1
      exact h1
    · apply (qmodEquiv_mb2g e B U).injective
      have h3 : (qmodEquiv_mb2g e B U).symm
          (QMod.mk (B.map e.toMonoidHom) (U.map e.toMonoidHom)
            ⟨e b, Subgroup.mem_map_of_mem _ b.2⟩) = QMod.mk B U b :=
        (qmodEquiv_mb2g e B U).symm_apply_eq.mpr rfl
      rw [endConj_apply_mb2g, h3] at hc2
      exact hc2

theorem indSet_map_mb2g (e : V ≃* W) (B U : Subgroup V) (S : Set (MulAut V)) :
    indSet (B.map e.toMonoidHom) (U.map e.toMonoidHom) (⇑(CFSG.Quasithin.H.congrHom e) '' S) =
      endConj_mb2g (qmodEquiv_mb2g e B U) '' indSet B U S := by
  ext γ'
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, h⟩
    refine ⟨(endConj_mb2g (qmodEquiv_mb2g e B U)).symm γ', ⟨g, hg, ?_⟩,
      RingEquiv.apply_symm_apply _ γ'⟩
    rw [induces_endConj_mb2g e B U, RingEquiv.apply_symm_apply]
    exact h
  · rintro ⟨γ, ⟨g, hg, h⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, (induces_endConj_mb2g e B U γ g).mp h⟩

theorem commutant_equiv_map (e : V ≃* W) (B U : Subgroup V) (S : Set (MulAut V)) :
    Nonempty (↥(commutant B U S) ≃+*
      ↥(commutant (B.map e.toMonoidHom) (U.map e.toMonoidHom)
        (⇑(CFSG.Quasithin.H.congrHom e) '' S))) := by
  refine ⟨RingEquiv.restrict (endConj_mb2g (qmodEquiv_mb2g e B U)) _ _ fun φ => ?_⟩
  rw [mem_commutant_iff, mem_commutant_iff, indSet_map_mb2g]
  constructor
  · intro hφ γ' ⟨γ, hγ, hγγ'⟩
    subst hγγ'
    rw [← map_mul, ← map_mul, hφ γ hγ]
  · intro hφ γ hγ
    apply (endConj_mb2g (qmodEquiv_mb2g e B U)).injective
    rw [map_mul, map_mul]
    exact hφ _ ⟨γ, hγ, rfl⟩

theorem commutant_equiv_map_subgroup (e : V ≃* W) (B U : Subgroup V)
    (K : Subgroup (MulAut V)) :
    Nonempty (↥(commutant B U (K : Set (MulAut V))) ≃+*
      ↥(commutant (B.map e.toMonoidHom) (U.map e.toMonoidHom)
        ((K.map (CFSG.Quasithin.H.congrHom e) : Subgroup (MulAut W)) : Set (MulAut W)))) := by
  rw [Subgroup.coe_map]
  exact commutant_equiv_map e B U _

end Transport

section Rings

private theorem add_self_eq_zero_mb2g {R : Type*} [Ring R] (h2 : (2 : R) = 0) (x : R) :
    x + x = 0 := by
  rw [← two_mul, h2, zero_mul]

theorem ring_iso_field4 {R : Type} [Ring R] [Finite R] [Nontrivial R] (h2 : (2 : R) = 0) (A : R)
    (hA : A * A + A + 1 = 0) (hcard : Nat.card R ≤ 4) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧ Nonempty (R ≃+* K) := by
  have h11 : (1 : R) + 1 = 0 := add_self_eq_zero_mb2g h2 1
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp at hA
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [mul_one, h11, zero_add] at hA
    exact one_ne_zero hA
  have hAA : A * A + A = 1 := by
    calc A * A + A = A * A + A + 1 + 1 := by rw [add_assoc _ 1 1, h11, add_zero]
      _ = 1 := by rw [hA, zero_add]
  have h01 : (0 : R) ≠ 1 := zero_ne_one
  have h0A : (0 : R) ≠ A := hA0.symm
  have h0A1 : (0 : R) ≠ A + 1 := by
    intro h
    apply hA1
    calc A = A + (1 + 1) := by rw [h11, add_zero]
      _ = (A + 1) + 1 := by rw [add_assoc]
      _ = 1 := by rw [← h, zero_add]
  have h1A : (1 : R) ≠ A := hA1.symm
  have h1A1 : (1 : R) ≠ A + 1 := by
    intro h
    apply hA0
    have := congrArg (· + 1) h.symm
    simpa using this
  have hAA1 : A ≠ A + 1 := by
    intro h
    have : (0 : R) = 1 := by
      have := congrArg (fun x => x - A) h
      simpa using this
    exact h01 this
  have hinj : Function.Injective (![0, 1, A, A + 1] : Fin 4 → R) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [h01, h01.symm, h0A, h0A.symm, h0A1, h0A1.symm, h1A, h1A.symm, h1A1, h1A1.symm, hAA1,
        hAA1.symm] at hij ⊢
  have hbij : Function.Bijective (![0, 1, A, A + 1] : Fin 4 → R) :=
    hinj.bijective_of_nat_card_le (by simpa using hcard)
  have hall : ∀ x : R, x = 0 ∨ x = 1 ∨ x = A ∨ x = A + 1 := by
    intro x
    obtain ⟨i, rfl⟩ := hbij.2 x
    fin_cases i <;> simp
  have hcomm : ∀ x y : R, x * y = y * x := by
    intro x y
    rcases hall x with rfl | rfl | rfl | rfl <;> rcases hall y with rfl | rfl | rfl | rfl <;>
      simp [mul_add, add_mul]
  have hfield : IsField R :=
    { exists_pair_ne := ⟨0, 1, h01⟩
      mul_comm := hcomm
      mul_inv_cancel := by
        intro a ha
        rcases hall a with h | h | h | h
        · exact absurd h ha
        · exact ⟨1, by rw [h, one_mul]⟩
        · exact ⟨A + 1, by rw [h, mul_add, mul_one, hAA]⟩
        · exact ⟨A, by rw [h, add_mul, one_mul, hAA]⟩ }
  refine ⟨R, hfield.toField, inferInstance, ?_, ⟨RingEquiv.refl R⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

theorem ring_iso_zmod2 {R : Type} [Ring R] [Finite R] [Nontrivial R] (hcard : Nat.card R ≤ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧ Nonempty (R ≃+* K) := by
  have : Fintype R := Fintype.ofFinite R
  have h2 : Fintype.card R = 2 := by
    have h1 : 1 < Nat.card R := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [← Nat.card_eq_fintype_card]
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨(ZMod.ringEquivOfPrime R Nat.prime_two h2).symm⟩⟩

theorem ring_iso_matrix2 {R : Type} [Ring R] [Finite R] [Nontrivial R] (h2 : (2 : R) = 0)
    (e : Fin 2 → Fin 2 → R) (he : ∀ i j k l, e i j * e k l = if j = k then e i l else 0)
    (hsum : e 0 0 + e 1 1 = 1) (hcard : Nat.card R ≤ 16) :
    Nonempty (R ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  haveI : CharP R 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let ι : ZMod 2 →+* R := ZMod.castHom (dvd_refl 2) R
  have hι : ∀ (a : ZMod 2) (x : R), ι a * x = x * ι a := by
    intro a x
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
    rw [map_natCast]
    exact (Nat.cast_commute n x).eq
  have hmm : ∀ (a b : ZMod 2) (x y : R), ι a * x * (ι b * y) = ι a * ι b * (x * y) := by
    intro a b x y
    calc ι a * x * (ι b * y) = ι a * (x * ι b) * y := by simp only [mul_assoc]
      _ = ι a * (ι b * x) * y := by rw [hι b x]
      _ = ι a * ι b * (x * y) := by simp only [mul_assoc]
  let Φ : Matrix (Fin 2) (Fin 2) (ZMod 2) →+* R :=
    { toFun := fun M => ∑ i, ∑ j, ι (M i j) * e i j
      map_one' := by
        simp [Fin.sum_univ_two, Matrix.one_apply, hsum]
      map_mul' := by
        intro M N
        simp only [Fin.sum_univ_two, Matrix.mul_apply, map_add, map_mul, add_mul, mul_add, hmm, he]
        simp
        abel
      map_zero' := by simp
      map_add' := by
        intro M N
        simp [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib] }
  have hinj : Function.Injective Φ := RingHom.injective Φ
  have hcardM : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = 16 := by
    simp [Matrix]
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le (by rw [hcardM]; exact hcard)
  exact ⟨(RingEquiv.ofBijective Φ hbij).symm⟩

end Rings

end CFSG.Quasithin.H13.Mat
