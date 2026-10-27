module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

section Lines

variable {X : Type*} [Group X] (p : ℕ)

@[expose] def lineSet (P : Subgroup X) (Φ : Subgroup X → Prop) : Set (Subgroup X) :=
  {Q | Q ≤ P ∧ Nat.card Q = p ∧ Φ Q}

@[expose] def OddLines (P : Subgroup X) : Prop :=
  ∃ Φ : Subgroup X → Prop,
    (∀ α : X ≃* X, P.map α.toMonoidHom = P → ∀ Q : Subgroup X, Φ Q → Φ (Q.map α.toMonoidHom)) ∧
    Odd (lineSet p P Φ).ncard

variable {p}

theorem map_map_symm' {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (K : Subgroup X) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  ext x
  simp

theorem map_symm_map' {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (K : Subgroup Y) :
    (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
  ext x
  simp

theorem map_map_conj {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (β : Y ≃* Y)
    (K : Subgroup X) :
    K.map (φ.trans (β.trans φ.symm)).toMonoidHom =
      ((K.map φ.toMonoidHom).map β.toMonoidHom).map φ.symm.toMonoidHom := by
  ext x
  simp

theorem map_map_symm_conj {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (β : Y ≃* Y)
    (Q : Subgroup Y) :
    (Q.map β.toMonoidHom).map φ.symm.toMonoidHom =
      (Q.map φ.symm.toMonoidHom).map (φ.trans (β.trans φ.symm)).toMonoidHom := by
  ext x
  simp

theorem OddLines.map {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {P : Subgroup X}
    (h : OddLines p P) : OddLines p (P.map φ.toMonoidHom) := by
  obtain ⟨Φ, hΦ, hodd⟩ := h
  refine ⟨fun Q' => Φ (Q'.map φ.symm.toMonoidHom), fun α hα Q' hQ' => ?_, ?_⟩
  · have hβ : P.map (φ.trans (α.trans φ.symm)).toMonoidHom = P := by
      rw [map_map_conj, hα, map_map_symm']
    have := hΦ (φ.trans (α.trans φ.symm)) hβ _ hQ'
    show Φ ((Q'.map α.toMonoidHom).map φ.symm.toMonoidHom)
    rw [map_map_symm_conj]
    exact this
  · have hset : lineSet p (P.map φ.toMonoidHom) (fun Q' => Φ (Q'.map φ.symm.toMonoidHom)) =
        Subgroup.map φ.toMonoidHom '' lineSet p P Φ := by
      ext Q'
      constructor
      · rintro ⟨hle, hcard, hQ⟩
        refine ⟨Q'.map φ.symm.toMonoidHom, ⟨?_, ?_, hQ⟩, map_symm_map' φ Q'⟩
        · calc Q'.map φ.symm.toMonoidHom ≤ (P.map φ.toMonoidHom).map φ.symm.toMonoidHom :=
                Subgroup.map_mono hle
            _ = P := map_map_symm' φ P
        · rw [← hcard]
          exact Nat.card_congr (Q'.equivMapOfInjective _ φ.symm.injective).toEquiv.symm
      · rintro ⟨Q, ⟨hle, hcard, hQ⟩, rfl⟩
        refine ⟨Subgroup.map_mono hle, ?_, ?_⟩
        · rw [← hcard]
          exact Nat.card_congr (Q.equivMapOfInjective _ φ.injective).toEquiv.symm
        · show Φ ((Q.map φ.toMonoidHom).map φ.symm.toMonoidHom)
          rw [map_map_symm']
          exact hQ
    rw [hset, Set.ncard_image_of_injective _ (Subgroup.map_injective φ.injective)]
    exact hodd

theorem OddLines.of_map_eq {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {P : Subgroup X}
    {P' : Subgroup Y} (hP : P.map φ.toMonoidHom = P') (h : OddLines p P') : OddLines p P := by
  have := h.map φ.symm
  rwa [← hP, map_map_symm'] at this

@[expose] def PTorusProp (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, (∀ x ∈ P, x ^ p = 1) →
    (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧ (Nat.card P = p ^ 2 → OddLines p P)

theorem PTorusProp.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : PTorusProp p Y) : PTorusProp p X := by
  intro P hexp
  obtain ⟨hab, hodd⟩ := h (P.map e.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one])
  refine ⟨fun a ha b hb => e.injective ?_, fun hP => OddLines.of_map_eq e rfl (hodd ?_)⟩
  · rw [map_mul, map_mul]
    exact hab _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  · rw [← hP]
    exact Nat.card_congr (P.equivMapOfInjective _ e.injective).toEquiv.symm

end Lines

section Fixed

variable {X : Type*} [Group X] {N : Type*} [Group N] {p : ℕ}

theorem exists_fixed_line (hN : IsPGroup 2 N) (ρ : N →* MulAut X) {P : Subgroup X}
    (hP : ∀ n, P.map (ρ n).toMonoidHom = P) (h : OddLines p P) :
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q = p ∧ ∀ n, Q.map (ρ n).toMonoidHom = Q := by
  obtain ⟨Φ, hΦ, hodd⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (Subgroup X) := lineSet p P Φ with hSdef
  have hS : ∀ n : N, ∀ Q ∈ S, Q.map (ρ n).toMonoidHom ∈ S := by
    rintro n Q ⟨hle, hcard, hQ⟩
    refine ⟨?_, ?_, hΦ (ρ n) (hP n) Q hQ⟩
    · calc Q.map (ρ n).toMonoidHom ≤ P.map (ρ n).toMonoidHom := Subgroup.map_mono hle
        _ = P := hP n
    · rw [← hcard]
      exact Nat.card_congr (Q.equivMapOfInjective _ (ρ n).injective).toEquiv.symm
  let _ : MulAction N S :=
    { smul := fun n q => ⟨q.1.map (ρ n).toMonoidHom, hS n q.1 q.2⟩
      one_smul := fun q => Subtype.ext (by
        show q.1.map (ρ 1).toMonoidHom = q.1
        ext x
        simp)
      mul_smul := fun a b q => Subtype.ext (by
        show q.1.map (ρ (a * b)).toMonoidHom =
          (q.1.map (ρ b).toMonoidHom).map (ρ a).toMonoidHom
        ext x
        simp) }
  have hnd : ¬ 2 ∣ Nat.card S := by
    rw [Nat.card_coe_set_eq]
    exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  obtain ⟨q, hq⟩ := hN.nonempty_fixed_point_of_prime_not_dvd_card S hnd
  refine ⟨q.1, q.2.1, q.2.2.1, fun n => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hq n)

end Fixed

end CFSG.Quasithin.H13.NQCore.U3O
