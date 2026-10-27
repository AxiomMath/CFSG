module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

@[expose] def lineSet {X : Type*} [Group X] (P : Subgroup X) (Φ : Subgroup X → Prop) :
    Set (Subgroup X) :=
  {Q | Q ≤ P ∧ Nat.card Q = 5 ∧ Φ Q}

@[expose] def OddLines {X : Type*} [Group X] (P : Subgroup X) : Prop :=
  ∃ Φ : Subgroup X → Prop,
    (∀ α : X ≃* X, P.map α.toMonoidHom = P → ∀ Q : Subgroup X, Φ Q → Φ (Q.map α.toMonoidHom)) ∧
    Odd (lineSet P Φ).ncard

@[expose] def E25OddLines (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, Nat.card P = 25 → (∀ x ∈ P, x ^ 5 = 1) → OddLines P

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
    (h : OddLines P) : OddLines (P.map φ.toMonoidHom) := by
  obtain ⟨Φ, hΦ, hodd⟩ := h
  refine ⟨fun Q' => Φ (Q'.map φ.symm.toMonoidHom), fun α hα Q' hQ' => ?_, ?_⟩
  ·
    have hβ : P.map (φ.trans (α.trans φ.symm)).toMonoidHom = P := by
      rw [map_map_conj, hα, map_map_symm']
    have hQ'' : Φ (Q'.map φ.symm.toMonoidHom) := hQ'
    have := hΦ (φ.trans (α.trans φ.symm)) hβ _ hQ''
    show Φ ((Q'.map α.toMonoidHom).map φ.symm.toMonoidHom)
    rw [map_map_symm_conj]
    exact this
  · have hset : lineSet (P.map φ.toMonoidHom) (fun Q' => Φ (Q'.map φ.symm.toMonoidHom)) =
        Subgroup.map φ.toMonoidHom '' lineSet P Φ := by
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
    {P' : Subgroup Y} (hP : P.map φ.toMonoidHom = P') (h : OddLines P') : OddLines P := by
  have := h.map φ.symm
  rwa [← hP, map_map_symm'] at this

theorem E25OddLines.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : E25OddLines Y) : E25OddLines X := by
  intro P hP hexp
  refine OddLines.of_map_eq e rfl (h (P.map e.toMonoidHom) ?_ ?_)
  · rw [← hP]
    exact Nat.card_congr (P.equivMapOfInjective _ e.injective).toEquiv.symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

section Fixed

variable {X : Type*} [Group X] {N : Type*} [Group N]

theorem exists_fixed_line (hN : IsPGroup 2 N) (ρ : N →* MulAut X) {P : Subgroup X}
    (hP : ∀ n, P.map (ρ n).toMonoidHom = P) (h : OddLines P) :
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q = 5 ∧ ∀ n, Q.map (ρ n).toMonoidHom = Q := by
  obtain ⟨Φ, hΦ, hodd⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (Subgroup X) := lineSet P Φ with hSdef
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

section Config

variable {A : Type} [Group A]

theorem map_conjNormal_subgroupOf' {L B : Subgroup A} [L.Normal] {t : A}
    (ht : t ∈ Subgroup.normalizer (B : Set A)) :
    (B.subgroupOf L).map (MulAut.conjNormal t).toMonoidHom = B.subgroupOf L := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h : (((MulAut.conjNormal t).symm x : L) : A) = t⁻¹ * x * t := by
    have : (MulAut.conjNormal t).symm x = MulAut.conjNormal t⁻¹ x := by
      rw [map_inv]
      rfl
    rw [this, MulAut.conjNormal_apply, inv_inv]
  rw [h]
  exact ((Subgroup.mem_normalizer_iff''.1 ht) x).symm

theorem noE25Config_of_oddLines {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → E25OddLines X) : NoE25Config F := by
  intro A _ _ L P T hL hcfg
  have hLn := hcfg.normal
  have hPL := hcfg.le
  have hP' : Nat.card (P.subgroupOf L) = 25 := by
    rw [← hcfg.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hodd := hF L hL (P.subgroupOf L) hP'
    (fun x hx => Subtype.ext (by simpa using hcfg.exp x (Subgroup.mem_subgroupOf.mp hx)))
  set N : Subgroup A := T ⊓ Subgroup.normalizer (P : Set A) with hNdef
  have hN2 : IsPGroup 2 N := hcfg.sylow.2.1.to_le inf_le_left
  let ρ : N →* MulAut L := (MulAut.conjNormal : A →* MulAut L).comp N.subtype
  obtain ⟨Q', hQ'P, hQ'5, hQ'⟩ := exists_fixed_line hN2 ρ
    (fun n => map_conjNormal_subgroupOf' n.2.2) hodd
  set Q := Q'.map L.subtype with hQdef
  have hQP : Q ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ'P hx)
  have hQ5 : Nat.card Q = 5 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQ'5]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (Q : Set A) := by
    rintro t ht
    have hα : Q'.map (MulAut.conjNormal t : MulAut L).toMonoidHom = Q' := hQ' ⟨t, ht⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : MulAut.conjNormal t x ∈ Q' := by
        rw [← hα]
        exact ⟨x, hx, rfl⟩
      exact ⟨_, hx', by simp [MulAut.conjNormal_apply]⟩
    · rintro ⟨y, hy, hyg⟩
      have hyg' : (y : A) = t * g * t⁻¹ := hyg
      have hgL : g ∈ L := by
        have := hLn.conj_mem _ y.2 t⁻¹
        rwa [hyg', show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at this
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      rw [← hα] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hxg : x = ⟨g, hgL⟩ := by
        apply Subtype.ext
        have h1 : t * (x : A) * t⁻¹ = (y : A) := by
          rw [← MulAut.conjNormal_apply]
          exact congrArg Subtype.val hxy
        rw [hyg'] at h1
        simpa using h1
      rw [← hxg]
      exact hx
  rcases hcfg.irred Q hQP hnorm with h | h
  · rw [h, Subgroup.card_bot] at hQ5
    omega
  · rw [h, hcfg.card] at hQ5
    omega

end Config

end FiveOdd

end CFSG.Quasithin.S146zY
