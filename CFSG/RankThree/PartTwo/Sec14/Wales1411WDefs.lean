module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W

variable {Q : Type*} [Group Q]

theorem not_three_dvd_card_of_isPGroup [Finite Q] {U : Subgroup Q} (h : IsPGroup 2 U) :
    ¬ 3 ∣ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  rw [hn]
  intro h3
  have h32 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem le_normalizer_sup_of_le [Finite Q] {E S T : Subgroup Q}
    (hS : E ≤ Subgroup.normalizer (S : Set Q)) (hT : E ≤ Subgroup.normalizer (T : Set Q)) :
    E ≤ Subgroup.normalizer ((S ⊔ T : Subgroup Q) : Set Q) := by
  intro e he
  have hconj : ∀ U : Subgroup Q, e ∈ Subgroup.normalizer (U : Set Q) →
      U.map (MulAut.conj e).toMonoidHom ≤ U := by
    rintro U hU _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hU u).mp hu
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have h1 : (S ⊔ T).map (MulAut.conj e).toMonoidHom ≤ S ⊔ T := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (hconj S (hS he)) (hconj T (hT he))
  exact h1 ⟨x, hx, rfl⟩

@[expose] def InvTwo (E H U : Subgroup Q) : Prop :=
  U ≤ H ∧ E ≤ Subgroup.normalizer (U : Set Q) ∧ IsPGroup 2 U

@[expose] def ETrans (Q : Type*) [Group Q] [Finite Q] (E : Subgroup Q) : Prop :=
  ∀ H : Subgroup Q, E ≤ Subgroup.normalizer (H : Set Q) →
    H = sSup {V : Subgroup Q | V ≤ H ∧ E ≤ Subgroup.normalizer (V : Set Q) ∧
      ¬ 3 ∣ Nat.card V} →
    ∀ S T : Subgroup Q, Maximal (InvTwo E H) S → Maximal (InvTwo E H) T →
      ∃ n ∈ H ⊓ Subgroup.normalizer (E : Set Q), T = S.map (MulAut.conj n).toMonoidHom

section Transport

variable {Q' : Type*} [Group Q'] (φ : Q ≃* Q')

theorem le_normalizer_map_iff {E U : Subgroup Q} :
    E.map φ.toMonoidHom ≤ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup Q') : Set Q') ↔
      E ≤ Subgroup.normalizer (U : Set Q) := by
  constructor
  · intro h x hx
    have hx' := h (Subgroup.mem_map_of_mem φ.toMonoidHom hx)
    rw [Subgroup.mem_normalizer_iff] at hx' ⊢
    intro u
    have := hx' (φ u)
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at this
    exact this
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_normalizer_iff]
    intro u'
    have hx' := Subgroup.mem_normalizer_iff.mp (h hx) (φ.symm u')
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
    simpa [map_mul, map_inv] using hx'

theorem invTwo_map_iff {E H U : Subgroup Q} :
    InvTwo (E.map φ.toMonoidHom) (H.map φ.toMonoidHom) (U.map φ.toMonoidHom) ↔ InvTwo E H U := by
  unfold InvTwo
  rw [le_normalizer_map_iff φ, Subgroup.map_le_map_iff_of_injective φ.injective]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have := h3.of_equiv ((U.equivMapOfInjective φ.toMonoidHom φ.injective).symm)
    exact this
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3.map φ.toMonoidHom⟩

theorem maximal_invTwo_map_iff {E H S : Subgroup Q} :
    Maximal (InvTwo (E.map φ.toMonoidHom) (H.map φ.toMonoidHom)) (S.map φ.toMonoidHom) ↔
      Maximal (InvTwo E H) S := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(invTwo_map_iff φ).mp h1, fun U hU hSU => ?_⟩
    have := h2 ((invTwo_map_iff φ).mpr hU)
      ((Subgroup.map_le_map_iff_of_injective φ.injective).mpr hSU)
    exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp this
  · rintro ⟨h1, h2⟩
    refine ⟨(invTwo_map_iff φ).mpr h1, fun U' hU' hSU' => ?_⟩
    have hU : U' = (U'.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
      rw [Subgroup.map_map]
      conv_lhs => rw [← Subgroup.map_id U']
      congr 1
      ext x
      simp
    rw [hU] at hU' hSU' ⊢
    rw [invTwo_map_iff φ] at hU'
    rw [Subgroup.map_le_map_iff_of_injective φ.injective] at hSU' ⊢
    exact h2 hU' hSU'

theorem ETrans.of_mulEquiv [Finite Q] [Finite Q'] {E : Subgroup Q} {E' : Subgroup Q'}
    (hE : E.map φ.toMonoidHom = E') (h : ETrans Q' E') : ETrans Q E := by
  subst hE
  intro H hEH hHgen S T hS hT
  have hH' : H.map φ.toMonoidHom = sSup {V : Subgroup Q' | V ≤ H.map φ.toMonoidHom ∧
      E.map φ.toMonoidHom ≤ Subgroup.normalizer (V : Set Q') ∧ ¬ 3 ∣ Nat.card V} := by
    apply le_antisymm
    · conv_lhs => rw [hHgen]
      rw [(Subgroup.gc_map_comap φ.toMonoidHom).l_sSup]
      refine iSup₂_le fun V hV => le_sSup ⟨Subgroup.map_mono hV.1,
        (le_normalizer_map_iff φ).mpr hV.2.1, ?_⟩
      rw [Subgroup.card_map_of_injective φ.injective]
      exact hV.2.2
    · refine sSup_le fun V hV => hV.1
  obtain ⟨n, hn, hnT⟩ := h (H.map φ.toMonoidHom) ((le_normalizer_map_iff φ).mpr hEH) hH'
    (S.map φ.toMonoidHom) (T.map φ.toMonoidHom) ((maximal_invTwo_map_iff φ).mpr hS)
    ((maximal_invTwo_map_iff φ).mpr hT)
  refine ⟨φ.symm n, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨h, hh, rfl⟩ := (Subgroup.mem_inf.mp hn).1
    simpa using hh
  · have hnE := (Subgroup.mem_inf.mp hn).2
    show φ.symm n ∈ Subgroup.normalizer (E : Set Q)
    rw [Subgroup.mem_normalizer_iff] at hnE ⊢
    intro e
    have := hnE (φ e)
    simp only [Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at this
    simpa [map_mul, map_inv] using this
  · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [hnT, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]

@[expose] def ETrans2 (Q : Type*) [Group Q] (E : Subgroup Q) : Prop :=
  ∀ S T : Subgroup Q, Maximal (InvTwo E (S ⊔ T)) S → Maximal (InvTwo E (S ⊔ T)) T →
    ∃ n ∈ (S ⊔ T) ⊓ Subgroup.normalizer (E : Set Q), T = S.map (MulAut.conj n).toMonoidHom

omit φ in
theorem ETrans.etrans2 [Finite Q] {E : Subgroup Q} (h : ETrans Q E) : ETrans2 Q E := by
  intro S T hS hT
  refine h (S ⊔ T) (le_normalizer_sup_of_le hS.prop.2.1 hT.prop.2.1) ?_ S T hS hT
  refine le_antisymm (sup_le (le_sSup ⟨le_sup_left, hS.prop.2.1, ?_⟩)
    (le_sSup ⟨le_sup_right, hT.prop.2.1, ?_⟩)) (sSup_le fun V hV => hV.1)
  · exact not_three_dvd_card_of_isPGroup hS.prop.2.2
  · exact not_three_dvd_card_of_isPGroup hT.prop.2.2

theorem ETrans2.of_mulEquiv {E : Subgroup Q} {E' : Subgroup Q'}
    (hE : E.map φ.toMonoidHom = E') (h : ETrans2 Q' E') : ETrans2 Q E := by
  subst hE
  intro S T hS hT
  have hmap : (S ⊔ T).map φ.toMonoidHom = S.map φ.toMonoidHom ⊔ T.map φ.toMonoidHom :=
    Subgroup.map_sup S T _
  have hS' := (maximal_invTwo_map_iff φ).mpr hS
  have hT' := (maximal_invTwo_map_iff φ).mpr hT
  rw [hmap] at hS' hT'
  obtain ⟨n, hn, hnT⟩ := h _ _ hS' hT'
  refine ⟨φ.symm n, ⟨?_, ?_⟩, ?_⟩
  · have hn1 := (Subgroup.mem_inf.mp hn).1
    rw [← hmap] at hn1
    obtain ⟨h, hh, rfl⟩ := hn1
    simpa using hh
  · have hnE := (Subgroup.mem_inf.mp hn).2
    show φ.symm n ∈ Subgroup.normalizer (E : Set Q)
    rw [Subgroup.mem_normalizer_iff] at hnE ⊢
    intro e
    have := hnE (φ e)
    simp only [Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at this
    simpa [map_mul, map_inv] using this
  · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [hnT, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]

end Transport

end CFSG.RankThree.PartTwo.Sec14.Wales1411W
