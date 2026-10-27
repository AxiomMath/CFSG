module

public import CFSG.Quasithin.Recognition.GoldschmidtGluing

public section

namespace CFSG.Quasithin

namespace GoldAmalgam

@[expose] def ofSubgroups {A B : Type*} [Group A] [Group B] (P : Subgroup A) (Q : Subgroup B)
    (e : P ≃* Q) : GoldAmalgam A P B :=
  ⟨P.subtype, Q.subtype.comp e.toMonoidHom, P.subtype_injective,
    Q.subtype_injective.comp e.injective⟩

theorem ofSubgroups_trans_eq_glue {A B : Type*} [Group A] [Group B] (P : Subgroup A)
    (Q : Subgroup B) (e₀ : P ≃* Q) (θ : MulAut P) :
    ofSubgroups P Q (θ.trans e₀) =
      glue P.subtype (Q.subtype.comp e₀.toMonoidHom) P.subtype_injective
        (Q.subtype_injective.comp e₀.injective) θ := rfl

@[expose] def searchOutput {A B : Type*} [Group A] [Group B] (P : Subgroup A) (Q : Subgroup B)
    (e₀ : P ≃* Q) : Set (MulAut P) :=
  {θ | (ofSubgroups P Q (θ.trans e₀)).IsFaithful}

section Orders

variable {A C B : Type*} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem card_edgeA_eq : Nat.card X.edgeA = Nat.card C :=
  Nat.card_congr (MonoidHom.ofInjective X.toA_injective).toEquiv.symm

theorem card_edgeB_eq : Nat.card X.edgeB = Nat.card C :=
  Nat.card_congr (MonoidHom.ofInjective X.toB_injective).toEquiv.symm

theorem card_A_eq (hA : X.edgeA.index = 3) : Nat.card A = 3 * Nat.card C := by
  have := X.edgeA.card_mul_index
  rw [card_edgeA_eq, hA] at this
  omega

theorem card_B_eq (hB : X.edgeB.index = 3) : Nat.card B = 3 * Nat.card C := by
  have := X.edgeB.card_mul_index
  rw [card_edgeB_eq, hB] at this
  omega

section FiniteC

variable [Finite C]

theorem exists_pow_card_of_card_le_128 (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (h128 : Nat.card C ≤ 128) :
    ∃ k, k ≤ 7 ∧ Nat.card C = 2 ^ k ∧ Nat.card A = 3 * 2 ^ k ∧ Nat.card B = 3 * 2 ^ k := by
  have hC := X.isPGroup_two hf hA hB
  obtain ⟨k, hk⟩ := hC.exists_card_eq
  refine ⟨k, ?_, hk, by rw [card_A_eq X hA, hk], by rw [card_B_eq X hB, hk]⟩
  have h : 2 ^ k ≤ 2 ^ 7 := by
    rw [← hk]
    exact h128
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem exists_sylow_eq_edgeA (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) : ∃ P : Sylow 2 A, (P : Subgroup A) = X.edgeA := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := X.isPGroup_edgeA (X.isPGroup_two hf hA hB)
  exact ⟨hE.toSylow (by rw [hA]; decide), rfl⟩

theorem exists_sylow_eq_edgeB (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) : ∃ Q : Sylow 2 B, (Q : Subgroup B) = X.edgeB :=
  X.swap.exists_sylow_eq_edgeA ((X.swap_isFaithful_iff).mpr hf) hB hA

end FiniteC

end Orders

section Representation

@[expose] noncomputable def equivConjSubgroup {A C : Type*} [Group A] [Group C] (i : C →* A)
    (hi : Function.Injective i) (g : A) (P : Subgroup A)
    (hP : i.range.map (MulAut.conj g).toMonoidHom = P) : C ≃* P :=
  ((MonoidHom.ofInjective hi).trans (MulEquiv.subgroupMap (MulAut.conj g) i.range)).trans
    (MulEquiv.subgroupCongr hP)

theorem coe_equivConjSubgroup {A C : Type*} [Group A] [Group C] (i : C →* A)
    (hi : Function.Injective i) (g : A) (P : Subgroup A)
    (hP : i.range.map (MulAut.conj g).toMonoidHom = P) (c : C) :
    ((equivConjSubgroup i hi g P hP c : P) : A) = g * i c * g⁻¹ := rfl

theorem map_conj_range_eq_of_smul_eq {A C : Type*} [Group A] [Group C] (i : C →* A)
    (S P : Sylow 2 A) (g : A) (hg : g • S = P) (hS : (S : Subgroup A) = i.range) :
    i.range.map (MulAut.conj g).toMonoidHom = P := by
  rw [← hS, ← hg, Sylow.coe_subgroup_smul]
  rfl

variable {A C B : Type*} [Group A] [Group C] [Group B] [Finite A] [Finite C] [Finite B]
  (X : GoldAmalgam A C B)

theorem exists_isIso_ofSubgroups (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (P : Sylow 2 A) (Q : Sylow 2 B) :
    ∃ e : (P : Subgroup A) ≃* (Q : Subgroup B),
      X.IsIso (ofSubgroups (P : Subgroup A) (Q : Subgroup B) e) := by
  obtain ⟨SA, hSA⟩ := X.exists_sylow_eq_edgeA hf hA hB
  obtain ⟨SB, hSB⟩ := X.exists_sylow_eq_edgeB hf hA hB
  obtain ⟨gA, hgA⟩ := MulAction.exists_smul_eq A SA P
  obtain ⟨gB, hgB⟩ := MulAction.exists_smul_eq B SB Q
  have hPA : X.toA.range.map (MulAut.conj gA).toMonoidHom = P :=
    map_conj_range_eq_of_smul_eq X.toA SA P gA hgA hSA
  have hQB : X.toB.range.map (MulAut.conj gB).toMonoidHom = Q :=
    map_conj_range_eq_of_smul_eq X.toB SB Q gB hgB hSB
  let eCA := equivConjSubgroup X.toA X.toA_injective gA P hPA
  let eCB := equivConjSubgroup X.toB X.toB_injective gB Q hQB
  refine ⟨eCA.symm.trans eCB, ⟨MulAut.conj gA, eCA, MulAut.conj gB, fun c => rfl, fun c => ?_⟩⟩
  show MulAut.conj gB (X.toB c) = ((eCA.symm.trans eCB) (eCA c) : B)
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem exists_mem_searchOutput (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (P : Sylow 2 A) (Q : Sylow 2 B)
    (e₀ : (P : Subgroup A) ≃* (Q : Subgroup B)) :
    ∃ θ ∈ searchOutput (P : Subgroup A) (Q : Subgroup B) e₀,
      X.IsIso (ofSubgroups (P : Subgroup A) (Q : Subgroup B) (θ.trans e₀)) := by
  obtain ⟨e, he⟩ := X.exists_isIso_ofSubgroups hf hA hB P Q
  have hee : (e.trans e₀.symm).trans e₀ = e := by
    ext x
    simp
  refine ⟨e.trans e₀.symm, ?_, ?_⟩
  · show (ofSubgroups (P : Subgroup A) (Q : Subgroup B) ((e.trans e₀.symm).trans e₀)).IsFaithful
    rw [hee]
    exact he.isFaithful hf
  · rw [hee]
    exact he

end Representation

theorem isFaithful_of_mem_searchOutput {A B : Type*} [Group A] [Group B] {P : Subgroup A}
    {Q : Subgroup B} {e₀ : P ≃* Q} {θ : MulAut P} (h : θ ∈ searchOutput P Q e₀) :
    (ofSubgroups P Q (θ.trans e₀)).IsFaithful := h

theorem sylow_index_eq_three_of_card {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (k : ℕ)
    (hG : Nat.card G = 3 * 2 ^ k) : (S : Subgroup G).index = 3 := by
  have h3 : (3 * 2 ^ k).factorization 2 = k := by
    rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  have hpos : 0 < 2 ^ k := by positivity
  have h1 := Sylow.card_eq_multiplicity S
  have h2 := (S : Subgroup G).card_mul_index
  rw [hG, h3] at h1
  rw [h1, hG] at h2
  have : 2 ^ k * (S : Subgroup G).index = 2 ^ k * 3 := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

section Soundness

variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

theorem ofSubgroups_isIndexThree (P : Sylow 2 A) (Q : Sylow 2 B)
    (e : (P : Subgroup A) ≃* (Q : Subgroup B))
    (k : ℕ) (hkA : Nat.card A = 3 * 2 ^ k) (hkB : Nat.card B = 3 * 2 ^ k) :
    (ofSubgroups (P : Subgroup A) (Q : Subgroup B) e).IsIndexThree := by
  refine ⟨?_, ?_⟩
  · have : (ofSubgroups (P : Subgroup A) (Q : Subgroup B) e).edgeA = P := by
      ext x
      simp [edgeA, ofSubgroups]
    rw [this]
    exact sylow_index_eq_three_of_card P k hkA
  · have : (ofSubgroups (P : Subgroup A) (Q : Subgroup B) e).edgeB = Q := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact (e c).2
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp [ofSubgroups]⟩
    rw [this]
    exact sylow_index_eq_three_of_card Q k hkB

end Soundness

section Closure

variable {A B : Type*} [Group A] [Group B]

theorem mem_searchOutput_of_mem_doubleCoset {P : Subgroup A} {Q : Subgroup B} {e₀ : P ≃* Q}
    {θ θ' : MulAut P} (hθ : θ ∈ searchOutput P Q e₀)
    (h : θ' ∈ DoubleCoset.doubleCoset θ
      (inducedAut (Q.subtype.comp e₀.toMonoidHom) : Set (MulAut P))
      (inducedAut P.subtype : Set (MulAut P))) :
    θ' ∈ searchOutput P Q e₀ := by
  have hiso := (isIso_glue_iff P.subtype_injective
    (Q.subtype_injective.comp e₀.injective) θ θ').mpr h
  exact hiso.isFaithful hθ

end Closure

theorem finite_isoClasses_of_card (n : ℕ) :
    ∃ S : Set (Subgroup (Equiv.Perm (Fin n))), S.Finite ∧
      ∀ (G : Type*) [Group G] [Finite G], Nat.card G = n → ∃ H ∈ S, Nonempty (G ≃* H) := by
  refine ⟨Set.univ, Set.finite_univ, ?_⟩
  intro G _ _ hG
  let e : G ≃ Fin n := Finite.equivFinOfCardEq hG
  let ι : G →* Equiv.Perm (Fin n) :=
    (e.permCongrHom : Equiv.Perm G →* Equiv.Perm (Fin n)).comp (MulAction.toPermHom G G)
  have hι : Function.Injective ι := by
    have h1 : Function.Injective (MulAction.toPermHom G G) := MulAction.toPerm_injective
    exact e.permCongrHom.injective.comp h1
  exact ⟨ι.range, Set.mem_univ _, ⟨MonoidHom.ofInjective hι⟩⟩

section Headline

variable {A C B : Type*} [Group A] [Group C] [Group B] [Finite A] [Finite C] [Finite B]
  (X : GoldAmalgam A C B)

theorem edge_le_128_search (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3)
    (h128 : Nat.card C ≤ 128) :
    (∃ k, k ≤ 7 ∧ Nat.card C = 2 ^ k ∧ Nat.card A = 3 * 2 ^ k ∧ Nat.card B = 3 * 2 ^ k) ∧
    (∃ P : Sylow 2 A, (P : Subgroup A) = X.edgeA) ∧
    (∃ Q : Sylow 2 B, (Q : Subgroup B) = X.edgeB) ∧
    ∀ (P : Sylow 2 A) (Q : Sylow 2 B) (e₀ : (P : Subgroup A) ≃* (Q : Subgroup B)),
      ∃ θ ∈ searchOutput (P : Subgroup A) (Q : Subgroup B) e₀,
        X.IsIso (ofSubgroups (P : Subgroup A) (Q : Subgroup B) (θ.trans e₀)) :=
  ⟨X.exists_pow_card_of_card_le_128 hf hA hB h128, X.exists_sylow_eq_edgeA hf hA hB,
    X.exists_sylow_eq_edgeB hf hA hB, fun P Q e₀ => X.exists_mem_searchOutput hf hA hB P Q e₀⟩

end Headline

end GoldAmalgam

end CFSG.Quasithin
