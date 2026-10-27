module

public import CFSG.Quasithin.Vol2.Ch11SecO11C
public import CFSG.Quasithin.Vol2.Ch11SecO11E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint QuasithinUnique

variable {Q : Type} [Group Q]

@[expose] def NoE9Pair (S : Subgroup Q) : Prop :=
  ∀ B₁ B₂ E : Subgroup Q, IsL24Sub S B₁ → IsL24Sub S B₂ → B₁ ≠ B₂ → Nat.card E = 9 →
    E ≤ Subgroup.normalizer (B₁ : Set Q) → E ≤ Subgroup.normalizer (B₂ : Set Q) → False

theorem L24Unique.noE9Pair {S : Subgroup Q} (h : L24Unique S) : NoE9Pair S :=
  fun _ _ _ h₁ h₂ hne _ _ _ => hne (h _ _ h₁ h₂)

theorem NoE9Pair.map_equiv {Q' : Type} [Group Q'] [Finite Q] {S : Subgroup Q} (h : NoE9Pair S)
    (e : Q ≃* Q') : NoE9Pair (S.map e.toMonoidHom) := by
  intro B₁ B₂ E h₁ h₂ hne hE hE₁ hE₂
  have := Finite.of_equiv Q e.toEquiv
  have hinj : ∀ B : Subgroup Q', Function.Injective (e.symm.toMonoidHom.comp B.subtype) :=
    fun B => e.symm.injective.comp B.subtype_injective
  have hS : (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id S
    ext
    simp
  have h₁' := IsL24Sub.map h₁ e.symm.toMonoidHom (hinj B₁)
  have h₂' := IsL24Sub.map h₂ e.symm.toMonoidHom (hinj B₂)
  rw [hS] at h₁' h₂'
  refine h _ _ (E.map e.symm.toMonoidHom) h₁' h₂'
    (fun h' => hne (Subgroup.map_injective e.symm.injective h'))
    ((Subgroup.card_map_of_injective e.symm.injective).trans hE)
    ((Subgroup.map_mono hE₁).trans (Subgroup.le_normalizer_map _))
    ((Subgroup.map_mono hE₂).trans (Subgroup.le_normalizer_map _))

theorem noE9Pair_of_sylow [Finite Q] {S₀ : Subgroup Q} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (h : NoE9Pair S₀) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) : NoE9Pair S := by
  obtain ⟨g, rfl⟩ := exists_conj_of_sylow hS₀ hS
  exact h.map_equiv (MulAut.conj g)

theorem isSylowTwoOf_map_equiv {Q' : Type} [Group Q'] (e : Q ≃* Q') {S : Subgroup Q}
    (h : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ :=
  isSylowTwoOf_top_map_of_surjective h e.toMonoidHom e.surjective

theorem l24Unique_of_equiv [Finite Q] {Γ : Type} {inst : Group Γ} {S₀ : Subgroup Γ}
    (hS₀ : IsSylowTwoOf S₀ ⊤) (h : L24Unique S₀) (hQ : Nonempty (Q ≃* Γ)) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : L24Unique S := by
  obtain ⟨e⟩ := hQ
  have := Finite.of_equiv Q e.toEquiv
  exact l24Unique_of_sylow (isSylowTwoOf_map_equiv e.symm hS₀) (h.map_equiv e.symm) hS

theorem noE9Pair_of_equiv [Finite Q] {Γ : Type} {inst : Group Γ} {S₀ : Subgroup Γ}
    (hS₀ : IsSylowTwoOf S₀ ⊤) (h : NoE9Pair S₀) (hQ : Nonempty (Q ≃* Γ)) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : NoE9Pair S := by
  obtain ⟨e⟩ := hQ
  have := Finite.of_equiv Q e.toEquiv
  exact noE9Pair_of_sylow (isSylowTwoOf_map_equiv e.symm hS₀) (h.map_equiv e.symm) hS

open CFSG.QuasithinUnique.L246A7 in
theorem isSylowTwoOf_pstdA : IsSylowTwoOf PstdA ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_PstdA]; norm_num), ?_⟩
  have h1 : (PstdA.subgroupOf (⊤ : Subgroup G7)).index = PstdA.index :=
    Subgroup.relIndex_top_right _
  have h := Subgroup.index_mul_card PstdA
  rw [card_PstdA, card_alt7] at h
  have h2 : PstdA.index = 315 := by omega
  rw [h1, h2]
  decide

open CFSG.QuasithinUnique.L246A7 in
theorem card_sup_pstdA {B : Subgroup G7} (hB : IsL24Sub PstdA B) : Nat.card ↥(B ⊔ PstdA) = 120 := by
  obtain ⟨m, hm⟩ := card_sup isSylowTwoOf_pstdA.2.1 hB
  have h8 : 8 ∣ 15 * 2 ^ m := by
    rw [← hm, ← card_PstdA]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h2520 : 15 * 2 ^ m ∣ 2520 := by
    rw [← hm, ← card_alt7]
    exact Subgroup.card_subgroup_dvd_card _
  have hm3 : m ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 15 * 2 ^ m := Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega)) 15
    have := h16.trans h2520
    norm_num at this
  rw [hm]
  interval_cases m <;> simp_all

theorem l24Unique_pstdA : L24Unique PstdA := fun _ _ h₁ h₂ =>
  eq_of_sup_eq isSylowTwoOf_pstdA.2.1 h₁ h₂
    (eq_of_card_eq_120 le_sup_right le_sup_right (card_sup_pstdA h₁) (card_sup_pstdA h₂))

theorem l24Unique_alt7 [Finite Q] (hQ : IsAlt 7 Q) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) :
    L24Unique S := by
  exact l24Unique_of_equiv isSylowTwoOf_pstdA l24Unique_pstdA hQ hS

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
