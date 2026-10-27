module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section General

variable {G : Type*} [Group G]

theorem mem_pCoreOf_iff_pCore (L : Subgroup G) (x : ↥L) :
    (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.Open.pCore 2 ↥L := by
  unfold pCoreOf
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem charTwo_top_of_charTwo (L : Subgroup G) (h : CharTwo L) : CharTwo (⊤ : Subgroup ↥L) := by
  intro x hx
  rw [CFSG.Quasithin.pCoreOf_top]
  have hxc : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    intro y hy
    have hy' : (⟨y, pCoreOf_le 2 L hy⟩ : ↥L) ∈ CFSG.Open.pCore 2 ↥L :=
      (mem_pCoreOf_iff_pCore L ⟨y, pCoreOf_le 2 L hy⟩).1 hy
    have hxc' := hx.2
    rw [CFSG.Quasithin.pCoreOf_top] at hxc'
    have := Subgroup.mem_centralizer_iff.mp hxc' _ hy'
    exact congrArg Subtype.val this
  exact (mem_pCoreOf_iff_pCore L x).1 (h ⟨x.2, hxc⟩)

end General

section Hyp

variable {G : Type} [Group G] [Finite G] {L₁ L₂ S : Subgroup G}

omit [Finite G] in
theorem faithful_ofSubgroupPair (hp : IsPGroup 2 ↥(L₁ ⊓ L₂)) (ho : pCoreOf 2 (L₁ ⊔ L₂) = ⊥) :
    (GoldAmalgam.ofSubgroupPair L₁ L₂).IsFaithful := by
  intro K hK1 hK2
  set K' : Subgroup G := K.map (L₁ ⊓ L₂).subtype with hK'
  have hmem : ∀ y : G, y ∈ K' ↔ ∃ k ∈ K, ((k : ↥(L₁ ⊓ L₂)) : G) = y := by
    intro y
    simp [hK', Subgroup.mem_map]
  have h1 : ∀ a ∈ L₁, ∀ y ∈ K', a * y * a⁻¹ ∈ K' := by
    intro a ha y hy
    obtain ⟨k, hk, rfl⟩ := (hmem y).1 hy
    have hkA : (⟨(k : G), (inf_le_left : L₁ ⊓ L₂ ≤ L₁) k.2⟩ : ↥L₁) ∈
        K.map (GoldAmalgam.ofSubgroupPair L₁ L₂).toA := ⟨k, hk, rfl⟩
    have := hK1.conj_mem _ hkA ⟨a, ha⟩
    obtain ⟨k', hk', hk'e⟩ := this
    refine (hmem _).2 ⟨k', hk', ?_⟩
    exact congrArg Subtype.val hk'e
  have h2 : ∀ a ∈ L₂, ∀ y ∈ K', a * y * a⁻¹ ∈ K' := by
    intro a ha y hy
    obtain ⟨k, hk, rfl⟩ := (hmem y).1 hy
    have hkB : (⟨(k : G), (inf_le_right : L₁ ⊓ L₂ ≤ L₂) k.2⟩ : ↥L₂) ∈
        K.map (GoldAmalgam.ofSubgroupPair L₁ L₂).toB := ⟨k, hk, rfl⟩
    have := hK2.conj_mem _ hkB ⟨a, ha⟩
    obtain ⟨k', hk', hk'e⟩ := this
    refine (hmem _).2 ⟨k', hk', ?_⟩
    exact congrArg Subtype.val hk'e
  have hle : K' ≤ L₁ ⊔ L₂ := fun y hy => by
    obtain ⟨k, -, rfl⟩ := (hmem y).1 hy
    exact Subgroup.mem_sup_left ((inf_le_left : L₁ ⊓ L₂ ≤ L₁) k.2)
  have hnorm : L₁ ⊔ L₂ ≤ Subgroup.normalizer (K' : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => h1 a ha y hy, fun hy => ?_⟩
      have := h1 a⁻¹ (inv_mem ha) _ hy
      simpa [mul_assoc] using this
    · refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => h2 a ha y hy, fun hy => ?_⟩
      have := h2 a⁻¹ (inv_mem ha) _ hy
      simpa [mul_assoc] using this
  have hpK : IsPGroup 2 K' := by
    have : K' ≤ L₁ ⊓ L₂ := fun y hy => by
      obtain ⟨k, -, rfl⟩ := (hmem y).1 hy
      exact k.2
    exact hp.to_le this
  have hbot := le_pCoreOf_of_le_normalizer 2 hle hnorm hpK
  rw [ho] at hbot
  refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => ?_
  have hk' : (k : G) ∈ K' := (hmem _).2 ⟨k, hk, rfl⟩
  have : (k : G) ∈ (⊥ : Subgroup G) := hbot hk'
  exact Subtype.ext (by simpa using this)

omit [Finite G] in
theorem card_quot_left
    (hQ : Nonempty (oTwoQuot ↥L₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L₁ ≃* ↥(Sz 0))) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card (OTwoQuot L₁) = 2 ^ k * 5 := by
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨1, le_rfl, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    norm_num
  · refine ⟨2, by norm_num, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.card_sz_zero]
    norm_num

omit [Finite G] in
theorem card_quot_right (hQ : IsL2Quot 1 (oTwoQuot ↥L₂)) :
    Nat.card (OTwoQuot L₂) = 2 ^ 1 * 3 := by
  obtain ⟨e⟩ := isL2Quot_one_iff_perm3.mp hQ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

theorem relIndex_left (h : Hyp111 L₁ L₂ S) (hS1 : S ≤ L₁) (hinf : L₁ ⊓ L₂ = S)
    (hQ : Nonempty (oTwoQuot ↥L₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L₁ ≃* ↥(Sz 0))) :
    (L₁ ⊓ L₂).relIndex L₁ = 5 := by
  obtain ⟨k, -, hk⟩ := card_quot_left hQ
  have hsyl : IsSylowTwoOf S L₁ := by
    have := h.h1.sylow
    rwa [inf_eq_left.mpr hS1] at this
  have := index_sylow_eq_of_card_quot hsyl (r := 5) (by decide) hk
  rw [hinf]
  exact this

theorem relIndex_right (h : Hyp111 L₁ L₂ S) (hS2 : S ≤ L₂) (hinf : L₁ ⊓ L₂ = S)
    (hQ : IsL2Quot 1 (oTwoQuot ↥L₂)) : (L₁ ⊓ L₂).relIndex L₂ = 3 := by
  have hsyl : IsSylowTwoOf S L₂ := by
    have := h.h2.sylow
    rwa [inf_eq_left.mpr hS2] at this
  have := index_sylow_eq_of_card_quot hsyl (r := 3) (by decide) (card_quot_right hQ)
  rw [hinf]
  exact this

theorem hyp53_of_hayashi (h : Hyp111 L₁ L₂ S) (hS1 : S ≤ L₁) (hS2 : S ≤ L₂) (hinf : L₁ ⊓ L₂ = S)
    (hN2 : L₂ ⊓ Subgroup.normalizer (S : Set G) = S)
    (hN1 : L₁ ⊓ Subgroup.normalizer (S : Set G) = S)
    (hQ1 : Nonempty (oTwoQuot ↥L₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L₁ ≃* ↥(Sz 0)))
    (hQ2 : IsL2Quot 1 (oTwoQuot ↥L₂)) :
    Hyp53 (GoldAmalgam.ofSubgroupPair L₁ L₂) := by
  have hp : IsPGroup 2 ↥(L₁ ⊓ L₂) := by
    rw [hinf]
    exact h.h1.pgroup
  have hsup : L₁ ⊔ L₂ ⊔ S = L₁ ⊔ L₂ := sup_eq_left.mpr (hS1.trans le_sup_left)
  have hct1 : CharTwo L₁ := by
    have := h.h1.charTwo
    have hb : borelOf L₂ S = S := by
      unfold borelOf
      rw [inf_eq_left.mpr hS2]
      exact hN2
    rwa [hb, sup_assoc, sup_idem, sup_eq_left.mpr hS1] at this
  have hct2 : CharTwo L₂ := by
    have := h.h2.charTwo
    have hb : borelOf L₁ S = S := by
      unfold borelOf
      rw [inf_eq_left.mpr hS1]
      exact hN1
    rwa [hb, sup_assoc, sup_idem, sup_eq_left.mpr hS2] at this
  refine ⟨inferInstance, inferInstance, faithful_ofSubgroupPair hp ?_, hp, ?_, ?_,
    charTwo_top_of_charTwo L₁ hct1, charTwo_top_of_charTwo L₂ hct2, hQ1, hQ2⟩
  · rw [← hsup]
    exact h.o2
  · rw [GoldAmalgam.ofSubgroupPair_edgeA_index]
    exact relIndex_left h hS1 hinf hQ1
  · rw [GoldAmalgam.ofSubgroupPair_edgeB_index]
    exact relIndex_right h hS2 hinf hQ2

end Hyp

end CFSG.Quasithin.Fan86
