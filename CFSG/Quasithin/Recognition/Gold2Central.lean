module

public import CFSG.Quasithin.EmptyFaithful.S146S3
public import CFSG.Quasithin.Recognition.GoldschmidtPushingUp
public import CFSG.Quasithin.Recognition.GoldschmidtStatement
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem gold2_charTwo_iff {X : Subgroup G} :
    CharTwo X ↔
      Subgroup.centralizer (CFSG.Open.pCore 2 ↥X : Set ↥X) ≤ CFSG.Open.pCore 2 ↥X := by
  constructor
  · intro h y hy
    have hy' : (y : G) ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro g ⟨p, hp, rfl⟩
      have := (Subgroup.mem_centralizer_iff.mp hy) p hp
      have h2 := congrArg Subtype.val this
      simpa using h2
    obtain ⟨p, hp, hpy⟩ := h hy'
    have : p = y := Subtype.ext hpy
    rwa [← this]
  · intro h g hg
    have hy : (⟨g, hg.1⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.Open.pCore 2 ↥X : Set ↥X) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro p hp
      have hc := (Subgroup.mem_centralizer_iff.mp hg.2) (p : G) ⟨p, hp, rfl⟩
      exact Subtype.ext (by simpa using hc)
    exact ⟨⟨g, hg.1⟩, h hy, rfl⟩

omit [Finite G] in
theorem gold2_conj_mem_of_normal_map {H C : Subgroup G} {K : Subgroup ↥C} (hCH : C ≤ H)
    (hN : (K.map (Subgroup.inclusion hCH)).Normal) {g h : G} (hg : g ∈ H)
    (hh : h ∈ K.map C.subtype) : g * h * g⁻¹ ∈ K.map C.subtype := by
  obtain ⟨k, hk, rfl⟩ := hh
  have hmem : Subgroup.inclusion hCH k ∈ K.map (Subgroup.inclusion hCH) := ⟨k, hk, rfl⟩
  obtain ⟨k₁, hk₁, hk₁eq⟩ := hN.conj_mem _ hmem ⟨g, hg⟩
  refine ⟨k₁, hk₁, ?_⟩
  have := congrArg Subtype.val hk₁eq
  simpa using this

omit [Finite G] in
theorem gold2_le_normalizer_map {H C : Subgroup G} {K : Subgroup ↥C} (hCH : C ≤ H)
    (hN : (K.map (Subgroup.inclusion hCH)).Normal) :
    H ≤ Subgroup.normalizer (K.map C.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact gold2_conj_mem_of_normal_map hCH hN hg
  · intro hgh
    have := gold2_conj_mem_of_normal_map hCH hN (H.inv_mem hg) hgh
    simpa [mul_assoc] using this

omit [Finite G] in
theorem gold2_isFaithful_ofSubgroupPair (I₁ I₂ : Subgroup G) (h2 : IsPGroup 2 ↥(I₁ ⊓ I₂))
    (hO : pCoreOf 2 (I₁ ⊔ I₂) = ⊥) : (GoldAmalgam.ofSubgroupPair I₁ I₂).IsFaithful := by
  intro K hKA hKB
  have hN1 : I₁ ≤ Subgroup.normalizer (K.map (I₁ ⊓ I₂).subtype : Set G) :=
    gold2_le_normalizer_map (inf_le_left : I₁ ⊓ I₂ ≤ I₁) hKA
  have hN2 : I₂ ≤ Subgroup.normalizer (K.map (I₁ ⊓ I₂).subtype : Set G) :=
    gold2_le_normalizer_map (inf_le_right : I₁ ⊓ I₂ ≤ I₂) hKB
  have hK'C : K.map (I₁ ⊓ I₂).subtype ≤ I₁ ⊓ I₂ := Subgroup.map_subtype_le K
  have hK'le : K.map (I₁ ⊓ I₂).subtype ≤ I₁ ⊔ I₂ :=
    hK'C.trans (inf_le_left.trans le_sup_left)
  have hK'2 : IsPGroup 2 (K.map (I₁ ⊓ I₂).subtype) := h2.to_le hK'C
  have hle : K.map (I₁ ⊓ I₂).subtype ≤ pCoreOf 2 (I₁ ⊔ I₂) :=
    le_pCoreOf_of_le_normalizer hK'le (sup_le hN1 hN2) hK'2
  rw [hO, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective K (I₁ ⊓ I₂).subtype_injective).mp hle

theorem gold2_isIndexThree_ofSubgroupPair {I₁ I₂ : Subgroup G}
    (e₁ : OTwoQuot I₁ ≃* Equiv.Perm (Fin 3)) (e₂ : OTwoQuot I₂ ≃* Equiv.Perm (Fin 3))
    (h₁ : IsSylowTwoOf (I₁ ⊓ I₂) I₁) (h₂ : IsSylowTwoOf (I₁ ⊓ I₂) I₂) :
    (GoldAmalgam.ofSubgroupPair I₁ I₂).IsIndexThree :=
  ⟨by rw [GoldAmalgam.ofSubgroupPair_edgeA_index]; exact relIndex_eq_three_of_isSylowTwoOf e₁ h₁,
    by rw [GoldAmalgam.ofSubgroupPair_edgeB_index]; exact relIndex_eq_three_of_isSylowTwoOf e₂ h₂⟩

theorem gold2_card_inf_le_sixteen_of_not_charTwo_right {I₁ I₂ : Subgroup G}
    (e₁ : OTwoQuot I₁ ≃* Equiv.Perm (Fin 3)) (e₂ : OTwoQuot I₂ ≃* Equiv.Perm (Fin 3))
    (h₁ : IsSylowTwoOf (I₁ ⊓ I₂) I₁) (h₂ : IsSylowTwoOf (I₁ ⊓ I₂) I₂)
    (hO : pCoreOf 2 (I₁ ⊔ I₂) = ⊥) (h : ¬ CharTwo I₂) : Nat.card ↥(I₁ ⊓ I₂) ≤ 16 := by
  have hfa := gold2_isFaithful_ofSubgroupPair I₁ I₂ h₁.2.1 hO
  have hidx := gold2_isIndexThree_ofSubgroupPair e₁ e₂ h₁ h₂
  have := (GoldAmalgam.ofSubgroupPair I₁ I₂).card_le_sixteen_of_not_centralizer_le hfa hidx.1 hidx.2
    (fun hc => h (gold2_charTwo_iff.mpr hc))
  exact this

theorem gold2_card_inf_le_sixteen_of_not_charTwo_left {I₁ I₂ : Subgroup G}
    (e₁ : OTwoQuot I₁ ≃* Equiv.Perm (Fin 3)) (e₂ : OTwoQuot I₂ ≃* Equiv.Perm (Fin 3))
    (h₁ : IsSylowTwoOf (I₁ ⊓ I₂) I₁) (h₂ : IsSylowTwoOf (I₁ ⊓ I₂) I₂)
    (hO : pCoreOf 2 (I₁ ⊔ I₂) = ⊥) (h : ¬ CharTwo I₁) : Nat.card ↥(I₁ ⊓ I₂) ≤ 16 := by
  have hfa := gold2_isFaithful_ofSubgroupPair I₁ I₂ h₁.2.1 hO
  have hidx := gold2_isIndexThree_ofSubgroupPair e₁ e₂ h₁ h₂
  have := (GoldAmalgam.ofSubgroupPair I₁ I₂).card_le_sixteen_of_not_centralizer_le_A hfa hidx.1
    hidx.2 (fun hc => h (gold2_charTwo_iff.mpr hc))
  exact this

@[expose] def GoldschmidtCentralAbelianBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I₁ I₂ : Subgroup G) (z : G),
    Nonempty (OTwoQuot I₁ ≃* Equiv.Perm (Fin 3)) → Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3)) →
    IsSylowTwoOf (I₁ ⊓ I₂) I₁ → IsSylowTwoOf (I₁ ⊓ I₂) I₂ →
    CharTwo I₁ → CharTwo I₂ → pCoreOf 2 (I₁ ⊔ I₂) = ⊥ →
    z ∈ I₁ ⊓ I₂ → z ≠ 1 → z ^ 2 = 1 → I₂ ≤ Subgroup.centralizer ({z} : Set G) →
    I₁ ⊓ Subgroup.centralizer ({z} : Set G) = I₁ ⊓ I₂ →
    Nat.card ↥(conjClosure (Subgroup.zpowers z) I₁) ≤ 4 →
    IsMulCommutative ↥(conjClosure (conjClosure (Subgroup.zpowers z) I₁) I₂) →
    Nat.card ↥(I₁ ⊓ I₂) ≤ 2 ^ 9

end CFSG.Quasithin
