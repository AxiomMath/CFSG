module

public import CFSG.Quasithin.EmptyFaithful.A38c7Core

public section

namespace CFSG.Quasithin.A38c7

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.FLc

private theorem isSylowTwoOf_map_hom_range {G K : Type*} [Group G] [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

private theorem exists_card_map_eq {A F : Type} [Group A] [Finite A] [Group F] {ρ : A →* F}
    (hker : IsPGroup 2 ρ.ker) {Y : Subgroup A} (hY : ∃ a, Nat.card Y = 2 ^ a * 3) :
    ∃ a', Nat.card (Y.map ρ) = 2 ^ a' * 3 := by
  obtain ⟨a, ha⟩ := hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (ρ.domRestrict Y).ker := by
    rw [MonoidHom.ker_domRestrict]
    exact hker.comap_of_injective Y.subtype Y.subtype_injective
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  have h1 : Nat.card (ρ.domRestrict Y).ker * (ρ.domRestrict Y).ker.index = Nat.card Y :=
    Subgroup.card_mul_index _
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, hk, ha] at h1
  have h2 : 2 ^ k ∣ 2 ^ a :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right ⟨_, h1.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2)
  refine ⟨d, Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) k) ?_⟩
  rw [h1, pow_add, mul_assoc]

private theorem exists_quotient_hom {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hSL : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    ∃ (F : Type) (_ : Group F) (_ : Finite F) (ρ : ↥L →* F) (φ : ↥S →* F),
      ρ.ker = CFSG.pCore 2 ↥L ∧
      (∀ (s : G) (hs : s ∈ S) (l : G) (hl : l ∈ L) (h : s * l * s⁻¹ ∈ L),
        φ ⟨s, hs⟩ * ρ ⟨l, hl⟩ * (φ ⟨s, hs⟩)⁻¹ = ρ ⟨s * l * s⁻¹, h⟩) ∧
      (∀ (x : G) (hs : x ∈ S) (hl : x ∈ L), φ ⟨x, hs⟩ = ρ ⟨x, hl⟩) := by
  set M : Subgroup G := Subgroup.normalizer (L : Set G) with hM
  set N : Subgroup G := (CFSG.pCore 2 ↥L).map L.subtype with hN
  have hLM : L ≤ M := Subgroup.le_normalizer
  have hSM : S ≤ M := le_normalizer_of_conj_mem hSL
  have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 ↥L)
  have hNM : (N.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMN
  refine ⟨↥M ⧸ N.subgroupOf M, inferInstance, inferInstance,
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hLM),
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hSM), ?_, ?_, ?_⟩
  · ext l
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem L.subtype_injective
  · intro s hs l hl h
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · intro x hs hl
    rfl

private theorem transfer5_of_hom {G F : Type} [Group G] [Finite G] [Group F] [Finite F]
    {L S Y₁ Y₂ : Subgroup G} (ρ : ↥L →* F) (φ : ↥S →* F)
    (hρφ : ∀ (s : G) (hs : s ∈ S) (l : G) (hl : l ∈ L) (h : s * l * s⁻¹ ∈ L),
      φ ⟨s, hs⟩ * ρ ⟨l, hl⟩ * (φ ⟨s, hs⟩)⁻¹ = ρ ⟨s * l * s⁻¹, h⟩)
    (hφ : ∀ (x : G) (hs : x ∈ S) (hl : x ∈ L), φ ⟨x, hs⟩ = ρ ⟨x, hl⟩)
    (hker : IsPGroup 2 ρ.ker) (e : ↥ρ.range ≃* SLt 5)
    (hSL : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) (hB : IsSylowTwoOf (S ⊓ L) L)
    (hY₁ : Y₁ ≤ L) (hY₁S : ∀ s ∈ S, ∀ y ∈ Y₁, s * y * s⁻¹ ∈ Y₁) (hY₁c : ∃ a, Nat.card Y₁ = 2 ^ a * 3)
    (hY₂ : Y₂ ≤ L) (hY₂S : ∀ s ∈ S, ∀ y ∈ Y₂, s * y * s⁻¹ ∈ Y₂) (hY₂c : ∃ a, Nat.card Y₂ = 2 ^ a * 3) :
    ∃ P₁ P₂ : Subgroup G,
      (S ⊓ L ≤ P₁ ∧ P₁ ≤ L ∧ P₁ ≠ L ∧ Y₁ ≤ P₁ ∧ Y₂ ≤ P₁ ∧ ∀ s ∈ S, ∀ p ∈ P₁, s * p * s⁻¹ ∈ P₁) ∧
      (S ⊓ L ≤ P₂ ∧ P₂ ≤ L ∧ P₂ ≠ L ∧ Y₁ ≤ P₂ ∧ Y₂ ≤ P₂ ∧ ∀ s ∈ S, ∀ p ∈ P₂, s * p * s⁻¹ ∈ P₂) ∧
      P₁ ⊔ P₂ = L := by
  have hconj : ∀ (s : G) (hs : s ∈ S) (l : ↥L), ∃ h : s * (l : G) * s⁻¹ ∈ L,
      φ ⟨s, hs⟩ * ρ l * (φ ⟨s, hs⟩)⁻¹ = ρ ⟨s * l * s⁻¹, h⟩ := fun s hs l =>
    ⟨hSL s hs l l.2, hρφ s hs l l.2 (hSL s hs l l.2)⟩
  have hinv : ∀ X : Subgroup G, (∀ s ∈ S, ∀ y ∈ X, s * y * s⁻¹ ∈ X) →
      ∀ w ∈ φ.range, ∀ b ∈ (X.subgroupOf L).map ρ, w * b * w⁻¹ ∈ (X.subgroupOf L).map ρ := by
    intro X hX w hw b hb
    obtain ⟨⟨s, hs⟩, rfl⟩ := hw
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨h, hy'⟩ := hconj s hs y
    rw [hy']
    exact ⟨⟨s * y * s⁻¹, h⟩, Subgroup.mem_subgroupOf.2 (hX s hs y (Subgroup.mem_subgroupOf.1 hy)), rfl⟩
  have hSLinv : ∀ s ∈ S, ∀ y ∈ S ⊓ L, s * y * s⁻¹ ∈ S ⊓ L := fun s hs y hy =>
    ⟨S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs), hSL s hs y hy.2⟩
  have hWL : ∀ w ∈ φ.range, ∀ l ∈ ρ.range, w * l * w⁻¹ ∈ ρ.range := by
    rintro w ⟨⟨s, hs⟩, rfl⟩ _ ⟨l, rfl⟩
    obtain ⟨h, hl⟩ := hconj s hs l
    rw [hl]
    exact ⟨_, rfl⟩
  have hBW : ((S ⊓ L).subgroupOf L).map ρ ≤ φ.range := by
    rintro _ ⟨y, hy, rfl⟩
    have hyS : (y : G) ∈ S := (Subgroup.mem_subgroupOf.1 hy).1
    exact ⟨⟨y, hyS⟩, hφ y hyS y.2⟩
  have hcard : ∀ Y : Subgroup G, Y ≤ L → (∃ a, Nat.card Y = 2 ^ a * 3) →
      ∃ a, Nat.card ((Y.subgroupOf L).map ρ) = 2 ^ a * 3 := by
    intro Y hYL hYc
    refine exists_card_map_eq hker ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv]
  obtain ⟨Q₁, Q₂, ⟨hBQ₁, hQ₁L, hQ₁ne, hY₁Q₁, hY₂Q₁, hQ₁W⟩, ⟨hBQ₂, hQ₂L, hQ₂ne, hY₁Q₂, hY₂Q₂, hQ₂W⟩, hsup⟩ :=
    core5 (W := φ.range) e (isSylowTwoOf_map_hom_range hB ρ) hBW hWL (hinv (S ⊓ L) hSLinv)
      (Subgroup.map_le_range _ _) (hinv Y₁ hY₁S) (hcard Y₁ hY₁ hY₁c)
      (Subgroup.map_le_range _ _) (hinv Y₂ hY₂S) (hcard Y₂ hY₂ hY₂c)
  have build : ∀ Q : Subgroup F, ((S ⊓ L).subgroupOf L).map ρ ≤ Q → Q ≤ ρ.range → Q ≠ ρ.range →
      (Y₁.subgroupOf L).map ρ ≤ Q → (Y₂.subgroupOf L).map ρ ≤ Q →
      (∀ w ∈ φ.range, ∀ p ∈ Q, w * p * w⁻¹ ∈ Q) →
      (S ⊓ L ≤ (Q.comap ρ).map L.subtype ∧ (Q.comap ρ).map L.subtype ≤ L ∧
        (Q.comap ρ).map L.subtype ≠ L ∧ Y₁ ≤ (Q.comap ρ).map L.subtype ∧
        Y₂ ≤ (Q.comap ρ).map L.subtype ∧
        ∀ s ∈ S, ∀ p ∈ (Q.comap ρ).map L.subtype, s * p * s⁻¹ ∈ (Q.comap ρ).map L.subtype) := by
    intro Q hBQ hQL hne hY₁Q hY₂Q hQW
    have hmem : ∀ (x : G) (hx : x ∈ L), x ∈ (Q.comap ρ).map L.subtype ↔ ρ ⟨x, hx⟩ ∈ Q := by
      intro x hx
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro h
        exact ⟨⟨x, hx⟩, h, rfl⟩
    refine ⟨?_, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
    · rintro x ⟨hxS, hxL⟩
      exact (hmem x hxL).2 (hBQ ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 ⟨hxS, hxL⟩, rfl⟩)
    · intro h
      refine hne (le_antisymm hQL ?_)
      rintro _ ⟨l, rfl⟩
      have hl : (l : G) ∈ (Q.comap ρ).map L.subtype := by
        rw [h]
        exact l.2
      exact (hmem l l.2).1 hl
    · intro y hy
      exact (hmem y (hY₁ hy)).2 (hY₁Q ⟨⟨y, hY₁ hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩)
    · intro y hy
      exact (hmem y (hY₂ hy)).2 (hY₂Q ⟨⟨y, hY₂ hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩)
    · rintro s hs _ ⟨p, hp, rfl⟩
      obtain ⟨h, hsp⟩ := hconj s hs p
      refine ⟨⟨s * p * s⁻¹, h⟩, ?_, rfl⟩
      show ρ ⟨s * p * s⁻¹, h⟩ ∈ Q
      rw [← hsp]
      exact hQW _ ⟨⟨s, hs⟩, rfl⟩ _ hp
  refine ⟨(Q₁.comap ρ).map L.subtype, (Q₂.comap ρ).map L.subtype,
    build Q₁ hBQ₁ hQ₁L hQ₁ne hY₁Q₁ hY₂Q₁ hQ₁W, build Q₂ hBQ₂ hQ₂L hQ₂ne hY₁Q₂ hY₂Q₂ hQ₂W, ?_⟩
  have h1 : Q₁.comap ρ ⊔ Q₂.comap ρ ≤
      ((Q₁.comap ρ).map L.subtype ⊔ (Q₂.comap ρ).map L.subtype).subgroupOf L := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left ⟨x, hx, rfl⟩)
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right ⟨x, hx, rfl⟩)
  have h2 : Q₁.comap ρ ⊔ Q₂.comap ρ = ⊤ := by
    rw [Subgroup.comap_sup_eq_of_le_range ρ hQ₁L hQ₂L, hsup]
    exact eq_top_iff.2 fun x _ => ⟨x, rfl⟩
  have h3 : ((Q₁.comap ρ).map L.subtype ⊔ (Q₂.comap ρ).map L.subtype).subgroupOf L = ⊤ :=
    eq_top_iff.2 (h2.symm.le.trans h1)
  exact le_antisymm (sup_le (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _))
    (Subgroup.subgroupOf_eq_top.1 h3)

theorem transfer5 {G : Type} [Group G] [Finite G] {L S Y₁ Y₂ : Subgroup G}
    (hSL : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (hB : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L)
    (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))))
    (hY₁ : Y₁ ≤ L) (hY₁S : ∀ s ∈ S, ∀ y ∈ Y₁, s * y * s⁻¹ ∈ Y₁) (hY₁c : ∃ a, Nat.card Y₁ = 2 ^ a * 3)
    (hY₂ : Y₂ ≤ L) (hY₂S : ∀ s ∈ S, ∀ y ∈ Y₂, s * y * s⁻¹ ∈ Y₂) (hY₂c : ∃ a, Nat.card Y₂ = 2 ^ a * 3) :
    ∃ P₁ P₂ : Subgroup G,
      (S ⊓ L ≤ P₁ ∧ P₁ ≤ L ∧ P₁ ≠ L ∧ Y₁ ≤ P₁ ∧ Y₂ ≤ P₁ ∧ ∀ s ∈ S, ∀ p ∈ P₁, s * p * s⁻¹ ∈ P₁) ∧
      (S ⊓ L ≤ P₂ ∧ P₂ ≤ L ∧ P₂ ≠ L ∧ Y₁ ≤ P₂ ∧ Y₂ ≤ P₂ ∧ ∀ s ∈ S, ∀ p ∈ P₂, s * p * s⁻¹ ∈ P₂) ∧
      P₁ ⊔ P₂ = L := by
  obtain ⟨F, _, _, ρ, φ, hker, hρφ, hφ⟩ := exists_quotient_hom (L := L) (S := S) hSL
  obtain ⟨q⟩ := hq
  have hp : IsPGroup 2 ρ.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  exact transfer5_of_hom ρ φ hρφ hφ hp
    ((QuotientGroup.quotientKerEquivRange ρ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (q.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm)))
    hSL hB hY₁ hY₁S hY₁c hY₂ hY₂S hY₂c

end CFSG.Quasithin.A38c7
