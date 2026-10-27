module

public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.H13.Lem1227Eq

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem relIndex_inf_normalizer_le (K W : Subgroup G) (F : Set (Subgroup G)) [Finite F]
    (hW : W ∈ F) (hF : ∀ k ∈ K, ∀ U ∈ F, cjSub k U ∈ F) :
    (K ⊓ Subgroup.normalizer (W : Set G)).relIndex K ≤ Nat.card F := by
  let f : (↥K ⧸ (K ⊓ Subgroup.normalizer (W : Set G)).subgroupOf K) → F :=
    Quotient.lift (fun k : ↥K => (⟨cjSub (k : G) W, hF k k.2 W hW⟩ : F)) (by
      intro k k' hkk'
      have hm : (k : G)⁻¹ * k' ∈ Subgroup.normalizer (W : Set G) := by
        have := QuotientGroup.leftRel_apply.1 hkk'
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this.2
      apply Subtype.ext
      ext x
      simp only [mem_cjSub]
      have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm) ((k : G)⁻¹ * x * k)
      have h2 : ((k : G)⁻¹ * k')⁻¹ * ((k : G)⁻¹ * x * k) * ((k : G)⁻¹ * k')⁻¹⁻¹ =
          (k' : G)⁻¹ * x * k' := by group
      rw [h2] at h1
      exact h1)
  have hinj : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H k =>
      induction b using QuotientGroup.induction_on with
      | H k' =>
        have h := congrArg Subtype.val hab
        change cjSub (k : G) W = cjSub (k' : G) W at h
        apply QuotientGroup.eq.2
        rw [Subgroup.mem_subgroupOf]
        have h2 : ∀ x : G, (k : G)⁻¹ * x * k ∈ W ↔ (k' : G)⁻¹ * x * k' ∈ W := fun x => by
          have := congrArg (fun U : Subgroup G => x ∈ U) h
          simpa only [mem_cjSub, eq_iff_iff] using this
        have hm' : ((k : G)⁻¹ * k')⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          have h3 := h2 ((k : G) * y * (k : G)⁻¹)
          have e1 : (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * k = y := by group
          have e2 : (k' : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * k' =
              ((k : G)⁻¹ * k')⁻¹ * y * ((k : G)⁻¹ * k')⁻¹⁻¹ := by group
          rw [e1, e2] at h3
          exact h3
        have hm := Subgroup.inv_mem _ hm'
        rw [inv_inv] at hm
        exact ⟨K.mul_mem (K.inv_mem k.2) k'.2, hm⟩
  exact Nat.card_le_card_of_injective f hinj

theorem mem_normalizer_of_conj_mem [Finite G] {W : Subgroup G} {g : G}
    (h : ∀ x ∈ W, g * x * g⁻¹ ∈ W) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  have hinj : Function.Injective (fun x : ↥W => (⟨g * x * g⁻¹, h x x.2⟩ : ↥W)) := by
    intro x y hxy
    have h1 : g * (x : G) * g⁻¹ = g * (y : G) * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h1)
  have hsurj := Finite.surjective_of_injective hinj
  have hback : ∀ x ∈ W, g⁻¹ * x * g ∈ W := by
    intro x hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have h2 : g * (y : G) * g⁻¹ = x := congrArg Subtype.val hy
    have h3 : (y : G) = g⁻¹ * x * g := by
      calc (y : G) = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * x * g := by rw [h2]
    rw [← h3]
    exact y.2
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  have := hback _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem card_family_le [Finite G] (C V : Subgroup G) (hCV : C ≤ V) (F : Set (Subgroup G))
    (m : ℕ) (hle : ∀ U ∈ F, C ≤ U ∧ U ≤ V) (hcard : ∀ U ∈ F, Nat.card U = m)
    (hdisj : ∀ U ∈ F, ∀ U' ∈ F, U ≠ U' → U ⊓ U' = C) :
    Nat.card F * (m - Nat.card C) + Nat.card C ≤ Nat.card V := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hFfin : F.Finite := Set.toFinite F
  have hcardU : ∀ U : Subgroup G, (Finset.univ.filter (· ∈ U)).card = Nat.card U := fun U => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let B : Subgroup G → Finset G := fun U =>
    (Finset.univ.filter (· ∈ U)) \ (Finset.univ.filter (· ∈ C))
  have hB : ∀ U ∈ F, (B U).card = m - Nat.card C := fun U hU => by
    have hsub : Finset.univ.filter (· ∈ C) ⊆ Finset.univ.filter (· ∈ U) := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hle U hU).1 hx
    rw [Finset.card_sdiff_of_subset hsub, hcardU, hcardU, hcard U hU]
  have hdisjB : ∀ U ∈ hFfin.toFinset, ∀ U' ∈ hFfin.toFinset, U ≠ U' → Disjoint (B U) (B U') := by
    intro U hU U' hU' hne
    rw [Set.Finite.mem_toFinset] at hU hU'
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    have : x ∈ U ⊓ U' := ⟨hx.1, hx'.1⟩
    rw [hdisj U hU U' hU' hne] at this
    exact hx.2 this
  have hsum := Finset.card_biUnion hdisjB
  have hsubV : hFfin.toFinset.biUnion B ⊆
      (Finset.univ.filter (· ∈ V)) \ (Finset.univ.filter (· ∈ C)) := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨U, hU, hxU⟩ := hx
    rw [Set.Finite.mem_toFinset] at hU
    simp only [B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hxU ⊢
    exact ⟨(hle U hU).2 hxU.1, hxU.2⟩
  have hCV' : Finset.univ.filter (· ∈ C) ⊆ Finset.univ.filter (· ∈ V) := fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hCV hx
  have h1 := Finset.card_le_card hsubV
  rw [Finset.card_sdiff_of_subset hCV', hcardU, hcardU, hsum] at h1
  have h2 : ∑ U ∈ hFfin.toFinset, (B U).card = Nat.card F * (m - Nat.card C) := by
    rw [Finset.sum_congr rfl (fun U hU => hB U ((Set.Finite.mem_toFinset hFfin).1 hU)),
      Finset.sum_const, smul_eq_mul, Nat.card_eq_card_finite_toFinset hFfin]
  rw [h2] at h1
  have hCle : Nat.card C ≤ Nat.card V := Subgroup.card_le_of_le hCV
  omega

end CFSG.Quasithin.H13.Lem1227Eq
