module

public import CFSG.Quasithin.EmptyFaithful.ModFA5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.ModF

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] {L S : Subgroup G}

@[expose] def toPerm (α : ↥L →* alternatingGroup (Fin 5)) : ↥L →* Perm (Fin 5) :=
  (alternatingGroup (Fin 5)).subtype.comp α

@[expose] def imgS (L S : Subgroup G) (α : ↥L →* alternatingGroup (Fin 5)) :
    Subgroup (Perm (Fin 5)) :=
  ((S ⊓ L).subgroupOf L).map (toPerm α)

variable {α : ↥L →* alternatingGroup (Fin 5)}

theorem toPerm_apply (x : ↥L) : toPerm α x = ((α x : alternatingGroup (Fin 5)) : Perm (Fin 5)) :=
  rfl

theorem sign_toPerm (x : ↥L) : Perm.sign (toPerm α x) = 1 :=
  Perm.mem_alternatingGroup.mp (α x).2

theorem toPerm_eq_iff (x y : ↥L) : toPerm α x = toPerm α y ↔ α x = α y :=
  ⟨fun h => Subtype.ext h, fun h => by rw [toPerm_apply, toPerm_apply, h]⟩

theorem mem_imgS_iff (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ S) (x : ↥L) :
    toPerm α x ∈ imgS L S α ↔ (x : G) ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp h
    have hy' : (y : G) ∈ S := (Subgroup.mem_subgroupOf.mp hy).1
    have hα : α y = α x := (toPerm_eq_iff y x).mp hxy
    have h1 : α (x * y⁻¹) = 1 := by rw [map_mul, map_inv, ← hα, mul_inv_cancel]
    have h2 : ((x * y⁻¹ : ↥L) : G) ∈ S := hker _ h1
    have h3 : (x : G) = ((x * y⁻¹ : ↥L) : G) * (y : G) := by simp
    rw [h3]
    exact S.mul_mem h2 hy'
  · intro h
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr ⟨h, x.2⟩, rfl⟩

theorem imgS_isPGroup (hP : IsSylowTwoOf (S ⊓ L) L) : IsPGroup 2 ↥(imgS L S α) :=
  (hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm).map _

theorem card_map_alpha (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ S)
    (hP : IsSylowTwoOf (S ⊓ L) L) : Nat.card ↥(((S ⊓ L).subgroupOf L).map α) = 4 := by
  classical
  set P₁ : Subgroup ↥L := (S ⊓ L).subgroupOf L with hP₁
  set P₂ : Subgroup (alternatingGroup (Fin 5)) := P₁.map α with hP₂
  have hkerle : α.ker ≤ P₁ := fun x hx => Subgroup.mem_subgroupOf.mpr ⟨hker x hx, x.2⟩
  have hcomap : P₂.comap α = P₁ := by
    rw [hP₂, Subgroup.comap_map_eq, sup_eq_left.mpr hkerle]
  have hidx : P₂.index = P₁.index := by
    rw [← Subgroup.index_comap_of_surjective P₂ hα, hcomap]
  have hodd : ¬ 2 ∣ P₂.index := by rw [hidx]; exact hP.2.2
  have hP₁2 : IsPGroup 2 ↥P₁ := hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm
  have hP₂2 : IsPGroup 2 ↥P₂ := hP₁2.map α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₂2
  have hmul := Subgroup.card_mul_index P₂
  rw [hk, a5_card] at hmul
  have h2k : 2 ^ k ∣ 60 := ⟨P₂.index, hmul.symm⟩
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h8.trans h2k
    omega
  interval_cases k
  · exfalso; apply hodd; omega
  · exfalso; apply hodd; omega
  · rw [hk]; norm_num

theorem card_imgS (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ S)
    (hP : IsSylowTwoOf (S ⊓ L) L) : Nat.card (imgS L S α) = 4 := by
  have hmap : imgS L S α =
      (((S ⊓ L).subgroupOf L).map α).map (alternatingGroup (Fin 5)).subtype := by
    rw [imgS, Subgroup.map_map]
    rfl
  rw [hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    card_map_alpha hα hker hP]

theorem exists_fixed (hP : IsSylowTwoOf (S ⊓ L) L) : ∃ p : Fin 5, ∀ g ∈ imgS L S α, g p = p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := (imgS_isPGroup (α := α) hP).card_modEq_card_fixedPoints (Fin 5)
  have h5 : Nat.card (Fin 5) = 5 := by simp
  rw [h5] at hmod
  have hne : Nat.card ↥(MulAction.fixedPoints ↥(imgS L S α) (Fin 5)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  have hpos : 0 < Nat.card ↥(MulAction.fixedPoints ↥(imgS L S α) (Fin 5)) := Nat.pos_of_ne_zero hne
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  refine ⟨p, fun g hg => ?_⟩
  have := MulAction.mem_fixedPoints.mp hp ⟨g, hg⟩
  simpa using this

theorem imgS_eq_klein (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ S)
    (hP : IsSylowTwoOf (S ⊓ L) L) {p : Fin 5} (hp : ∀ g ∈ imgS L S α, g p = p) (g : Perm (Fin 5)) :
    g ∈ imgS L S α ↔ g ∈ klein p := by
  classical
  have hcard := card_imgS hα hker hP
  have hsub : ∀ g ∈ imgS L S α, g ∈ klein p := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hg
    have hg4 : (toPerm α x) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := ↥(imgS L S α)) (x := ⟨toPerm α x, hg⟩)
      rw [hcard] at this
      exact congrArg Subtype.val this
    have h2 := no_order_four _ (sign_toPerm x) hg4
    simp only [klein, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h2, sign_toPerm x, hp _ hg⟩
  constructor
  · exact hsub g
  · intro hgk
    set T : Finset (Perm (Fin 5)) := Finset.univ.filter fun g => g ∈ imgS L S α with hT
    have hTsub : T ⊆ klein p := fun g hg => hsub g (Finset.mem_filter.mp hg).2
    have hTcard : T.card = 4 := by
      rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have heq : T = klein p :=
      Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard, card_klein p])
    have : g ∈ T := by rw [heq]; exact hgk
    exact (Finset.mem_filter.mp this).2

theorem exists_normalizing_lift (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ S)
    (hP : IsSylowTwoOf (S ⊓ L) L) {i j : Fin 5} (hij : i ≠ j) :
    ∃ c : ↥L, (c : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      (toPerm α c) ^ 3 = 1 ∧ toPerm α c ≠ 1 ∧
      (toPerm α c * swap i j * (toPerm α c)⁻¹ * swap i j) ^ 3 = 1 ∧
      toPerm α c * swap i j * (toPerm α c)⁻¹ * swap i j ≠ 1 := by
  obtain ⟨p, hp⟩ := exists_fixed (α := α) hP
  have hk := imgS_eq_klein hα hker hP hp
  obtain ⟨γ, hs, hγp, hγ3, hγ1, hc3, hc1⟩ := swapConj p i j hij
  obtain ⟨c, hc⟩ := hα ⟨γ, Perm.mem_alternatingGroup.mpr hs⟩
  have hcγ : toPerm α c = γ := by rw [toPerm_apply, hc]
  have hconj : ∀ g ∈ klein p, γ * g * γ⁻¹ ∈ klein p := by
    intro g hg
    simp only [klein, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · calc γ * g * γ⁻¹ * (γ * g * γ⁻¹) = γ * (g * g) * γ⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · simp [Perm.sign_mul, Perm.sign_inv, hs, h2]
    · have hinv : γ⁻¹ p = p := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hγp.symm
      simp only [Perm.mul_apply, hinv, h3, hγp]
  have hconjmem : ∀ x : ↥L, (x : G) ∈ S → ((c * x * c⁻¹ : ↥L) : G) ∈ S := by
    intro x hx
    have hxm : toPerm α x ∈ imgS L S α := (mem_imgS_iff hker x).mpr hx
    have h1 : toPerm α (c * x * c⁻¹) ∈ imgS L S α := by
      rw [map_mul, map_mul, map_inv, hcγ]
      exact (hk _).mpr (hconj _ ((hk _).mp hxm))
    exact (mem_imgS_iff hker _).mp h1
  refine ⟨c, ?_, by rw [hcγ]; exact hγ3, by rw [hcγ]; exact hγ1, by rw [hcγ]; exact hc3,
    by rw [hcγ]; exact hc1⟩
  have hfwd : ∀ x ∈ S ⊓ L, (c : G) * x * (c : G)⁻¹ ∈ S ⊓ L := by
    intro x hx
    have hxL : x ∈ L := hx.2
    have := hconjmem ⟨x, hxL⟩ hx.1
    refine ⟨?_, ?_⟩
    · simpa using this
    · exact L.mul_mem (L.mul_mem c.2 hxL) (L.inv_mem c.2)
  have hconj' : ∀ g ∈ klein p, γ⁻¹ * g * γ⁻¹⁻¹ ∈ klein p := by
    intro g hg
    simp only [klein, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    have hinv : γ⁻¹ p = p := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hγp.symm
    refine ⟨?_, ?_, ?_⟩
    · calc γ⁻¹ * g * γ⁻¹⁻¹ * (γ⁻¹ * g * γ⁻¹⁻¹) = γ⁻¹ * (g * g) * γ⁻¹⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · simp [Perm.sign_mul, Perm.sign_inv, hs, h2]
    · simp only [Perm.mul_apply, inv_inv, hγp, h3, hinv]
  have hbwd : ∀ x ∈ S ⊓ L, (c : G)⁻¹ * x * ((c : G)⁻¹)⁻¹ ∈ S ⊓ L := by
    intro x hx
    have hxL : x ∈ L := hx.2
    have hxm : toPerm α ⟨x, hxL⟩ ∈ imgS L S α := (mem_imgS_iff hker _).mpr hx.1
    have hd : toPerm α c⁻¹ = γ⁻¹ := by rw [map_inv, hcγ]
    have hdinv : toPerm α (c⁻¹)⁻¹ = (γ⁻¹)⁻¹ := by rw [map_inv, hd]
    have h1 : toPerm α (c⁻¹ * ⟨x, hxL⟩ * c⁻¹⁻¹) ∈ imgS L S α := by
      rw [map_mul, map_mul, hd, hdinv]
      exact (hk _).mpr (hconj' _ ((hk _).mp hxm))
    have h2 := (mem_imgS_iff hker _).mp h1
    refine ⟨?_, ?_⟩
    · simpa using h2
    · exact L.mul_mem (L.mul_mem (L.inv_mem c.2) hxL) (L.inv_mem (L.inv_mem c.2))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hfwd x hx
  · intro hx
    have := hbwd _ hx
    simpa [mul_assoc] using this

theorem not_le_normalizer (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ S)
    (hP : IsSylowTwoOf (S ⊓ L) L) : ¬ L ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  intro hN
  have hnormal : ((S ⊓ L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hN
  have := hnormal.map α hα
  have hc := card_map_alpha hα hker hP
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((S ⊓ L).subgroupOf L).map α) with h | h
  · rw [h, Subgroup.card_bot] at hc
    omega
  · rw [h, Subgroup.card_top, a5_card] at hc
    omega

end CFSG.Quasithin.ModF
