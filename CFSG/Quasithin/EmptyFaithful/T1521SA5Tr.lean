module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5S5

public section

namespace CFSG.Quasithin.A5S5

open Equiv

variable {G : Type*} [Group G] {N : Subgroup G}

@[expose] def imageUnder (π : N →* Perm (Fin 5)) (H : Subgroup G) : Subgroup (Perm (Fin 5)) :=
  (H.subgroupOf N).map π

theorem mem_imageUnder {π : N →* Perm (Fin 5)} {H : Subgroup G} {g : Perm (Fin 5)} :
    g ∈ imageUnder π H ↔ ∃ y : N, (y : G) ∈ H ∧ π y = g := by
  unfold imageUnder
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem imageUnder_mono {π : N →* Perm (Fin 5)} {H H' : Subgroup G} (h : H ≤ H') :
    imageUnder π H ≤ imageUnder π H' := by
  intro g hg
  obtain ⟨y, hy, rfl⟩ := mem_imageUnder.1 hg
  exact mem_imageUnder.2 ⟨y, h hy, rfl⟩

theorem pi_mem_imageUnder {π : N →* Perm (Fin 5)} {H : Subgroup G} {y : N} (hy : (y : G) ∈ H) :
    π y ∈ imageUnder π H :=
  mem_imageUnder.2 ⟨y, hy, rfl⟩

theorem imageUnder_le_normalizer {π : N →* Perm (Fin 5)} {H₁ H₂ : Subgroup G}
    (h : H₁ ≤ Subgroup.normalizer (H₂ : Set G)) :
    imageUnder π H₁ ≤ Subgroup.normalizer (imageUnder π H₂ : Set (Perm (Fin 5))) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  obtain ⟨y₁, hy₁, rfl⟩ := mem_imageUnder.1 ha
  obtain ⟨y₂, hy₂, rfl⟩ := mem_imageUnder.1 hb
  refine mem_imageUnder.2 ⟨y₁ * y₂ * y₁⁻¹, ?_, by simp⟩
  have := Subgroup.le_normalizer_iff.1 h _ hy₁ _ hy₂
  simpa using this

theorem isPGroup_imageUnder {π : N →* Perm (Fin 5)} {H : Subgroup G} {p : ℕ} (hH : IsPGroup p H) :
    IsPGroup p (imageUnder π H) :=
  (hH.comap_subtype (K := N)).map π

theorem eq_one_of_normalizes_odd {π : N →* Perm (Fin 5)} {S J K Y : Subgroup G} {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hKS : K ≤ S) (hJS : J ≤ S) (hS : IsPGroup 2 S)
    (hKalt : imageUnder π K ≤ alternatingGroup (Fin 5)) (hKcard : Nat.card (imageUnder π K) = 4)
    (hJodd : ∃ j : N, (j : G) ∈ J ∧ Perm.sign (π j) = -1)
    (hSJ : S ≤ Subgroup.normalizer (J : Set G)) (hYJ : Y ≤ Subgroup.normalizer (J : Set G))
    (hY : IsPGroup p Y) : ∀ y : N, (y : G) ∈ Y → π y = 1 := by
  have hbot := eq_bot_of_normalizes_odd (K := imageUnder π K) (S := imageUnder π S)
    (J := imageUnder π J) (Y := imageUnder π Y) hp hKalt hKcard (imageUnder_mono hKS)
    (isPGroup_imageUnder hS) (imageUnder_mono hJS)
    (by obtain ⟨j, hj, hs⟩ := hJodd; exact ⟨π j, pi_mem_imageUnder hj, hs⟩)
    (imageUnder_le_normalizer hSJ) (imageUnder_le_normalizer hYJ) (isPGroup_imageUnder hY)
  intro y hy
  have := pi_mem_imageUnder (π := π) hy
  rw [hbot] at this
  exact (Subgroup.mem_bot).1 this

theorem mem_imageUnder_of_sign_eq_one {π : N →* Perm (Fin 5)} {S K : Subgroup G}
    (hKS : K ≤ S) (hS : IsPGroup 2 S) (hKalt : imageUnder π K ≤ alternatingGroup (Fin 5))
    (hKcard : Nat.card (imageUnder π K) = 4) {x : Perm (Fin 5)} (hx : x ∈ imageUnder π S)
    (hsx : Perm.sign x = 1) : x ∈ imageUnder π K := by
  have hT : IsPGroup 2 (imageUnder π S ⊓ alternatingGroup (Fin 5) : Subgroup (Perm (Fin 5))) :=
    (isPGroup_imageUnder (π := π) hS).to_le inf_le_left
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have hTA : Nat.card ↥(imageUnder π S ⊓ alternatingGroup (Fin 5)) ∣ 60 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le (inf_le_right)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  have h4 : Nat.card ↥(imageUnder π S ⊓ alternatingGroup (Fin 5)) ≤ 4 := by
    rw [hn] at hTA ⊢
    have hn2 : n ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ n := by omega
      have := (Nat.pow_dvd_pow 2 h3).trans hTA
      norm_num at this
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 4 := by norm_num
  have hle : imageUnder π K ≤ imageUnder π S ⊓ alternatingGroup (Fin 5) :=
    le_inf (imageUnder_mono hKS) hKalt
  have heq : imageUnder π K = imageUnder π S ⊓ alternatingGroup (Fin 5) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hKcard]; exact h4)
  rw [heq]
  exact ⟨hx, Perm.mem_alternatingGroup.2 hsx⟩

theorem le_sup_of_forall_sign_eq_one {π : N →* Perm (Fin 5)} {S J K C : Subgroup G} (hSN : S ≤ N)
    (hJS : J ≤ S) (hKS : K ≤ S) (hS : IsPGroup 2 S)
    (hKalt : imageUnder π K ≤ alternatingGroup (Fin 5))
    (hKcard : Nat.card (imageUnder π K) = 4) (hker : ∀ y : N, π y = 1 → (y : G) ∈ C)
    (hJ : ∀ j : N, (j : G) ∈ J → Perm.sign (π j) = 1) : J ≤ K ⊔ (S ⊓ C) := by
  intro j hj
  have hjN : j ∈ N := hSN (hJS hj)
  have hjS : j ∈ S := hJS hj
  have h1 : π ⟨j, hjN⟩ ∈ imageUnder π K :=
    mem_imageUnder_of_sign_eq_one hKS hS hKalt hKcard (pi_mem_imageUnder hjS) (hJ ⟨j, hjN⟩ hj)
  obtain ⟨s, hsK, hs⟩ := mem_imageUnder.1 h1
  have hsS : (s : G) ∈ S := hKS hsK
  have hc : ((s⁻¹ * ⟨j, hjN⟩ : N) : G) ∈ C := hker _ (by rw [map_mul, map_inv, hs, inv_mul_cancel])
  have hcS : ((s⁻¹ * ⟨j, hjN⟩ : N) : G) ∈ S := by
    have : ((s⁻¹ * ⟨j, hjN⟩ : N) : G) = (s : G)⁻¹ * j := rfl
    rw [this]
    exact S.mul_mem (S.inv_mem hsS) hjS
  have : j = (s : G) * ((s⁻¹ * ⟨j, hjN⟩ : N) : G) := by
    show j = (s : G) * ((s : G)⁻¹ * j)
    group
  rw [this]
  exact Subgroup.mul_mem_sup hsK ⟨hcS, hc⟩

theorem card_eq_four_of_odd_index {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 60)
    {H : Subgroup Γ} (hH : IsPGroup 2 H) (hodd : ¬ 2 ∣ H.index) : Nat.card H = 4 := by
  have h1 := H.card_mul_index
  rw [hΓ] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hH
  rw [hn] at h1 ⊢
  have hn2 : n ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ n := by omega
    have : 2 ^ 3 ∣ 60 := by
      rw [← h1]
      exact (Nat.pow_dvd_pow 2 h3).trans (Dvd.intro _ rfl)
    norm_num at this
  interval_cases n
  · exfalso
    apply hodd
    omega
  · exfalso
    apply hodd
    omega
  · rfl

theorem imageUnder_eq_map {π : N →* Perm (Fin 5)} {L K : Subgroup G} (hLN : L ≤ N)
    (α : ↥L →* alternatingGroup (Fin 5))
    (hπα : ∀ (ℓ : G) (hℓ : ℓ ∈ L),
      π ⟨ℓ, hLN hℓ⟩ = ((α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5))) (hKL : K ≤ L) :
    imageUnder π K = (K.subgroupOf L).map ((alternatingGroup (Fin 5)).subtype.comp α) := by
  ext x
  rw [mem_imageUnder, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hyK, rfl⟩
    have hyL : (y : G) ∈ L := hKL hyK
    refine ⟨⟨(y : G), hyL⟩, Subgroup.mem_subgroupOf.2 hyK, ?_⟩
    simpa using (hπα (y : G) hyL).symm
  · rintro ⟨l, hl, rfl⟩
    have hlK : (l : G) ∈ K := Subgroup.mem_subgroupOf.1 hl
    refine ⟨⟨(l : G), hLN l.2⟩, hlK, ?_⟩
    simpa using hπα (l : G) l.2

theorem imageUnder_le_alt {π : N →* Perm (Fin 5)} {L K : Subgroup G} (hLN : L ≤ N)
    (α : ↥L →* alternatingGroup (Fin 5))
    (hπα : ∀ (ℓ : G) (hℓ : ℓ ∈ L),
      π ⟨ℓ, hLN hℓ⟩ = ((α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5))) (hKL : K ≤ L) :
    imageUnder π K ≤ alternatingGroup (Fin 5) := by
  rw [imageUnder_eq_map hLN α hπα hKL]
  rintro x ⟨l, -, rfl⟩
  exact (α l).2

theorem card_imageUnder_eq_four [Finite G] {π : N →* Perm (Fin 5)} {L K : Subgroup G} (hLN : L ≤ N)
    (α : ↥L →* alternatingGroup (Fin 5))
    (hπα : ∀ (ℓ : G) (hℓ : ℓ ∈ L),
      π ⟨ℓ, hLN hℓ⟩ = ((α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)))
    (hα : Function.Surjective α) (hKL : K ≤ L) (hker : α.ker ≤ K.subgroupOf L)
    (hK2 : IsPGroup 2 K) (hodd : ¬ 2 ∣ (K.subgroupOf L).index) :
    Nat.card (imageUnder π K) = 4 := by
  rw [imageUnder_eq_map hLN α hπα hKL]
  have hinj : Function.Injective (alternatingGroup (Fin 5)).subtype :=
    (alternatingGroup (Fin 5)).subtype_injective
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have h2 : IsPGroup 2 ((K.subgroupOf L).map α) :=
    (hK2.comap_subtype (K := L)).map α
  have h3 : ((K.subgroupOf L).map α).index = (K.subgroupOf L).index :=
    Subgroup.index_map_eq (K.subgroupOf L) hα hker
  have hmm : (K.subgroupOf L).map ((alternatingGroup (Fin 5)).subtype.comp α) =
      ((K.subgroupOf L).map α).map (alternatingGroup (Fin 5)).subtype :=
    (Subgroup.map_map _ _ _).symm
  rw [hmm, Subgroup.card_map_of_injective hinj]
  exact card_eq_four_of_odd_index hA h2 (by rw [h3]; exact hodd)

end CFSG.Quasithin.A5S5
