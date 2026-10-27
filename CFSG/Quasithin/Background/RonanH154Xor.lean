module

public import CFSG.Quasithin.Background.RonanH143E2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin.RonanH143

@[expose] def dot5 (h u : ℕ) : Bool :=
  ((h &&& u).testBit 0) ^^ ((h &&& u).testBit 1) ^^ ((h &&& u).testBit 2) ^^
    ((h &&& u).testBit 3) ^^ ((h &&& u).testBit 4)

@[expose] def xorSub (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) : Subgroup P24 where
  carrier := {g | ∃ u ∈ S, g = nq2Perm u}
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨xor32 s t, hS s hs t ht, nq2Perm_mul s t⟩
  one_mem' := ⟨0, h0, nq2Perm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, inv_eq_of_mul_eq_one_right (nq2Perm_sq t)⟩

theorem mem_xorSub_iff {S : Finset (Fin 32)} {h0 : (0 : Fin 32) ∈ S}
    {hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S} {g : P24} :
    g ∈ xorSub S h0 hS ↔ ∃ u ∈ S, g = nq2Perm u := Iff.rfl

theorem xorSub_le_NQ2 (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) : xorSub S h0 hS ≤ NQ2 := by
  intro g hg
  obtain ⟨u, _, rfl⟩ := mem_xorSub_iff.1 hg
  exact mem_NQ2_iff.2 ⟨u, rfl⟩

theorem card_xorSub (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) : Nat.card (xorSub S h0 hS) = S.card := by
  have hset : ((xorSub S h0 hS : Subgroup P24) : Set P24) =
      ((S.image nq2Perm : Finset P24) : Set P24) := by
    ext g
    simp only [SetLike.mem_coe, mem_xorSub_iff, Finset.mem_coe, Finset.mem_image]
    exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injective S nq2Perm_injective]

theorem isElemAbelian_xorSub (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) : IsElemAbelian 2 (xorSub S h0 hS) :=
  isElemAbelian_of_le (xorSub_le_NQ2 S h0 hS) isElemAbelian_NQ2

theorem isE2k_xorSub {k : ℕ} (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) (hk : S.card = 2 ^ k) : IsE2k k (xorSub S h0 hS) :=
  ⟨isElemAbelian_xorSub S h0 hS, by rw [card_xorSub S h0 hS, hk]⟩

theorem exists_xorSub_of_le_NQ2 (A : Subgroup P24) (hA : A ≤ NQ2) :
    ∃ (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S) (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S),
      A = xorSub S h0 hS := by
  classical
  refine ⟨Finset.univ.filter (fun u => nq2Perm u ∈ A), ?_, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [nq2Perm_zero]; exact A.one_mem⟩
  · intro s hs t ht
    rw [Finset.mem_filter] at hs ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← nq2Perm_mul]
    exact A.mul_mem hs.2 ht.2
  · ext g
    rw [mem_xorSub_iff]
    constructor
    · intro hg
      obtain ⟨u, hu⟩ := mem_NQ2_iff.1 (hA hg)
      refine ⟨u, ?_, hu⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [← hu]; exact hg⟩
    · rintro ⟨u, hu, rfl⟩
      rw [Finset.mem_filter] at hu
      exact hu.2

theorem xor32_cancel_l : ∀ s t : Fin 32, xor32 s (xor32 s t) = t := by decide +kernel

theorem xor32_cancel_r : ∀ s t : Fin 32, xor32 (xor32 s t) t = s := by decide +kernel

theorem dot5_zero32 : ∀ h : Fin 32, dot5 (h : ℕ) ((0 : Fin 32) : ℕ) = false := by
  decide +kernel

theorem dot5_zero_left32 : ∀ u : Fin 32, dot5 ((0 : Fin 32) : ℕ) (u : ℕ) = false := by
  decide +kernel

theorem dot5_xor32 : ∀ h a b : Fin 32,
    dot5 (h : ℕ) ((xor32 a b : Fin 32) : ℕ) = (dot5 (h : ℕ) (a : ℕ) ^^ dot5 (h : ℕ) (b : ℕ)) := by
  decide +kernel

theorem dot5_basis_exists : ∀ b1 b2 b4 b8 b16 : Bool, ∃ h : Fin 32,
    dot5 (h : ℕ) ((1 : Fin 32) : ℕ) = b1 ∧ dot5 (h : ℕ) ((2 : Fin 32) : ℕ) = b2 ∧
    dot5 (h : ℕ) ((4 : Fin 32) : ℕ) = b4 ∧ dot5 (h : ℕ) ((8 : Fin 32) : ℕ) = b8 ∧
    dot5 (h : ℕ) ((16 : Fin 32) : ℕ) = b16 := by
  decide +kernel

@[expose] def bitPart32 (k v : Fin 32) : Fin 32 := if (k : ℕ) &&& (v : ℕ) = 0 then 0 else k

theorem xor32_decomp : ∀ v : Fin 32,
    v = xor32 (xor32 (xor32 (xor32 (bitPart32 1 v) (bitPart32 2 v)) (bitPart32 4 v))
      (bitPart32 8 v)) (bitPart32 16 v) := by
  decide +kernel

theorem xor32_mem_of_not_mem (S : Finset (Fin 32)) (hcard : S.card = 16)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) {a b : Fin 32} (ha : a ∉ S) (hb : b ∉ S) :
    xor32 a b ∈ S := by
  classical
  have hinj : Function.Injective (xor32 a) := by
    intro x y hxy
    have h := congrArg (xor32 a) hxy
    rwa [xor32_cancel_l, xor32_cancel_l] at h
  have hC : (S.image (xor32 a)).card = 16 := by
    rw [Finset.card_image_of_injective S hinj, hcard]
  have hdisj : Disjoint S (S.image (xor32 a)) := by
    rw [Finset.disjoint_left]
    intro x hxS hxC
    obtain ⟨s, hsS, hsx⟩ := Finset.mem_image.1 hxC
    apply ha
    have h1 := hS x hxS s hsS
    rw [← hsx, xor32_cancel_r] at h1
    exact h1
  have hcov : S ∪ S.image (xor32 a) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hC, hcard, Fintype.card_fin]
  have hbU : b ∈ S ∪ S.image (xor32 a) := by
    rw [hcov]
    exact Finset.mem_univ b
  rcases Finset.mem_union.1 hbU with hbS | hbC
  · exact absurd hbS hb
  · obtain ⟨s, hsS, hsb⟩ := Finset.mem_image.1 hbC
    rw [← hsb, xor32_cancel_l]
    exact hsS

theorem xor32_eq_of_basis (φ ψ : Fin 32 → Bool)
    (hφ : ∀ a b, φ (xor32 a b) = (φ a ^^ φ b)) (hψ : ∀ a b, ψ (xor32 a b) = (ψ a ^^ ψ b))
    (h0 : φ 0 = ψ 0) (h1 : φ 1 = ψ 1) (h2 : φ 2 = ψ 2) (h4 : φ 4 = ψ 4) (h8 : φ 8 = ψ 8)
    (h16 : φ 16 = ψ 16) : ∀ u : Fin 32, φ u = ψ u := by
  have hT : ∀ a b, φ a = ψ a → φ b = ψ b → φ (xor32 a b) = ψ (xor32 a b) := by
    intro a b ha hb
    rw [hφ, hψ, ha, hb]
  have hbit : ∀ k v : Fin 32, φ k = ψ k → φ (bitPart32 k v) = ψ (bitPart32 k v) := by
    intro k v hk
    unfold bitPart32
    split
    · exact h0
    · exact hk
  intro u
  rw [xor32_decomp u]
  exact hT _ _ (hT _ _ (hT _ _ (hT _ _ (hbit 1 u h1) (hbit 2 u h2)) (hbit 4 u h4))
    (hbit 8 u h8)) (hbit 16 u h16)

theorem index_two_xor32 (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) (hcard : S.card = 16) :
    ∃ h : Fin 32, h ≠ 0 ∧ ∀ u : Fin 32, u ∈ S ↔ dot5 (h : ℕ) (u : ℕ) = false := by
  obtain ⟨φ, hφu⟩ : ∃ φ : Fin 32 → Bool, ∀ u, φ u = decide (u ∉ S) :=
    ⟨fun u => decide (u ∉ S), fun u => rfl⟩
  have hmem : ∀ u : Fin 32, u ∈ S ↔ φ u = false := by
    intro u
    simp [hφu]
  have hnmem : ∀ u : Fin 32, u ∉ S ↔ φ u = true := by
    intro u
    simp [hφu]
  have hφ0 : φ 0 = false := (hmem 0).1 h0
  have hadd : ∀ a b : Fin 32, φ (xor32 a b) = (φ a ^^ φ b) := by
    intro a b
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · have hab : xor32 a b ∈ S := hS a ha b hb
      simp [(hmem _).1 hab, (hmem a).1 ha, (hmem b).1 hb]
    · have hab : xor32 a b ∉ S := by
        intro hab
        apply hb
        have h' := hS a ha _ hab
        rwa [xor32_cancel_l] at h'
      simp [(hnmem _).1 hab, (hmem a).1 ha, (hnmem b).1 hb]
    · have hab : xor32 a b ∉ S := by
        intro hab
        apply ha
        have h' := hS _ hab b hb
        rwa [xor32_cancel_r] at h'
      simp [(hnmem _).1 hab, (hnmem a).1 ha, (hmem b).1 hb]
    · have hab : xor32 a b ∈ S := xor32_mem_of_not_mem S hcard hS ha hb
      simp [(hmem _).1 hab, (hnmem a).1 ha, (hnmem b).1 hb]
  obtain ⟨h, hh1, hh2, hh4, hh8, hh16⟩ := dot5_basis_exists (φ 1) (φ 2) (φ 4) (φ 8) (φ 16)
  have hP : ∀ u : Fin 32, φ u = dot5 (h : ℕ) (u : ℕ) :=
    xor32_eq_of_basis φ (fun u => dot5 (h : ℕ) (u : ℕ)) hadd (fun a b => dot5_xor32 h a b)
      (by
        show φ 0 = dot5 (h : ℕ) ((0 : Fin 32) : ℕ)
        rw [hφ0, dot5_zero32])
      hh1.symm hh2.symm hh4.symm hh8.symm hh16.symm
  have hh0 : h ≠ 0 := by
    intro hh
    have hall : ∀ u : Fin 32, u ∈ S := by
      intro u
      rw [hmem u, hP u, hh]
      exact dot5_zero_left32 u
    have hSuniv : S = Finset.univ := Finset.eq_univ_iff_forall.2 hall
    rw [hSuniv, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  refine ⟨h, hh0, fun u => ?_⟩
  rw [hmem u, hP u]

theorem exists_hyperplane (A : Subgroup P24) (hA : A ≤ NQ2)
    (hcard : Nat.card A * 2 = Nat.card NQ2) :
    ∃ h : Fin 32, h ≠ 0 ∧ ∀ g : P24, g ∈ A ↔ ∃ u : Fin 32, g = nq2Perm u ∧ dot5 (h : ℕ) (u : ℕ) = false := by
  obtain ⟨S, h0, hS, rfl⟩ := exists_xorSub_of_le_NQ2 A hA
  rw [card_xorSub, card_NQ2] at hcard
  obtain ⟨h, hh0, hiff⟩ := index_two_xor32 S h0 hS (by omega)
  refine ⟨h, hh0, fun g => ?_⟩
  rw [mem_xorSub_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rfl, (hiff u).1 hu⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨u, (hiff u).2 hu, rfl⟩

end CFSG.Quasithin.RonanH154
