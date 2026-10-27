module

public import CFSG.Quasithin.Recognition.J2RecQ8D8

public section

namespace CFSG.Quasithin

theorem card_preimage_of_surjective {G P : Type*} [Group G] [Group P] (φ : G →* P)
    (hφ : Function.Surjective φ) (T : Set P) :
    Nat.card (φ ⁻¹' T) = Nat.card φ.ker * Nat.card T := by
  obtain ⟨s, hs⟩ := hφ.hasRightInverse
  have e : (φ ⁻¹' T) ≃ φ.ker × T :=
    { toFun := fun p => (⟨(s (φ p.1))⁻¹ * p.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]⟩, ⟨φ p.1, p.2⟩)
      invFun := fun q => ⟨s q.2.1 * q.1.1, by
          show φ (s q.2.1 * q.1.1) ∈ T
          rw [map_mul, hs, MonoidHom.mem_ker.mp q.1.2, mul_one]
          exact q.2.2⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp
      right_inv := fun q => by
        obtain ⟨⟨k, hk⟩, ⟨t, ht⟩⟩ := q
        have hk' : φ k = 1 := hk
        have h1 : φ (s t * k) = t := by rw [map_mul, hs, hk', mul_one]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show (s (φ (s t * k)))⁻¹ * (s t * k) = k
          rw [h1, inv_mul_cancel_left]
        · exact h1 }
  rw [Nat.card_congr e, Nat.card_prod]

private theorem card_sq_mem_kernel :
    Nat.card {p : QuaternionGroup 2 × DihedralGroup 4 //
      p * p = 1 ∨ p * p = (QuaternionGroup.a 2, DihedralGroup.r 2)} = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem IsQ8D8.card_sq_eq_one {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P) :
    Nat.card {x : P // x * x = 1} = 12 := by
  obtain ⟨φ, hsurj, hφeq, -, -⟩ := h.exists_hom
  have hcard : Nat.card P = 32 := h.1
  have hκ : φ (QuaternionGroup.a 2, DihedralGroup.r 2) = 1 := by
    have h1 : ((QuaternionGroup.a 2, DihedralGroup.r 2) :
        QuaternionGroup 2 × DihedralGroup 4) =
        (QuaternionGroup.a 2, 1) * (1, DihedralGroup.r 2) := by simp
    have h2 : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) *
        (QuaternionGroup.a 2, 1) = 1 := by decide
    rw [h1, map_mul, ← hφeq, ← map_mul, h2, map_one]
  have hκne : ((QuaternionGroup.a 2, DihedralGroup.r 2) :
      QuaternionGroup 2 × DihedralGroup 4) ≠ 1 := by decide
  have hcardG : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 64 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hkercard : Nat.card φ.ker = 2 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcard,
      hcardG] at h1
    omega
  have hker : ∀ p : QuaternionGroup 2 × DihedralGroup 4,
      φ p = 1 ↔ p = 1 ∨ p = (QuaternionGroup.a 2, DihedralGroup.r 2) := by
    intro p
    constructor
    · intro hp
      obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : φ.ker)).1 hkercard
      by_cases hp1 : p = 1
      · exact Or.inl hp1
      · right
        have e1 : (⟨p, hp⟩ : φ.ker) = y := huniq _ (fun h' => hp1 (congrArg Subtype.val h'))
        have e2 : (⟨_, hκ⟩ : φ.ker) = y := huniq _ (fun h' => hκne (congrArg Subtype.val h'))
        exact congrArg Subtype.val (e1.trans e2.symm)
    · rintro (rfl | rfl)
      · exact map_one φ
      · exact hκ
  have hpre := card_preimage_of_surjective φ hsurj {x : P | x * x = 1}
  have e : (φ ⁻¹' {x : P | x * x = 1}) ≃
      {p : QuaternionGroup 2 × DihedralGroup 4 //
        p * p = 1 ∨ p * p = (QuaternionGroup.a 2, DihedralGroup.r 2)} :=
    Equiv.subtypeEquivRight (fun p => by
      show φ p * φ p = 1 ↔ _
      rw [← map_mul, hker])
  rw [Nat.card_congr e, card_sq_mem_kernel, hkercard] at hpre
  have h3 : Nat.card ↑{x : P | x * x = 1} = Nat.card {x : P // x * x = 1} := rfl
  omega

end CFSG.Quasithin
