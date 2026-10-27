module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAltTenA
public import CFSG.Quasithin.H13.VolIAltCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverAltTenBK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.VolI CFSG.Quasithin.G6 Subgroup Equiv

@[expose] def s16c11_v1_ev10 (i j : Fin 10) : PermMod 10 :=
  Multiplicative.ofAdd fun k => if k = i ∨ k = j then 1 else 0

@[expose] def s16c11_v1_comm4 (σ τ υ ω : ↥(alternatingGroup (Fin 10))) (a b c d : PermMod 10) :
    PermMod 10 :=
  permAct 10 (σ : Perm (Fin 10)) a * a⁻¹ * (permAct 10 (τ : Perm (Fin 10)) b * b⁻¹) *
    (permAct 10 (υ : Perm (Fin 10)) c * c⁻¹) * (permAct 10 (ω : Perm (Fin 10)) d * d⁻¹)

theorem s16c11_v1_comm4_mem (σ τ υ ω : ↥(alternatingGroup (Fin 10))) {a b c d : PermMod 10}
    (ha : a ∈ coreMod 10) (hb : b ∈ coreMod 10) (hc : c ∈ coreMod 10) (hd : d ∈ coreMod 10) :
    s16c11_v1_comm4 σ τ υ ω a b c d ∈ coreMod 10 :=
  mul_mem (mul_mem (mul_mem (mul_mem (permAct_mem_coreMod _ ha) (inv_mem ha))
    (mul_mem (permAct_mem_coreMod _ hb) (inv_mem hb)))
    (mul_mem (permAct_mem_coreMod _ hc) (inv_mem hc)))
    (mul_mem (permAct_mem_coreMod _ hd) (inv_mem hd))

@[expose] def s16c11_v1_lifts123Ten : List (PermMod 10) :=
  [1, s16c11_v1_ev10 1 0, s16c11_v1_ev10 2 0, s16c11_v1_ev10 3 0]

@[expose] def s16c11_v1_lifts345Ten : List (PermMod 10) :=
  [1, s16c11_v1_ev10 3 0, s16c11_v1_ev10 4 0, s16c11_v1_ev10 5 0]

@[expose] def s16c11_v1_lifts567Ten : List (PermMod 10) :=
  [1, s16c11_v1_ev10 5 0, s16c11_v1_ev10 6 0, s16c11_v1_ev10 7 0]

@[expose] def s16c11_v1_lifts789Ten : List (PermMod 10) :=
  [1, s16c11_v1_ev10 7 0, s16c11_v1_ev10 8 0, s16c11_v1_ev10 9 0]

theorem s16c11_v1_lifts123Ten_mem : ∀ a ∈ s16c11_v1_lifts123Ten, a ∈ coreMod 10 := by
  simp only [mem_coreMod]
  decide +kernel

theorem s16c11_v1_lifts345Ten_mem : ∀ a ∈ s16c11_v1_lifts345Ten, a ∈ coreMod 10 := by
  simp only [mem_coreMod]
  decide +kernel

theorem s16c11_v1_lifts567Ten_mem : ∀ a ∈ s16c11_v1_lifts567Ten, a ∈ coreMod 10 := by
  simp only [mem_coreMod]
  decide +kernel

theorem s16c11_v1_lifts789Ten_mem : ∀ a ∈ s16c11_v1_lifts789Ten, a ∈ coreMod 10 := by
  simp only [mem_coreMod]
  decide +kernel

theorem s16c11_v1_evenOn_ten_123_card : (evenOn (1 : Fin 10) 2 3).card = 4 := by decide +kernel

theorem s16c11_v1_evenOn_ten_345_card : (evenOn (3 : Fin 10) 4 5).card = 4 := by decide +kernel

theorem s16c11_v1_evenOn_ten_567_card : (evenOn (5 : Fin 10) 6 7).card = 4 := by decide +kernel

theorem s16c11_v1_evenOn_ten_789_card : (evenOn (7 : Fin 10) 8 9).card = 4 := by decide +kernel

theorem s16c11_v1_comm_mem_evenOn_ten_123 : ∀ m : PermMod 10,
    permAct 10 (s16c11_v1_c123 : Perm (Fin 10)) m * m⁻¹ ∈ evenOn 1 2 3 := by
  refine S16V1K.comm_mem_of (cs := [1, 4, 8, 2, 16, 32, 64, 128, 256, 512]) (B := [6, 12]) rfl
    (by decide +kernel) (by decide +kernel) ?_
  simp only [evenOn, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

theorem s16c11_v1_comm_mem_evenOn_ten_345 : ∀ m : PermMod 10,
    permAct 10 (s16c11_v1_c345 : Perm (Fin 10)) m * m⁻¹ ∈ evenOn 3 4 5 := by
  refine S16V1K.comm_mem_of (cs := [1, 2, 4, 16, 32, 8, 64, 128, 256, 512]) (B := [24, 48]) rfl
    (by decide +kernel) (by decide +kernel) ?_
  simp only [evenOn, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

theorem s16c11_v1_comm_mem_evenOn_ten_567 : ∀ m : PermMod 10,
    permAct 10 (s16c11_v1_c567 : Perm (Fin 10)) m * m⁻¹ ∈ evenOn 5 6 7 := by
  refine S16V1K.comm_mem_of (cs := [1, 2, 4, 8, 16, 64, 128, 32, 256, 512]) (B := [96, 192]) rfl
    (by decide +kernel) (by decide +kernel) ?_
  simp only [evenOn, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

theorem s16c11_v1_comm_mem_evenOn_ten_789 : ∀ m : PermMod 10,
    permAct 10 (s16c11_v1_c789 : Perm (Fin 10)) m * m⁻¹ ∈ evenOn 7 8 9 := by
  refine S16V1K.comm_mem_of (cs := [1, 2, 4, 8, 16, 32, 64, 256, 512, 128]) (B := [384, 768])
    rfl (by decide +kernel) (by decide +kernel) ?_
  simp only [evenOn, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

theorem s16c11_v1_coreMod_ten_eq : ∀ m : PermMod 10, m ∈ coreMod 10 →
    ∃ a ∈ s16c11_v1_lifts123Ten, ∃ b ∈ s16c11_v1_lifts345Ten,
      ∃ c ∈ s16c11_v1_lifts567Ten, ∃ d ∈ s16c11_v1_lifts789Ten,
        m = s16c11_v1_comm4 s16c11_v1_c123 s16c11_v1_c345 s16c11_v1_c567 s16c11_v1_c789 a b c d ∨
          m = s16c11_v1_comm4 s16c11_v1_c123 s16c11_v1_c345 s16c11_v1_c567 s16c11_v1_c789
            a b c d * allOnes 10 := by
  have h1 : s16c11_v1_lifts123Ten.map
      (fun a => permAct 10 (s16c11_v1_c123 : Perm (Fin 10)) a * a⁻¹) =
        S16V1K.X1.map (H.Mathieu.toW 10) := by decide +kernel
  have h2 : s16c11_v1_lifts345Ten.map
      (fun a => permAct 10 (s16c11_v1_c345 : Perm (Fin 10)) a * a⁻¹) =
        S16V1K.X2.map (H.Mathieu.toW 10) := by decide +kernel
  have h3 : s16c11_v1_lifts567Ten.map
      (fun a => permAct 10 (s16c11_v1_c567 : Perm (Fin 10)) a * a⁻¹) =
        S16V1K.X3.map (H.Mathieu.toW 10) := by decide +kernel
  have h4 : s16c11_v1_lifts789Ten.map
      (fun a => permAct 10 (s16c11_v1_c789 : Perm (Fin 10)) a * a⁻¹) =
        S16V1K.X4.map (H.Mathieu.toW 10) := by decide +kernel
  have hone : allOnes 10 = H.Mathieu.toW 10 1023 := by decide +kernel
  exact S16V1K.coreMod_of h1 h2 h3 h4 hone

theorem s16c11_v1_allOnes_ten_mem : allOnes 10 ∈ coreMod 10 := by
  rw [mem_coreMod]
  decide

theorem s16c11_v1_orderOf_allOnes_ten : orderOf (allOnes 10) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem s16c11_v1_card_coreMod_ten : Nat.card (coreMod 10) = 512 := by
  have h : (coreMod 10 : Set (PermMod 10)) =
      ↑(Finset.univ.filter fun x : PermMod 10 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide +kernel

theorem s16c11_v1_mk_eq_mk_iff_ten {m m' : ↥(coreMod 10)} :
    (QuotientGroup.mk m : DnQuot 10) = QuotientGroup.mk m' ↔
      (m' : PermMod 10) = m ∨ (m' : PermMod 10) = m * allOnes 10 := by
  rw [QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv, mem_inf]
  constructor
  · rintro ⟨h, -⟩
    rw [mem_zpowers_iff_mem_range_orderOf, s16c11_v1_orderOf_allOnes_ten] at h
    simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨k, hk, hk'⟩ := h
    interval_cases k
    · left
      rw [pow_zero, eq_comm, inv_mul_eq_one] at hk'
      exact hk'.symm
    · right
      rw [pow_one, eq_comm, inv_mul_eq_iff_eq_mul] at hk'
      exact hk'
  · rintro (h | h)
    · rw [h, inv_mul_cancel]
      exact ⟨one_mem _, one_mem _⟩
    · rw [h, inv_mul_cancel_left]
      exact ⟨mem_zpowers _, s16c11_v1_allOnes_ten_mem⟩

theorem s16c11_v1_card_dnQuot_ten : Nat.card (DnQuot 10) = 256 := by
  have hle : zpowers (allOnes 10) ≤ coreMod 10 := zpowers_le.2 s16c11_v1_allOnes_ten_mem
  have hN : Nat.card ((zpowers (allOnes 10) ⊓ coreMod 10).subgroupOf (coreMod 10)) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, inf_eq_left.2 hle,
      Nat.card_zpowers, s16c11_v1_orderOf_allOnes_ten]
  have h := card_eq_card_quotient_mul_card_subgroup
    ((zpowers (allOnes 10) ⊓ coreMod 10).subgroupOf (coreMod 10))
  rw [s16c11_v1_card_coreMod_ten, hN] at h
  show Nat.card (↥(coreMod 10) ⧸ (zpowers (allOnes 10) ⊓ coreMod 10).subgroupOf (coreMod 10)) =
    256
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
