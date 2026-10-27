module

public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem inv_eq_self_of_sq (hV : ∀ v : V, v ^ 2 = 1) (x : V) : x⁻¹ = x := by
  have h := hV x
  rw [pow_two, mul_eq_one_iff_eq_inv] at h
  exact h.symm

theorem commV_zpowers_le_fixV_b4 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} (hg : g ^ 2 = 1) :
    commV (Subgroup.zpowers g) ≤ fixV (Subgroup.zpowers g) :=
  CFSG.Quasithin.commV_zpowers_le_fixV_of_involution hV hg

theorem card_eq_two_pow_top [Finite V] (hV : ∀ v : V, v ^ 2 = 1) : Nat.card V = 2 ^ rk V := by
  have := card_eq_two_pow hV (⊤ : Subgroup V)
  rwa [Subgroup.card_top, rk_top] at this

theorem card_commV_mul_card_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) :
    Nat.card (commV (Subgroup.zpowers g)) * Nat.card (fixV (Subgroup.zpowers g)) =
      Nat.card V := by
  rw [card_eq_two_pow hV (commV (Subgroup.zpowers g)),
    card_eq_two_pow hV (fixV (Subgroup.zpowers g)), ← pow_add, rk_commV_add_rk_fixV,
    card_eq_two_pow_top hV]

theorem commV_zpowers_eq_bot_iff {g : MulAut V} : commV (Subgroup.zpowers g) = ⊥ ↔ g = 1 := by
  rw [commV_eq_commSub, commSub_eq_bot_iff]
  constructor
  · intro h
    ext v
    have := h (Subgroup.mem_top v)
    rw [mem_fixV_zpowers_iff] at this
    simpa using this
  · rintro rfl
    intro v _
    rw [mem_fixV_zpowers_iff]
    simp

theorem commHom_mem_commV (g : MulAut V) (v : V) :
    g v * v⁻¹ ∈ commV (Subgroup.zpowers g) :=
  Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, v, rfl⟩

theorem bounds_of_transvections [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {G : Subgroup (MulAut V)} {t₁ t₂ t₃ : MulAut V}
    (hgen : ∀ S : Subgroup (MulAut V), t₁ ∈ S → t₂ ∈ S → t₃ ∈ S → G ≤ S)
    (c₁ : Nat.card (fixV (Subgroup.zpowers t₁)) = 8) (c₂ : Nat.card (fixV (Subgroup.zpowers t₂)) = 8)
    (c₃ : Nat.card (fixV (Subgroup.zpowers t₃)) = 8) :
    Nat.card (commV G) ≤ 8 ∧ Nat.card V ≤ 8 * Nat.card (fixV G) := by
  have hr : ∀ t : MulAut V, Nat.card (fixV (Subgroup.zpowers t)) = 8 →
      Nat.card (commV (Subgroup.zpowers t)) = 2 := by
    intro t ht
    have h := card_commV_mul_card_fixV hV t
    rw [ht, hcard] at h
    omega
  have hsup : ∀ A B : Subgroup V, Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
    intro A B
    have h := card_sup_mul_card_inf A B
    have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
    calc Nat.card ↥(A ⊔ B) = Nat.card ↥(A ⊔ B) * 1 := by ring
      _ ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := Nat.mul_le_mul_left _ hpos
      _ = Nat.card A * Nat.card B := h
  set Y : Subgroup V := commV (Subgroup.zpowers t₁) ⊔ commV (Subgroup.zpowers t₂) ⊔
    commV (Subgroup.zpowers t₃) with hY
  have hYcard : Nat.card Y ≤ 8 := by
    calc Nat.card Y ≤ Nat.card ↥(commV (Subgroup.zpowers t₁) ⊔ commV (Subgroup.zpowers t₂)) *
          Nat.card (commV (Subgroup.zpowers t₃)) := hsup _ _
      _ ≤ (Nat.card (commV (Subgroup.zpowers t₁)) * Nat.card (commV (Subgroup.zpowers t₂))) *
          Nat.card (commV (Subgroup.zpowers t₃)) := Nat.mul_le_mul_right _ (hsup _ _)
      _ = 8 := by rw [hr t₁ c₁, hr t₂ c₂, hr t₃ c₃]
  have hGY : G ≤ centQuot Y := by
    refine hgen _ ?_ ?_ ?_
    · intro v
      exact (le_sup_left.trans le_sup_left : commV (Subgroup.zpowers t₁) ≤ Y)
        (commHom_mem_commV t₁ v)
    · intro v
      exact (le_sup_right.trans le_sup_left : commV (Subgroup.zpowers t₂) ≤ Y)
        (commHom_mem_commV t₂ v)
    · intro v
      exact (le_sup_right : commV (Subgroup.zpowers t₃) ≤ Y) (commHom_mem_commV t₃ v)
  refine ⟨?_, ?_⟩
  · have : commV G ≤ Y := by
      unfold commV
      rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      exact hGY hx v
    exact (Subgroup.card_le_of_le this).trans hYcard
  ·
    have hF : fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂) ⊓
        fixV (Subgroup.zpowers t₃) ≤ fixV G := by
      intro v hv g hg
      have hS : G ≤ MulAction.stabilizer (MulAut V) v := by
        refine hgen _ ?_ ?_ ?_
        · exact (mem_fixV_zpowers_iff.mp hv.1.1)
        · exact (mem_fixV_zpowers_iff.mp hv.1.2)
        · exact (mem_fixV_zpowers_iff.mp hv.2)
      exact hS hg
    have hi : ∀ t : MulAut V, Nat.card (fixV (Subgroup.zpowers t)) = 8 →
        (fixV (Subgroup.zpowers t)).index = 2 := by
      intro t ht
      have h := Subgroup.card_mul_index (fixV (Subgroup.zpowers t))
      rw [ht, hcard] at h
      omega
    have hidx : (fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂) ⊓
        fixV (Subgroup.zpowers t₃)).index ≤ 8 := by
      calc _ ≤ (fixV (Subgroup.zpowers t₁) ⊓ fixV (Subgroup.zpowers t₂)).index *
            (fixV (Subgroup.zpowers t₃)).index := Subgroup.index_inf_le
        _ ≤ ((fixV (Subgroup.zpowers t₁)).index * (fixV (Subgroup.zpowers t₂)).index) *
            (fixV (Subgroup.zpowers t₃)).index :=
          Nat.mul_le_mul_right _ (Subgroup.index_inf_le)
        _ = 8 := by rw [hi t₁ c₁, hi t₂ c₂, hi t₃ c₃]
    have hidx' : (fixV G).index ≤ 8 :=
      (Subgroup.index_antitone hF).trans hidx
    have h := Subgroup.card_mul_index (fixV G)
    calc Nat.card V = Nat.card (fixV G) * (fixV G).index := h.symm
      _ ≤ Nat.card (fixV G) * 8 := Nat.mul_le_mul_left _ hidx'
      _ = 8 * Nat.card (fixV G) := by ring

end CFSG.Quasithin
