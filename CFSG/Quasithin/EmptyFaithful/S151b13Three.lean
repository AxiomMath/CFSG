module

public import CFSG.Quasithin.EmptyFaithful.S151bRank

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

section Glue

variable {M V : Subgroup G}

theorem mem_QhatStarOn_iff151b (hV : IsElemAbelian 2 V) (A : Subgroup (MulAut ↥V)) :
    A ∈ QhatStarOn M V ↔ A ∈ QhatStar (autI hV M) := by
  unfold QhatStarOn
  rw [dite_eq_left hV]
  exact Iff.rfl

theorem qhatOn_eq_qhatOf151b (hV : IsElemAbelian 2 V) : qhatOn M V = qhatOf (autI hV M) := by
  rw [qhatOn_eq hV]
  rfl

theorem qOn_eq_qOf151b (hV : IsElemAbelian 2 V) : qOn M V = qOf (autI hV M) := by
  rw [qOn_eq hV]
  rfl

end Glue

theorem rAV_autI_eq_of_exact151b {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hA2 : IsElemAbelian2 (autI hV A)) {k : ℕ}
    (hk : rk (autI hV A) = k)
    (hexact : Nat.card V = 2 * Nat.card (autI hV A) *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :
    rAV (autI hV A) = ((k + 1 : ℕ) : ℚ) / (k : ℚ) := by
  have hAcard : Nat.card (autI hV A) = 2 ^ k := by rw [B1.card_elemAbelian hA2, hk]
  have hfix := card_fixV_autI hV hAN
  have hidx := Subgroup.index_mul_card (fixV (autI hV A))
  have hVcard : Nat.card (IntMod V hV) = Nat.card V := rfl
  have hcpos : 0 < Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hindex : (fixV (autI hV A)).index = 2 ^ (k + 1) := by
    rw [hfix, hVcard, hexact, hAcard] at hidx
    have : (fixV (autI hV A)).index *
        Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
        2 ^ (k + 1) * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
      rw [hidx, pow_succ]
      ring
    exact Nat.eq_of_mul_eq_mul_right hcpos this
  unfold rAV rkIdx
  rw [hindex, hk, padicValNat.prime_pow]

section Core

variable {T M V A : Subgroup G}

theorem corank_one_mem_QhatStar151b (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hqhat : qhatOf (autI hV M) = ((2 : ℚ) : WithTop ℚ))
    (hq : qOf (autI hV M) = ((2 : ℚ) : WithTop ℚ))
    (hrank : ∀ E : Subgroup (MulAut (IntMod V hV)), E ≤ autI hV T → IsElemAbelian2 E →
      Nat.card E ≤ 4)
    (hA : IsElemAbelianCorank T 1 A) (hA1 : autI hV A ≠ ⊥) :
    Nat.card (autI hV A) = 2 ∧ autI hV A ∈ QhatStar (autI hV M) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTN
  have hAM : A ≤ M := hA.1.trans hTM
  have hA1' : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hA1 ((autI_eq_bot_iff hV hAN).mpr h)
  have hW : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hFF : ¬ IsFFModule (autI hV M) := by
    intro hff
    have h1 := ((B1_4_5 hW (autI hV M)).out 1 3).mp hff
    rw [hq] at h1
    have h2 : (2 : ℚ) ≤ 1 := by exact_mod_cast h1
    norm_num at h2
  have hexact := card_eq_two_mul_of_corank_one151b hV hVT hTN hJ hA hA1' hAM hMN hFF
  have hA2 : IsA2 (autI hV M) (autI hV A) := isA2_autI hV hMN hAM hA.2.1 hA1'
  have hAT : autI hV A ≤ autI hV T := autI_mono hV hA.1
  have hcard4 : Nat.card (autI hV A) ≤ 4 := hrank _ hAT hA2.2.2
  have hcub : commSeries (autI hV A) 3 = ⊥ :=
    commSeries_three_eq_bot_of_card_le_four151b hW hA2.2.2 hcard4
  have hAcard : Nat.card (autI hV A) = 2 ^ rk (autI hV A) := B1.card_elemAbelian hA2.2.2
  have hrkpos : 0 < rk (autI hV A) := by
    rcases Nat.eq_zero_or_pos (rk (autI hV A)) with h0 | h0
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hA2.2.2.isPGroup).mp h0) hA2.2.1
    · exact h0
  have hrkle : rk (autI hV A) ≤ 2 := by
    by_contra hgt
    have : 2 ^ 3 ≤ 2 ^ rk (autI hV A) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hqhat' : (((2 : ℚ) : WithTop ℚ)) ≤ kq (autI hV M) 3 := hqhat.ge
  have hge := le_kq_iff.mp hqhat' (autI hV A) hA2 hcub
  have hr := rAV_autI_eq_of_exact151b hV hAN hA2.2.2 rfl hexact
  have hk1 : rk (autI hV A) = 1 := by
    by_contra hne
    have hk2 : rk (autI hV A) = 2 := by omega
    rw [hr, hk2] at hge
    norm_num at hge
  refine ⟨by rw [hAcard, hk1]; norm_num, ?_⟩
  rw [hk1] at hr
  have hr2 : rAV (autI hV A) = 2 := by rw [hr]; norm_num
  refine ⟨2, hqhat, le_rfl, ⟨⟨hA2, hr2.le⟩, hcub⟩, fun B hB hBA => ?_⟩
  have hBne : B ≠ ⊥ := hB.1.1.2.1
  have hBcard : 2 ≤ Nat.card B := by
    by_contra hlt
    have hpos : 0 < Nat.card B := Nat.card_pos
    exact hBne (Subgroup.card_eq_one.mp (by omega))
  have hAc2 : Nat.card (autI hV A) = 2 := by rw [hAcard, hk1]; norm_num
  exact Subgroup.eq_of_le_of_card_ge hBA (by omega)

end Core

end CFSG.Quasithin
