module

public import CFSG.Quasithin.Background.Asc81cPfOrd3
public import CFSG.Quasithin.Background.Asc81cPfOdd3

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] [Finite W]

section Sub

theorem mParam_le_mParam {G G' : Subgroup (MulAut W)} (h : G' ≤ G) :
    E3.mParam G ≤ E3.mParam G' := by
  have := finite_mulAut (W := W)
  have hrk : ∀ K : Subgroup W, rkIdx K ≤ rk W := fun K => by
    have := rk_add_rkIdx K
    omega
  have hne : ∀ K : Subgroup (MulAut W), Even (Nat.card K) →
      ∃ t ∈ K, orderOf t = 2 := fun K hK => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.1 hK)
    exact ⟨t, t.2, by rw [Subgroup.orderOf_coe, ht]⟩
  unfold E3.mParam
  by_cases hG' : Even (Nat.card G')
  · have hG : Even (Nat.card G) := (even_iff_two_dvd.2 ((even_iff_two_dvd.1 hG').trans
      (Subgroup.card_dvd_of_le h)))
    simp only [hG, hG', ↓reduceIte]
    obtain ⟨t, ht, ht2⟩ := hne G' hG'
    have hne' : Set.Nonempty
        {n | ∃ t ∈ G', orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} :=
      ⟨rkIdx (fixV (Subgroup.zpowers t)), t, ht, ht2, rfl⟩
    have hmem := Nat.sInf_mem hne'
    obtain ⟨s, hs, hs2, hseq⟩ := hmem
    rw [hseq]
    exact Nat.sInf_le ⟨s, h hs, hs2, rfl⟩
  · simp only [hG', ↓reduceIte]
    split_ifs with hG
    · obtain ⟨t, ht, ht2⟩ := hne G hG
      have h1 : sInf {n | ∃ t ∈ G, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} ≤
          rkIdx (fixV (Subgroup.zpowers t)) := Nat.sInf_le ⟨t, ht, ht2, rfl⟩
      exact h1.trans (hrk _)
    · exact le_rfl

theorem hyp102_of_le {G G' X : Subgroup (MulAut W)} (h : Hyp102 G X) (hG' : G' ≤ G)
    (hX : X ≤ G') : Hyp102 G' X :=
  ⟨⟨hX, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, fun g hg => h.1.2.2.2.2.2 g (hG' hg)⟩,
    lt_of_lt_of_le h.2 (mParam_le_mParam hG')⟩

theorem card_eq_three_or_seven_le (hW : ∀ w : W, w ^ 2 = 1) {G X : Subgroup (MulAut W)}
    (hX : Hyp101 G X) : Nat.card X = 3 ∨ 7 ≤ Nat.card X := by
  have h1 := card_commSub hX
  rw [card_eq_two_pow hW] at h1
  have h2 : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot _).2 hX.2.1
  have h3 : rk (commSub (⊤ : Subgroup W) X) ≠ 0 := fun h => by
    rw [h, pow_zero] at h1
    omega
  have h4 : rk (commSub (⊤ : Subgroup W) X) ≠ 1 := fun h => by
    rw [h, pow_one] at h1
    omega
  rcases Nat.lt_or_ge (rk (commSub (⊤ : Subgroup W) X)) 3 with h5 | h5
  · have h6 : rk (commSub (⊤ : Subgroup W) X) = 2 := by omega
    rw [h6] at h1
    left
    omega
  · right
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h5
    omega

open scoped Pointwise in
theorem card_sup_of_le_normalizer {Γ : Type*} [Group Γ] {X Y : Subgroup Γ}
    (hXN : X ≤ Subgroup.normalizer (Y : Set Γ)) (hXY : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right X Y hXN
  let f : ↥X × ↥Y → ↥(X ⊔ Y) := fun p =>
    ⟨p.1 * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h1 : (a : Γ) * b = a' * b' := congrArg Subtype.val hab
      have h2 : (a' : Γ)⁻¹ * a = b' * (b : Γ)⁻¹ := by
        calc (a' : Γ)⁻¹ * a = (a' : Γ)⁻¹ * (a * b) * (b : Γ)⁻¹ := by group
          _ = (a' : Γ)⁻¹ * (a' * b') * (b : Γ)⁻¹ := by rw [h1]
          _ = b' * (b : Γ)⁻¹ := by group
      have h3 : (a' : Γ)⁻¹ * a ∈ X ⊓ Y := ⟨X.mul_mem (X.inv_mem a'.2) a.2, h2 ▸
        Y.mul_mem b'.2 (Y.inv_mem b.2)⟩
      rw [hXY, Subgroup.mem_bot] at h3
      have ha : a = a' := Subtype.ext (inv_mul_eq_one.1 h3).symm
      have hb : b = b' := Subtype.ext (by
        rw [ha] at h1
        exact mul_left_cancel h1)
      rw [ha, hb]
    · rintro ⟨g, hg⟩
      have hg' : g ∈ ((X : Set Γ) * (Y : Set Γ)) := by rw [← hset]; exact hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

end Sub

section Pair

variable {G X Y : Subgroup (MulAut W)}

theorem eq_of_card_seven_le (hW : ∀ w : W, w ^ 2 = 1) {Z Z' : Subgroup (MulAut W)}
    (hZ : Hyp101 G Z) (hZ' : Hyp101 G Z') (h7 : 7 ≤ Nat.card Z) (h7' : 7 ≤ Nat.card Z')
    (h21 : Nat.card ↥(Z ⊔ Z') = 21) : Z = Z' := by
  have hdvd : ∀ T : Subgroup (MulAut W), T ≤ Z ⊔ Z' → Hyp101 G T → 7 ≤ Nat.card T →
      Nat.card T = 7 := by
    intro T hT hT1 hT7
    have h1 : Nat.card T ∣ 21 := h21 ▸ Subgroup.card_dvd_of_le hT
    rcases card_eq_three_or_seven_le hW hT1 with h3 | h3
    · omega
    · have h2 : Nat.card T ≤ 21 := Nat.le_of_dvd (by norm_num) h1
      interval_cases h : Nat.card T <;> first | rfl | (norm_num at h1)
      have h4 := card_commSub hT1
      rw [card_eq_two_pow hW, h] at h4
      have h5 : rk (commSub (⊤ : Subgroup W) T) < 5 := by
        by_contra h6
        push Not at h6
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h6
        omega
      interval_cases rk (commSub (⊤ : Subgroup W) T) <;> omega
  exact eq_of_card_seven h21 le_sup_left le_sup_right (hdvd Z le_sup_left hZ h7)
    (hdvd Z' le_sup_right hZ' h7')

theorem pair_theorem (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp102 G X)
    (hY : Hyp102 G Y) : Commutes X Y ∨ Nat.card ↥(X ⊔ Y) = 21 := by
  suffices key : ∀ N : ℕ, ∀ (G X Y : Subgroup (MulAut W)), Nat.card ↥(X ⊔ Y) = N →
      Hyp102 G X → Hyp102 G Y → 7 ≤ Nat.card Y → Commutes X Y ∨ Nat.card ↥(X ⊔ Y) = 21 by
    rcases card_eq_three_or_seven_le hW hY.1 with hY3 | hY7
    · rcases card_eq_three_or_seven_le hW hX.1 with hX3 | hX7
      · exact ord3_pair hW hX hY hX3 hY3
      · rcases key _ G Y X rfl hY hX hX7 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [sup_comm]; exact h)
    · exact key _ G X Y rfl hX hY hY7
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro G X Y hN hX hY hY7
  have := finite_mulAut (W := W)
  set G' := X ⊔ Y with hG'
  have hG'G : G' ≤ G := sup_le hX.1.1 hY.1.1
  have hX' : Hyp102 G' X := hyp102_of_le hX hG'G le_sup_left
  have hY' : Hyp102 G' Y := hyp102_of_le hY hG'G le_sup_right
  set Δ : Set (Subgroup (MulAut W)) := {Z | ∃ g ∈ G', Z = Y.map (MulAut.conj g).toMonoidHom}
    with hΔ
  have hYΔ : Y ∈ Δ := ⟨1, G'.one_mem, by rw [map_conj_one]⟩
  have hcard : ∀ Z ∈ Δ, Nat.card Z = Nat.card Y := by
    rintro Z ⟨g, -, rfl⟩
    exact (Nat.card_congr (Subgroup.equivMapOfInjective Y _
      (MulEquiv.injective (MulAut.conj g))).toEquiv).symm
  have hT : TransSetting G' Δ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro Z ⟨g, hg, rfl⟩
      exact hyp102_map_conj hY' hg
    · rintro g hg Z ⟨h, hh, rfl⟩
      exact ⟨g * h, G'.mul_mem hg hh, by rw [map_conj_map_conj]⟩
    · rintro Z ⟨g, hg, rfl⟩ Z' ⟨h, hh, rfl⟩
      exact ⟨h * g⁻¹, G'.mul_mem hh (G'.inv_mem hg), by
        rw [map_conj_map_conj, mul_assoc, inv_mul_cancel, mul_one]⟩
    · intro Z hZ Z' hZ'
      have hZh : Hyp102 G' Z := by
        obtain ⟨g, hg, rfl⟩ := hZ
        exact hyp102_map_conj hY' hg
      have hZ'h : Hyp102 G' Z' := by
        obtain ⟨g, hg, rfl⟩ := hZ'
        exact hyp102_map_conj hY' hg
      by_cases hsup : Z ⊔ Z' = G'
      · exact Or.inr hsup
      · left
        have hle : Z ⊔ Z' ≤ G' := sup_le hZh.1.1 hZ'h.1.1
        have hlt : Nat.card ↥(Z ⊔ Z') < N := by
          rw [← hN]
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h => hsup ?_
          exact Subgroup.eq_of_le_of_card_ge hle h.ge
        rcases ih _ hlt G' Z Z' rfl hZh hZ'h (by rw [hcard Z' hZ']; exact hY7) with h | h
        · exact h
        · have := eq_of_card_seven_le hW hZh.1 hZ'h.1 (by rw [hcard Z hZ]; exact hY7)
            (by rw [hcard Z' hZ']; exact hY7) h
          subst this
          exact commutes_self_of_isCyclic hZh.1.2.2.1
  have hcomm : ∀ Z ∈ Δ, ∀ Z' ∈ Δ, Commutes Z Z' := fun Z hZ Z' hZ' =>
    hT.commutes hW hZ hZ' (by rw [hcard Z hZ]; exact hY7)
  by_cases hXΔ : X ∈ Δ
  · exact Or.inl (hcomm X hXΔ Y hYΔ)
  have hXN : ∀ x ∈ X, Y.map (MulAut.conj x).toMonoidHom = Y := by
    refine ten_eight hW hY' hX'.1 fun x hx x' hx' a ha b hb => ?_
    exact hcomm _ ⟨x, Subgroup.mem_sup_left hx, rfl⟩ _ ⟨x', Subgroup.mem_sup_left hx', rfl⟩ a ha
      b hb
  have hXN' : X ≤ Subgroup.normalizer (Y : Set (MulAut W)) := fun x hx =>
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hXN x hx)
  by_cases hXY : Commutes X Y
  · exact Or.inl hXY
  right
  have hnc : ∃ y ∈ Y, ∃ x ∈ X, y * x ≠ x * y := by
    by_contra hall
    push Not at hall
    exact hXY fun x hx y hy => (hall y hy x hx).symm
  obtain ⟨hY7', hX3⟩ := ten_six hW hY'.1 hX'.1 hXN' hnc
  have hbot : X ⊓ Y = ⊥ := by
    have h1 : Nat.card ↥(X ⊓ Y) ∣ 3 := hX3 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(X ⊓ Y) ∣ 7 := hY7' ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(X ⊓ Y) = 1 := by
      have := Nat.dvd_gcd h1 h2
      simpa using this
    exact Subgroup.eq_bot_of_card_eq _ h3
  rw [card_sup_of_le_normalizer hXN' hbot, hX3, hY7']

end Pair

end Pf

end Asc81c

end CFSG.Quasithin
