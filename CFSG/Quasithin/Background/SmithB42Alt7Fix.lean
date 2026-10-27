module

public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace B42Alt7

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm

theorem eq_of_six {x y : Fin 7 → ZMod 2} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0)
    {a b c d e f : Fin 7} (hnd : [a, b, c, d, e, f].Nodup)
    (h : ∀ i ∈ [a, b, c, d, e, f], x i = y i) : x = y := by
  classical
  funext g
  by_cases hg : g ∈ [a, b, c, d, e, f]
  · exact h g hg
  · have hl : (g :: [a, b, c, d, e, f]).Nodup := List.nodup_cons.2 ⟨hg, hnd⟩
    have huniv : (g :: [a, b, c, d, e, f]).toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hl]
      rfl
    have hsx := List.sum_toFinset x hl
    have hsy := List.sum_toFinset y hl
    rw [huniv, hx] at hsx
    rw [huniv, hy] at hsy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      h a (by simp), h b (by simp), h c (by simp), h d (by simp), h e (by simp),
      h f (by simp)] at hsx
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsy
    exact add_right_cancel (hsx.symm.trans hsy)

theorem eq_of_fix_R4 {x y : Fin 7 → ZMod 2} {a b c d e f : Fin 7}
    (hnd : [a, b, c, d, e, f].Nodup) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0)
    (hx1 : ∀ i, x ((swap e f)⁻¹ i) = x i) (hx2 : ∀ i, x ((swap a b * swap c d)⁻¹ i) = x i)
    (hx3 : ∀ i, x ((swap a c * swap b d)⁻¹ i) = x i)
    (hy1 : ∀ i, y ((swap e f)⁻¹ i) = y i) (hy2 : ∀ i, y ((swap a b * swap c d)⁻¹ i) = y i)
    (hy3 : ∀ i, y ((swap a c * swap b d)⁻¹ i) = y i) (ha : x a = y a) (he : x e = y e) :
    x = y := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hab, hac, had, -, -⟩, ⟨-, -, -, -⟩, ⟨hcd, -, -⟩, -, -⟩ := hnd'
  have kb : ∀ z : Fin 7 → ZMod 2, (∀ i, z ((swap a b * swap c d)⁻¹ i) = z i) → z b = z a := by
    intro z hz
    have h := hz b
    rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne hac had] at h
    exact h.symm
  have kc : ∀ z : Fin 7 → ZMod 2, (∀ i, z ((swap a c * swap b d)⁻¹ i) = z i) → z c = z a := by
    intro z hz
    have h := hz c
    rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne hab had] at h
    exact h.symm
  have kd : ∀ z : Fin 7 → ZMod 2, (∀ i, z ((swap a c * swap b d)⁻¹ i) = z i) → z d = z b := by
    intro z hz
    have h := hz d
    rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply,
      swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hcd), swap_apply_right] at h
    exact h.symm
  have kf : ∀ z : Fin 7 → ZMod 2, (∀ i, z ((swap e f)⁻¹ i) = z i) → z f = z e := by
    intro z hz
    have h := hz f
    rw [swap_inv, swap_apply_right] at h
    exact h.symm
  refine eq_of_six hx hy hnd ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha
  · rw [kb x hx2, kb y hy2, ha]
  · rw [kc x hx3, kc y hy3, ha]
  · rw [kd x hx3, kd y hy3, kb x hx2, kb y hy2, ha]
  · exact he
  · rw [kf x hx1, kf y hy1, he]

variable {S : Type} [CommGroup S]

theorem realizesVia_of_equivariant {D : FFModel} (hD : D.IsActionModel) (hker : D.ker = ⊥)
    (H : Subgroup (MulAut S)) (π : D.Gam →* ↥H) (hπ : Function.Surjective π)
    (β : S ≃* ↥D.sec)
    (hβ : ∀ (γ : D.Gam) (s : S), (β (((π γ : ↥H) : MulAut S) s) : D.Amb) = D.act γ (β s)) :
    D.RealizesVia H ⊤ ⊥ π := by
  refine ⟨hπ, le_top, hD.ker_le, fun _ u _ => trivial,
    fun _ z hz => by simpa using hz, hD.sec_inv, hD.ker_inv, ?_⟩
  refine ⟨(QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
    (β.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom), ?_, ?_, ?_⟩
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨β.symm m, trivial⟩, by simp⟩
  · intro u
    show (QuotientGroup.mk (β (u : S)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot,
      Subgroup.mem_bot]
    constructor
    · intro h
      have : β (u : S) = 1 := Subtype.ext h
      exact β.injective (by rw [this, map_one])
    · intro h
      rw [h, map_one]
      rfl
  · intro γ u m hu hm hum
    have hu' : (QuotientGroup.mk (β (u : S)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
        QuotientGroup.mk m := hum
    have hbm : β (u : S) = m := by
      have := QuotientGroup.eq.1 hu'
      rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot] at this
      have h2 : ((β (u : S))⁻¹ * m : ↥D.sec) = 1 := Subtype.ext this
      exact inv_mul_eq_one.1 h2
    show (QuotientGroup.mk (β (((π γ : ↥H) : MulAut S) (u : S))) :
      ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    congr 1
    apply Subtype.ext
    rw [hβ γ (u : S), hbm]

theorem le_of_pow_le {s k idx b r : ℕ} (hs : 0 < s) (hidx : idx ∣ 2 ^ s) (hb : b = 2 ^ k)
    (h1 : 2 ^ s ≤ idx ^ r) (h2 : b ^ r ≤ 2 ^ s) : b ≤ idx := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx
  subst hb
  rw [← pow_mul] at h1 h2
  have h1' : s ≤ i * r := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have h2' : k * r ≤ s := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, mul_zero] at h1'
      omega
    · exact h
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_mul_le_mul_right (h2'.trans h1') hr)

theorem four_le_of_pow_le {idx r : ℕ} (hidx : idx ∣ 2 ^ 4) (h1 : 2 ^ 4 ≤ idx ^ r)
    (h2 : 4 ^ r ≤ 2 ^ 6) : 4 ≤ idx := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx
  have hr : r ≤ 3 := by
    by_contra h
    push Not at h
    have : 4 ^ 4 ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) h
    omega
  by_contra h
  push Not at h
  have hi1 : i ≤ 1 := by
    by_contra h'
    push Not at h'
    have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h'
    omega
  have : (2 ^ i) ^ r ≤ 2 ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

end B42Alt7

end CFSG.Quasithin
