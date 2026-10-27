module

public import CFSG.RankThree.GF2n.Stroth80.Sec93CentConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem card_dvd_sum_card_fixed {H : Type*} [Group H] [Fintype H] {α : Type*} [Fintype α]
    [DecidableEq α] (φ : H →* Equiv.Perm α) :
    Fintype.card H ∣ ∑ h : H, Fintype.card {a : α // φ h a = a} := by
  classical
  letI : MulAction H α := MulAction.compHom α φ
  have hsum : (∑ h : H, Fintype.card {a : α // φ h a = a}) =
      ∑ h : H, Fintype.card ↥(MulAction.fixedBy α h) := by
    refine Finset.sum_congr rfl fun h _ => ?_
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => Iff.rfl)
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := H) (X := α)
  rw [hsum, hB]
  exact dvd_mul_left _ _

theorem card_fixed_points_conj {Y : Type} [Group Y] {α : Type} (φ : Y →* Equiv.Perm α) (g z : Y) :
    Nat.card {i : α // φ (g * z * g⁻¹) i = i} = Nat.card {i : α // φ z i = i} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (φ g).symm fun i => ?_)
  rw [map_mul, map_mul, map_inv]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  constructor
  · intro h
    have h2 := congrArg (φ g).symm h
    simpa using h2
  · intro h
    rw [h, Equiv.apply_symm_apply]

theorem mem_of_mul_self_eq_one_of_fixedPoints {Y : Type} [Group Y] [Finite Y] {α : Type}
    [Finite α] (φ : Y →* Equiv.Perm α) {T : Subgroup Y} (hT : IsWC T) {m N a : ℕ} (hm : 1 ≤ m)
    (hTcard : Nat.card T = 2 ^ m)
    (hTconj : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y)
    (hinv : ∀ z : Y, z * z = 1 → z ≠ 1 →
      Nat.card {i // φ z i = i} = a ∨ Nat.card {i // φ z i = i} = 0)
    (hone : ∀ z w : Y, z * z = 1 → z ≠ 1 → w * w = 1 → w ≠ 1 →
      Nat.card {i // φ z i = i} = a → Nat.card {i // φ w i = i} = a → IsConj z w)
    (hα : Nat.card α = N) (hN1 : ¬ 2 ^ m ∣ N) (hN2 : ¬ 2 ^ (m + 1) ∣ N + (2 ^ m - 1) * a)
    {x : Y} (hx : x ∈ Subgroup.centralizer (T : Set Y)) (hx2 : x * x = 1) : x ∈ T := by
  classical
  by_contra hxT
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Fintype α := Fintype.ofFinite α
  set fc : Y → ℕ := fun y => Nat.card {i : α // φ y i = i} with hfc
  have hfc1 : fc 1 = N := by
    rw [← hα]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun i => by rw [map_one]; rfl)
  have hsumT : ∀ c : ℕ, (∀ t ∈ T, t ≠ 1 → fc t = c) →
      ∑ h : ↥T, fc (h : Y) = N + (2 ^ m - 1) * c := by
    intro c hc
    have h1 : ∀ h : ↥T, fc (h : Y) = if h = 1 then N else c := by
      intro h
      by_cases h1 : h = 1
      · simp [h1, hfc1]
      · have : (h : Y) ≠ 1 := fun h' => h1 (Subtype.ext h')
        simp [h1, hc _ h.2 this]
    rw [Finset.sum_congr rfl (fun h _ => h1 h),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥T))]
    have h2 : ∑ x ∈ Finset.univ.erase (1 : ↥T), (if x = 1 then N else c) = (2 ^ m - 1) * c := by
      rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)]),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hTcard, smul_eq_mul]
    rw [h2]
    simp
  have hT1ne : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hTcard
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1ne
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have hc : ∀ t ∈ T, t ≠ 1 → fc t = fc t₀ := by
    intro t ht ht1
    obtain ⟨g, hg⟩ := isConj_iff.1 (hTconj t ht ht1 t₀ ht₀ ht₀1')
    rw [← hg]
    exact (card_fixed_points_conj φ g t).symm
  have hdiv₁ : 2 ^ m ∣ ∑ h : ↥T, fc (h : Y) := by
    have h := card_dvd_sum_card_fixed (φ.comp T.subtype)
    rw [← Nat.card_eq_fintype_card, hTcard] at h
    refine h.trans (dvd_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    exact (Nat.card_eq_fintype_card (α := {i : α // φ y i = i})).symm
  have ht₀a : fc t₀ = a := by
    rcases hinv t₀ (elemAbelian_mul_self hT.1 ht₀) ht₀1' with h | h
    · exact h
    · exfalso
      have hs := hsumT (fc t₀) hc
      have h0 : fc t₀ = 0 := h
      rw [hs, h0, mul_zero, add_zero] at hdiv₁
      exact hN1 hdiv₁
  have hTa : ∀ t ∈ T, t ≠ 1 → fc t = a := fun t ht ht1 => (hc t ht ht1).trans ht₀a
  obtain ⟨E, hTE, hE⟩ := exists_isElemAbelian_gt hT.1 hx hx2 hxT
  have hE0 : ∀ e ∈ E, e ∉ T → fc e = 0 := by
    intro e heE heT
    have he1 : e ≠ 1 := fun h => heT (h ▸ T.one_mem)
    have he2 : e * e = 1 := hE.mul_self_eq_one heE
    rcases hinv e he2 he1 with h8 | h0
    · exfalso
      refine heT (mem_of_isConj_of_mem_wc hT ?_ he1 ht₀
        (hone e t₀ he2 he1 (elemAbelian_mul_self hT.1 ht₀) ht₀1' h8 ht₀a))
      exact Subgroup.mem_centralizer_iff.2 fun t ht => hE.comm (hTE.le ht) heE
    · exact h0
  have hdivE : Nat.card E ∣ ∑ e : ↥E, fc (e : Y) := by
    have h := card_dvd_sum_card_fixed (φ.comp E.subtype)
    rw [← Nat.card_eq_fintype_card] at h
    refine h.trans (dvd_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    exact (Nat.card_eq_fintype_card (α := {i : α // φ y i = i})).symm
  have hsumE : ∑ e : ↥E, fc (e : Y) = ∑ h : ↥T, fc (h : Y) := by
    rw [← Finset.sum_subset (s₁ := Finset.univ.image
      (fun h : ↥T => (⟨h.1, hTE.le h.2⟩ : ↥E))) (Finset.subset_univ _) ?_]
    · rw [Finset.sum_image]
      intro h _ h' _ hh
      exact Subtype.ext (by simpa using hh)
    · intro e _ he
      refine hE0 e e.2 fun heT => he ?_
      exact Finset.mem_image.2 ⟨⟨e, heT⟩, Finset.mem_univ _, rfl⟩
  have hE2 : IsPGroup 2 E := hE.isPGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hE2.exists_card_eq
  have hlt : Nat.card T < Nat.card E := Subgroup.card_lt_of_lt hTE
  rw [hTcard, hj] at hlt
  have hmj : m + 1 ≤ j := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
    omega
  apply hN2
  rw [hsumE, hsumT a hTa, hj] at hdivE
  exact (pow_dvd_pow 2 hmj).trans hdivE

end CFSG.RankThree.GF2n.Stroth80
