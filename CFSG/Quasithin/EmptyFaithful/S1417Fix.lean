module

public import CFSG.Quasithin.EmptyFaithful.S1417Sylow

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S1417

section Fix

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem card_fixV_of_card_two {L J : Subgroup (MulAut W)} (hN : ActsAsNaturalL2 L (commV L))
    (htop : commV L = ⊤) (hJL : J ≤ L) (hJ2 : Nat.card J = 2) : Nat.card (fixV J) = 2 := by
  obtain ⟨s, hsJ, hs1, hsu⟩ := exists_eq_of_card_eq_two hJ2
  have hs2 : s ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥J) (x := ⟨s, hsJ⟩)
    rw [hJ2] at this
    exact congrArg Subtype.val this
  obtain ⟨a, ha, ha1, haf⟩ := exists_fixed_vector hN (fun l hl u hu => commV_stable L hl hu)
    (hJL hsJ) hs2 hs1
  have hfix : ∀ u : W, u ∈ fixV J ↔ (u = 1 ∨ u = a) := by
    intro u
    constructor
    · intro h
      exact (haf u (by rw [htop]; trivial)).mp (h s hsJ)
    · intro h x hx
      rcases hsu x hx with rfl | rfl
      · rfl
      · exact (haf u (by rw [htop]; trivial)).mpr h
  rw [Nat.card_eq_two_iff' (1 : fixV J)]
  refine ⟨⟨a, (hfix a).mpr (Or.inr rfl)⟩, fun h => ha1 (congrArg Subtype.val h), fun z hz => ?_⟩
  rcases (hfix z).mp z.2 with h | h
  · exact absurd (Subtype.ext h) hz
  · exact Subtype.ext h

variable {L₁ L₂ S T' : Subgroup (MulAut W)}

theorem fixV_swap (hS : IsSylowTwoOf S (L₁ ⊔ L₂)) (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hLinf : L₁ ⊓ L₂ = ⊥) (hinf : commV L₁ ⊓ commV L₂ = ⊥) (hUtop : commV L₁ ⊔ commV L₂ = ⊤)
    (hST : S ≤ T') {τ : MulAut W} (hτ : τ ∈ T') (hτS : B1.conjAut τ S = S)
    (hτ₁ : B1.conjAut τ L₁ = L₂) (hτ₂ : B1.conjAut τ L₂ = L₁)
    (hU₁ : ∀ u ∈ commV L₁, τ u ∈ commV L₂) (hU₂ : ∀ u ∈ commV L₂, τ u ∈ commV L₁) :
    Nat.card (fixV S) = 4 ∧ ∃ a₁ ∈ commV L₁, ∃ a₂ ∈ commV L₂, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      ∀ w : W, (∀ x ∈ T', x w = w) → (w = 1 ∨ w = a₁ * a₂) := by
  classical
  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ := exists_sylowData hS hN₁ hN₂ hc hLinf hinf hUtop
  obtain ⟨hτa₁, hτa₂⟩ := hd.swap_apply hτS hτ₁ hτ₂ hU₁ hU₂
  have hdisj : ∀ x, x ∈ commV L₁ → x ∈ commV L₂ → x = 1 := by
    intro x h₁ h₂
    have : x ∈ commV L₁ ⊓ commV L₂ := ⟨h₁, h₂⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have d1 : (1 : W) ≠ a₁ := fun h => hd.a₁_ne h.symm
  have d2 : (1 : W) ≠ a₂ := fun h => hd.a₂_ne h.symm
  have d4 : a₁ ≠ a₂ := fun h => hd.a₁_ne (hdisj a₁ hd.a₁_mem (h ▸ hd.a₂_mem))
  have d3 : (1 : W) ≠ a₁ * a₂ := by
    intro h
    apply hd.a₁_ne
    have h' : a₁ = a₂⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    exact hdisj a₁ hd.a₁_mem (h' ▸ (commV L₂).inv_mem hd.a₂_mem)
  have d5 : a₁ ≠ a₁ * a₂ := fun h => hd.a₂_ne (by simpa using h)
  have d6 : a₂ ≠ a₁ * a₂ := fun h => hd.a₁_ne (by simpa using h)
  refine ⟨?_, a₁, hd.a₁_mem, a₂, hd.a₂_mem, hd.a₁_ne, hd.a₂_ne, fun w hw => ?_⟩
  · have hset : ((fixV S : Subgroup W) : Set W) = ↑({1, a₁, a₂, a₁ * a₂} : Finset W) := by
      ext w
      simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact hd.fixS w
    have h1 : Nat.card (fixV S) = (((fixV S : Subgroup W) : Set W)).ncard :=
      Nat.card_coe_set_eq _
    rw [h1, hset, Set.ncard_coe_finset]
    simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
  · have hw' := (hd.fixS w).mp fun x hx => hw x (hST hx)
    have hτw := hw τ hτ
    rcases hw' with h | h | h | h
    · exact Or.inl h
    · exfalso
      rw [h, hτa₁] at hτw
      exact d4 hτw.symm
    · exfalso
      rw [h, hτa₂] at hτw
      exact d4 hτw
    · exact Or.inr h

omit [Finite W] in
theorem sq_mem_sup {X : Subgroup (MulAut W)} (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinf : commV L₁ ⊓ commV L₂ = ⊥) (hUtop : commV L₁ ⊔ commV L₂ = ⊤)
    (hperm : ∀ g ∈ X, (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁))
    (hcv₁ : ∀ g ∈ X, (commV L₁).map g.toMonoidHom = commV (B1.conjAut g L₁))
    (hcv₂ : ∀ g ∈ X, (commV L₂).map g.toMonoidHom = commV (B1.conjAut g L₂)) {g : MulAut W}
    (hg : g ∈ X) : g * g ∈ L₁ ⊔ L₂ := by
  refine mem_sup_of_fix hN₁ hN₂ hc hinf hUtop hcv₁ hcv₂ (X.mul_mem hg hg) ?_ ?_
  · rw [conjAut_mul]
    rcases hperm g hg with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rw [h1, h1]
    · rw [h1, h2]
  · rw [conjAut_mul]
    rcases hperm g hg with ⟨-, h2⟩ | ⟨h1, h2⟩
    · rw [h2, h2]
    · rw [h2, h1]

omit [Finite W] in
theorem eq_one_of_odd_of_fixed_pair (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hLinf : L₁ ⊓ L₂ = ⊥) (hinf : commV L₁ ⊓ commV L₂ = ⊥) {a₁ a₂ : W} (ha₁ : a₁ ∈ commV L₁)
    (ha₂ : a₂ ∈ commV L₂) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1) {g : MulAut W}
    (hgL : g ∈ L₁ ⊔ L₂) (hodd : Odd (orderOf g)) (hg : g (a₁ * a₂) = a₁ * a₂) : g = 1 := by
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hgL
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : commV L₂ ⊓ commV L₁ = ⊥ := by rw [inf_comm]; exact hinf
  have e1 : l₂ a₁ = a₁ := apply_eq_of_mem_commV_of_commute hc' hinf' hl₂ ha₁
  have e2 : l₁ (l₂ a₂) = l₂ a₂ :=
    apply_eq_of_mem_commV_of_commute hc hinf hl₁ (commV_stable L₂ hl₂ ha₂)
  have hfix : l₁ a₁ * l₂ a₂ = a₁ * a₂ := by
    have : (l₁ * l₂) (a₁ * a₂) = l₁ a₁ * l₂ a₂ := by
      rw [MulAut.mul_apply, map_mul, e1, map_mul, e2]
    rw [← this]
    exact hg
  obtain ⟨hl₁a, hl₂a⟩ := eq_of_mul_eq_of_inf_eq_bot hinf (commV_stable L₁ hl₁ ha₁) ha₁
    (commV_stable L₂ hl₂ ha₂) ha₂ hfix
  have hcomm : l₁ * l₂ = l₂ * l₁ := hc l₁ hl₁ l₂ hl₂
  set n := orderOf (l₁ * l₂) with hn
  have hn1 : (l₁ * l₂) ^ n = 1 := pow_orderOf_eq_one _
  have hpow : l₁ ^ n * l₂ ^ n = 1 := by
    rw [← Commute.mul_pow hcomm]
    exact hn1
  have hl₁n : l₁ ^ n = 1 := by
    have h1 : l₁ ^ n ∈ L₁ ⊓ L₂ := ⟨L₁.pow_mem hl₁ n, by
      have : l₁ ^ n = (l₂ ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hpow
      rw [this]
      exact L₂.inv_mem (L₂.pow_mem hl₂ n)⟩
    rw [hLinf, Subgroup.mem_bot] at h1
    exact h1
  have hl₂n : l₂ ^ n = 1 := by
    rw [hl₁n, one_mul] at hpow
    exact hpow
  have hodd₁ : Odd (orderOf l₁) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hl₁n)
  have hodd₂ : Odd (orderOf l₂) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hl₂n)
  have h1 : l₁ = 1 := eq_one_of_odd_of_fixed hN₁ (fun l hl u hu => commV_stable L₁ hl hu) hl₁
    hodd₁ ha₁ ha₁1 hl₁a
  have h2 : l₂ = 1 := eq_one_of_odd_of_fixed hN₂ (fun l hl u hu => commV_stable L₂ hl hu) hl₂
    hodd₂ ha₂ ha₂1 hl₂a
  rw [h1, h2, mul_one]

omit [Finite W] in
theorem mem_of_sq_mem_of_odd {H : Subgroup (MulAut W)} {g : MulAut W} (hsq : g * g ∈ H)
    (hodd : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : g = (g * g) ^ (m + 1) := by
    have : g ^ (orderOf g + 1) = g := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    calc g = g ^ (orderOf g + 1) := this.symm
      _ = g ^ (2 * (m + 1)) := by congr 1; omega
      _ = (g * g) ^ (m + 1) := by rw [pow_mul, sq]
  rw [h1]
  exact H.pow_mem hsq _

end Fix

end S1417

end CFSG.Quasithin
