module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkB

public section

namespace CFSG.Quasithin.E9

open CFSG.Quasithin.H23P4
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_one_or_sixteen {V X : Subgroup G} (hV : Nat.card V = 16) (hXV : X ≤ V)
    (h : Nat.card X ≡ 1 [MOD 5]) : Nat.card X = 1 ∨ Nat.card X = 16 := by
  have hdvd : Nat.card X ∣ 16 := hV ▸ Subgroup.card_dvd_of_le hXV
  have hmem : Nat.card X ∈ Nat.divisors 16 := by simp [hdvd]
  have h16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [h16] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rw [h1] at h
    exact absurd h (by decide)
  · rw [h1] at h
    exact absurd h (by decide)
  · rw [h1] at h
    exact absurd h (by decide)
  · exact Or.inr h1

theorem exists_centralizer_eq_bot {V Y : Subgroup G} (hV : Nat.card V = 16) (hY5 : IsPGroup 5 Y)
    (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hVY : ⁅V, Y⁆ = V) :
    ∃ y ∈ Y, V ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ y ∈ Y, ∀ v ∈ V, y * v = v * y := by
    intro y hy v hv
    obtain ⟨k, hk⟩ := hY5 ⟨y, hy⟩
    have hyk : y ^ 5 ^ k = 1 := congrArg Subtype.val hk
    have hmod := card_modEq_card_fixed (X := V) (fun x hx => hYV y hy x hx) hyk
    rw [hV] at hmod
    have h1 : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ≡ 1 [MOD 5] :=
      hmod.symm.trans (by decide : 16 ≡ 1 [MOD 5])
    rcases card_eq_one_or_sixteen hV inf_le_left h1 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) (hcon y hy)
    · have hVC : V ⊓ Subgroup.centralizer ({y} : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hV])
      have hv' : v ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by
        rw [hVC]
        exact hv
      exact Subgroup.mem_centralizer_iff.1 hv'.2 y rfl
  have hbot : V = ⊥ := by
    rw [← hVY]
    refine le_bot_iff.mp (Subgroup.commutator_le.2 fun v hv y hy => ?_)
    rw [Subgroup.mem_bot, commutatorElement_def, (hall y hy v hv).symm]
    group
  have h1 : Nat.card V = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  omega

theorem eq_bot_or_eq_of_five_card_sixteen {V Y W : Subgroup G} (hV : Nat.card V = 16)
    (hY5 : IsPGroup 5 Y) (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hVY : ⁅V, Y⁆ = V)
    (hW : W ≤ V) (hWY : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) : W = ⊥ ∨ W = V := by
  obtain ⟨y, hy, hyC⟩ := exists_centralizer_eq_bot hV hY5 hYV hVY
  obtain ⟨k, hk⟩ := hY5 ⟨y, hy⟩
  have hyk : y ^ 5 ^ k = 1 := congrArg Subtype.val hk
  have hmod := card_modEq_card_fixed (X := W) (fun x hx => hWY y hy x hx) hyk
  have hWC : W ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_right _ hW) hyC.le)
  rw [hWC, Subgroup.card_bot] at hmod
  rcases card_eq_one_or_sixteen hV hW hmod with h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hW (by rw [h, hV]))

end CFSG.Quasithin.E9
