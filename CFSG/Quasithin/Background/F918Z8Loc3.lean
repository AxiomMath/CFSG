module

public import CFSG.Quasithin.Background.F918Z8Def3
public import CFSG.Quasithin.Background.F918V3Stmt
public import CFSG.Quasithin.Background.F918Z7Syl
public import CFSG.Quasithin.Background.F918Z8i

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D321LocSuz : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y),
    LocCfg Γ Λ S V → (∃ n, IsSz n ↥Λ) → ∀ A ∈ QhatStar Γ, A ≤ S →
      (∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ Λ, a * x = x * a) → False

@[expose] def D321LocFaith : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y),
    LocCfg Γ Λ S V → ∀ A ∈ QhatStar Γ, A ≤ S →
      (∀ a ∈ A, (∀ x ∈ Λ, a * x = x * a) → a = 1) → LocShape Λ

theorem loc_unfaith_nonsuz (hD392 : D392) {Y : Type} [CommGroup Y] [Finite Y]
    {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y} (h : LocCfg Γ Λ S V)
    (hsz : ¬ ∃ n, IsSz n ↥Λ) {A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar Γ) (hAS : A ≤ S)
    (hunf : ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ Λ, a * x = x * a) : False := by
  obtain ⟨X, -, hXM, hXc, -, -, -, -, -, h3X⟩ :=
    hD392 Y Γ Λ S Λ V h.std rfl h.hq (Or.inl h.VS) A hA hAS hunf
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3X
  have hx3 : (x : MulAut Y) ^ (3 ^ 1) = 1 := by
    have : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  have h1 : (x : MulAut Y) = 1 :=
    h.hK x (hXM x.2) (fun y hy => hXc x x.2 y hy) 3 Nat.prime_three (by norm_num)
      (a38_three_dvd h.a38 hsz) ⟨1, hx3⟩
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem d321Local_of_parts (hD392 : D392) (hSuz : D321LocSuz) (hFaith : D321LocFaith) :
    D321Local := by
  intro Y _ _ Γ Λ S V h
  obtain ⟨A, hA, hAS⟩ := exists_qhatStar_le_sylow h.std.hyp.sylow h.hq
  by_cases hf : ∀ a ∈ A, (∀ x ∈ Λ, a * x = x * a) → a = 1
  · exact hFaith Y Γ Λ S V h A hA hAS hf
  · exfalso
    push Not at hf
    obtain ⟨a, ha, hc, hne⟩ := hf
    by_cases hsz : ∃ n, IsSz n ↥Λ
    · exact hSuz Y Γ Λ S V h hsz A hA hAS ⟨a, ha, hne, hc⟩
    · exact loc_unfaith_nonsuz hD392 h hsz hA hAS ⟨a, ha, hne, hc⟩

end CFSG.Quasithin
