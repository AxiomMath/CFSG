module

public import CFSG.Quasithin.EmptyFaithful.S143VG94
public import CFSG.Quasithin.EmptyFaithful.S143WCl
public import CFSG.Quasithin.EmptyFaithful.SzN29G10
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.G9Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN29

@[expose] def G94StmtSolv : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A : Subgroup (GLV V)) (m : ℕ), G94Hyp Γ A m → Group.IsSolvable ↥Γ → G94Concl Γ A m

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem dim_cases_of_hyp_solv {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)} (hyp : G111Hyp B Γ v₁ W X X₀)
    (hsqtk : IsQuotientOfSQTKTauCeti ↥Γ) (hsolv : Group.IsSolvable ↥Γ) (h94 : G94StmtSolv)
    (hno : ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
      Nat.card N ≠ 3 ∧ Nat.card N ≠ 5) :
    (Module.finrank (ZMod 2) V = 2 ∧ Nat.card Γ = 6) ∨
      (Module.finrank (ZMod 2) V = 4 ∧ 18 ∣ Nat.card Γ) := by
  have h101 := hyp.toG101Hyp
  have hO2 : pCoreOf 2 Γ = ⊥ := h101.g10_3_pCoreOf_eq_bot
  rcases g10_5_solv g10_3 V B Γ v₁ W X X₀ h101 hsolv with hirr | hred
  · obtain ⟨k, hk⟩ := h101.exists_card_X
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', pow_zero] at hk
      have hX1 : ∀ x ∈ X, x = 1 := by
        intro x hx
        have hsub : Subsingleton ↥X := Nat.card_eq_one_iff_unique.1 hk |>.1
        exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥X) 1)
      rcases hyp.three with h3 | ⟨a, ha, -, hv⟩
      · obtain ⟨w, hw⟩ : ∃ w, B v₁ w ≠ 0 := by
          by_contra hall
          push Not at hall
          exact h101.point (h101.nondegenerate v₁ hall)
        rcases h3 w (fun x hx => by rw [hX1 x hx]; rfl) with hw0 | hw1
        · exact hw (by rw [hw0, map_zero])
        · exact hw (by rw [hw1]; exact h101.alt v₁)
      · have : a = 1 := hX1 a ha
        subst this
        have : v₁ = 0 := by
          obtain ⟨u, hu⟩ := hv
          rw [← hu]
          simp
        exact h101.point this
    have hbound : Module.finrank (ZMod 2) V ≤ 2 * (k + 1) := by
      refine h101.dim_le_two_mul.trans (Nat.mul_le_mul_left 2 (Nat.succ_le_succ ?_))
      have hdvd : X₀.relIndex X ∣ 2 ^ k := by
        rw [← hk]
        exact Subgroup.relIndex_dvd_card X₀ X
      calc Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 (2 ^ k) :=
            Nat.log_mono_right (Nat.le_of_dvd (by positivity) hdvd)
        _ = k := Nat.log_pow Nat.one_lt_two k
    have hfaith := S143V.faithful_of_solvable h101.X_le (IsPGroup.of_card hk) hsolv hO2
    have hyp94 : G94Hyp Γ X k :=
      { quotient := hsqtk
        A_le := h101.X_le
        A_elem := h101.X_isElemAbelian
        A_card := hk
        A_ne := hk1
        bound := hbound
        irreducible := hirr
        faithful := hfaith }
    rcases h94 V Γ X k hyp94 hsolv with ⟨-, hd, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩, -⟩ | ⟨-, hd4, hcase⟩ |
        ⟨-, hd4, -, h18⟩ | ⟨-, h3⟩
    · refine Or.inl ⟨hd, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      simp [Nat.factorial]
    · obtain ⟨N, hNΓ, hNn, hN5⟩ := S143V.exists_normal_five_of_dihedral h101.X_le e
      exact absurd hN5 (hno N hNΓ hNn).2
    · rcases hcase with ⟨hGL, -⟩ | ⟨q, -, -, -, h18⟩
      · obtain ⟨N, hNΓ, hNn, hN3⟩ := S143V.exists_normal_three_of_gammaL24 hGL
        exact absurd hN3 (hno N hNΓ hNn).1
      · exact Or.inr ⟨hd4, h18⟩
    · exact Or.inr ⟨hd4, h18⟩
    · obtain ⟨N, hNΓ, hNn, hN3⟩ := S143V.exists_normal_three_of_concl3 h3
      exact absurd hN3 (hno N hNΓ hNn).1
  · exact Or.inr hred

theorem dim_cases_of_rank_solv {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)} (hyp : G111Hyp B Γ v₁ W X X₀)
    (hsqtk : IsQuotientOfSQTKTauCeti ↥Γ) (hsolv : Group.IsSolvable ↥Γ) (h94 : G94StmtSolv)
    (hX₀ : X₀ ≠ ⊥) :
    (Module.finrank (ZMod 2) V = 2 ∧ Nat.card Γ = 6) ∨
      (Module.finrank (ZMod 2) V = 4 ∧ 18 ∣ Nat.card Γ) := by
  have h101 := hyp.toG101Hyp
  have hO2 : pCoreOf 2 Γ = ⊥ := h101.g10_3_pCoreOf_eq_bot
  rcases g10_5_solv g10_3 V B Γ v₁ W X X₀ h101 hsolv with hirr | hred
  · obtain ⟨k, hk⟩ := h101.exists_card_X
    have hrank : Module.finrank (ZMod 2) V ≤ 2 * k := S143W.rank_le_of_ne_bot h101 hX₀ hk
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      have hd0 : Module.finrank (ZMod 2) V ≤ 0 := by omega
      have : 0 < Module.finrank (ZMod 2) V :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v₁, h101.point⟩
      omega
    have hbound : Module.finrank (ZMod 2) V ≤ 2 * (k + 1) := by omega
    have hfaith := S143V.faithful_of_solvable h101.X_le (IsPGroup.of_card hk) hsolv hO2
    have hyp94 : G94Hyp Γ X k :=
      { quotient := hsqtk
        A_le := h101.X_le
        A_elem := h101.X_isElemAbelian
        A_card := hk
        A_ne := hk1
        bound := hbound
        irreducible := hirr
        faithful := hfaith }
    rcases h94 V Γ X k hyp94 hsolv with ⟨-, hd, ⟨e⟩⟩ | ⟨hm, hd4, -, -⟩ | ⟨hm, hd4, -⟩ |
        ⟨-, hd4, -, h18⟩ | ⟨hm, hd6, -⟩
    · refine Or.inl ⟨hd, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      simp [Nat.factorial]
    · omega
    · omega
    · exact Or.inr ⟨hd4, h18⟩
    · omega
  · exact Or.inr hred

end SzN29

end CFSG.Quasithin
