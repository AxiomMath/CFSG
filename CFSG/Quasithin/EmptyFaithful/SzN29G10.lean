module

public import CFSG.Quasithin.EmptyFaithful.SzN29NS
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.Quasithin.Background.G10FourFive
public import CFSG.Quasithin.Background.G10FourGL
public import CFSG.Quasithin.Background.G10FourSmall
public import CFSG.Quasithin.Background.G10FourSolv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN29

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem g10Four_big_solv (hsolv : Group.IsSolvable ↥Γ) (hyp : G101Hyp B Γ v₁ W X X₀)
    {H : Subgroup (GLV V)} (hHΓ : H ≤ Γ) (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    {U : Submodule (ZMod 2) V} (hirr : IsIrr (H ⊔ X) U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0)
    (hn3 : 3 ≤ Module.finrank (ZMod 2) U) : False := by
  have hXK : X ≤ H ⊔ X := le_sup_right
  have hUK : Invariant (H ⊔ X) U := hirr.1
  have hUH : Invariant H U := fun h hh u hu => hUK h (Subgroup.mem_sup_left hh) u hu
  have hUX : Invariant X U := fun x hx u hu => hUK x (hXK hx) u hu
  obtain ⟨hWU, -, -, hfull, hker⟩ := hyp.counting U hUX h1 h2
  have hα : (B v₁).domRestrict U ≠ 0 := by
    intro hzero
    obtain ⟨u, hu, hne⟩ := h2
    exact hne (by simpa using LinearMap.congr_fun hzero ⟨u, hu⟩)
  have hall1 : AutAll (H ⊔ X) U :=
    autAll_of_fullTransvections (H ⊔ X) U hirr ((B v₁).domRestrict U) hα
      (fun a ha => by
        obtain ⟨x, hx, hxa⟩ := hfull a ha
        exact ⟨x, hXK hx, hxa⟩)
  have hall : AutAll H U :=
    autAll_of_comm_quotient U hn3 H X hUH hUX (fun x hx h hh => hHn x (hyp.X_le hx) h hh)
      hyp.X_comm hall1
  have hHs : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHΓ)
      (Subgroup.inclusion_injective hHΓ)
  exact false_of_solvable_autAll hHs hUH hall hn3

end SzN29

namespace SzN29

theorem g10_4_solv :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
      G101Hyp B Γ v₁ W X X₀ → Group.IsSolvable ↥Γ → ∀ (H : Subgroup (GLV V)), H ≤ Γ →
        (∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) → H ≠ ⊥ →
        ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → U ≠ ⊤ → IsIrr (H ⊔ X) U →
          (H = Γ ∨ (v₁ ∉ U ∧ commSpace X U ≠ ⊥)) → G1004Concl Γ U := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp hsolv H hHΓ hHn hH1 U hU0 hU1 hirr hcase
  have hUK : Invariant (H ⊔ X) U := hirr.1
  have hUH : Invariant H U := fun h hh u hu => hUK h (Subgroup.mem_sup_left hh) u hu
  have hUX : Invariant X U := fun x hx u hu => hUK x (Subgroup.mem_sup_right hx) u hu
  obtain ⟨h1, h2⟩ : v₁ ∉ U ∧ ∃ u ∈ U, B v₁ u ≠ 0 := by
    rcases hcase with hHG | ⟨h1, hc⟩
    · have hUΓ : Invariant Γ U := by
        rw [← hHG]
        exact hUH
      exact ⟨hyp.notMem_of_invariant hUΓ hU1, hyp.exists_not_perp_of_invariant hUΓ hU0⟩
    · exact ⟨h1, hyp.exists_not_perp_of_comm hUX h1 hc⟩
  obtain ⟨hWU, -, -, -, -⟩ := hyp.counting U hUX h1 h2
  have hW1 : 1 ≤ Module.finrank (ZMod 2) W := by
    apply Nat.succ_le_of_lt
    apply Module.finrank_pos_iff_exists_ne_zero.2
    exact ⟨⟨v₁, hyp.mem_W⟩, fun h => hyp.point (congrArg Subtype.val h)⟩
  have hn1 : 1 ≤ Module.finrank (ZMod 2) U := by
    apply Nat.succ_le_of_lt
    apply Module.finrank_pos_iff_exists_ne_zero.2
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    exact ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  have hWle := hyp.finrank_isotropic_le
  obtain ⟨r, hr⟩ : Even (Module.finrank (ZMod 2) V) :=
    LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) (fun v => hyp.alt v) hyp.nondegenerate'
  have hcases : Module.finrank (ZMod 2) U = 1 ∨ Module.finrank (ZMod 2) U = 2 ∨
      3 ≤ Module.finrank (ZMod 2) U := by omega
  rcases hcases with hn | hn | hn
  · exfalso
    rcases hcase with hHG | ⟨-, hc⟩
    · have hUΓ : Invariant Γ U := by
        rw [← hHG]
        exact hUH
      exact g10Four_n_one_case_one hyp hUΓ h1 h2 hn (by omega)
    · exact hc (g10Four_n_one_case_two hyp hUX h1 h2 hn)
  · have hd4 : Module.finrank (ZMod 2) V = 4 := by omega
    refine ⟨hd4, hn, ?_⟩
    rcases hcase with hHG | ⟨-, -⟩
    · have hUΓ : Invariant Γ U := by
        rw [← hHG]
        exact hUH
      exact isSolvable_of_invariant_subspace_four B hyp.alt hyp.nondegenerate hd4 Γ
        (fun γ hγ v w => hyp.isometry γ hγ v w) U hUΓ hU0 hU1
    · exact isSolvable_of_normal_invariant_two B hyp.alt hyp.nondegenerate hd4 Γ H
        (fun γ hγ v w => hyp.isometry γ hγ v w) hHΓ hHn hH1 U hn hUH
  · exact (g10Four_big_solv hsolv hyp hHΓ hHn hirr h1 h2 hn).elim

theorem g10_5_solv (h3 : G1003Stmt) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
      G101Hyp B Γ v₁ W X X₀ → Group.IsSolvable ↥Γ → G1005Concl Γ := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp hsolv
  by_cases hirrΓ : IsIrr Γ ⊤
  · exact Or.inl hirrΓ
  right
  have hO2 : pCoreOf 2 Γ = ⊥ := (h3 V B Γ v₁ W X X₀ hyp).2
  have hbt : (⊥ : Submodule (ZMod 2) V) < ⊤ := by
    rw [bot_lt_iff_ne_bot]
    intro h
    have : v₁ ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← h]
      trivial
    exact hyp.point (by simpa using this)
  obtain ⟨J, hJinv, hJ0, hJ1⟩ : ∃ J : Submodule (ZMod 2) V, Invariant Γ J ∧ J ≠ ⊥ ∧ J ≠ ⊤ := by
    by_contra hcon
    apply hirrΓ
    refine ⟨fun _ _ _ _ => trivial, hbt, fun J hJ _ _ => ?_⟩
    by_contra hJne
    push Not at hJne
    exact hcon ⟨J, hJ, hJne.1, hJne.2⟩
  obtain ⟨U, hUJ, hU0, hUinv, hUmin⟩ := g10Four_exists_irr_le Γ _ J rfl hJinv hJ0
  have hU1 : U ≠ ⊤ := fun h => hJ1 (top_le_iff.1 (h ▸ hUJ))
  have hirrU : IsIrr (Γ ⊔ X) U := by
    rw [sup_eq_left.2 hyp.X_le]
    exact ⟨hUinv, bot_lt_iff_ne_bot.2 hU0, fun T hT _ hTU => hUmin T hT hTU⟩
  have hV2 : 2 ≤ Module.finrank (ZMod 2) V := by
    have h1 : 1 ≤ Module.finrank (ZMod 2) U := by
      apply Nat.succ_le_of_lt
      apply Module.finrank_pos_iff_exists_ne_zero.2
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      exact ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h)⟩
    have h2 : Module.finrank (ZMod 2) U < Module.finrank (ZMod 2) V :=
      Submodule.finrank_lt hU1
    omega
  have hΓ1 : Γ ≠ ⊥ := by
    intro hΓ
    have hle : Submodule.span (ZMod 2) (MulAction.orbit Γ v₁) ≤ Submodule.span (ZMod 2) {v₁} := by
      apply Submodule.span_mono
      rintro w ⟨γ, rfl⟩
      have : (γ : GLV V) = 1 := (Subgroup.eq_bot_iff_forall Γ).1 hΓ γ.1 γ.2
      show (γ : GLV V) v₁ = v₁
      rw [this]
      rfl
    rw [hyp.span_orbit] at hle
    have := Submodule.finrank_mono hle
    rw [finrank_top, finrank_span_singleton hyp.point] at this
    omega
  obtain ⟨hd4, hU2, -⟩ := g10_4_solv V B Γ v₁ W X X₀ hyp hsolv Γ le_rfl
    (fun γ hγ h hh => Γ.mul_mem (Γ.mul_mem hγ hh) (Γ.inv_mem hγ)) hΓ1 U hU0 hU1 hirrU (Or.inl rfl)
  refine ⟨hd4, ?_⟩
  have h36 := g10Four_card_dvd hyp hO2 hUinv hU2 hd4
  have h9 : 9 ∣ Nat.card Γ := by
    have hOodd : Odd (MulAction.orbit Γ v₁).ncard := by
      rw [← MulAction.index_stabilizer]
      exact hyp.odd_index
    have hOdvd : (MulAction.orbit Γ v₁).ncard ∣ Nat.card Γ := by
      rw [← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    have hO4 : 4 ≤ (MulAction.orbit Γ v₁).ncard := by
      have : Fintype (MulAction.orbit Γ v₁) := Fintype.ofFinite _
      have h1 := finrank_span_le_card (R := ZMod 2) (MulAction.orbit Γ v₁)
      rw [hyp.span_orbit, finrank_top, hd4] at h1
      rwa [Set.ncard_eq_toFinset_card']
    have h36' : (MulAction.orbit Γ v₁).ncard ∣ 36 := hOdvd.trans h36
    have hle36 : (MulAction.orbit Γ v₁).ncard ≤ 36 := Nat.le_of_dvd (by norm_num) h36'
    have hodd' := Nat.odd_iff.1 hOodd
    have h9' : (MulAction.orbit Γ v₁).ncard = 9 := by
      generalize (MulAction.orbit Γ v₁).ncard = k at *
      interval_cases k <;> omega
    rwa [h9'] at hOdvd
  have h2 : 2 ∣ Nat.card Γ := by
    by_contra hnot
    obtain ⟨j, hj⟩ := hyp.exists_card_X
    have hXΓ : Nat.card X ∣ Nat.card Γ := Subgroup.card_dvd_of_le hyp.X_le
    have hj0 : j = 0 := by
      by_contra hj0
      apply hnot
      have h2X : 2 ∣ Nat.card X := by
        rw [hj]
        exact dvd_pow_self 2 hj0
      exact h2X.trans hXΓ
    have hX1 : Nat.card X = 1 := by
      rw [hj, hj0]
      rfl
    have hrel : X₀.relIndex X = 1 := by
      have hd := Subgroup.relIndex_dvd_card X₀ X
      rw [hX1] at hd
      exact Nat.dvd_one.1 hd
    have hrank := hyp.rank
    rw [hrel, Nat.log_one_right, hd4] at hrank
    have hW := hyp.finrank_isotropic_le
    rw [hd4] at hW
    omega
  have h18 : 2 * 9 ∣ Nat.card Γ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h9
  simpa using h18

end SzN29

end CFSG.Quasithin
