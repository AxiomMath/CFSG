module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup

section Abstract

variable {C : Type*} [Group C]

theorem inverts_of_fpf [Finite C] {Y : Subgroup C} {u : C} (hu : u ^ 2 = 1)
    (hY : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) (hf : ∀ y ∈ Y, u * y = y * u → y = 1) :
    ∀ y ∈ Y, u * y * u⁻¹ = y⁻¹ := by
  classical
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  let φ : Y → Y := fun y => ⟨(y : C)⁻¹ * (u * y * u⁻¹), Y.mul_mem (Y.inv_mem y.2) (hY y y.2)⟩
  have hinj : Function.Injective φ := by
    intro y y' h
    have h' : (y : C)⁻¹ * (u * y * u⁻¹) = (y' : C)⁻¹ * (u * y' * u⁻¹) := congrArg Subtype.val h
    have h1 : (y' : C) * (y : C)⁻¹ = u * ((y' : C) * (y : C)⁻¹) * u⁻¹ := by
      have h2 : (y' : C) * ((y : C)⁻¹ * (u * y * u⁻¹)) = u * y' * u⁻¹ := by rw [h']; group
      calc (y' : C) * (y : C)⁻¹
          = ((y' : C) * ((y : C)⁻¹ * (u * y * u⁻¹))) * (u * y * u⁻¹)⁻¹ := by group
        _ = (u * y' * u⁻¹) * (u * y * u⁻¹)⁻¹ := by rw [h2]
        _ = u * ((y' : C) * (y : C)⁻¹) * u⁻¹ := by group
    have hwY : (y' : C) * (y : C)⁻¹ ∈ Y := Y.mul_mem y'.2 (Y.inv_mem y.2)
    have hw := hf _ hwY (by
      calc u * ((y' : C) * (y : C)⁻¹) = (u * ((y' : C) * (y : C)⁻¹) * u⁻¹) * u := by group
        _ = ((y' : C) * (y : C)⁻¹) * u := by rw [← h1])
    have : (y' : C) = y := by
      calc (y' : C) = ((y' : C) * (y : C)⁻¹) * y := by group
        _ = y := by rw [hw]; group
    exact Subtype.ext this.symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨y, hy⟩ := hsurj ⟨w, hw⟩
  have hwy : w = (y : C)⁻¹ * (u * y * u⁻¹) := (congrArg Subtype.val hy).symm
  have hu2 : u⁻¹ * u⁻¹ = 1 := by rw [hui]; rwa [← pow_two]
  rw [hwy]
  calc u * ((y : C)⁻¹ * (u * y * u⁻¹)) * u⁻¹
      = u * (y : C)⁻¹ * u * y * (u⁻¹ * u⁻¹) := by group
    _ = u * (y : C)⁻¹ * u * y := by rw [hu2]; group
    _ = u * (y : C)⁻¹ * u⁻¹ * y := by rw [hui]
    _ = ((y : C)⁻¹ * (u * y * u⁻¹))⁻¹ := by group

theorem eq_bot_of_three_fpf [Finite C] {Y : Subgroup C} {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1)
    (hu₂ : u₂ ^ 2 = 1) (h₁ : ∀ y ∈ Y, u₁ * y * u₁⁻¹ ∈ Y) (h₂ : ∀ y ∈ Y, u₂ * y * u₂⁻¹ ∈ Y)
    (f₁ : ∀ y ∈ Y, u₁ * y = y * u₁ → y = 1) (f₂ : ∀ y ∈ Y, u₂ * y = y * u₂ → y = 1)
    (f₁₂ : ∀ y ∈ Y, u₁ * u₂ * y = y * (u₁ * u₂) → y = 1) : Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have i₁ := inverts_of_fpf hu₁ h₁ f₁ y hy
  have i₂ := inverts_of_fpf hu₂ h₂ f₂ y hy
  have i₁' : u₁ * y⁻¹ * u₁⁻¹ = y := by
    have := congrArg (fun a => a⁻¹) i₁
    simpa [mul_assoc] using this
  have hc : u₁ * u₂ * y = y * (u₁ * u₂) := by
    have e₂ : u₂ * y = y⁻¹ * u₂ := by
      calc u₂ * y = (u₂ * y * u₂⁻¹) * u₂ := by group
        _ = y⁻¹ * u₂ := by rw [i₂]
    have e₁ : u₁ * y⁻¹ = y * u₁ := by
      calc u₁ * y⁻¹ = (u₁ * y⁻¹ * u₁⁻¹) * u₁ := by group
        _ = y * u₁ := by rw [i₁']
    calc u₁ * u₂ * y = u₁ * (u₂ * y) := by group
      _ = u₁ * (y⁻¹ * u₂) := by rw [e₂]
      _ = (u₁ * y⁻¹) * u₂ := by group
      _ = (y * u₁) * u₂ := by rw [e₁]
      _ = y * (u₁ * u₂) := by group
  simpa using f₁₂ y hy hc

def kleinSubgroup {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1) (hc : u₁ * u₂ = u₂ * u₁) :
    Subgroup C where
  carrier := {1, u₁, u₂, u₁ * u₂}
  one_mem' := by simp
  mul_mem' := by
    have i₁ : u₁ * u₁ = 1 := by rwa [← pow_two]
    have i₂ : u₂ * u₂ = 1 := by rwa [← pow_two]
    have e1 : u₁ * (u₁ * u₂) = u₂ := by rw [← mul_assoc, i₁, one_mul]
    have e3 : u₁ * u₂ * u₁ = u₂ := by rw [hc, mul_assoc, i₁, mul_one]
    have e4 : u₁ * u₂ * u₂ = u₁ := by rw [mul_assoc, i₂, mul_one]
    have e2 : u₂ * (u₁ * u₂) = u₁ := by
      calc u₂ * (u₁ * u₂) = (u₂ * u₁) * u₂ := (mul_assoc _ _ _).symm
        _ = (u₁ * u₂) * u₂ := by rw [← hc]
        _ = u₁ := e4
    have e5 : u₁ * u₂ * (u₁ * u₂) = 1 := by
      calc u₁ * u₂ * (u₁ * u₂) = (u₁ * u₂ * u₁) * u₂ := (mul_assoc _ _ _).symm
        _ = u₂ * u₂ := by rw [e3]
        _ = 1 := i₂
    have f1 : u₂ * u₁ = u₁ * u₂ := hc.symm
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, i₁, i₂, e1, e2, e3,
        e4, e5, f1, true_or, or_true]
  inv_mem' := by
    have i₁ : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    have i₂ : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · simp [i₁]
    · simp [i₂]
    · show (u₁ * u₂)⁻¹ ∈ ({1, u₁, u₂, u₁ * u₂} : Set C)
      rw [mul_inv_rev, i₁, i₂]
      exact Or.inr (Or.inr (Or.inr hc.symm))


theorem kleinSubgroup_isPGroup {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) : IsPGroup 2 ↥(kleinSubgroup hu₁ hu₂ hc) := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : C) ^ 2 = 1 := by
    rcases g.2 with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact hu₁
    · rw [h]; exact hu₂
    · rw [h, Commute.mul_pow hc, hu₁, hu₂, one_mul]
  have hg' : g ^ 2 = 1 := Subtype.ext hg
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg') with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem eq_one_of_pgroup_commute {Yc : Subgroup C} {p : ℕ} [Fact p.Prime] [Finite C]
    (hYp : IsPGroup p Yc) {u : C} (hp : ¬ p ∣ Nat.card (centralizer ({u} : Set C)))
    {y : C} (hy : y ∈ Yc) (hyu : u * y = y * u) : y = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hYp ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hk
  have hyC : y ∈ centralizer ({u} : Set C) := Subgroup.mem_centralizer_singleton_iff.mpr hyu.symm
  have hd : orderOf y ∣ Nat.card (centralizer ({u} : Set C)) := by
    have := orderOf_dvd_natCard (⟨y, hyC⟩ : centralizer ({u} : Set C))
    rwa [Subgroup.orderOf_mk] at this
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    apply hp
    refine (dvd_pow_self p hpos.ne').trans ?_
    rw [← hk]; exact hd

theorem not_dvd_card_of_klein [Finite C] {X : Subgroup C} [X.Normal] (hXodd : Odd (Nat.card X))
    {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1) (hc : u₁ * u₂ = u₂ * u₁)
    {p : ℕ} (hp : p.Prime) (hp₁ : ¬ p ∣ Nat.card (centralizer ({u₁} : Set C)))
    (hp₂ : ¬ p ∣ Nat.card (centralizer ({u₂} : Set C)))
    (hp₁₂ : ¬ p ∣ Nat.card (centralizer ({u₁ * u₂} : Set C))) : ¬ p ∣ Nat.card X := by
  intro hpX
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : Subgroup C := kleinSubgroup hu₁ hu₂ hc
  have hV2 : IsPGroup 2 V := kleinSubgroup_isPGroup hu₁ hu₂ hc
  let φ : ↥V →* MulAut ↥X := (MulAut.conjNormal : C →* MulAut ↥X).comp V.subtype
  let _ : MulDistribMulAction ↥V ↥X := MulDistribMulAction.compHom ↥X φ
  have hcop : ¬ 2 ∣ Nat.card X := by
    rcases hXodd with ⟨k, hk⟩; omega
  obtain ⟨Y, hY⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
    (G := ↥X) (A := ↥V) 2 p hV2 hcop
  set Yc : Subgroup C := (Y : Subgroup X).map X.subtype with hYc
  have hYp : IsPGroup p Yc := Y.isPGroup'.map X.subtype
  have hinv : ∀ v ∈ V, ∀ y ∈ Yc, v * y * v⁻¹ ∈ Yc := by
    intro v hv y hy
    obtain ⟨e, he, rfl⟩ := hy
    have h1 := hY ⟨v, hv⟩ e he
    refine ⟨_, h1, ?_⟩
    exact MulAut.conjNormal_apply v e
  have hu₁V : u₁ ∈ V := Or.inr (Or.inl rfl)
  have hu₂V : u₂ ∈ V := Or.inr (Or.inr (Or.inl rfl))
  have hbot : Yc = ⊥ := by
    refine eq_bot_of_three_fpf hu₁ hu₂ (hinv u₁ hu₁V) (hinv u₂ hu₂V) ?_ ?_ ?_
    · intro y hy h
      exact eq_one_of_pgroup_commute hYp hp₁ hy h
    · intro y hy h
      exact eq_one_of_pgroup_commute hYp hp₂ hy h
    · intro y hy h
      exact eq_one_of_pgroup_commute hYp hp₁₂ hy h
  have hcard : Nat.card Yc = 1 := by rw [hbot]; simp
  have hcardY : Nat.card Yc = p ^ (Nat.card X).factorization p := by
    rw [hYc, Subgroup.card_map_of_injective X.subtype_injective, Y.card_eq_multiplicity]
  have hpos : 0 < (Nat.card X).factorization p := by
    have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
    exact (hp.dvd_iff_one_le_factorization hne).mp hpX
  rw [hcardY] at hcard
  have : p ^ (Nat.card X).factorization p ≠ 1 := by
    intro h
    rcases pow_eq_one_iff.mp h with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hpos.ne' h1
  exact this hcard

end Abstract

end CFSG.Sporadic.Recognition.JankoWong
