module

public import CFSG.Quasithin.Background.SzG11SNC
public import CFSG.Quasithin.Background.SzG11TwoDescent

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin CFSG.Quasithin.SzG11NC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem smul_comm_of_mem [Finite V] {H : Subgroup (GLV V)} {hirr : IsIrr H ⊤} {h : GLV V}
    (hh : h ∈ H) (e : CommF H hirr) (v : V) : h (e • v) = e • h v := by
  rw [CommF.smul_def, CommF.smul_def]
  exact (mem_commutantOf.1 e.val_mem h hh v).symm

theorem card_commF_eq_four [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ X X₀ : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V}
    (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤)
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (h4 : 4 ≤ Nat.card (CommF H hirr))
    (hd : 6 ≤ Module.finrank (ZMod 2) V) : Nat.card (CommF H hirr) = 4 := by
  by_contra hne
  have hVne : Nontrivial V := nontrivial_of_isIrr_top hirr
  have hchar : CharP (CommF H hirr) 2 := by
    refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply smul_left_inj_of_ne_zero hv
    rw [two_smul, zmod_two_add_self, zero_smul]
  have : Fintype (CommF H hirr) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (CommF H hirr) 2
  have hm' : Nat.card (CommF H hirr) = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have h8 : 8 ≤ Nat.card (CommF H hirr) := by
    generalize (m : ℕ) = n at hm'
    by_contra hlt
    push Not at hlt
    have hn3 : n < 3 := by
      by_contra hcon
      push Not at hcon
      have : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    have h4' : 4 ≤ 2 ^ n := hm' ▸ h4
    have hne' : 2 ^ n ≠ 4 := hm' ▸ hne
    clear hm' hlt
    interval_cases n <;> (revert h4' hne'; norm_num)
  have hsl : ∀ x ∈ X, ∃ σ : CommF H hirr ≃+* CommF H hirr,
      ∀ (e : CommF H hirr) (v : V), x (e • v) = σ e • x v :=
    fun x hx => CommF.exists_semilinear Γ hnorm (hyp.X_le hx)
  exact not_three_of_field (CommF H hirr) h8 hd X hyp.X_sq hsl v₁ hyp.point hyp.three

theorem commF_dichotomy [Finite V] {Γ H : Subgroup (GLV V)} (hirr : IsIrr H ⊤)
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hE : Nat.card (CommF H hirr) = 4)
    {γ : GLV V} (hγ : γ ∈ Γ) :
    (∀ (e : CommF H hirr) (v : V), γ (e • v) = e • γ v) ∨
      (∀ (e : CommF H hirr) (v : V), γ (e • v) = e ^ 2 • γ v) := by
  obtain ⟨σ, hσ⟩ := CommF.exists_semilinear Γ hnorm hγ
  have h2 := two_eq_zero_of_card_four hE
  obtain ⟨ω, hω0, hω1, hωsq, hall⟩ := E4_cases hE h2
  have hσω : σ ω = ω ∨ σ ω = ω + 1 := by
    have h1 : σ ω ^ 2 = σ ω + 1 := by
      have := congrArg σ hωsq
      rwa [map_pow, map_add, map_one] at this
    rcases hall (σ ω) with h | h | h | h
    · rw [h] at h1
      exfalso
      exact one_ne_zero (show (1 : CommF H hirr) = 0 by linear_combination -h1)
    · rw [h] at h1
      exfalso
      exact one_ne_zero (show (1 : CommF H hirr) = 0 by linear_combination -h1)
    · exact Or.inl h
    · exact Or.inr h
  rcases hσω with h | h
  · left
    have hid : ∀ e, σ e = e := by
      intro e
      rcases hall e with rfl | rfl | rfl | rfl
      · exact map_zero σ
      · exact map_one σ
      · exact h
      · rw [map_add, map_one, h]
    intro e v
    rw [hσ e v, hid e]
  · right
    have hfr : ∀ e, σ e = e ^ 2 := by
      intro e
      rcases hall e with rfl | rfl | rfl | rfl
      · rw [map_zero]; ring
      · rw [map_one]; ring
      · rw [h, hωsq]
      · rw [map_add, map_one, h]
        linear_combination (-1 : CommF H hirr) * hωsq - ω * h2
    intro e v
    rw [hσ e v, hfr e]

theorem exists_frobenius_involution [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ X X₀ : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V}
    (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤)
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hE : Nat.card (CommF H hirr) = 4)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant H, ∃ v, x (f v) ≠ f (x v)) :
    ∃ x₀ ∈ X, x₀ * x₀ = 1 ∧ ∀ (e : CommF H hirr) (v : V), x₀ (e • v) = e ^ 2 • x₀ v := by
  obtain ⟨x, hxX, f, hf, v, hne⟩ := hex
  refine ⟨x, hxX, hyp.X_sq x hxX, ?_⟩
  rcases commF_dichotomy hirr hnorm hE (hyp.X_le hxX) with hlin | hfrob
  · exfalso
    apply hne
    have hf' : f ∈ commutantOf H := by rwa [endCommutant_eq_commutantOf] at hf
    have := hlin (CommF.mk (hirr := hirr) f hf') v
    rwa [CommF.smul_def, CommF.smul_def, CommF.val_mk] at this
  · exact hfrob

theorem exists_scalar_of_mem_endCommutant [Finite V] {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤)
    (K : Type) [Field K] [Finite K] (sc : K →+* Module.End (ZMod 2) V)
    (hsc : ∀ κ, ∀ h ∈ H, ∀ v, sc κ (h v) = h (sc κ v))
    (hcard : Nat.card (CommF H hirr) ≤ Nat.card K) {f : Module.End (ZMod 2) V}
    (hf : f ∈ endCommutant H) : ∃ κ : K, f = sc κ := by
  have : Nontrivial V := nontrivial_of_isIrr_top hirr
  let g : K → CommF H hirr := fun κ => CommF.mk (sc κ) (mem_commutantOf.2 (hsc κ))
  have hg : Function.Injective g := fun κ κ' h => sc.injective (congrArg CommF.val h)
  have hbij : Function.Bijective g := hg.bijective_of_nat_card_le hcard
  have hf' : f ∈ commutantOf H := by rwa [endCommutant_eq_commutantOf] at hf
  obtain ⟨κ, hκ⟩ := hbij.2 (CommF.mk (hirr := hirr) f hf')
  exact ⟨κ, (congrArg CommF.val hκ).symm⟩

theorem normalClosure_le_conf {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ L : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} [Finite V] (hs : SzG11S.Conf B Γ v₁ W X X₀ L) :
    normalClosure Γ L ≤ Γ :=
  normalClosure_le hs.h108.component.1

theorem card_commF_of_scalars [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ X X₀ L : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V}
    (hs : SzG11S.Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) (sc : K →+* Module.End (ZMod 2) V)
    (hsc : ∀ κ, ∀ h ∈ normalClosure Γ L, ∀ v, sc κ (h v) = h (sc κ v))
    (hd : 6 ≤ Module.finrank (ZMod 2) V) :
    Nat.card (CommF (normalClosure Γ L) (SzG11S.isIrr_top_of_conf hs hp)) = 4 :=
  card_commF_eq_four hs.hyp (SzG11S.isIrr_top_of_conf hs hp) (normalClosure_normal Γ L)
    (by rw [← hK]; exact CommF.card_le K sc hsc) hd

end CFSG.Quasithin.G11.SzG11S.Two
