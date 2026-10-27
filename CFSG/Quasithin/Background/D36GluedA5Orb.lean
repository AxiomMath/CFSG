module

public import CFSG.Quasithin.Background.D36GluedA5Fin
public import CFSG.Quasithin.Background.P3GL24A5
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.A5Orb

theorem five_le_index {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 60)
    (hs : IsSimpleGroup Γ) (H : Subgroup Γ) (hH : H ≠ ⊤) : 5 ≤ H.index := by
  have hdvd := H.index_normalCore_dvd_factorial_index
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
  · rw [h, Subgroup.index_bot, hΓ] at hdvd
    have h5 : 5 ∣ Nat.factorial H.index := Nat.dvd_trans (by norm_num) hdvd
    exact (Nat.Prime.dvd_factorial (by norm_num)).mp h5
  · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH

theorem exists_five_set {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 60)
    (hs : IsSimpleGroup Γ) {M : Type} [CommGroup M] [Finite M] [MulDistribMulAction Γ M]
    (hM : Nat.card M = 16) (hfix : ∀ x : M, (∀ γ : Γ, γ • x = x) → x = 1)
    {p : M} (hp : p ≠ 1) {g l : Γ} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hl2 : l * l = 1)
    (hl1 : l ≠ 1) (hgp : g • p = p) (hlp : l • p = p) :
    ∃ R : Set M, R.ncard = 5 ∧ (1 : M) ∉ R ∧ (∀ γ : Γ, ∀ x ∈ R, γ • x ∈ R) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  set H : Subgroup Γ := MulAction.stabilizer Γ p with hH
  have hgH : g ∈ H := hgp
  have hlH : l ∈ H := hlp
  have hg : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hl : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1
  have h3 : 3 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨g, hgH⟩ : H)
    rwa [Subgroup.orderOf_mk, hg] at this
  have h2 : 2 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨l, hlH⟩ : H)
    rwa [Subgroup.orderOf_mk, hl] at this
  have hHne : H ≠ ⊤ := by
    intro htop
    apply hp
    refine hfix p fun γ => ?_
    have : γ ∈ H := by rw [htop]; trivial
    exact this
  have h5 := five_le_index hΓ hs H hHne
  have hmul := H.card_mul_index
  rw [hΓ] at hmul
  have hle : Nat.card H ≤ 12 := by
    by_contra hcon
    push Not at hcon
    have : 13 * 5 ≤ Nat.card H * H.index := Nat.mul_le_mul hcon h5
    omega
  have hcases : (Nat.card H = 6 ∧ H.index = 10) ∨ (Nat.card H = 12 ∧ H.index = 5) := by
    have hpos : 0 < Nat.card H := Nat.card_pos
    have h6 : Nat.card H = 6 ∨ Nat.card H = 12 := by omega
    rcases h6 with h6 | h6
    · left; refine ⟨h6, ?_⟩; rw [h6] at hmul; omega
    · right; refine ⟨h6, ?_⟩; rw [h6] at hmul; omega
  have hord := MulAction.index_stabilizer Γ p
  have hne1 : ∀ γ : Γ, ∀ x : M, x ≠ 1 → γ • x ≠ 1 := by
    intro γ x hx h
    apply hx
    have : γ⁻¹ • (γ • x) = γ⁻¹ • (1 : M) := by rw [h]
    simpa using this
  have hOne : (1 : M) ∉ MulAction.orbit Γ p := by
    rintro ⟨γ, hγ⟩
    exact hne1 γ p hp hγ
  rcases hcases with ⟨-, hidx⟩ | ⟨-, hidx⟩
  ·
    have horb : (MulAction.orbit Γ p).ncard = 10 := by rw [← hord]; exact hidx
    refine ⟨{x | x ≠ 1} \ MulAction.orbit Γ p, ?_, fun h => h.1 rfl, ?_⟩
    · have hsub : MulAction.orbit Γ p ⊆ {x | x ≠ 1} := by
        rintro _ ⟨γ, rfl⟩
        exact hne1 γ p hp
      rw [Set.ncard_diff hsub, horb]
      have hc : ({x | x ≠ 1} : Set M).ncard = 15 := by
        have : ({x | x ≠ 1} : Set M) = Set.univ \ {(1 : M)} := by
          ext x; simp
        rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hM]
      rw [hc]
    · intro γ x hx
      refine ⟨hne1 γ x hx.1, fun hmem => hx.2 ?_⟩
      obtain ⟨δ, hδ⟩ := hmem
      refine ⟨γ⁻¹ * δ, ?_⟩
      have hδ' : δ • p = γ • x := hδ
      show (γ⁻¹ * δ) • p = x
      rw [mul_smul, hδ']
      simp
  · have horb : (MulAction.orbit Γ p).ncard = 5 := by rw [← hord]; exact hidx
    refine ⟨MulAction.orbit Γ p, horb, hOne, ?_⟩
    rintro γ x ⟨δ, rfl⟩
    exact ⟨γ * δ, by simp [mul_smul]⟩

theorem exists_A4_fixed {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 60)
    (hs : IsSimpleGroup Γ) {X : Type} [MulAction Γ X] (R : Set X) (hR5 : R.ncard = 5)
    (hRinv : ∀ γ : Γ, ∀ x ∈ R, γ • x ∈ R) (hnf : ∀ x ∈ R, ∃ γ : Γ, γ • x ≠ x) :
    ∃ e₁ e₂ c : Γ, e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      e₁ ≠ e₂ ∧ c * e₁ * c⁻¹ = e₂ ∧ c * e₂ * c⁻¹ = e₁ * e₂ ∧
      ∃ v ∈ R, e₁ • v = v ∧ e₂ • v = v ∧ c • v = v := by
  let ψ : Γ →* Equiv.Perm R :=
    { toFun := fun γ =>
        { toFun := fun x => ⟨γ • (x : X), hRinv γ x x.2⟩
          invFun := fun x => ⟨γ⁻¹ • (x : X), hRinv γ⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (inv_smul_smul γ _)
          right_inv := fun x => Subtype.ext (smul_inv_smul γ _) }
      map_one' := Equiv.ext fun x => Subtype.ext (one_smul Γ _)
      map_mul' := fun a b => Equiv.ext fun x => Subtype.ext (mul_smul a b _) }
  have hψ : ∀ γ : Γ, ∀ x : R, ((ψ γ x : R) : X) = γ • (x : X) := fun _ _ => rfl
  have hne : R.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  haveI : Finite R := (Set.finite_of_ncard_pos (by omega : 0 < R.ncard)).to_subtype
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hne
      obtain ⟨γ, hγ⟩ := hnf x hx
      have hker : γ ∈ ψ.ker := by rw [h]; trivial
      rw [MonoidHom.mem_ker] at hker
      apply hγ
      have := congrArg (fun σ : Equiv.Perm R => ((σ ⟨x, hx⟩ : R) : X)) hker
      simpa [hψ] using this
  have hcardR : Nat.card R = 5 := by rw [Nat.card_coe_set_eq]; exact hR5
  let β : R ≃ Fin 5 := Finite.equivFinOfCardEq hcardR
  let ψ' : Γ →* Equiv.Perm (Fin 5) := β.permCongrHom.toMonoidHom.comp ψ
  have hinj' : Function.Injective ψ' := β.permCongrHom.injective.comp hinj
  have hψ'apply : ∀ γ : Γ, ∀ i : Fin 5, ψ' γ i = β (ψ γ (β.symm i)) := fun γ i => rfl
  have hrange : Nat.card ψ'.range = 60 := by
    rw [← hΓ]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  have halt := CFSG.Quasithin.G11.G118.gl24_eq_alt_of_card_sixty ψ'.range hrange
  obtain ⟨k12, k22, k32, k42, k52, k62, k72', k72, k82, k92, k102, k112, k122, k132⟩ :=
    CFSG.Quasithin.A5Fin.kleinData
  have hmem : ∀ a : Equiv.Perm (Fin 5), Equiv.Perm.sign a = 1 → ∃ γ : Γ, ψ' γ = a := by
    intro a ha
    have : a ∈ ψ'.range := by
      rw [halt]
      exact Equiv.Perm.mem_alternatingGroup.mpr ha
    exact this
  obtain ⟨e₁, he₁⟩ := hmem _ k82
  obtain ⟨e₂, he₂⟩ := hmem _ k92
  obtain ⟨c, hc⟩ := hmem _ k102
  have hmap : ∀ x y : Γ, ψ' x = ψ' y → x = y := fun x y h => hinj' h
  have hfixpt : ∀ γ : Γ, ∀ a : Equiv.Perm (Fin 5), ψ' γ = a → a 4 = 4 →
      γ • ((β.symm 4 : R) : X) = ((β.symm 4 : R) : X) := by
    intro γ a hγa ha4
    have h1 := hψ'apply γ 4
    rw [hγa, ha4] at h1
    have h2 : ψ γ (β.symm 4) = β.symm 4 := by
      apply β.injective
      rw [Equiv.apply_symm_apply]
      exact h1.symm
    have := congrArg (fun y : R => (y : X)) h2
    simpa [hψ] using this
  refine ⟨e₁, e₂, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ((β.symm 4 : R) : X), (β.symm 4).2, ?_, ?_, ?_⟩
  · apply hmap; rw [map_mul, he₁, map_one]; exact k12
  · apply hmap; rw [map_mul, he₂, map_one]; exact k22
  · apply hmap; rw [map_mul, map_mul, he₁, he₂]; exact k32
  · intro h; apply k42; rw [← he₁, h, map_one]
  · intro h; apply k52; rw [← he₂, h, map_one]
  · intro h; apply k62; rw [← he₁, ← he₂, h]
  · apply hmap; rw [map_mul, map_mul, map_inv, hc, he₁, he₂]; exact k72'
  · apply hmap; rw [map_mul, map_mul, map_inv, hc, he₂, map_mul, he₁, he₂]; exact k72
  · exact hfixpt e₁ _ he₁ k112
  · exact hfixpt e₂ _ he₂ k122
  · exact hfixpt c _ hc k132

end CFSG.Quasithin.A5Orb
