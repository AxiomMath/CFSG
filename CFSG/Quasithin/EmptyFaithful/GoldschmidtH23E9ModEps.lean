module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2b

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

theorem false_of_free_action {Γ X : Type*} [Group Γ] [Finite Γ] [MulAction Γ X] [Finite X]
    (x₀ : X) (hfix : ∀ g : Γ, g • x₀ = x₀)
    (hfree : ∀ (g : Γ) (x : X), x ≠ x₀ → g • x = x → g = 1)
    (hΓ : Nat.card Γ = 9) (hX : Nat.card X = 16) : False := by
  classical
  have hnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz⟩ := exists_ne x₀
  have hinj : ∀ y : X, y ≠ x₀ → Function.Injective fun g : Γ => g • y := by
    intro y hy g h hgh
    have hgh' : g • y = h • y := hgh
    have h1 : (h⁻¹ * g) • y = y := by rw [mul_smul, hgh', inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ _ hy h1)).symm
  have hne : ∀ y : X, y ≠ x₀ → ∀ g : Γ, g • y ≠ x₀ := by
    intro y hy g hg
    apply hy
    have : y = g⁻¹ • (g • y) := (inv_smul_smul g y).symm
    rw [this, hg, hfix]
  let F₁ : Option Γ → X := fun o => o.elim x₀ fun g => g • z
  have hF₁ : Function.Injective F₁ := by
    rintro (_ | g) (_ | h) hgh
    · rfl
    · exact absurd hgh.symm (hne z hz h)
    · exact absurd hgh (hne z hz g)
    · exact congrArg some (hinj z hz hgh)
  have hnotsurj : ¬ Function.Surjective F₁ := by
    intro hs
    have := Nat.card_le_card_of_surjective _ hs
    rw [Finite.card_option, hΓ] at this
    omega
  obtain ⟨z', hz'⟩ : ∃ z' : X, ∀ o : Option Γ, F₁ o ≠ z' := by
    by_contra hcon
    exact hnotsurj fun x => by_contra fun hx => hcon ⟨x, fun o ho => hx ⟨o, ho⟩⟩
  have hz'0 : z' ≠ x₀ := fun h => hz' none h.symm
  have hz'g : ∀ g : Γ, g • z ≠ z' := fun g h => hz' (some g) h
  let F₂ : Option (Γ ⊕ Γ) → X := fun o => o.elim x₀ fun s => s.elim (fun g => g • z) fun g => g • z'
  have hF₂ : Function.Injective F₂ := by
    rintro (_ | g | g) (_ | h | h) hgh
    · rfl
    · exact absurd hgh.symm (hne z hz h)
    · exact absurd hgh.symm (hne z' hz'0 h)
    · exact absurd hgh (hne z hz g)
    · exact congrArg (fun g => some (Sum.inl g)) (hinj z hz hgh)
    · exfalso
      have h1 : g • z = h • z' := hgh
      apply hz'g (h⁻¹ * g)
      rw [mul_smul, h1, inv_smul_smul]
    · exact absurd hgh (hne z' hz'0 g)
    · exfalso
      have h1 : g • z' = h • z := hgh
      apply hz'g (g⁻¹ * h)
      rw [mul_smul, ← h1, inv_smul_smul]
    · exact congrArg (fun g => some (Sum.inr g)) (hinj z' hz'0 hgh)
  have := Nat.card_le_card_of_injective _ hF₂
  rw [Finite.card_option, Nat.card_sum, hΓ] at this
  omega

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem exists_eps (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (_hτ : S.τ ∈ Mb)
    (hE9 : ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ ε : MulAut W, ε ∈ Mb ∧ orderOf ε = 3 ∧ (∀ w ∈ S.W₁, ε w = w) ∧ ε * S.a₂ = S.a₂ * ε ∧
      ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w := by
  obtain ⟨E, hEMb, hEab, hE9⟩ := hE9
  have hE3 : ∀ g ∈ E, g ^ 3 = 1 := hEab.2
  have hodd : ∀ g ∈ E, Odd (orderOf g) := fun g hg =>
    (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hE3 g hg))
  have hstab : ∀ g ∈ E, S.Stab₁ g ∧ S.Stab₂ g := by
    intro g hg
    rcases S.stab_or_swap hW (hnorm g (hEMb hg)) with h | h
    · exact h
    · exfalso
      have h2 := S.stab_mul_of_swap h h
      have h3 : g = (g * g) * (g * g) := by
        calc g = g ^ 3 * g := by rw [hE3 g hg, one_mul]
          _ = (g * g) * (g * g) := by rw [pow_three]; simp only [mul_assoc]
      have h4 : S.Stab₁ g := by
        rw [h3]
        intro w
        exact (h2.1 w).trans (h2.1 ((g * g) w))
      exact S.not_stab₁_of_swap hcard h h4
  have hc₁ : ∀ g ∈ E, g * S.a₁ = S.a₁ * g := fun g hg =>
    commute_of_conj_odd_five151b S.orderOf_a₁_five
      (S.mem_zpowers_a₁_conj hW hcard (hnorm g (hEMb hg)) (hstab g hg)) (hodd g hg)
  have hc₂ : ∀ g ∈ E, g * S.a₂ = S.a₂ * g := fun g hg =>
    commute_of_conj_odd_five151b S.orderOf_a₂_five
      (S.mem_zpowers_a₂_conj hW hcard (hnorm g (hEMb hg)) (hstab g hg)) (hodd g hg)
  obtain ⟨ε, hεE, hε1, hεW₁⟩ : ∃ ε ∈ E, ε ≠ 1 ∧ ∀ w ∈ S.W₁, ε w = w := by
    by_contra hcon
    have hfreeW : ∀ g ∈ E, (∀ w ∈ S.W₁, g w = w) → g = 1 := by
      intro g hg hgw
      by_contra hg1
      exact hcon ⟨g, hg, hg1, hgw⟩
    let s : SubMulAction E W :=
      { carrier := (S.W₁ : Set W)
        smul_mem' := fun g v hv => ((hstab g g.2).1 v).mp hv }
    let x₀ : ↥s := ⟨1, S.W₁.one_mem⟩
    have hfix : ∀ g : E, g • x₀ = x₀ := fun g => Subtype.ext (map_one (g : MulAut W))
    have hfree : ∀ (g : E) (x : ↥s), x ≠ x₀ → g • x = x → g = 1 := by
      intro g x hx hgx
      have hx1 : x.1 ≠ 1 := fun h => hx (Subtype.ext h)
      have hfix1 : (g : MulAut W) x.1 = x.1 := congrArg Subtype.val hgx
      have := S.fix_W₁_of_commute hW hcard (g := g.1) (hc₁ g.1 g.2) x.2 hx1 hfix1
      exact Subtype.ext (hfreeW g.1 g.2 this)
    have hX : Nat.card ↥s = 16 := (rfl : Nat.card ↥s = Nat.card ↥S.W₁).trans (S.card_W₁ hcard)
    exact false_of_free_action x₀ hfix hfree hE9 hX
  have hε3 : orderOf ε = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hE3 ε hεE) hε1
  refine ⟨ε, hEMb hεE, hε3, hεW₁, hc₂ ε hεE, ?_⟩
  intro w hw hw1 hfix
  apply hε1
  have h2 := S.swap.fix_W₁_of_commute hW hcard (g := ε)
    (by rw [swap_a₁]; exact hc₂ ε hεE) hw hw1 hfix
  exact S.eq_one_of_fix_W₁_W₂ hεW₁ fun v hv => h2 v hv

theorem exists_eps₁ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hE9 : ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ ε : MulAut W, ε ∈ Mb ∧ orderOf ε = 3 ∧ (∀ w ∈ S.W₂, ε w = w) ∧ ε * S.a₁ = S.a₁ * ε ∧
      ∀ w ∈ S.W₁, w ≠ 1 → ε w ≠ w := by
  have hnorm' : ∀ g ∈ Mb, ∀ z ∈ S.swap.A₁ ⊔ S.swap.A₂,
      g * z * g⁻¹ ∈ S.swap.A₁ ⊔ S.swap.A₂ := by
    intro g hg z hz
    have hz' : z ∈ S.A₁ ⊔ S.A₂ := by rwa [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl,
      sup_comm] at hz
    have := hnorm g hg z hz'
    rwa [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl, sup_comm]
  obtain ⟨ε, h1, h2, h3, h4, h5⟩ := S.swap.exists_eps hW hcard hnorm' hτ hE9
  exact ⟨ε, h1, h2, h3, by rwa [swap_a₂] at h4, h5⟩

end CFSG.Quasithin.SixData151b
