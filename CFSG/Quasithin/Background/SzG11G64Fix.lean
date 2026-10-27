module

public import CFSG.Quasithin.Background.SzG11G64Real
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin

namespace SzG11

open CFSG.Quasithin.G64 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem card_statedSL_three_zmod2 : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem false_of_symCore_factorType {n : ℕ} (hn : n = 6 ∨ n = 8) {H : Subgroup (MulAut V)}
    {U : Subgroup V} (hc : G64.SymmetricCore H U ⊥ n) (hf : G64.FactorType H) : False := by
  obtain ⟨π, hπ⟩ := hc
  have hinj : Function.Injective π :=
    RealizesVia.injective_of_faithful' (symCore_faithful (by omega)) hπ
  have hH : Nat.card H = Nat.card (Equiv.Perm (Fin n)) :=
    (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
  rw [Nat.card_perm, Nat.card_fin] at hH
  rcases hf with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have := Nat.card_congr e.toEquiv
    rw [card_statedSL_two (K := ZMod 2) (by simp), hH] at this
    rcases hn with rfl | rfl <;> simp [Nat.factorial] at this
  · have := Nat.card_congr e.toEquiv
    rw [card_statedSL_three_zmod2, hH] at this
    rcases hn with rfl | rfl <;> simp [Nat.factorial] at this
  · have := Nat.card_congr e.toEquiv
    rw [Nat.card_perm, Nat.card_fin, hH] at this
    rcases hn with rfl | rfl <;> simp [Nat.factorial] at this

theorem coord_const_of_mem_zpowers_allOnes {n : ℕ} {x : G6.PermMod n}
    (hx : x ∈ Subgroup.zpowers (G6.allOnes n)) (k l : Fin n) :
    Multiplicative.toAdd x k = Multiplicative.toAdd x l := by
  obtain ⟨z, rfl⟩ := hx
  simp [G6.allOnes, toAdd_zpow]

theorem symDn_fixed_eq_one {n : ℕ} (hn : 3 ≤ n) {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : Equiv.Perm (Fin n) →* ↥H} (h : (FFModel.symDn n).RealizesVia H U ⊥ π) :
    ∀ u ∈ U, (∀ l ∈ H, l u = u) → u = 1 := by
  obtain ⟨β, hrange, hker, he⟩ := exists_secHomU h
  intro u hu hfix
  obtain ⟨m, rfl⟩ : u ∈ β.range := hrange ▸ hu
  set x : G6.PermMod n := Subtype.val m with hx
  have hxc : x ∈ G6.coreMod n := m.2
  have hσ : ∀ σ : Equiv.Perm (Fin n), G6.permAct n σ x * x⁻¹ ∈
      Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := by
    intro σ
    have hm : G6.permAct n σ x ∈ (FFModel.symDn n).sec := G6.permAct_mem_coreMod σ hxc
    have h1 : β ⟨G6.permAct n σ x, hm⟩ = ((π σ : ↥H) : MulAut V) (β m) := he σ m hm
    have h2 : β ⟨G6.permAct n σ x, hm⟩ = β m := by
      rw [h1]
      exact hfix _ (π σ).2
    have h3 : β (⟨G6.permAct n σ x, hm⟩ * m⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact (hker _).1 h3
  have hconst : ∀ i j : Fin n, Multiplicative.toAdd x i = Multiplicative.toAdd x j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
        intro l _
        by_cases hl : l = i
        · simp [hl]
        · simp [hcon l hl]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h2 := Finset.card_le_two (a := i) (b := j)
      omega
    have h1 := coord_const_of_mem_zpowers_allOnes (hσ (Equiv.swap i j)).1 i k
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply,
      Equiv.swap_inv, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hki hkj] at h1
    have : Multiplicative.toAdd x j - Multiplicative.toAdd x i = 0 := by
      rw [sub_eq_add_neg]
      exact h1.trans (add_neg_cancel _)
    exact (sub_eq_zero.1 this).symm
  have hm : x ∈ Subgroup.zpowers (G6.allOnes n) := by
    refine ⟨((Multiplicative.toAdd x ⟨0, by omega⟩ : ZMod 2).val : ℤ), ?_⟩
    apply Multiplicative.toAdd.injective
    funext l
    simp [G6.allOnes, toAdd_zpow, hconst l ⟨0, by omega⟩]
  exact (hker m).2 ⟨hm, hxc⟩

theorem fixed_eq_one_of_moduleType {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hm : G64.ModuleType H U) (hf : G64.FactorType H) :
    ∀ u ∈ U, (∀ l ∈ H, l u = u) → u = 1 := by
  rcases hm with ⟨n, h2, h5, K, _, _, hK, π, hπ⟩ | ⟨n, h5, h8, π, hπ⟩ | ⟨n, h68, hc⟩
  · exact B5.nat_fixed_eq_one h2 hπ
  · exact symDn_fixed_eq_one (by omega) hπ
  · exact (false_of_symCore_factorType h68 hc hf).elim

end SzG11

end CFSG.Quasithin
