module

public import CFSG.Quasithin.Background.G118E11

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace G118

section Generic

variable {G : Type*} [Group G]

theorem exists_noncyclic_exp3 [Finite G] {a b : G} (hab : a * b = b * a) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) :
    ∃ E : Subgroup G, E = Subgroup.closure {a, b} ∧ a ∈ E ∧ b ∈ E ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ ¬ IsCyclic ↥E := by
  set E : Subgroup G := Subgroup.closure {a, b} with hE
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hS : ({a, b} : Set G) ⊆ Subgroup.centralizer ({a, b} : Set G) := by
    intro x hx y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hab.symm
    · exact hab
    · rfl
  have hEle : E ≤ Subgroup.centralizer ({a, b} : Set G) := (Subgroup.closure_le _).2 hS
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.closure_le_centralizer_centralizer _ hx) y
      (hEle hy)).symm
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha3
      · exact hb3
    | one => simp
    | mul x y hx hy h1 h2 =>
      have hxy : Commute x y := hcomm x hx y hy
      rw [hxy.mul_pow, h1, h2, one_mul]
    | inv x _ h1 => rw [inv_pow, h1, inv_one]
  refine ⟨E, hE, haE, hbE, hcomm, hexp, fun hcyc => ?_⟩
  have hexpE : Monoid.exponent ↥E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hexp x x.2)
  rw [IsCyclic.exponent_eq_card] at hexpE
  have hA : Subgroup.zpowers a ≤ E := (Subgroup.zpowers_le).2 haE
  have hacard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have h3E : 3 ∣ Nat.card E := hacard ▸ Subgroup.card_dvd_of_le hA
  have hEcard : Nat.card E = 3 := Nat.dvd_antisymm hexpE h3E
  have hAE : Subgroup.zpowers a = E :=
    Subgroup.eq_of_le_of_card_ge hA (by rw [hEcard, hacard])
  have hbA : b ∈ Subgroup.zpowers a := by rw [hAE]; exact hbE
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbA
  have ha3' : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
  have hmod : a ^ k = a ^ (k % 3) := zpow_eq_zpow_emod k ha3'
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hmod] at hk
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk
    exact hb1 hk.symm
  · rw [h1, zpow_one] at hk
    exact hba hk.symm
  · rw [h2] at hk
    exact hba2 (by rw [← hk]; norm_cast)

end Generic

section Cent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def centΓ (Γ H : Subgroup (GLV V)) : Subgroup (GLV V) :=
  Γ ⊓ Subgroup.centralizer (H : Set (GLV V))

theorem mem_centΓ_iff {Γ H : Subgroup (GLV V)} {x : GLV V} :
    x ∈ centΓ Γ H ↔ x ∈ Γ ∧ ∀ h ∈ H, h * x = x * h := by
  unfold centΓ
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem centΓ_conj {Γ H : Subgroup (GLV V)} (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    ∀ γ ∈ Γ, ∀ c ∈ centΓ Γ H, γ * c * γ⁻¹ ∈ centΓ Γ H := by
  intro γ hγ c hc
  obtain ⟨hcΓ, hcH⟩ := mem_centΓ_iff.1 hc
  refine mem_centΓ_iff.2 ⟨Γ.mul_mem (Γ.mul_mem hγ hcΓ) (Γ.inv_mem hγ), fun h hh => ?_⟩
  have h1 : γ⁻¹ * h * γ ∈ H := by
    have := hN γ⁻¹ (Γ.inv_mem hγ) h hh
    simpa using this
  have h2 := hcH _ h1
  calc h * (γ * c * γ⁻¹) = γ * ((γ⁻¹ * h * γ) * c) * γ⁻¹ := by group
    _ = γ * (c * (γ⁻¹ * h * γ)) * γ⁻¹ := by rw [h2]
    _ = (γ * c * γ⁻¹) * h := by group

theorem le_normalizer_centΓ {Γ H : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) :
    Γ ≤ Subgroup.normalizer (centΓ Γ H : Set (GLV V)) := by
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => centΓ_conj hN γ hγ x hx
  · intro hx
    have := centΓ_conj hN γ⁻¹ (Γ.inv_mem hγ) _ hx
    simpa [mul_assoc] using this

theorem card_centralizer_eq_six [Finite V] {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (D : E11Data H I) (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2) :
    Nat.card ↥(Subgroup.centralizer (H : Set (GLV V))) = 6 := by
  let _ : Fintype D.F := Fintype.ofFinite D.F
  rw [Nat.card_congr D.θ.toEquiv, card_linearEquiv_finrank_two hk]
  have : Fintype.card D.F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [this]
  norm_num

theorem pCoreOf_two_le_of_normalizer [Finite V] {C Γ : Subgroup (GLV V)} (hCΓ : C ≤ Γ)
    (hN : Γ ≤ Subgroup.normalizer (C : Set (GLV V))) : pCoreOf 2 C ≤ pCoreOf 2 Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 C).trans hCΓ)
    (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C)

end Cent

end G118

end G11

end CFSG.Quasithin
