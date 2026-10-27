module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSModelSix
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Six

public section

namespace CFSG.Quasithin

open scoped Pointwise
open Equiv CFSG.QuasithinUnique.Borel252.A6 CFSG.Quasithin.F6.GoldAmS

theorem exists_conj_of_sylow_sub {G : Type} [Group G] [Finite G] {A D₁ D₂ : Subgroup G}
    (h1 : D₁ ≤ A) (h2 : D₂ ≤ A) (p1 : IsPGroup 2 D₁) (p2 : IsPGroup 2 D₂)
    (i1 : ¬ 2 ∣ D₁.relIndex A) (i2 : ¬ 2 ∣ D₂.relIndex A) :
    ∃ c ∈ A, D₁.map (MulAut.conj c).toMonoidHom = D₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E₁ : Subgroup A := D₁.subgroupOf A
  let E₂ : Subgroup A := D₂.subgroupOf A
  have pE₁ : IsPGroup 2 E₁ := p1.comap_of_injective A.subtype A.subtype_injective
  have pE₂ : IsPGroup 2 E₂ := p2.comap_of_injective A.subtype A.subtype_injective
  let P₁ : Sylow 2 A := pE₁.toSylow i1
  let P₂ : Sylow 2 A := pE₂.toSylow i2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq A P₁ P₂
  have hcE : (MulAut.conj c) • E₁ = E₂ := by
    have := congrArg (fun P : Sylow 2 A => (P : Subgroup A)) hc
    simp only [Sylow.coe_subgroup_smul] at this
    rwa [show (P₁ : Subgroup A) = E₁ from IsPGroup.toSylow_coe _ _,
      show (P₂ : Subgroup A) = E₂ from IsPGroup.toSylow_coe _ _] at this
  refine ⟨c, c.2, ?_⟩
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyE : (⟨y, h1 hy⟩ : A) ∈ E₁ := hy
    have : MulAut.conj c ⟨y, h1 hy⟩ ∈ (MulAut.conj c) • E₁ :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hyE
    rw [hcE] at this
    exact this
  · intro hx
    have hxE : (⟨x, h2 hx⟩ : A) ∈ E₂ := hx
    rw [← hcE, Subgroup.mem_smul_pointwise_iff_exists] at hxE
    obtain ⟨e, he, hex⟩ := hxE
    refine ⟨e, he, ?_⟩
    simpa using congrArg Subtype.val hex

theorem le_of_inf_alt_le {Y Y' : Subgroup S6} {t₀ : S6} (hY : t₀ ∈ Y) (hY' : t₀ ∈ Y')
    (ht : Equiv.Perm.sign t₀ = -1)
    (h : Y ⊓ alternatingGroup (Fin 6) ≤ Y' ⊓ alternatingGroup (Fin 6)) : Y ≤ Y' := by
  intro x hx
  by_cases hxA : x ∈ alternatingGroup (Fin 6)
  · exact (h ⟨hx, hxA⟩).1
  · have hs : Equiv.Perm.sign x = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | h1
      · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h1) hxA
      · exact h1
    have hxt : x * t₀ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs, ht]
      rfl
    have := (h ⟨Y.mul_mem hx hY, hxt⟩).1
    have e : x = (x * t₀) * t₀⁻¹ := by group
    rw [e]
    exact Y'.mul_mem this (Y'.inv_mem hY')

theorem eq_of_inf_alt_eq {X X' : Subgroup S6} {t₀ : S6} (hX : t₀ ∈ X) (hX' : t₀ ∈ X')
    (ht : Equiv.Perm.sign t₀ = -1)
    (h : X ⊓ alternatingGroup (Fin 6) = X' ⊓ alternatingGroup (Fin 6)) : X = X' :=
  le_antisymm (le_of_inf_alt_le hX hX' ht h.le) (le_of_inf_alt_le hX' hX ht h.ge)

theorem relIndex_A6_eq {D : Subgroup S6} (hD : D ≤ A6s) (hc : Nat.card D = 8) :
    D.relIndex A6s = 45 := by
  have h := Subgroup.relIndex_mul_card (H := D) (K := A6s)
  rw [inf_eq_left.2 hD, hc, card_A6] at h
  omega

theorem isPGroup_of_card_eight {D : Subgroup S6} (hc : Nat.card D = 8) : IsPGroup 2 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 3) (by rw [hc]; norm_num)

theorem S6K1_le_A6 : S6K1 ≤ A6s := fun _ hg =>
  Equiv.Perm.mem_alternatingGroup.2 (mem_S6K1.1 hg).2

theorem S6K2_le_A6 : S6K2 ≤ A6s := fun _ hg =>
  Equiv.Perm.mem_alternatingGroup.2 (mem_S6K2.1 hg).2

theorem S6K12_le_A6 : S6K1 ⊓ S6K2 ≤ A6s := inf_le_left.trans S6K1_le_A6

theorem conj_A6s_eq {c : S6} (hc : c ∈ A6s) : A6s.map (MulAut.conj c).toMonoidHom = A6s := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact A6s.mul_mem (A6s.mul_mem hc hy) (A6s.inv_mem hc)
  · intro hx
    refine ⟨c⁻¹ * x * c, A6s.mul_mem (A6s.mul_mem (A6s.inv_mem hc) hx) hc, by group⟩

theorem exists_lattice_A6 : ∃ Sa' Sb' : Subgroup S6, ∀ Y : Subgroup S6, S6K1 ⊓ S6K2 ≤ Y →
    Y ≤ A6s → Y = S6K1 ⊓ S6K2 ∨ Y = Sa' ∨ Y = Sb' ∨ Y = A6s := by
  obtain ⟨c, hcA, hc⟩ := exists_conj_of_sylow_sub (A := A6s) (D₁ := D0) (D₂ := S6K1 ⊓ S6K2)
    D0_le_A6 S6K12_le_A6 (isPGroup_of_card_eight card_D0) (isPGroup_of_card_eight card_S6H)
    (by rw [relIndex_A6_eq D0_le_A6 card_D0]; norm_num)
    (by rw [relIndex_A6_eq S6K12_le_A6 card_S6H]; norm_num)
  refine ⟨Sa.map (MulAut.conj c).toMonoidHom, Sb.map (MulAut.conj c).toMonoidHom,
    fun Y hDY hYA => ?_⟩
  have hc' : ∀ x ∈ D0, c * x * c⁻¹ ∈ S6K1 ⊓ S6K2 := fun x hx => by
    rw [← hc]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hY₀D : D0 ≤ Y.map (MulAut.conj c⁻¹).toMonoidHom := fun x hx =>
    ⟨c * x * c⁻¹, hDY (hc' x hx), by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hY₀A : Y.map (MulAut.conj c⁻¹).toMonoidHom ≤ A6s := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact A6s.mul_mem (A6s.mul_mem (A6s.inv_mem hcA) (hYA hy)) (by simpa using hcA)
  have hY : Y = (Y.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨x, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      have : c * (c⁻¹ * y * c⁻¹⁻¹) * c⁻¹ = y := by group
      rw [this]
      exact hy
  rcases six_overgroups _ hY₀D hY₀A with h | h | h | h
  · left
    rw [hY, h, hc]
  · right; left
    rw [hY, h]
  · right; right; left
    rw [hY, h]
  · right; right; right
    rw [hY, h]
    exact conj_A6s_eq hcA

theorem lattice_A6 (Y : Subgroup S6) (hDY : S6K1 ⊓ S6K2 ≤ Y) (hYA : Y ≤ A6s) :
    Y = S6K1 ⊓ S6K2 ∨ Y = S6K1 ∨ Y = S6K2 ∨ Y = A6s := by
  obtain ⟨Sa', Sb', L⟩ := exists_lattice_A6
  have hc1 : Nat.card S6K1 = 24 := card_S6K1
  have hc2 : Nat.card S6K2 = 24 := card_S6K2
  have hcA : Nat.card (A6s : Subgroup S6) = 360 := card_A6
  have hcD : Nat.card ↥(S6K1 ⊓ S6K2) = 8 := card_S6H
  have hne : S6K1 ≠ S6K2 := fun h => by
    rw [h, inf_idem] at hcD
    omega
  have hK1 : S6K1 = Sa' ∨ S6K1 = Sb' := by
    rcases L S6K1 inf_le_left S6K1_le_A6 with h | h | h | h
    · rw [h] at hc1; omega
    · exact Or.inl h
    · exact Or.inr h
    · have h24 : Nat.card (A6s : Subgroup S6) = 24 := h ▸ hc1
      rw [hcA] at h24
      exact absurd h24 (by norm_num)
  have hK2 : S6K2 = Sa' ∨ S6K2 = Sb' := by
    rcases L S6K2 inf_le_right S6K2_le_A6 with h | h | h | h
    · rw [h] at hc2; omega
    · exact Or.inl h
    · exact Or.inr h
    · have h24 : Nat.card (A6s : Subgroup S6) = 24 := h ▸ hc2
      rw [hcA] at h24
      exact absurd h24 (by norm_num)
  rcases L Y hDY hYA with h | h | h | h
  · exact Or.inl h
  · rcases hK1 with e1 | e1
    · exact Or.inr (Or.inl (h.trans e1.symm))
    · rcases hK2 with e2 | e2
      · exact Or.inr (Or.inr (Or.inl (h.trans e2.symm)))
      · exact absurd (e1.trans e2.symm) hne
  · rcases hK1 with e1 | e1
    · rcases hK2 with e2 | e2
      · exact absurd (e1.trans e2.symm) hne
      · exact Or.inr (Or.inr (Or.inl (h.trans e2.symm)))
    · exact Or.inr (Or.inl (h.trans e1.symm))
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin
