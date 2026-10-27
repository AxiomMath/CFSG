module

public import CFSG.Quasithin.Background.G11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_ne_zero_fixed_of_isPGroup [Nontrivial V] {N : Subgroup (GLV V)} (hN : IsPGroup 2 N) :
    ∃ v : V, v ≠ 0 ∧ ∀ n ∈ N, n v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hN.card_modEq_card_fixedPoints V
  have hcardV : 2 ∣ Nat.card V := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : Fintype V := Fintype.ofFinite V
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
    have h2 : 0 < Module.finrank (ZMod 2) V :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨v, hv⟩
    rw [Nat.card_eq_fintype_card, h1, ZMod.card]
    exact dvd_pow_self 2 h2.ne'
  have hcardF : 2 ∣ Nat.card (MulAction.fixedPoints N V) := (hmod.dvd_iff dvd_rfl).1 hcardV
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (MulAction.fixedPoints N V) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : (a : V) = 0 := by
      by_contra h0
      exact h0 (by
        obtain ⟨n, hn, hne⟩ := hcon a h0
        exact absurd (MulAction.mem_fixedPoints.1 a.2 ⟨n, hn⟩) hne)
    have hb : (b : V) = 0 := by
      by_contra h0
      exact h0 (by
        obtain ⟨n, hn, hne⟩ := hcon b h0
        exact absurd (MulAction.mem_fixedPoints.1 b.2 ⟨n, hn⟩) hne)
    rw [ha, hb]
  have hle : Nat.card (MulAction.fixedPoints N V) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  have hpos : 0 < Nat.card (MulAction.fixedPoints N V) :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, MulAction.mem_fixedPoints.2 fun n => smul_zero _⟩⟩, inferInstance⟩
  have h1 : Nat.card (MulAction.fixedPoints N V) = 1 := le_antisymm hle hpos
  rw [h1] at hcardF
  exact absurd hcardF (by norm_num)

theorem eq_bot_of_isPGroup_normal {Γ : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤)
    {N : Subgroup (GLV V)} (hNn : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (hN2 : IsPGroup 2 N) :
    N = ⊥ := by
  obtain ⟨w, -, hw⟩ := IsConcreteLE.exists_of_lt hirr.2.1
  have hw0 : w ≠ 0 := fun h => hw (by rw [h]; exact Submodule.zero_mem _)
  have : Nontrivial V := nontrivial_of_ne w 0 hw0
  obtain ⟨v, hv0, hvfix⟩ := exists_ne_zero_fixed_of_isPGroup hN2
  have hinv : Invariant Γ (fixedSpace N) := invariant_fixedSpace hNn
  have hJ := hirr.2.2 (fixedSpace N) hinv bot_le le_top
  have htop : fixedSpace N = ⊤ := by
    rcases hJ with h | h
    · exfalso
      have hmem : v ∈ fixedSpace N := hvfix
      rw [h] at hmem
      exact hv0 (by simpa using hmem)
    · exact h
  rw [eq_bot_iff]
  intro n hn
  have hfix : ∀ u : V, n u = u := fun u => by
    have hu : u ∈ fixedSpace N := by rw [htop]; trivial
    exact hu n hn
  rw [Subgroup.mem_bot]
  exact LinearEquiv.ext hfix

end CFSG.Quasithin.SzN31
