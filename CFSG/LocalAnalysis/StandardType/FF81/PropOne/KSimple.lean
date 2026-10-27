module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.KFixed
import CFSG.Mathlib.GroupTheory.LayerSimpleOrCube
import CFSG.Mathlib.GroupTheory.SLElemAbelianNine
import CFSG.Mathlib.GroupTheory.ThreeCopiesNormalizer
import CFSG.Mathlib.GroupTheory.LiftNormalizing
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem exists_map_data {H Y : Type} [Group H] [Group Y] (f : H →* Y)
    (hf : Function.Injective f) {E T : Subgroup H} {c : ℕ}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = c)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set H)) :
    ∃ E' T' : Subgroup Y, CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = c ∧
      T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ E' ≤ Subgroup.normalizer (T' : Set Y) := by
  refine ⟨E.map f, T.map f, hE.map f, ?_, ?_, hT2.map f, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, hcard]
  · intro hbot
    exact hT ((Subgroup.map_eq_bot_iff_of_injective (H := T) (f := f) hf).mp hbot)
  · exact (Subgroup.map_mono (f := f) hET).trans (Subgroup.le_normalizer_map f)

theorem isSimpleGroup_ksec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) :
    IsSimpleGroup (Ksec R) ∧ ∃ x y : Ksec R, x * y ≠ y * x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β, hβ, -, O, J', hfix, hOJ, hcom, hcop, hJ'model⟩ := exists_fixed_ksec h hJ hR
  have hJ'simple : IsSimpleGroup ↥J' := by
    rcases hJ'model with h4 | h5
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h4
    · exact CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h5
  have hJ'nonab : ∃ x ∈ J', ∃ y ∈ J', x * y ≠ y * x := by
    by_contra hc
    have hcomm : IsMulCommutative ↥J' := IsMulCommutative.of_comm fun (x y : ↥J') => by
      by_contra hxy
      exact hc ⟨(x : Ksec R), x.2, (y : Ksec R), y.2, fun h => hxy (Subtype.ext h)⟩
    have hprime : (Nat.card ↥J').Prime :=
      (@Group.is_simple_iff_prime_card ↥J' _ hcomm).mp hJ'simple
    rcases hJ'model with h4 | h5
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h4] at hprime
      norm_num at hprime
    · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h5] at hprime
      norm_num at hprime
  have hO : pPrimeCore 3 (Xq R) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (G := ↥(Subgroup.centralizer (R : Set G))) Nat.prime_three
  have hab := abelian_sylow_xq h hR
  rcases CFSG.LayerSimpleOrCube.simple_or_cube_layer hO hab β hβ hfix hOJ hcom hcop hJ'simple
      hJ'nonab with hKsimple | ⟨S₀, S₁, S₂, e₀, e₁, e₂, h₀₁, h₀₂, h₁₂, hi₀₁, hi₀₁₂, -⟩
  · obtain ⟨x, -, y, -, hxy⟩ := hJ'nonab
    exact ⟨hKsimple, x, y, hxy⟩
  exfalso
  have hJ'nine : ∃ E T : Subgroup ↥J', CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set ↥J') := by
    rcases hJ'model with h4 | h5
    · exact CFSG.SLElemAbelianNine.exists_elemAbelian_nine_normalizer (J := ↥J') (m := 4)
        (Or.inl rfl) h4
    · exact CFSG.SLElemAbelianNine.exists_elemAbelian_nine_normalizer (J := ↥J') (m := 5)
        (Or.inr rfl) h5
  obtain ⟨E₃, T₃, hE₃, hcard₃, hT₃, hT₃₂, hE₃T₃⟩ :=
    CFSG.ThreeCopiesNormalizer.exists_three_copies (Y := Ksec R) (J := ↥J') hJ'nine
      e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ hi₀₁ hi₀₁₂
  obtain ⟨E₁, T₁, hE₁, hcard₁, hT₁, hT₁₂, hE₁T₁⟩ :=
    exists_map_data (f := (CFSG.layer (Xq R)).subtype) (CFSG.layer (Xq R)).subtype_injective
      hE₃ hcard₃ hT₃ hT₃₂ hE₃T₃
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (R : Set G))) := by
    have hcop3 : Nat.Coprime 3
        (Nat.card (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (R : Set G)))) :=
      CFSG.pPrimeCore_coprime_card
    exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop3
  obtain ⟨E₂, T₂, hE₂, hcard₂, hT₂, hT₂₂, hE₂T₂⟩ :=
    CFSG.LiftNormalizing.exists_lift_normalizer
      (H := ↥(Subgroup.centralizer (R : Set G)))
      (N := CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (R : Set G))) hN hE₁ hT₁ hT₁₂ hE₁T₁
  obtain ⟨E₄, T₄, hE₄, hcard₄, hT₄, hT₄₂, hE₄T₄⟩ :=
    exists_map_data (f := (Subgroup.centralizer (R : Set G)).subtype)
      (Subgroup.centralizer (R : Set G)).subtype_injective hE₂ hcard₂ hT₂ hT₂₂ hE₂T₂
  have hle := card_le_of_normalizer_isPGroup_two h.hypA h.model hT₄ hT₄₂ hE₄T₄ hE₄
  rw [hcard₄, hcard₁] at hle
  norm_num at hle

end CFSG.StandardType.FF81.PropOne

end
