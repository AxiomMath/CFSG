module

import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)
open CFSG.Sporadic.RuSchreier (ru_card_mulAut_elementary)

private theorem not_seven_dvd_prod_GL_three {d : ℕ} (hd : d ≤ 5) :
    ¬ 7 ∣ ∏ i : Fin d, (3 ^ d - 3 ^ (i : ℕ)) := by
  interval_cases d <;> decide

theorem k150s_not_seven_dvd_card_mulAut_of_three_group {R : Type} [Group R] [Finite R]
    (hR : IsPGroup 3 R) (hcard : Nat.card R ≤ 3 ^ 5) : ¬ 7 ∣ Nat.card (MulAut R) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut R) := MulEquiv.finite_left
  obtain ⟨-, hcomm, hpow, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hR
  have hd5 : d ≤ 5 := by
    have h1 : Nat.card (R ⧸ frattini R) ≤ 3 ^ 5 :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (frattini R))).trans hcard
    rw [hd] at h1
    by_contra hlt
    have h2 : 3 ^ 6 ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 3 ^ 6 ≤ 3 ^ 5 := h2.trans h1
    norm_num at h3
  have hAut : Nat.card (MulAut (R ⧸ frattini R)) = ∏ i : Fin d, (3 ^ d - 3 ^ (i : ℕ)) :=
    ru_card_mulAut_elementary (isMulCommutative_iff.1 hcomm) hpow hd
  have hker : IsPGroup 3 (quotientAutomorphism (frattini R)).ker :=
    (CFSG.GroupTheory.frattini_automorphism_kernel hR).2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  intro h7
  rw [← Subgroup.card_ker_mul_card_range (quotientAutomorphism (frattini R)), hk] at h7
  have h7' : 7 ∣ Nat.card (quotientAutomorphism (frattini R)).range :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 7 3)).dvd_of_dvd_mul_left h7
  have h7'' := h7'.trans
    (Subgroup.card_subgroup_dvd_card (quotientAutomorphism (frattini R)).range)
  rw [hAut] at h7''
  exact not_seven_dvd_prod_GL_three hd5 h7''

theorem k150s_not_dvd_card_of_normalizes {S : Type} [Group S] [Finite S] {C L : Subgroup S}
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hK : IsPGroup 3 ↥(Subgroup.centralizer (L : Set S) ⊓ C)) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hAut : ¬ p ∣ Nat.card (MulAut L)) : ¬ p ∣ Nat.card C := by
  have hCN : C ≤ Subgroup.normalizer (L : Set S) := fun g hg =>
    Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hLn g hg h hh, fun hh => by
      have h2 := hLn g⁻¹ (C.inv_mem hg) _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [e] at h2⟩
  let φ : C →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hCN)
  have hkerL : ∀ g : C, g ∈ φ.ker → (g : S) ∈ Subgroup.centralizer (L : Set S) := fun g hg => by
    have h1 : (⟨g, hCN g.2⟩ : Subgroup.normalizer (L : Set S)) ∈ L.normalizerMonoidHom.ker := hg
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  let ι : φ.ker →* ↥(Subgroup.centralizer (L : Set S) ⊓ C) :=
    (C.subtype.comp φ.ker.subtype).codRestrict _ fun g =>
      Subgroup.mem_inf.2 ⟨hkerL g.1 g.2, g.1.2⟩
  have hι : Function.Injective ι := fun a b hab => by
    have h1 : ((ι a : _) : S) = ((ι b : _) : S) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hker : IsPGroup 3 φ.ker := hK.of_injective ι hι
  have : Finite (MulAut L) := MulEquiv.finite_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  intro hpC
  rw [← Subgroup.card_ker_mul_card_range φ, hk] at hpC
  rcases (Nat.Prime.dvd_mul hp).1 hpC with h1 | h1
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1))
  · exact hAut (h1.trans (Subgroup.card_subgroup_dvd_card φ.range))

theorem k150s_not_seven_dvd_card_of_selfCentralizing_three {S : Type} [Group S] [Finite S]
    {C R : Subgroup S} (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hcent : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) (hcard : Nat.card R ≤ 3 ^ 5) :
    ¬ 7 ∣ Nat.card C := by
  refine k150s_not_dvd_card_of_normalizes hRn ?_ (by norm_num) (by norm_num)
    (k150s_not_seven_dvd_card_mulAut_of_three_group hR3 hcard)
  exact hR3.of_injective (Subgroup.inclusion hcent) (Subgroup.inclusion_injective hcent)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
