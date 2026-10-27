module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)
open CFSG.Sporadic.RuSchreier (ru_card_mulAut_elementary)

private theorem not_dvd_prod_GL_three {d : ℕ} (hd : d ≤ 7) :
    ¬ 25 ∣ ∏ i : Fin d, (3 ^ d - 3 ^ (i : ℕ)) := by
  interval_cases d <;> decide

theorem not_dvd_card_mulAut_of_three_group {R : Type} [Group R] [Finite R] (hR : IsPGroup 3 R)
    (hcard : Nat.card R ≤ 3 ^ 7) : ¬ 25 ∣ Nat.card (MulAut R) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut R) := MulEquiv.finite_left
  obtain ⟨-, hcomm, hpow, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hR
  have hd7 : d ≤ 7 := by
    have h1 : Nat.card (R ⧸ frattini R) ≤ 3 ^ 7 :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (frattini R))).trans hcard
    rw [hd] at h1
    by_contra hlt
    have h2 : 3 ^ 8 ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 3 ^ 8 ≤ 3 ^ 7 := h2.trans h1
    norm_num at h3
  have hAut : Nat.card (MulAut (R ⧸ frattini R)) = ∏ i : Fin d, (3 ^ d - 3 ^ (i : ℕ)) :=
    ru_card_mulAut_elementary (isMulCommutative_iff.1 hcomm) hpow hd
  have hker : IsPGroup 3 (quotientAutomorphism (frattini R)).ker :=
    (CFSG.GroupTheory.frattini_automorphism_kernel hR).2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  intro h25
  rw [← Subgroup.card_ker_mul_card_range (quotientAutomorphism (frattini R)), hk] at h25
  have h25' : 25 ∣ Nat.card (quotientAutomorphism (frattini R)).range :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 25 3)).dvd_of_dvd_mul_left h25
  have h25'' := h25'.trans
    (Subgroup.card_subgroup_dvd_card (quotientAutomorphism (frattini R)).range)
  rw [hAut] at h25''
  exact not_dvd_prod_GL_three hd7 h25''

theorem not_dvd_card_of_selfCentralizing_three {S : Type} [Group S] [Finite S] {C R : Subgroup S}
    (hRC : R ≤ C) (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hcent : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) (hcard : Nat.card R ≤ 3 ^ 7) :
    ¬ 25 ∣ Nat.card C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCN : C ≤ Subgroup.normalizer (R : Set S) := fun g hg =>
    Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hRn g hg h hh, fun hh => by
      have h2 := hRn g⁻¹ (C.inv_mem hg) _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [e] at h2⟩
  let φ : C →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hCN)
  have hkerR : ∀ g : C, g ∈ φ.ker → (g : S) ∈ R := fun g hg => by
    have h1 : (⟨g, hCN g.2⟩ : Subgroup.normalizer (R : Set S)) ∈ R.normalizerMonoidHom.ker := hg
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    exact hcent (Subgroup.mem_inf.2 ⟨h1, g.2⟩)
  let ι : φ.ker →* R := (C.subtype.comp φ.ker.subtype).codRestrict R fun g => hkerR g.1 g.2
  have hι : Function.Injective ι := fun a b hab => by
    have h1 : ((ι a : R) : S) = ((ι b : R) : S) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hker : IsPGroup 3 φ.ker := hR3.of_injective ι hι
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  intro h25
  rw [← Subgroup.card_ker_mul_card_range φ, hk] at h25
  have h25' : 25 ∣ Nat.card φ.range :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 25 3)).dvd_of_dvd_mul_left h25
  exact not_dvd_card_mulAut_of_three_group hR3 hcard
    (h25'.trans (Subgroup.card_subgroup_dvd_card φ.range))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
