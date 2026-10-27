module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

namespace CFSG
end CFSG
open CFSG

section Main

public theorem CFSG.proposition_4_6 {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (S : Subgroup R) [S.Normal]
    (hSncyc : ¬ IsCyclic S) :
    ∃ A : Subgroup R, A.Normal ∧ A ≤ S ∧ Nat.card A = p ^ 2 ∧ IsElementaryAbelian p A := by
  classical
  letI : Fact (IsPGroup p S) := ⟨(Fact.out : IsPGroup p R).to_subgroup S⟩
  let Z2S : Subgroup S := Subgroup.upperCentralSeries S 2
  let Ω : Subgroup Z2S := omega₁ (G := ↥Z2S) (p := p)
  have hΩ_noncyc : ¬ IsCyclic Ω := (lemma_4_5_c (R := ↥S) (p := p) hpodd hSncyc).1
  have hΩ_nontrivial : Nontrivial Ω := Nontrivial.of_not_isCyclic hΩ_noncyc
  have hZ2S_p : IsPGroup p Z2S := (Fact.out : IsPGroup p S).to_subgroup Z2S
  have hΩ_p : IsPGroup p Ω := hZ2S_p.to_subgroup Ω
  obtain ⟨n, hn_pos, hΩ_card⟩ := hΩ_p.nontrivial_iff_card.mp hΩ_nontrivial
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    have hΩ_card_p : Nat.card Ω = p := by
      simpa [hn1] using hΩ_card
    exact hΩ_noncyc (isCyclic_of_prime_card hΩ_card_p)
  have htwo_le_n : 2 ≤ n := by
    have h1lt : 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt hn_pos) hn_ne_one.symm
    exact Nat.succ_le_of_lt h1lt
  let K : Subgroup S := z2OmegaCandidate (G := ↥S) p
  have hK_char : K.Characteristic := by
    simpa [K] using z2OmegaCandidate_characteristic (G := ↥S) p
  let Kbar : Subgroup R := K.map S.subtype
  have hKbar_normal : Kbar.Normal := by
    letI : K.Characteristic := hK_char
    dsimp [Kbar]
    exact ConjAct.normal_of_characteristic_of_normal
  letI : Kbar.Normal := hKbar_normal
  have hK_card : Nat.card K = p ^ n := by
    calc
      Nat.card K = Nat.card Ω := by
        dsimp [K, z2OmegaCandidate, Ω, Z2S]
        exact Subgroup.card_map_of_injective (K := Ω) (f := Z2S.subtype) Subtype.coe_injective
      _ = p ^ n := hΩ_card
  have hKbar_card : Nat.card Kbar = p ^ n := by
    calc
      Nat.card Kbar = Nat.card K := Subgroup.card_map_of_injective (K := K) (f := S.subtype) Subtype.coe_injective
      _ = p ^ n := hK_card
  have hKbar_le_S : Kbar ≤ S := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  obtain ⟨A, hA_normal, hA_le_Kbar, hAcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) (N := Kbar) hKbar_normal hKbar_card 2 htwo_le_n
  have hA_le_S : A ≤ S := hA_le_Kbar.trans hKbar_le_S
  have hKexp_dvd : Monoid.exponent K ∣ p := by
    simpa [K] using z2OmegaCandidate_exponent_dvd_p_of_odd (G := ↥S) (p := p) hpodd
  have hApow : ∀ a : A, a ^ p = 1 := by
    intro a
    apply Subtype.ext
    have haKbar : (a : R) ∈ Kbar := hA_le_Kbar a.property
    rcases Subgroup.mem_map.mp haKbar with ⟨z, hzK, hza⟩
    have hz_powK : (⟨z, hzK⟩ : K) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hKexp_dvd ⟨z, hzK⟩
    have hz_pow : (((z : S) : R) ^ p = 1) := by
      simpa using congrArg (fun t : K => (((t : K) : S) : R)) hz_powK
    have hza' : (((z : S) : R)) = (a : R) := hza
    simpa [hza'] using hz_pow
  refine ⟨A, hA_normal, hA_le_S, hAcard, ?_⟩
  exact isElementaryAbelian_of_card_eq_p_sq_of_forall_pow_eq_one (S := A) (p := p) hAcard hApow


end Main
