module

public import CFSG.Quasithin.EmptyFaithful.R3c18R4
public import CFSG.Quasithin.EmptyFaithful.R3c18WF4
public import CFSG.RankThree.PartOne.KLC.TriTorus
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.Quasithin.EmptyFaithful.R3c18W

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.Assembly.LowTwoRank

section Certificates

set_option linter.unusedSectionVars false


theorem d4Rank_holds : D4Rank := by
  intro f K _ _ σ hf hK hσ p hp hp5 hcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf5 : 3 < p := by omega
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
  rcases hcl with h | h | h | h
  · have h1 : p ∣ 2 ^ f - 1 := by
      have : (p : ℤ) ∣ ((2 ^ f - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hq1]
        push_cast
        exact h
      exact_mod_cast this
    exact CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi1 (σ := σ.toRingHom)
      ⟨hp, hp5, hf, hK, hσ, h1⟩
  · exact CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi2 (ℓ := 2) hf hK σ hσ hp hf5
      (by push_cast; exact h)
  · exact CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi36 (ℓ := 2) hf hK σ hσ (ε := 1)
      (Or.inl rfl) hp (by push_cast; simpa using h)
  · exact CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi36 (ℓ := 2) hf hK σ hσ (ε := -1)
      (Or.inr rfl) hp (by push_cast; convert h using 1; ring)

theorem d4Class_holds : D4Class := by
  intro f K _ _ σ hf hK hσ p hp hp5 h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  obtain ⟨-, -, -, -, -, -, -, ⟨iso⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hmod : ChevalleyExceptionalModel ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      .trialityD4 2 f :=
    ⟨⟨Nat.prime_two, hf, rfl⟩, K, inferInstance, inferInstance, hK, σ.toRingHom, hσ,
      ⟨iso.symm⟩⟩
  have hpT : p ∣ Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    dvd_card_of_two_le_pRank hp h2
  obtain ⟨m, hm, hdvd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion (p := p)
    (ℓ := 2) (f := f) hp (by omega) (by omega) hmod).1 hpT).2.2.2.2 rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · left
    have : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) - 1 := by simpa [exhaustionPhi] using hdvd
    simpa using this
  · right; left
    have : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) + 1 := by simpa [exhaustionPhi] using hdvd
    simpa using this
  · right; right; left
    have : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ((2 ^ f : ℕ) : ℤ) + 1 := by
      simpa [exhaustionPhi] using hdvd
    simpa using this
  · right; right; right
    have : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 - ((2 ^ f : ℕ) : ℤ) + 1 := by
      simpa [exhaustionPhi] using hdvd
    simpa using this
  · exfalso
    have hd : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 4 - ((2 ^ f : ℕ) : ℤ) ^ 2 + 1 := by
      simpa [exhaustionPhi] using hdvd
    have h24 : (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
    have hpd : p ∣ (2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 := by
      have h1 : (p : ℤ) ∣ (((2 ^ f) ^ 4 - (2 ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        push_cast at hd
        exact hd
      exact_mod_cast h1
    have h1 := CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve Nat.prime_two hf K hK σ hσ hp
      hp5 hpd
    omega

theorem qLiePRank_holds : QLiePRank :=
  qLiePRank_of_shapes g2PRankShape_holds sp4PRankShape_holds l3PRankShape_holds
    u3PRankShape_holds f4ReeClass_holds f4ReeRank_holds d4Class_holds d4Rank_holds

end Certificates

end R3c18

end CFSG.Quasithin

