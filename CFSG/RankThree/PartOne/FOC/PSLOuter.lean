module

public import CFSG.RankThree.PartOne.KC.LinearPrimeSubfieldFixedGroup
public import CFSG.RankThree.PartOne.KC.LinearNonsplitSubfieldFixedGroup
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem fixed_eq_range_psl {ℓ f p n : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hn3 : 3 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) (σ : K ≃+* K)
    (hσ : orderOf σ = p) :
    {x : projectiveSL n K | fieldAut n K σ x = x} =
      ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range : Set (projectiveSL n K)) := by
  by_cases hpq : p ∣ ℓ ^ f - 1
  · have hpn : ¬ p ∣ n := fun hpn => hdiagK (Nat.dvd_gcd hpn (hK ▸ hpq))
    have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
    exact (higher_linear_prime_subfield_fixed_group_and_full_centralizer hℓ hp hpℓ hf hn3 hcop
      hK σ hσ).2.1
  · exact (nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer hℓ hp (by omega) hpℓ hf
      hn3 hK hpq σ hσ).2.2.1

theorem fixSub_simple_of_outer_psl {ℓ f p n : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hn3 : 3 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (α : MulAut (projectiveSL n K)) (hαp : α ^ p = 1) (hαinn : α ∉ innerAut (projectiveSL n K)) :
    IsSimpleGroup ↥(fixSub α) ∧ ∃ a b : ↥(fixSub α), a * b ≠ b * a := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαinn (h1 ▸ (innerAut (projectiveSL n K)).one_mem)
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hE : α ∈ semilinearAutGroup n K := by
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2' : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hαp]
    exact Subgroup.one_mem _
  have hD : α ∉ linearAutGroup n K := by
    intro hD
    exact hαinn (OutStructure.linear_D2 hp hn3 hdiagK _ hD 1
      (by rw [pow_one, hαp]; exact Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn3 hK
  obtain ⟨hpf, σ, hσord, ⟨h, -, hαh⟩, hkcard⟩ := hdesc p hp hpℓ α hE hD hαord
  have hfixset := fixed_eq_range_psl hℓ hp hp5 hpℓ hn3 hf hK hdiagK σ hσord
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) (semilinearFixedSubfield σ)
  have hfixeq : fixSub (fieldAut n K σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
    ext x
    exact Set.ext_iff.mp hfixset x
  have hs : IsSimpleGroup (projectiveSL n ↥(semilinearFixedSubfield σ)) :=
    KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnab : ∃ a b : projectiveSL n ↥(semilinearFixedSubfield σ), a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL
      (n := n) (K := ↥(semilinearFixedSubfield σ)) hn3
    push Not at h1
    exact h1
  let eNk : ↥(linearSubfieldInclusion n (semilinearFixedSubfield σ)).range ≃*
      projectiveSL n ↥(semilinearFixedSubfield σ) := (MonoidHom.ofInjective hinj).symm
  let φ : projectiveSL n K ≃* projectiveSL n K := (h⁻¹ : MulAut (projectiveSL n K))
  have hφα : MulAut.congr φ α = fieldAut n K σ := by
    have : MulAut.congr φ α = h⁻¹ * α * h⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  have hfix : fixSub (fieldAut n K σ) = (fixSub α).map φ.toMonoidHom := by
    rw [← hφα]
    exact fixSub_congr φ α
  let e1 : ↥(fixSub α) ≃* ↥(fixSub (fieldAut n K σ)) :=
    (Subgroup.equivMapOfInjective (fixSub α) φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  let e2 : ↥(fixSub (fieldAut n K σ)) ≃*
      ↥(linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :=
    MulEquiv.subgroupCongr hfixeq
  let e3 : ↥(fixSub α) ≃* projectiveSL n ↥(semilinearFixedSubfield σ) :=
    (e1.trans e2).trans eNk
  have := hs
  refine ⟨e3.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e3.symm a, e3.symm b, fun hc => hab ?_⟩
  have := congrArg e3 hc
  simpa using this

end CFSG.RankThree.PartOne.FOC
