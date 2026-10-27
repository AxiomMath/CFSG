module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TDefs
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.Walter.Transitivity.Coprime
import CFSG.Walter.Transitivity.Family

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1521T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_two_p_of_ext1521 {A : Subgroup G} (hA : IsE27 A) (h146 : Item146 A (lB A))
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {P X T₀ : Subgroup G}
    (hE : Ext1521 A P X T₀) (hPQ : P ∈ scriptQ A (lB A)) (hPp : IsPGroup p P)
    (hPR : P ≤ inSubgroup CFSG.solvableRadical (pPrimeCoreOf 3 (delta A (lB A) X))) :
    ∃ H T Q : Subgroup G, H ∈ scriptQ A (lB A) ∧ H ≤ X ∧ Group.IsSolvable H ∧
      (∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p) ∧ P ≤ H ∧
      CFSG.Open.fusionIsSylowIn 2 T H ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      Ext1521 A P X T ∧ CFSG.Open.fusionIsSylowIn p Q H ∧ P ≤ Q ∧
      A ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := delta A (lB A) X
  let O : Subgroup G := pPrimeCoreOf 3 D
  let R₀ : Subgroup G := inSubgroup CFSG.solvableRadical O
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_sSup (S := collectionIn (scriptQ A (lB A)) X) fun Q hQ => hQ.1.1.2.2
  have hDO : D ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 D
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAD.trans (normalizer_le_normalizer_pPrimeCoreOf 3 D)
  haveI hchar : (CFSG.solvableRadical ↥O).Characteristic :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_characteristic
  have hNO : Subgroup.normalizer (O : Set G) ≤ Subgroup.normalizer (R₀ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (K := CFSG.solvableRadical ↥O)
  have hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G) := hAO.trans hNO
  have hT₀Q : T₀ ∈ scriptQ A (lB A) := hE.mem_t.1.1
  have hT₀X : T₀ ≤ X := hE.mem_t.1.2
  have hT₀2 : IsPGroup 2 T₀ := isPGroup_of_mem_scriptQPi Nat.prime_two hE.mem_t
  have hT₀D : T₀ ≤ D := le_delta hT₀Q hT₀X
  have hT₀R₀ : T₀ ≤ Subgroup.normalizer (R₀ : Set G) := hT₀D.trans (hDO.trans hNO)
  have hOpi : IsPiSubgroup (piCompl 3) O :=
    (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 D))
  have hR₀pi : IsPiSubgroup (piCompl 3) R₀ :=
    isPiSubgroup_piCompl_of_le hOpi (Subgroup.map_subtype_le _)
  have hT₀pi2 : IsPiSubgroup (piOf 2) T₀ :=
    (isPiSubgroup_piOf_iff Nat.prime_two T₀).mpr hT₀2
  have hT₀pi : IsPiSubgroup (piCompl 3) T₀ := by
    intro q hq
    have hq2 : (q : ℕ) = 2 := hT₀pi2 q hq
    show (q : ℕ) ≠ 3
    rw [hq2]
    norm_num
  let Z : Subgroup G := R₀ ⊔ T₀
  have hZpi : IsPiSubgroup (piCompl 3) Z := by
    have h := isPiSubgroup_piCompl_sup hT₀pi hR₀pi hT₀R₀
    rwa [sup_comm] at h
  have hR₀solv : Group.IsSolvable R₀ := by
    letI : Group.IsSolvable (CFSG.solvableRadical ↥O) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    let f : ↥(CFSG.solvableRadical ↥O) →* R₀ :=
      { toFun := fun x => ⟨x.1, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    exact Group.isSolvable_of_surjective (f := f) hf
  have hT₀solv : Group.IsSolvable T₀ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent T₀ := hT₀2.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hZsolv : Group.IsSolvable Z := by
    dsimp only [Z]
    exact CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hT₀R₀ hR₀solv hT₀solv
  have hAT₀ : A ≤ Subgroup.normalizer (T₀ : Set G) := hT₀Q.1.2.2
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := by
    dsimp only [Z]
    exact le_normalizer_sup hAR₀ hAT₀
  have hZ : Z ∈ invariantPiSubgroups ⊤ A (piCompl 3) := ⟨le_top, hZpi, hAZ⟩
  let K : Subgroup G := delta A (lB A) Z
  have hKQ : K ∈ scriptQ A (lB A) := by
    dsimp only [K]
    exact delta_mem_scriptQ hA h146 hZ
  have hKZ : K ≤ Z := by
    dsimp only [K]
    exact delta_le Z
  have hR₀D : R₀ ≤ D :=
    (Subgroup.map_subtype_le (CFSG.solvableRadical ↥O)).trans (pPrimeCoreOf_le 3 D)
  have hZX : Z ≤ X := by
    dsimp only [Z]
    exact sup_le (hR₀D.trans (delta_le X)) hT₀X
  have hKX : K ≤ X := hKZ.trans hZX
  have hPZ : P ≤ Z := hPR.trans le_sup_left
  have hPK : P ≤ K := by
    dsimp only [K]
    exact le_delta hPQ hPZ
  have hT₀Z : T₀ ≤ Z := le_sup_right
  have hT₀K : T₀ ≤ K := by
    dsimp only [K]
    exact le_delta hT₀Q hT₀Z
  have hKsolv : Group.IsSolvable K := by
    haveI : Group.IsSolvable Z := hZsolv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKZ)
  have hKpi : IsPiSubgroup (piCompl 3) K := isPiSubgroup_piCompl_of_le hZpi hKZ
  have hK3 : ¬ 3 ∣ Nat.card K :=
    (isPiSubgroup_piCompl_iff Nat.prime_three K).mp hKpi
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    rw [hA.2]
    have h3cop : Nat.Coprime 3 (Nat.card K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3
    simpa only [show (27 : ℕ) = 3 ^ 3 by norm_num] using h3cop.pow_left 3
  let π : Set Nat.Primes := {q | (q : ℕ) = 2 ∨ (q : ℕ) = p}
  have hPpi : IsPiSubgroup π P := by
    intro q hq
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn] at hq
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.2 (Fact.out : p.Prime)).mp
      (q.2.dvd_of_dvd_pow hq))
  have hT₀pip : IsPiSubgroup π T₀ := by
    intro q hq
    obtain ⟨n, hn⟩ := hT₀2.exists_card_eq
    rw [hn] at hq
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp
      (q.2.dvd_of_dvd_pow hq))
  obtain ⟨S, hSK, hSpi, hAS, hPS, c, hcKc, hT₀Sc⟩ :=
    CFSG.Walter.Transitivity.exists_conjBy_of_coprime_action
      (A := A) (K := K) (L₁ := P) (L₂ := T₀) (π := π)
      hKQ.1.2.2 hKsolv hcop hPK hT₀K hPpi hT₀pip hPQ.1.2.2 hT₀Q.1.2.2
  have hSQ : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le hKQ hSK hAS
  have hSX : S ≤ X := hSK.trans hKX
  have hSsolv : Group.IsSolvable S := by
    haveI : Group.IsSolvable K := hKsolv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hSK)
  have hSprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card S → r = 2 ∨ r = p :=
    fun r hr hd => hSpi ⟨r, hr⟩ hd
  let T₁ : Subgroup G := T₀.conjBy c⁻¹
  have hcA : c ∈ Subgroup.centralizer (A : Set G) := hcKc.2
  have hcA_inv : c⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
    (Subgroup.centralizer (A : Set G)).inv_mem hcA
  have hT₁S : T₁ ≤ S := by
    dsimp only [T₁]
    calc T₀.conjBy c⁻¹ ≤ (S.conjBy c).conjBy c⁻¹ := Subgroup.map_mono hT₀Sc
      _ = S := Subgroup.conjBy_inv S c
  have hT₁2 : IsPGroup 2 T₁ := by
    dsimp only [T₁]
    exact IsPGroup.map hT₀2 (MulAut.conj c⁻¹).toMonoidHom
  have hT₁card : Nat.card T₁ = Nat.card T₀ := by
    dsimp only [T₁]
    exact Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  have hAT₁ : A ≤ Subgroup.normalizer (T₁ : Set G) := by
    dsimp only [T₁]
    exact CFSG.Walter.Transitivity.le_normalizer_conjBy hcA_inv hT₀Q.1.2.2
  have h3S : ¬ 3 ∣ Nat.card S := by
    intro h3
    rcases hSpi ⟨3, Nat.prime_three⟩ h3 with h | h
    · norm_num at h
    · exact hp3 h.symm
  obtain ⟨T, hTsyl, hT₁T, hAT⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      (r := 3) (q := 2) Nat.prime_three Nat.prime_two hA.isPGroup h3S hAS hT₁S hT₁2 hAT₁
  obtain ⟨Q, hQsyl, hPQS, hAQ⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      (r := 3) (q := p) Nat.prime_three (Fact.out : p.Prime) hA.isPGroup h3S hAS hPS hPp
      hPQ.1.2.2
  have hTQ : T ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hKQ (hTsyl.1.trans hSK) hAT
  have hTX : T ≤ X := (hTsyl.1.trans hSK).trans hKX
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hTpi : IsPiSubgroup (piOf 2) T := (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2
  have hExt : Ext1521 A P X T :=
    { mem_y2 := hE.mem_y2
      le_x := hE.le_x
      mem_t := ⟨⟨hTQ, hTX⟩, hTpi⟩
      card_le := by
        intro X' hX' hPX' T' hT'
        refine (hE.card_le X' hX' hPX' T' hT').trans ?_
        rw [← hT₁card]
        exact Subgroup.card_le_of_le hT₁T
      normalizer_le := hE.normalizer_le }
  exact ⟨S, T, Q, hSQ, hSX, hSsolv, hSprime, hPS, hTsyl, hAT, hExt, hQsyl, hPQS, hAQ⟩

end CFSG.RankThree.PartTwo.Sec15.Proof1521T
