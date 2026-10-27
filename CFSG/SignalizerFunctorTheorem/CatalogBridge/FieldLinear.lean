module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.RankThree.PartOne.KC.LinearNonsplitSubfieldFixedGroup
import CFSG.RankThree.Automorphisms.LinearHigherCoprime
import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem exists_char_card (K : Type*) [Field K] [Finite K] :
    ∃ ℓ f : ℕ, ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨ℓ, hcharK⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  exact ⟨ℓ, n, hℓ, hcharK, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem dvd_card_projectiveSL_of_dvd {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K) : r ∣ Nat.card (projectiveSL n K) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hSL := card_SL_eq (K := K) (n := n) (by omega)
  have hsplit := (scalars n K).card_eq_card_quotient_mul_card_subgroup
  have hZ := card_scalars_dvd (K := K) (n := n) (by omega)
  have hN : 1 ≤ n * (n - 1) / 2 := by
    rw [Nat.one_le_div_iff (by norm_num)]
    have : 2 ≤ n - 1 ∨ n = 2 := by omega
    rcases this with h | rfl
    · nlinarith
    · norm_num
  have hrSL : r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [hSL]
    exact Dvd.dvd.mul_right (hrq.trans (dvd_pow_self _ (by omega))) _
  have hcop : Nat.Coprime r (Nat.card (scalars n K)) := by
    have h1 : Nat.Coprime r (Nat.card K - 1) := by
      refine (Nat.Prime.coprime_iff_not_dvd hr).mpr fun hd => ?_
      have : r ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hrq hd
      rw [Nat.sub_sub_self hq1.le] at this
      exact hr.one_lt.ne' (Nat.dvd_one.mp this)
    exact Nat.Coprime.coprime_dvd_right hZ h1
  rw [hsplit] at hrSL
  exact (Nat.Coprime.dvd_of_dvd_mul_right hcop hrSL)

theorem three_dvd_card_projectiveSL {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ Nat.card (projectiveSL n K) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  by_cases h3 : 3 ∣ Nat.card K
  · exact dvd_card_projectiveSL_of_dvd (by omega) Nat.prime_three h3
  by_cases h31 : 3 ∣ Nat.card K - 1
  · exact h31.trans (CFSG.RankThree.Automorphisms.sub_one_dvd_card_projectiveSL hn)
  have hSL := card_SL_eq (K := K) (n := n) (by omega)
  have hsplit := (scalars n K).card_eq_card_quotient_mul_card_subgroup
  have hZ := card_scalars_dvd (K := K) (n := n) (by omega)
  have hcop : Nat.Coprime 3 (Nat.card (scalars n K)) := by
    refine Nat.Coprime.coprime_dvd_right hZ ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h31
  have h2 : 3 ∣ Nat.card K ^ 2 - 1 := by
    have : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
    rcases this with h | h
    · exact absurd (by omega) h31
    · have h' : Nat.card K ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
  have hSL3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [hSL]
    refine Dvd.dvd.mul_left ?_ _
    exact h2.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1)
      (Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩))
  rw [hsplit] at hSL3
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop hSL3

theorem linear_prime_numerics {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hpT : ¬ p ∣ Nat.card (projectiveSL n K)) :
    ∃ ℓ f' : ℕ, ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ f' ∧ Nat.card K = ℓ ^ f' ∧ p ≠ ℓ ∧ 3 < p ∧
      ¬ p ∣ ℓ ^ f' - 1 := by
  obtain ⟨ℓ, f', hℓ, hcharK, hf'1, hK⟩ := exists_char_card K
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have hdvd : p ∣ Nat.card K := by
      rw [hK]
      exact dvd_pow_self p (by omega)
    exact hpT (dvd_card_projectiveSL_of_dvd (by omega) hp hdvd)
  have hp3 : 3 < p := by
    have h2 := hp.two_le
    have h3 : p ≠ 3 := by
      rintro rfl
      exact hpT (three_dvd_card_projectiveSL hn)
    obtain ⟨m, hm⟩ := hodd
    omega
  have hpq' : ¬ p ∣ ℓ ^ f' - 1 := by
    intro h
    rw [← hK] at h
    exact hpT (h.trans (CFSG.RankThree.Automorphisms.sub_one_dvd_card_projectiveSL hn))
  exact ⟨ℓ, f', hℓ, hcharK, hf'1, hK, hpℓ, hp3, hpq'⟩

theorem fixed_fieldAut_eq_range {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hpT : ¬ p ∣ Nat.card (projectiveSL n K)) {σ : K ≃+* K}
    (hσ : orderOf σ = p) :
    signalizerFixedSubgroup (fieldAut n K σ) =
      (CFSG.RankThree.PartOne.linearSubfieldInclusion n
        (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).range := by
  obtain ⟨ℓ, f', hℓ, hcharK, hf'1, hK, hpℓ, hp3, hpq'⟩ := linear_prime_numerics hn hp hodd hpT
  obtain ⟨-, -, hset, -⟩ :=
    CFSG.RankThree.PartOne.nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer hℓ hp
      hp3 hpℓ hf'1 hn hK hpq' σ hσ
  exact Subgroup.ext fun x => Set.ext_iff.mp hset x

theorem fieldClauses_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hpT : ¬ p ∣ Nat.card (projectiveSL n K))
    (hNL : ∀ σ : K ≃+* K, orderOf σ = p →
      FStarSimple (signalizerFixedSubgroup (fieldAut n K σ)) →
      NonLocalized (signalizerFixedSubgroup (fieldAut n K σ))) :
    FieldClauses p (projectiveSL n K) := by
  rintro ⟨f, hf⟩
  obtain ⟨ℓ, f', hℓ, hcharK, hf'1, hK, hpℓ, hp3, hpq'⟩ := linear_prime_numerics hn hp hodd hpT
  have hfE : f ∈ semilinearAutGroup n K :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd hn
      (by rw [hf]; exact hodd)
  have hpq : Nat.Coprime (Nat.card K - 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      hpT (h.trans (CFSG.RankThree.Automorphisms.sub_one_dvd_card_projectiveSL hn))).symm
  have hDcop : Nat.Coprime (Nat.card (linearAutGroup n K)) p := by
    obtain ⟨hID, -⟩ := standard_outer_quotients (n := n) (K := K)
    have hID' : CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K) ≤
        linearAutGroup n K := hID
    rw [← Subgroup.relIndex_mul_card
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K))
      (linearAutGroup n K), inf_of_le_left hID']
    refine Nat.Coprime.mul_left ?_ (CFSG.RankThree.Automorphisms.coprime_card_inner hp hpT)
    exact Nat.Coprime.coprime_dvd_left
      ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.relIndex_inner_linearAutGroup_dvd
        (k := K) (by omega : 1 ≤ n)).trans (Nat.gcd_dvd_right _ _)) hpq
  have hfD : f ∉ linearAutGroup n K := fun h => by
    have hdvd := orderOf_dvd_natCard (⟨f, h⟩ : linearAutGroup n K)
    rw [Subgroup.orderOf_mk, hf] at hdvd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDcop.symm hdvd)
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf'1 hn hK
  obtain ⟨-, σ, hσ, -, -⟩ := hdesc p hp hpℓ f hfE hfD hf
  obtain ⟨-, -, hset, ⟨hsimp, hnc⟩, -, -, -, -, hfix, -, -⟩ :=
    CFSG.RankThree.PartOne.nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer hℓ hp
      hp3 hpℓ hf'1 hn hK hpq' σ hσ
  have hord : orderOf (fieldAut n K σ) = p := by
    rw [CFSG.RankThree.PartOne.KCLinearSubfield.orderOf_fieldAut hn σ]; exact hσ
  have hCeq : signalizerFixedSubgroup (fieldAut n K σ) =
      (CFSG.RankThree.PartOne.linearSubfieldInclusion n
        (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).range :=
    Subgroup.ext fun x => Set.ext_iff.mp hset x
  have hsC : IsSimpleGroup (signalizerFixedSubgroup (fieldAut n K σ)) := by
    rw [hCeq]; exact hsimp
  have hnC : ∃ a b : signalizerFixedSubgroup (fieldAut n K σ), a * b ≠ b * a := by
    rw [hCeq]
    push Not at hnc
    exact hnc
  have hF := fStarSimple_of_simple hsC hnC
  refine ⟨fieldAut n K σ, hord, fixedClauses_of_stabilizer hord hF (hNL σ hσ) ?_⟩
  intro g hg
  have hmem : g ∈ fixingSubgroup (MulAut (projectiveSL n K))
      ((CFSG.RankThree.PartOne.linearSubfieldInclusion n
        (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).range :
          Set (projectiveSL n K)) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ signalizerFixedSubgroup (fieldAut n K σ) := by rw [hCeq]; exact hy
    exact hg y hy'
  rw [hfix] at hmem
  exact hmem

end CFSG.SignalizerFunctorTheorem.CatalogBridge
