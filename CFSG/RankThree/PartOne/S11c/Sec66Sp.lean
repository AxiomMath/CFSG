module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut)
open CFSG.RankThree.CASymplecticSubfield (subfieldFixedGroup)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

@[expose] def Sp4SubfieldCaseExcluded : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LieModel T .PSp 2 2 p →
    ∀ (α : MulAut T) (q : T) (U : Subgroup T), orderOf α = p → α ∉ innerAut T → q ≠ 1 →
      q ^ p = 1 → α q = q → U ≠ ⊥ → IsPGroup 2 ↥U → (∀ u ∈ U, α u ∈ U) →
      (∀ u ∈ U, q * u * q⁻¹ ∈ U) → (∃ u ∈ U, α u ≠ u ∨ q * u * q⁻¹ ≠ u) → False

theorem sec66T_K1_PSp (hdeg : Sp4SubfieldCaseExcluded) : Sec66T_K1 .PSp := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSp n 2 f := (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp n K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'ord : orderOf (MulAut.congr e α) = p := (orderOf_congr e α).trans hord
  have hα'p : MulAut.congr e α ^ p = 1 := by
    have := pow_orderOf_eq_one (MulAut.congr e α)
    rwa [hα'ord] at this
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup n K := by
    have hidx' : (spSemilinearAutGroup n K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup n K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ f - 1) = 1 := by
      have h1 : (2 : ℕ) ^ f % 2 = 0 := by
        obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hf
        rw [pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ f := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, σ, hσord, -, h, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  obtain ⟨-, hkcard, -, -, hinj, hfixiff, -, hns, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      Nat.prime_two hp (by omega) hp2 hf hn hK σ hσord
  have hfp1 : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
  have hff' : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  by_cases hdegen : n = 2 ∧ 2 ^ (f / p) = 2
  ·
    exfalso
    obtain ⟨hn2, h2⟩ := hdegen
    have h1 : f / p = 1 := by
      have h3 : (2 : ℕ) ^ (f / p) = 2 ^ 1 := by rw [h2, pow_one]
      exact Nat.pow_right_injective (le_refl 2) h3
    have hfp : f = p := by
      have h3 := Nat.mul_div_cancel' hpf
      rw [h1, mul_one] at h3
      exact h3.symm
    rw [hn2, hfp] at hM
    exact hdeg T p hp hp5 hM α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv
  ·
    obtain ⟨hsimple, hnab⟩ := hns hdegen
    have hfixeq : fixSub (fieldAut n K σ) = subfieldFixedGroup K n σ := by
      ext x
      exact (hfixiff x).symm
    let eK : ↥(subfieldFixedGroup K n σ) ≃* StatedProj (StatedSp n ↥(descentField σ)) :=
      (MonoidHom.ofInjective hinj).symm
    let eX : ↥(fixSub (fieldAut n K σ)) ≃* StatedProj (StatedSp n ↥(descentField σ)) :=
      (MulEquiv.subgroupCongr hfixeq).trans eK
    have hs1 : IsSimpleGroup ↥(subfieldFixedGroup K n σ) := hsimple
    have hs2 : IsSimpleGroup ↥(fixSub (fieldAut n K σ)) :=
      (MulEquiv.subgroupCongr hfixeq).isSimpleGroup
    have hs3 : IsSimpleGroup (StatedProj (StatedSp n ↥(descentField σ))) := eX.symm.isSimpleGroup
    have hnab' : ∃ a b : StatedProj (StatedSp n ↥(descentField σ)), a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := hnab
      exact ⟨eK x, eK y, fun hc => hxy (eK.injective (by rw [map_mul, map_mul]; exact hc))⟩
    have hXmodel : LieModel (StatedProj (StatedSp n ↥(descentField σ))) .PSp n 2 (f / p) :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨⟨Nat.prime_two, hfp1, hn, fun hc => hdegen ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩,
          ↥(descentField σ), inferInstance, inferInstance, hkcard, ⟨MulEquiv.refl _⟩⟩
    have hfix := lieModel_fixRes_of_simple hnab' eX hXmodel
    refine fieldAutT_of_conj_fix e hM hff' hfp1 α (fieldAut n K σ) h⁻¹ ?_ hfix
    rw [hαh]
    group

end CFSG.RankThree.PartOne.Sec66T
