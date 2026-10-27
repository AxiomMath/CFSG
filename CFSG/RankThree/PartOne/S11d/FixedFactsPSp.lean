module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpMain
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut)
open CFSG.RankThree.CASymplecticSubfield (subfieldFixedGroup)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

theorem fixedFacts_PSp {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : LieModel T .PSp n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (hadm₀ : StatedLieAdmissible .PSp n 2 f₀)
    (α : MulAut T) (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixedFacts p α := by
  have hC : StatedClassicalModel T .PSp n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ n := hC.1.2.2.1
  have hp2 : p ≠ 2 := by omega
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp n K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p :=
    orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ (innerAut _).one_mem))
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
    have hcop : Nat.gcd 2 (2 ^ (p * f₀) - 1) = 1 := by
      have h1 : (2 : ℕ) ^ (p * f₀) % 2 = 0 := by
        obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hf
        rw [hg, pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ (p * f₀) := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, σ, hσord, -, h, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  obtain ⟨-, hkcard, -, -, hinj, hfixiff, -, hns, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      Nat.prime_two hp (by omega) hp2 hf hn hK σ hσord
  rw [hfdiv] at hkcard
  have hdegen : ¬ (n = 2 ∧ 2 ^ (p * f₀ / p) = 2) := by
    rw [hfdiv]
    exact fun hc => hadm₀.2.2.2 (by rw [hc.1, hc.2])
  obtain ⟨hsimple, hnab⟩ := hns hdegen
  have hfixeq : fixSub (fieldAut n K σ) = subfieldFixedGroup K n σ := by
    ext x
    exact (hfixiff x).symm
  have hNL : NonLocalized (fixSub (fieldAut n K σ)) := by
    have : NeZero n := ⟨by omega⟩
    have hσp : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
    have h1 : fixSub (fieldAut n K σ) =
        (CFSG.RankThree.PartOne.KCSpComm.subfieldProj (r := n) σ).range :=
      CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range (hp.odd_of_ne_two hp2) hσp
    rw [h1]
    exact SignalizerFunctorTheorem.NonLocal.nonLocalized_spSubfield hn σ
  set φ : T ≃* StatedProj (StatedSp n K) := e.trans (h⁻¹ : MulAut (StatedProj (StatedSp n K)))
    with hφ
  have hφα : MulAut.congr φ α = fieldAut n K σ := by
    have : MulAut.congr φ α = h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  let eK : ↥(subfieldFixedGroup K n σ) ≃* StatedProj (StatedSp n ↥(descentField σ)) :=
    (MonoidHom.ofInjective hinj).symm
  let eX : ↥(fixSub (MulAut.congr φ α)) ≃* StatedProj (StatedSp n ↥(descentField σ)) :=
    (MulEquiv.subgroupCongr (by rw [hφα, hfixeq])).trans eK
  have hs1 : IsSimpleGroup ↥(subfieldFixedGroup K n σ) := hsimple
  have hs3 : IsSimpleGroup (StatedProj (StatedSp n ↥(descentField σ))) := eK.symm.isSimpleGroup
  have hnab' : ∃ a b : StatedProj (StatedSp n ↥(descentField σ)), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨eK x, eK y, fun hc => hxy (eK.injective (by rw [map_mul, map_mul]; exact hc))⟩
  have hfp1 : 1 ≤ f₀ := hf₀
  have hXmodel : LieModel (StatedProj (StatedSp n ↥(descentField σ))) .PSp n 2 f₀ :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨⟨Nat.prime_two, hfp1, hn, fun hc => hdegen ⟨(Prod.mk.inj hc).1, by
          rw [hfdiv]; exact (Prod.mk.inj hc).2⟩⟩,
        ↥(descentField σ), inferInstance, inferInstance, hkcard, ⟨MulEquiv.refl _⟩⟩
  exact fixedFacts_of_simple φ α hM hf₀ eX hnab' (by rw [hφα]; exact hNL) (Or.inl hXmodel)

theorem tagFixedFacts_PSp : TagFixedFacts .PSp := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hadm : StatedLieAdmissible .PSp n 2 f₀ := by
    rcases admissible_of_fixModel hX₀ with h | ⟨h, -, -⟩
    · exact h
    · exact absurd h (by decide)
  exact fixedFacts_PSp hp hp5 hM hf₀ hadm α hαp hαinn

end CFSG.RankThree.PartOne.FieldFix
