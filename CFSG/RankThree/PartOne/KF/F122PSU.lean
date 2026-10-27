module

public import CFSG.RankThree.PartOne.S11c.Sec66PSU
public import CFSG.RankThree.PartOne.KF.F122Sp

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartTwo.Census CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)
open CFSG.Assembly.RankThreeEven (localRank)

theorem psu_aut_false {T : Type} [Group T] [Finite T] {p n f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel T .PSU n 2 f) (hn4 : 4 ≤ n)
    (hdiag : ¬ p ∣ Nat.gcd n (2 ^ f + 1))
    (hlower : ∀ (f₀ : ℕ) (k : Type) [Field k] [Finite k] [CharP k 2]
      (_ : UnitaryFieldData 2 f₀ k), f = p * f₀ →
      2 ≤ localRank p (StatedProj (StatedSU n (2 ^ f₀) k)))
    {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hLRA : LocalRankAut p T α) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨K, _, _, hU, hn3, hq, ⟨e⟩⟩ := psu_prime_form_model hC
  have hfinP : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv T e.toEquiv
  set α' := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hmem => hαinn ((mem_innerAut_congr e α).mp hmem)
  have hα'p : α' ^ p = 1 := by
    have := pow_orderOf_eq_one α'
    rwa [hα'ord] at this
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set σ := primeFormFieldFactor hU hC1 hn3 hq α' with hσ
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hαD : α' ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor hU hC1 hn3 hq]
      exact hσ1
    exact hα'inn (mem_innerAut_of_mem_D hU hn3 hq hp hdiag hαD hα'p)
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hα'p, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, -, -, -, -, M, hMconj⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hU hn3 hq hp hp2 hp2
      α' hα'ord σ rfl hσord
  obtain ⟨f', hff'⟩ := hpf
  have hf : 1 ≤ f := by
    have := hC.1.2.1
    exact this
  have hf'1 : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h0 | h0
    · rw [h0, mul_zero] at hff'
      omega
    · exact h0
  have hdiv : f / p = f' := by rw [hff', Nat.mul_div_cancel_left _ hp.pos]
  set β := primeFormFieldHom hU hC1 σ with hβ
  set ψ := (primeFormConjHom hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ with hψ
  have hψα : ψ * α' * ψ⁻¹ = β := by
    rw [hψ, inv_inv]
    exact hMconj
  have hq₀ : ¬(n = 3 ∧ 2 ^ (f / p) = 2) := fun hc => by omega
  set h₀ := fixSubfield_unitaryFieldData hU hp hp2 hσord with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar hU hp hp2 hσord
  set N := (subfieldPSU hU h₀ hbar n).range with hN
  have hNΓ : N ≤ fixSub β := range_subfieldPSU_le hU n h₀ hbar
  have hjinj := subfieldPSU_injective hU h₀ hbar n (by omega)
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥N := MonoidHom.ofInjective hjinj
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h₀
    (isPrimeFormGram_one (n := n)) hn3 hq₀
  let eS : StatedProj (StatedSU n (2 ^ (f / p)) (fixSubfield σ)) ≃* ↥N :=
    ((eT.trans (unitaryPSUEquiv h₀ (by omega : 1 ≤ n))).symm).trans eJ
  have hff'' : f = p * (f / p) := by rw [hdiv]; exact hff'
  have : Fintype ↥(fixSubfield σ) := Fintype.ofFinite _
  have : CharP ↥(fixSubfield σ) 2 :=
    charP_of_card_eq_prime_pow (f := 2 * (f / p)) (by rw [← Nat.card_eq_fintype_card]; exact h₀.card)
  have hNrank : 2 ≤ localRank p ↥N := by
    rw [← localRank_eq_of_mulEquiv eS hp]
    exact hlower (f / p) ↥(fixSubfield σ) h₀ hff''
  have hβrank : 2 ≤ localRank p ↥(fixSub β) :=
    hNrank.trans (PlaneAux.localRank_le_of_injective hp (Subgroup.inclusion hNΓ)
      (Subgroup.inclusion_injective hNΓ))
  have hψ' : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β := by rw [hψα]
  let e12 : ↥(fixSub α) ≃* ↥(fixSub β) :=
    ((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ')
  have hN2 : 2 ≤ localRank p ↥(fixSub α) := by
    rw [localRank_eq_of_mulEquiv e12 hp]
    exact hβrank
  exact false_of_localRank_fixed hp hαp hαinn (fixSub α) (fun y hy => hy) hN2 hLRA

theorem kf122Row9_holds : KF122Row 9 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, -, hpq, hC⟩ := hmodel
  refine psu_aut_false (n := 4) hp hp5 hC (by norm_num) ?_ ?_ hαp hαinn hLRA
  · intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  · intro f₀ k _ _ _ h₀ hf
    have hpk : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp (hf ▸ hpq)
    have h1 := le_localRank_statedSU_torus (K := k) h₀ hp (k := 1) (n := 4) hpk (by norm_num)
      (Or.inr fun hd => by
        have := Nat.le_of_dvd (by norm_num) hd
        omega)
    simpa using h1

end CFSG.RankThree.PartOne
