module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem admissible_F4 {f : ℕ} (hf : 1 ≤ f) : StatedLieAdmissible .F4 0 2 f :=
  ⟨Nat.prime_two, hf, rfl⟩

theorem untwistedTag_F4 : untwistedTag .F4 = some ReeTag.F4.tag := rfl

theorem sec66T_K2_F4 :
    Sec66T_K2 .F4 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_F4 hM
  have hf : 1 ≤ f := hadm.2.1
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hKcard
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hKcard
  refine no_plane_of_cyclic_quotient hp (Θ.comp (MulAut.congr e).toMonoidHom) ?_ E hE hcard hEinn
  intro x hx _
  have hx' : Θ (MulAut.congr e x) = 1 := hx
  have hmem : MulAut.congr e x ∈ Θ.ker := hx'
  rw [hΘker] at hmem
  exact (mem_innerAut_congr e x).mp hmem

theorem sec66T_K1_F4 :
    Sec66T_K1 .F4 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  obtain ⟨n, f, hadmf, hM⟩ := hmodel
  have hn0 : n = 0 := ((lieModel_untwisted_iff untwistedTag_F4).mp hM).1
  subst hn0
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_F4 hM
  have hf : 1 ≤ f := hadmf.2.1
  have hp2 : p ≠ 2 := by omega
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hKcard
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  set α' : MulAut (adjointGroup ReeTag.F4.tag K) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hKcard
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α'
  obtain ⟨-, hpf, ⟨σ, hσ⟩, hdesc, -⟩ :=
    even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hKcard hp hp2 ⊤ le_top
      ⟨α', Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x a a.2 hxa
  obtain ⟨hσord, ψ, hψ⟩ := hdesc σ hσ
  obtain ⟨f', hff'⟩ := hpf
  obtain ⟨hJC1, -, hsimple, hnc, -⟩ :=
    even_F4_canonical_field_centralizer_all_orders hf hKcard σ
  exact fieldAutT_of_conj_entrywise untwistedTag_F4 hp (admissible_F4 (one_le_of_mul_eq hf hff'))
    hf hKcard e hM α σ hσord hff' ψ hψ hJC1 hsimple hnc

end CFSG.RankThree.PartOne.Sec66T
