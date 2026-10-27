module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8Noninner

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem admissible_E7 {f : ℕ} (hf : 1 ≤ f) : StatedLieAdmissible .E7 0 2 f :=
  ⟨Nat.prime_two, hf, rfl⟩

theorem admissible_E8 {f : ℕ} (hf : 1 ≤ f) : StatedLieAdmissible .E8 0 2 f :=
  ⟨Nat.prime_two, hf, rfl⟩

theorem sec66T_K2_E78
    (t : StatedLieTag) (τ : Tag)
    (ht : untwistedTag t = some τ) (hτ : τ = .E7 ∨ τ = .E8) : Sec66T_K2 t := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv ht hM
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hKcard τ hτ
  have : IsCyclic (K ≃+* K) := isCyclic_ringAut hf hKcard
  refine no_plane_of_cyclic_quotient hp (Θ.comp (MulAut.congr e).toMonoidHom) ?_ E hE hcard hEinn
  intro x hx _
  have hx' : Θ (MulAut.congr e x) = 1 := hx
  have hmem : MulAut.congr e x ∈ Θ.ker := hx'
  rw [hΘker] at hmem
  exact (mem_innerAut_congr e x).mp hmem

theorem sec66T_K1_E78
    (t : StatedLieTag) (τ : Tag)
    (ht : untwistedTag t = some τ) (hτ : τ = .E7 ∨ τ = .E8)
    (hadm : ∀ {f : ℕ}, 1 ≤ f → StatedLieAdmissible t 0 2 f) : Sec66T_K1 t := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  obtain ⟨n, f, hadmf, hM⟩ := hmodel
  have hn0 : n = 0 := ((lieModel_untwisted_iff ht).mp hM).1
  subst hn0
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv ht hM
  have hf : 1 ≤ f := hadmf.2.1
  set α' : MulAut (adjointGroup τ K) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨hNF, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hKcard τ hτ
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hα'eq : α' = MulAut.conj x * entrywiseAdjointAut τ σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpf, ⟨ψ, hψ⟩, -⟩ :=
    even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ hf K hKcard hp ⊤ le_top
      ⟨α', Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hα'eq
  obtain ⟨f', hff'⟩ := hpf
  obtain ⟨hJC1, -, hsimple, hnc, -⟩ :=
    even_E7_E8_canonical_field_centralizer_all_orders τ hτ hf K hKcard σ
  exact fieldAutT_of_conj_entrywise ht hp (hadm (one_le_of_mul_eq hf hff')) hf hKcard e hM α σ
    hσord hff' ψ hψ hJC1 hsimple hnc

end CFSG.RankThree.PartOne.Sec66T
