module

public import CFSG.RankThree.PartOne.KLC.Assembly
public import CFSG.RankThree.PartOne.S11c.Sec66E6
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8Noninner

public section

namespace CFSG.RankThree.PartOne.KLC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
  CFSG.RankThree.Chevalley SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag)



theorem stdForm_E78 {t : StatedLieTag} {τ : Tag} (ht : untwistedTag t = some τ)
    (hτ : τ = .E7 ∨ τ = .E8) : StdForm t τ := by
  intro T _ _ p f₀ hp hp5 hf₀ hM α hαp hαinn
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv ht hM
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup τ K) := MulAut.congr e α with hα'
  obtain ⟨hNF, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hKcard τ hτ
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hα'eq : α' = MulAut.conj x * entrywiseAdjointAut τ σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpf, ⟨ψ, hψ⟩, -⟩ :=
    even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ hf K hKcard hp ⊤ le_top
      ⟨α', Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hα'eq
  refine ⟨K, hKf, hKfin, σ, e.trans ψ, hKcard, hσord, ?_⟩
  have : MulAut.congr (e.trans ψ) α = ψ * MulAut.congr e α * ψ⁻¹ := rfl
  rw [this]
  exact hψ

theorem stdForm_E6 : StdForm .E6 Tag.E6 := by
  intro T _ _ p f₀ hp hp5 hf₀ hM α hαp hαinn
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_E6 hM
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup Tag.E6 K) := MulAut.congr e α with hα'
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨⟨σ, -, hσord, ψ, hψ⟩, hpf, -⟩ :=
    even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hKcard Θ hΘ hp
      (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  refine ⟨K, hKf, hKfin, σ, e.trans ψ, hKcard, hσord, ?_⟩
  have : MulAut.congr (e.trans ψ) α = ψ * MulAut.congr e α * ψ⁻¹ := rfl
  rw [this]
  exact hψ

end CFSG.RankThree.PartOne.KLC
