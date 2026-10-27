module

public import CFSG.RankThree.PartOne.KLC.Assembly
public import CFSG.RankThree.PartOne.S11c.Sec66G2

public section

namespace CFSG.RankThree.PartOne.TCX.G2

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
  CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

open CFSG.RankThree.PartOne.KLC (StdForm)


theorem stdForm_G2 : StdForm .G2 Tag.G2 := by
  intro T _ _ p f₀ hp hp5 hf₀ hM α hαp hαinn
  have hf : 2 ≤ p * f₀ := by
    have : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
    have : 2 ≤ p := hp.two_le
    nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
      hKcard
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup Tag.G2 K) := MulAut.congr e α with hα'
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf K hKcard
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hform : α' = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hxσ u, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_entrywiseAdjointAut, Subgroup.coe_inv]
  obtain ⟨hσord, -, ⟨h, hh⟩, -⟩ := even_G2_noninner_prime_local_core_trivial (K := K) (f := p * f₀)
    (p := p) hf hKcard hp ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
    (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hform
  let φ : T ≃* adjointGroup Tag.G2 K := e.trans (MulAut.conj h)
  refine ⟨K, hKf, hKfin, σ, φ, hKcard, hσord, ?_⟩
  have h2 : MulAut.congr φ α = MulAut.conj h * MulAut.congr e α * (MulAut.conj h)⁻¹ := rfl
  exact h2.trans hh

end CFSG.RankThree.PartOne.TCX.G2
