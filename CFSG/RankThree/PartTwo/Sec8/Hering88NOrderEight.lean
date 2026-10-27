module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2TwoProof
public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2TwoResidual

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

namespace G2Two

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open
open scoped commutatorElement


theorem mats8_sq : ∀ i : Fin 8, mmul (mats8 i) (mats8 i) = 1 := by decide +kernel

theorem ord8_checks : mpow (mword [0, 1, 4, 0, 4, 1]) 8 = 1 ∧ mpow (mword [0, 1, 4, 0, 4, 1]) 4 ≠ 1 := by
  decide +kernel

theorem gens8_inv (i : Fin 8) : (gens8 i)⁻¹ = gens8 i :=
  inv_eq_of_cmat (cmat_gens8 i) (by rw [← mmul_eq]; exact mats8_sq i)

@[expose] noncomputable def ord8 : ↥(cayleyGroup (ZMod 2)) := ⁅gens8 0, gens8 1 * gens8 4⁆

theorem ord8_eq : ord8 = wordEval gens8 [0, 1, 4, 0, 4, 1] := by
  rw [ord8, commutatorElement_def, _root_.mul_inv_rev, gens8_inv, gens8_inv, gens8_inv]
  simp only [wordEval, mul_one, mul_assoc]

theorem ord8_mem : ord8 ∈ commutator ↥(cayleyGroup (ZMod 2)) :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem ord8_pow_eight : ord8 ^ 8 = 1 :=
  cmat_injective (by rw [map_pow, ord8_eq, cmat_wordEval_gens8, ← mpow_eq, ord8_checks.1, map_one])

theorem ord8_pow_four : ord8 ^ 4 ≠ 1 := fun h => ord8_checks.2 (by
  rw [mpow_eq, ← cmat_wordEval_gens8, ← ord8_eq, ← map_pow, h, map_one])

end G2Two

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open


theorem map_commutator_mulEquiv {M M' : Type*} [Group M] [Group M'] (f : M ≃* M') :
    (commutator M).map f.toMonoidHom = commutator M' := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ f.surjective]

theorem exists_pow_eight_of_isoGTwoEven_one {Q : Type} [Group Q] {R : Subgroup Q}
    (h : IsoGTwoEven R 1) :
    ∃ t ∈ inSubgroup perfectResidual R, t ^ 8 = 1 ∧ t ^ 4 ≠ 1 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨φ, -⟩ := G2Two.exists_mulEquiv_cayley_two hK2
  have hres := (perfectResidual_g2_two hK2).1
  set ψ : ↥R ≃* ↥(cayleyGroup (ZMod 2)) := e.trans φ with hψ
  have hmem : ψ.symm G2Two.ord8 ∈ perfectResidual R := by
    rw [← KFacts.perfectResidual_map_mulEquiv e.symm, hres]
    refine ⟨φ.symm G2Two.ord8, ?_, rfl⟩
    rw [← map_commutator_mulEquiv φ.symm]
    exact ⟨_, G2Two.ord8_mem, rfl⟩
  refine ⟨(ψ.symm G2Two.ord8 : Q), ⟨_, hmem, rfl⟩, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, G2Two.ord8_pow_eight, map_one, Subgroup.coe_one]
  · intro h4
    apply G2Two.ord8_pow_four
    have h1 : ψ.symm (G2Two.ord8 ^ 4) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4)
    exact ψ.symm.injective (h1.trans (map_one _).symm)

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
