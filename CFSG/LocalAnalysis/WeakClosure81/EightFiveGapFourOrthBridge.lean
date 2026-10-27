module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFourOrth
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module QuadraticMap Subgroup

theorem nonempty_mulEquiv_isometryCore {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nonempty (↥(CFSG.MatrixModel.isometryCore Q₀) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hcl : CFSG.MatrixModel.isometryCore Q₀ =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hQ
  refine ⟨((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap _).trans
    (MulEquiv.subgroupCongr ?_)⟩
  rw [hcl]
  exact Subgroup.map_comap_eq_self_of_surjective
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _

section Transport

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem not_centralInSylow_of_mulEquiv_orth {Y : Type} [Group Y] [Finite Y]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) (hd4 : 4 ≤ finrank K V)
    (e : Y ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (d : Y) (hdd : d * d = 1)
    (hcl : Subgroup.normalClosure ({d} : Set Y) = ⊤) :
    ¬ CentralInSylow Y (Subgroup.zpowers d) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := Finite.of_equiv Y e.toEquiv
  intro hc
  have hmap := centralInSylow_map e.toMonoidHom e.surjective _ hc
  rw [MonoidHom.map_zpowers] at hmap
  refine not_centralInSylow_orth hQ hd4 (e d) ?_ ?_ hmap
  · rw [← map_mul, hdd, map_one]
  · have := Subgroup.map_normalClosure ({d} : Set Y) e.toMonoidHom e.surjective
    rw [hcl, Set.image_singleton, Subgroup.map_top_of_surjective _ e.surjective] at this
    exact this.symm

end Transport

theorem not_centralInSylow_of_isOrthGp {Y : Type} [Group Y] [Finite Y] {m n : ℕ}
    (hY : IsOrthGp Y m n) (d : Y) (hdd : d * d = 1)
    (hcl : Subgroup.normalClosure ({d} : Set Y) = ⊤) :
    ¬ CentralInSylow Y (Subgroup.zpowers d) := by
  rcases hY with ⟨k, hk, -, F, _, _, hF, ⟨e⟩⟩ | ⟨k, hk, -, F, _, _, hF, b, c, hirr, ⟨e⟩⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    have hco : ⇑(CFSG.LieType.Universal.Spin.quadPlus k F) = CFSG.PGLModel.plusQuadForm k :=
      (CFSG.LieType.Universal.Spin.coe_quadPlus k F).trans rfl
    obtain ⟨e'⟩ := nonempty_mulEquiv_isometryCore hco
    refine not_centralInSylow_of_mulEquiv_orth
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus k F) ?_ (e.trans e') d hdd hcl
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    have hco : ⇑(CFSG.LieType.Universal.Spin.quadMinus (k + 1) F b c) =
        CFSG.PGLModel.minusQuadForm k b c :=
      (CFSG.LieType.Universal.Spin.coe_quadMinus (k + 1) F b c).trans rfl
    obtain ⟨e'⟩ := nonempty_mulEquiv_isometryCore hco
    refine not_centralInSylow_of_mulEquiv_orth
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (k + 1) F hirr)
      ?_ (e.trans e') d hdd hcl
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega

end CFSG.LocalAnalysis.WeakClosure81

end
