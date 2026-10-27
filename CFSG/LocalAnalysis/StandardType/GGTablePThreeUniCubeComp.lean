module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCompEq
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeIsComp
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeQS
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCQ

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

theorem uni_cube_block_component {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg n K q)} (hδ : IsConjBy d δ') {μ : K} (hμ : μ ^ 3 = 1) (hQS : CubeBlockQS q d μ) :
    ∃ Q : Subgroup (PSUg n K q), IsComponentOf Q (ggAutFixedSubgroup δ') ∧
      (∀ x, x ∈ Q ↔ InCubeBlock d μ x) ∧
      Nonempty (Q ⧸ Subgroup.center Q ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d μ))) K q)) := by
  refine ⟨eigBlock q d μ, ?_, fun x => mem_eigBlock_iff, ?_⟩
  · exact uni_cube_eigBlock_isComponent hK hq3 hn hd hd3 hδ hμ hQS
  · exact uni_cube_eigBlock_centerQuot hK hq3 hn hd hd3 hμ

theorem uni_cube_component_block {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg n K q)} (hδ : IsConjBy d δ') {Q : Subgroup (PSUg n K q)}
    (hQ : IsComponentOf Q (ggAutFixedSubgroup δ')) :
    ∃ μ : K, μ ^ 3 = 1 ∧ CubeBlockQS q d μ ∧ ∀ x, x ∈ Q ↔ InCubeBlock d μ x := by
  obtain ⟨μ, hμ, hQe⟩ := uni_cube_component_eq_eigBlock hK hq3 hn hd hd3 hδ hQ
  subst hQe
  exact ⟨μ, hμ, (uni_cube_eigBlock_quasisimple_iff hK hq3 hn hd hd3 hμ).mp hQ.2.2,
    fun x => mem_eigBlock_iff⟩

end CFSG.StandardType.TablePThreeKG

end
