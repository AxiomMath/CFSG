module

public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem isInnerAut_of_mem_commutator_of_trialityD4
    {X : Type} [Group X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) {σ : MulAut X}
    (hσ : σ ∈ commutator (MulAut X)) : IsInnerAut σ := by
  obtain ⟨⟨-, hn, -⟩, K, _, _, hK, σK, hσK, ⟨e⟩⟩ := hX
  have hσb : Function.Bijective σK :=
    ⟨σK.injective, Finite.surjective_of_injective σK.injective⟩
  let σe : K ≃+* K := RingEquiv.ofBijective σK hσb
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -, -, -, ⟨f⟩⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σe hσK
  let C := graphFixedRootGroup TwistTag.D4 K σe.toRingHom
  let eC : X ≃* C := e.trans f
  have hτ : MulAut.congr eC σ ∈ commutator (MulAut C) := by
    have h1 : MulAut.congr eC σ ∈
        (commutator (MulAut X)).map (MulAut.congr eC).toMonoidHom := ⟨σ, hσ, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  haveI : IsCyclic (K ≃+* K) := hcyc
  haveI : IsMulCommutative (K ≃+* K) := IsCyclic.isMulCommutative
  have hcomm_le : commutator (MulAut C) ≤ Θ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' (Θ a) (Θ b)
  have hinner : IsInnerAut (MulAut.congr eC σ) := by
    rw [IsInnerAut, ← hker]
    exact hcomm_le hτ
  exact (isInnerAut_congr eC σ).mp hinner

end CFSG.RankThree.PartTwo.KFacts

end
