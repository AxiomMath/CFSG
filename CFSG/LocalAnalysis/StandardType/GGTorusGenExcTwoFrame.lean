module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoComp
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcMain
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.GroupTheory.ConjClassGeneration

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ExcTwoGen

theorem le_closure_conj_of_ggWeylIrred {R : Type} [Group R] {E J : Subgroup R}
    (hirr : GGWeylIrred E) {w : R} (hwJ : w ∈ J) (hwE : w ∈ E) (hw1 : w ≠ 1) :
    E ≤ Subgroup.closure (⋃ n ∈ Subgroup.normalizer (E : Set R),
      (fun s => n * s * n⁻¹) '' ((J ⊓ E : Subgroup R) : Set R)) := by
  have hCE : Subgroup.closure (⋃ n ∈ Subgroup.normalizer (E : Set R),
      (fun s => n * s * n⁻¹) '' ((J ⊓ E : Subgroup R) : Set R)) ≤ E := by
    rw [Subgroup.closure_le]
    intro u hu
    simp only [Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨n, hn, s, hs, rfl⟩ := hu
    exact (Subgroup.mem_normalizer_iff.mp hn s).mp hs.2
  rcases hirr _ hCE (fun g hg u hu => CFSG.GroupTheory.conj_mem_closure_iUnion_conj _ _ hg hu) with
    hbot | htop
  · refine absurd ?_ hw1
    rw [← Subgroup.mem_bot, ← hbot]
    exact Subgroup.subset_closure (Set.mem_biUnion (Subgroup.one_mem _)
      ⟨w, Subgroup.mem_inf.mpr ⟨hwJ, hwE⟩, by group⟩)
  · exact htop.ge

section Frame


private theorem ggWeylIrred_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hpq : 3 ∣ Nat.card K + 1) {E : Subgroup (adjointGroup τ K)}
    (hE : IsElemAbelian 3 E) (hr : 3 ^ (τ.rank - 1) ≤ Nat.card E)
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) : GGWeylIrred E := by
  rcases hτ with rfl | rfl
  · have h6 : 3 ^ 6 ≤ Nat.card E := hr
    exact Irred937.ggSCWeylIrred_adjoint_E7_add (Or.inl rfl) K hpq E hE h6
      (le_trans (by norm_num) h6) hsc
  · have h7 : 3 ^ 7 ≤ Nat.card E := hr
    exact Irred937.ggSCWeylIrred_adjoint_E8_add (Or.inl rfl) K hpq E hE h7
      (le_trans (by norm_num) h7) hsc

theorem ggTorusGenR_adjoint_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) : GGTorusGenR 3 (τ.rank - 1) (adjointGroup τ K) := by
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  intro E hE hr hsc x hx hx1 J hJ c hc _
  have hSC : ∀ y ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), y ^ 3 = 1 → y ∈ E :=
    fun y hy hy3 => hsc y (fun e he => (Subgroup.mem_centralizer_iff.mp hy e he).symm) hy3
  have hF := Irred937.exists_langFrame_of_sc hτ (Or.inl rfl) K hpq E hE hr hSC
  have hcE : c ∈ E := mem_of_commute_of_langFrame_two hτ hK hsc hF
    fun e he => (Subgroup.mem_centralizer_iff.mp hc e he).symm
  obtain ⟨w, hwJ, hwE, hw1⟩ :=
    exists_mem_ne_one_of_isComponentOf_of_langFrame_two hτ hK hsc hF hx hx1 hJ
  refine ⟨J ⊓ E, Subgroup.normalizer (E : Set (adjointGroup τ K)), fun g => ⟨1, ?_⟩,
    fun s hs => ?_, inf_le_left, subset_rfl,
    le_closure_conj_of_ggWeylIrred (ggWeylIrred_two hτ hpq hE hr hsc) hwJ hwE hw1 hcE⟩
  · exact Subtype.ext (by simpa using hE.2 g g.2.2)
  · exact Subgroup.mem_centralizer_iff.mpr fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨s, hs.2⟩)

end Frame

end ExcTwoGen

end CFSG.StandardType
