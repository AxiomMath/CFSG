module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSolvable
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.PartOne.KE.SLnShape

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.Open (IsElemAbelian)

private theorem ggPA3_isSolvable_familyCentralizer_unit
    {τ : Tag} {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (a : Fin τ.rank → Lˣ)
    (ha : ∀ i, a i ^ p = 1) (hKer : familyKernel (fun _ : Unit => a) = ∅) :
    Group.IsSolvable ↥(familyCentralizer τ L (fun _ : Unit => a)) := by
  classical
  have hker' : rootCharKernel a = ∅ := by
    rw [← hKer]
    ext α
    change (IsRoot τ α ∧ rootChar a α = 1) ↔
      (IsRoot τ α ∧ ∀ _ : Unit, rootChar a α = 1)
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 ()⟩⟩
  have hKR : kernelReflectionGroup a = ⊥ := by
    rw [kernelReflectionGroup, hker']
    simp
  have hNbot : (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) = ⊥ := by
    rw [hKR]
    ext x
    simp [Subgroup.mem_subgroupOf]
  haveI hHs : Group.IsSolvable ↥(rootCharStabilizerSubgroup a) := by
    have hQ : Group.IsSolvable (↥(rootCharStabilizerSubgroup a) ⧸
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_quotient hp ha
    haveI := hQ
    have hN : Group.IsSolvable ↥((kernelReflectionGroup a).subgroupOf
        (rootCharStabilizerSubgroup a)) := by
      rw [hNbot]
      infer_instance
    haveI := hN
    exact Group.isSolvable_of_ker_le_range
      ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).subtype
      (QuotientGroup.mk' ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hgroup : familyGroup (K := L) (fun _ : Unit => a) = torusGroup τ L := by
    rw [familyGroup, hKer, rootSpan]
    simp
  have hmono : ∀ g : ↥(familyCentralizer τ L (fun _ : Unit => a)),
      ∃ w ∈ rootCharStabilizerSubgroup a, ∃ m ∈ torusGroup τ L,
        (g : ModGL τ L) = m * canonicalRep (coxeterSystem τ) L w := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := familyCentralizer_le_mul τ L (fun _ : Unit => a) g.2
    rw [hgroup] at hm
    exact ⟨w, mem_rootCharStabilizerSubgroup.2 (hw ()), m, hm, hmg⟩
  have hmem : ∀ g : ↥(familyCentralizer τ L (fun _ : Unit => a)),
      (g : ModGL τ L) ∈ monomialSubgroup τ L := by
    intro g
    obtain ⟨w, -, m, hm, hmg⟩ := hmono g
    rw [hmg]
    exact mul_mem (Subgroup.mem_sup_left hm)
      (canonicalRep_mem_monomialSubgroup' (K := L) w)
  let ψ : ↥(familyCentralizer τ L (fun _ : Unit => a)) →* monomialSubgroup τ L :=
    MonoidHom.codRestrict (Subgroup.subtype _) _ hmem
  have hψ : Function.Injective ψ := by
    intro g g' h
    exact Subtype.ext (congrArg (fun x : monomialSubgroup τ L => (x : ModGL τ L)) h)
  obtain ⟨ρ, hρmaps, hsolv⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.isSolvable_comap_weylQuotient τ L
      (rootCharStabilizerSubgroup a)
  have hρψ : ∀ g, ρ (ψ g) ∈ rootCharStabilizerSubgroup a := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := hmono g
    have h1 : MapsRootLines (ψ g : (Module.End L (RootModule τ L))ˣ) (1 * w) := by
      have e : (ψ g : (Module.End L (RootModule τ L))ˣ) =
          m * canonicalRep (coxeterSystem τ) L w := hmg
      rw [e]
      exact (mapsRootLines_of_mem_torusGroup hm).mul (mapsRootLines_canonicalRep w)
    rw [(hρmaps (ψ g)).unique h1, one_mul]
    exact hw
  let ψ' : ↥(familyCentralizer τ L (fun _ : Unit => a)) →*
      ↥((rootCharStabilizerSubgroup a).comap ρ) :=
    ψ.codRestrict ((rootCharStabilizerSubgroup a).comap ρ) hρψ
  haveI := hsolv
  refine Group.isSolvable_of_isSolvable_injective (f := ψ') ?_
  intro g g' h
  exact hψ (congrArg Subtype.val h)

theorem isSolvable_centralizer_of_familyKernel_empty
    {τ : Tag} {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (a : Fin τ.rank → Lˣ)
    (ha : ∀ i, a i ^ p = 1) (hKer : familyKernel (fun _ : Unit => a) = ∅) :
    Group.IsSolvable ↥(adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
  classical
  have hEq : (adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a}) =
      familyCentralizer τ L (fun _ : Unit => a) := by
    ext g
    simp only [familyCentralizer, Subgroup.mem_inf, Subgroup.mem_iInf]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 ()⟩⟩
  have hfam := ggPA3_isSolvable_familyCentralizer_unit (p := p) hp a ha hKer
  let e : ↥(adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a}) →*
      ↥(familyCentralizer τ L (fun _ : Unit => a)) :=
    MonoidHom.codRestrict (Subgroup.subtype _) _ (fun x => hEq ▸ x.2)
  have he : Function.Injective e := fun x y h =>
    Subtype.ext (congrArg
      (fun z : ↥(familyCentralizer τ L (fun _ : Unit => a)) => (z : ModGL τ L)) h)
  haveI : Group.IsSolvable ↥(familyCentralizer τ L (fun _ : Unit => a)) := hfam
  exact Group.isSolvable_of_isSolvable_injective (f := e) he

end CFSG.StandardType
