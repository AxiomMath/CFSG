module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.LieType.Chevalley.BorelStructure
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcAdj
import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
import CFSG.LieType.Chevalley.PinnedBridge
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.LieType.Chevalley.PerfectSimpleRoot
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LayerExc

theorem jcoreE_exists_unit {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpf : p ∣ 2 ^ f - 1) : ∃ t : (GaloisField 2 f)ˣ, (t : GaloisField 2 f) ^ 2 ≠ 1 := by
  haveI := Fact.mk hp
  have hcard : p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rwa [Nat.card_units, GaloisField.card 2 f (by omega)]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hcard
  refine ⟨t, fun h => hp2 ?_⟩
  have h1 : t ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [ht] at h2
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2

private theorem jcoreE_adj_component
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) {t : Kˣ}
    (ht : (t : K) ^ 2 ≠ 1) {l : Fin τ.rank → Kˣ} (hl : l ^ p = 1) {v : adjointGroup τ K}
    (hv : (v : ModGL τ K) = rootDiagUnit τ l) {L : Subgroup (adjointGroup τ K)}
    (hL : IsComponentOf L (Subgroup.centralizer {v})) :
    ∃ i : KernelComponent (famChar ({l} : Set (Fin τ.rank → Kˣ))),
      L = (componentRootSpan K (famChar ({l} : Set (Fin τ.rank → Kˣ))) i).comap
        (adjointGroup τ K).subtype := by
  classical
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hF : ∀ b ∈ ({l} : Set (Fin τ.rank → Kˣ)), ∃ n : ℕ, b ^ p ^ n = 1 := fun b hb =>
    ⟨1, by rw [pow_one, Set.mem_singleton_iff.mp hb]; exact hl⟩
  rw [LayerPDivExc.centralizer_singleton_eq_famCentralizer hv] at hL
  exact StepTwoToralExc.exists_eq_of_isComponentOf_subCoreFamily
    (LayerPDivExc.isSubCoreFamily_famCentralizer _ ht
      (exists_ggDer_famStabilizerSubgroup_le_reflection hp _ hF)) hL

private theorem jcoreE_rootLevi_le
    {τ : Tag} (F : RootOperatorFamily τ) {K : Type} [Field K]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) :
    ∃ γ, IsRoot τ γ ∧ ggRootLevi (adjDatum F K) γ ≤
      (componentRootSpan K χ i).comap (adjointGroup τ K).subtype := by
  obtain ⟨α, rfl⟩ := Quotient.exists_rep i
  have hle : ∀ β ∈ componentRoots χ ⟦α⟧, rootGroup F K β ≤
      (componentRootSpan K χ ⟦α⟧).comap (adjointGroup τ K).subtype := by
    intro β hβ g hg
    have hr : IsRoot τ β := hβ.fst.1
    rw [rootGroup_of_isRoot hr, ← F.subgroupOf_rootSubgroup_eq K ⟨β, hr⟩] at hg
    have h1 : CFSG.Blueprint.Chevalley.rootSubgroup τ K β ≤
        rootSpan τ K (componentRoots χ ⟦α⟧) := le_iSup₂_of_le β hβ le_rfl
    exact h1 (Subgroup.mem_subgroupOf.mp hg)
  have hα : (α : Fin τ.rank → ℤ) ∈ componentRoots χ ⟦α⟧ := ⟨α.2, rfl⟩
  exact ⟨α, α.2.1, sup_le (hle _ hα) (hle _ (StepTwoToralExc.neg_mem_componentRoots' hα))⟩

theorem jcoreE_adj_rootLevi
    {τ : Tag} (F : RootOperatorFamily τ) {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) {v : adjointGroup τ K}
    (hv : (v : ModGL τ K) ∈ torusGroup τ K) (hvp : v ^ p = 1) {L : Subgroup (adjointGroup τ K)}
    (hL : IsComponentOf L (Subgroup.centralizer {v})) :
    ∃ γ, IsRoot τ γ ∧ ggRootLevi (adjDatum F K) γ ≤ L := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hv
  have hlp : l ^ p = 1 := rootDiagUnit_injective (by
    rw [← rootDiagUnit_pow, ← hl, rootDiagUnit_one, ← Subgroup.coe_pow, hvp, Subgroup.coe_one])
  obtain ⟨i, rfl⟩ := jcoreE_adj_component hp ht hlp hl hL
  exact jcoreE_rootLevi_le F i

end CFSG.StandardType

end
