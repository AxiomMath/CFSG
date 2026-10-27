module

public import CFSG.SignalizerFunctorTheorem.Solvable.ThompsonBridge
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Solvable

variable {G : Type*} [Group G] [Finite G]

theorem zj_normalizer_refinement
    (prime rank q : ℕ) (prime_prime : prime.Prime) (q_prime : q.Prime) (hq : 5 ≤ q)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (W : Subgroup G) (hW : W ≠ ⊥) (hWcomp : solvableSignalizerCompatible prime rank actor values W)
    (hWq : IsPGroup q W)
    (P : Sylow q (signalizerNormalizerCompletion prime rank actor values W))
    (normalized : actor ≤ Subgroup.normalizer
      ((P : Subgroup (signalizerNormalizerCompletion prime rank actor values W)).map
        (signalizerNormalizerCompletion prime rank actor values W).subtype : Set G)) :
    let U := signalizerNormalizerCompletion prime rank actor values W
    let T := (P : Subgroup U).map U.subtype
    let Z := embeddedOrderThompsonCenter T
    let L := signalizerNormalizerCompletion prime rank actor values Z
    T ≠ ⊥ ∧ Z ≠ ⊥ ∧ solvableSignalizerCompatible prime rank actor values T ∧
      solvableSignalizerCompatible prime rank actor values Z ∧
      solvableSignalizerCompatible prime rank actor values L ∧
      (primeSetCore (GroupType := U) ({q}ᶜ)).map U.subtype ⊔ (U ⊓ L) = U ∧ W ≤ L := by
  intro U T Z L
  have hUcomp : solvableSignalizerCompatible prime rank actor values U :=
    locally_complete.1 W hW hWcomp
  have : Group.IsSolvable U := hUcomp.2
  have control := signalizer_normalizer_completion_control prime rank prime_prime actor W elementary
    large values conditions.coprime hWcomp.1 hUcomp.1
  have hWU : W ≤ U := control.2.1
  have : (W.subgroupOf U).Normal := control.2.2.1
  have hWqU : IsPGroup q (W.subgroupOf U) := hWq.comap_of_injective U.subtype U.subtype_injective
  have hWT : W ≤ T := by
    have hmap := Subgroup.map_mono (f := U.subtype) (hWqU.le_sylow_of_normal P)
    rwa [Subgroup.map_subgroupOf_eq_of_le hWU] at hmap
  have hTne : T ≠ ⊥ := fun h => hW (le_bot_iff.mp (h ▸ hWT))
  have hTq : IsPGroup q T := P.isPGroup'.map U.subtype
  have hTcomp : solvableSignalizerCompatible prime rank actor values T :=
    solvable_signalizer_compatible_of_le prime rank actor values U T hUcomp
      (Subgroup.map_subtype_le _) normalized
  obtain ⟨hZne, -⟩ := embedded_order_thompson_center_pgroup q q_prime T hTq hTne
  obtain ⟨hZle, -, hZnorm⟩ := embedded_order_thompson_center_properties T actor normalized
  have hZcomp : solvableSignalizerCompatible prime rank actor values Z :=
    solvable_signalizer_compatible_of_le prime rank actor values T Z hTcomp hZle hZnorm
  have hLcomp : solvableSignalizerCompatible prime rank actor values L :=
    locally_complete.1 Z hZne hZcomp
  have controlZ := signalizer_normalizer_completion_control prime rank prime_prime actor Z
    elementary large values conditions.coprime hZcomp.1 hLcomp.1
  have hLle : L ≤ Subgroup.normalizer (Z : Set G) :=
    iSup_le fun _ => iSup_le fun _ => inf_le_right
  have hnormalizerNormalized : actor ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.normalizer (Z : Set G) : Subgroup G) : Set G) :=
    normalizer_inf_of_le actor U _ hUcomp.1.1 (normalizer_normalized actor Z hZnorm)
  have hnormalizerCompatible := solvable_signalizer_compatible_of_le prime rank actor values U _
    hUcomp inf_le_left hnormalizerNormalized
  have hnormalizerLe : U ⊓ Subgroup.normalizer (Z : Set G) ≤ L :=
    controlZ.2.2.2 _ hnormalizerCompatible.1 inf_le_right
  have hintersection : U ⊓ L = U ⊓ Subgroup.normalizer (Z : Set G) :=
    le_antisymm (inf_le_inf le_rfl hLle) (le_inf inf_le_left hnormalizerLe)
  have hfactor := solvable_zj_factorization q_prime hq U P
  have hWnormalizer : W ≤ Subgroup.normalizer (Z : Set G) :=
    normal_prime_subgroup_le_ambient_supplement q q_prime U W _ hWU ‹_› hWq hfactor.symm
  exact ⟨hTne, hZne, hTcomp, hZcomp, hLcomp, by rwa [hintersection],
    (le_inf hWU hWnormalizer).trans hnormalizerLe⟩

end CFSG.SignalizerFunctorTheorem.Solvable
