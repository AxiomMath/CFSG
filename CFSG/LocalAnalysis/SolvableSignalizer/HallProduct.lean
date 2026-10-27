module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.Adapter
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianHallProductCompleteness

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise

open Internal
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]

omit [Finite A] [Finite G] in
private theorem lift_mul_lift_eq_lift_top_iff (α : A →* MulAut G) (H K : Subgroup G) :
    (lift α H : Set (Ambient α)) * (lift α K : Set (Ambient α)) =
        (lift α ⊤ : Set (Ambient α)) ↔
      (H : Set G) * (K : Set G) = Set.univ := by
  simp only [lift, Subgroup.coe_map, ← Set.image_mul, Subgroup.coe_top]
  exact (embed_injective α).image_injective.eq_iff

theorem isComplete_of_abelian_hall_product
    (p : ℕ) (α : A →* MulAut G) (θ : A → Subgroup G)
    (d : Datum p α θ) (hloc : LocallyComplete p α θ)
    (hrank : p ^ 3 ≤ Nat.card A)
    (q : ℕ) (hq : q ∈ spectrum θ) (Q : Subgroup G)
    (hQ : CompatibleAt p α θ {q} Q) (habelian : IsMulCommutative Q)
    (hprod : (completion (primeSubfunctor α θ (spectrum θ \ {q})) : Set G) *
      (Q : Set G) = Set.univ)
    : IsComplete p α θ ∧ completion θ = ⊤ ∧ Group.IsSolvable G := by
  have hlarge : p ^ (1 + 2) ≤ Nat.card (actor α) := by
    rw [card_actor]
    exact hrank
  have hqspec : q ∈ signalizerSpectrum p 1 (actor α) (values α θ) := by
    rw [signalizerSpectrum_values d]
    exact hq
  have hcompat : solvableSignalizerCompatible p 1 (actor α) (values α θ) (lift α Q) :=
    (compatible_iff_lift d Q).mp hQ.1
  have hpg : IsPGroup q (lift α Q) :=
    (CFSG.primeSupported_singleton_iff_isPGroup q hq.1).mp hQ.2 |>.of_equiv (liftEquiv α Q)
  have hab : IsMulCommutative (lift α Q) := by
    refine IsMulCommutative.of_comm (fun x y => ?_)
    obtain ⟨a, rfl⟩ := (liftEquiv α Q).surjective x
    obtain ⟨b, rfl⟩ := (liftEquiv α Q).surjective y
    rw [← map_mul, ← map_mul, mul_comm']
  have hvalues_le : ∀ S ∈ signalizerFunctorEk p 1 (actor α), values α θ S ≤ lift α ⊤ :=
    fun _ _ => (lift_le_lift α).mpr le_top
  have hwhole : subgroupProduct
        (signalizerPrimeCompletion p 1 (actor α) (values α θ)
          (signalizerSpectrum p 1 (actor α) (values α θ) \ {q})) (lift α Q) =
      (lift α ⊤ : Set (Ambient α)) := by
    have hK : signalizerPrimeCompletion p 1 (actor α) (values α θ) (spectrum θ \ {q}) =
        lift α (completion (primeSubfunctor α θ (spectrum θ \ {q}))) :=
      iSup_signalizerPrimeValue_values d _
    rw [signalizerSpectrum_values d, hK]
    exact (lift_mul_lift_eq_lift_top_iff α _ _).mpr hprod
  obtain ⟨hcompletion, hcompatible⟩ :=
    CFSG.SignalizerFunctor.Helpers.abelian_hall_product_complete p 1 q d.prime hq.1
      (actor α) (lift α ⊤) (lift α Q) (isElemAbelian_actor d) hlarge (values α θ)
      (solvableSignalizerConditions_values d) ((locallyComplete_iff d).mp hloc) hqspec hcompat.1
      hpg hab hvalues_le hwhole
  have hctop : completion θ = ⊤ := by
    apply lift_injective α
    rw [← iSup_values_eq_lift_completion d]
    exact hcompletion
  have hcomplete : IsComplete p α θ :=
    (compatible_iff_lift d (completion θ)).mpr (by rw [hctop]; exact hcompatible)
  have hsolv : Group.IsSolvable (⊤ : Subgroup G) := hctop ▸ hcomplete.2.1
  exact ⟨hcomplete, hctop,
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G)).toMonoidHom)
      (Subgroup.topEquiv (G := G)).surjective⟩

end CFSG.SolvableSignalizer
