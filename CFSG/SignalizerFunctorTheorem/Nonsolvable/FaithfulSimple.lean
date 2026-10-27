module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.Reduction
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.FaithfulSimple.FixedSection

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

@[expose] def NoFaithfulKStarSimpleAt (p : ℕ) : Prop :=
  ∀ (V : Type) [Group V] [Finite V] [IsSimpleGroup V], (∃ x y : V, x * y ≠ y * x) →
    Nat.Coprime p (Nat.card V) → ∀ A : Subgroup (MulAut V), IsElemAbelian p A →
    p ^ 3 ≤ Nat.card A →
    (∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (signalizerFixedSubgroup a)) → False

theorem faithfulSectionExclusionAt_of (p : ℕ) (hp : p.Prime) (h : NoFaithfulKStarSimpleAt p) :
    FaithfulSectionExclusionAt p := by
  intro G _ _ A hA hlarge Θ _ hB hcomp K L hKW hLK _ hAK hAL hsimple hnc
  by_contra hcon
  have := hsimple
  have hinj : Function.Injective (sectionAction hAK hAL) := by
    rw [injective_iff_map_eq_one]
    intro a ha1
    by_contra hne
    refine hcon ⟨a, a.2, fun h1 => hne (Subtype.ext h1), fun x hx => ?_⟩
    exact (sectionAction_mk_eq_iff hAK hAL a ⟨x, hx⟩).mp (by rw [ha1]; rfl)
  have hcopK : Nat.Coprime p (Nat.card K) :=
    hcomp.1.of_dvd_right (Subgroup.card_dvd_of_le hKW)
  have hcopL : Nat.Coprime p (Nat.card L) := hcopK.of_dvd_right (Subgroup.card_dvd_of_le hLK)
  have hcopV : Nat.Coprime p (Nat.card (K ⧸ L.subgroupOf K)) :=
    hcopK.of_dvd_right (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))
  have := hA.1
  refine h (K ⧸ L.subgroupOf K) hnc hcopV (sectionAction hAK hAL).range ⟨⟨⟨?_⟩⟩, ?_⟩ ?_ ?_
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show sectionAction hAK hAL a * sectionAction hAK hAL b =
      sectionAction hAK hAL b * sectionAction hAK hAL a
    rw [← map_mul, ← map_mul, mul_comm' a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (hA.2 a a.2), map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hlarge
  · intro f hf hf1
    obtain ⟨a, rfl⟩ := hf
    have ha1 : (a : G) ≠ 1 := fun h1 => hf1 (by rw [show a = 1 from Subtype.ext h1, map_one])
    have hz := zpowers_mem_E1 hp hA a.2 ha1
    refine mcBrideHypothesisB_fixed hp hLK hAK hAL (hA.2 a a.2) hcopL hcopV (hB _ hz) ?_
    rw [← centralizer_zpowers, ← hcomp.2 _ hz]
    exact inf_le_inf_right _ hKW

end CFSG.SignalizerFunctorTheorem
