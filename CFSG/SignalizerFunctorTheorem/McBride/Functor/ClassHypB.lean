module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Class
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

@[expose] def hypBClass (p : ℕ) : SigClass.{u} :=
  fun _ _ _ _ X => signalizerMcBrideHypothesisB p X

theorem signalizerMcBrideHypothesisB_map_iff {G K : Type*} [Group G] [Finite G] [Group K]
    [Finite K] {p : ℕ} (f : G →* K) (hf : Function.Injective f) {X : Subgroup G} :
    signalizerMcBrideHypothesisB p X ↔ signalizerMcBrideHypothesisB p (X.map f) := by
  have hcard : Nat.card (X.map f) = Nat.card X := Subgroup.card_map_of_injective hf
  constructor
  · intro hX
    refine signalizerMcBrideHypothesisB_iff.mpr ⟨hX.1, hcard ▸ hX.2.1, ?_⟩
    intro S _ _ _ hS hnc
    exact signalizerMcBrideHypothesisA_of_isSectionOf hX ((isSectionOf_map_iff f hf X S).mp hS) hnc
  · intro hX
    refine signalizerMcBrideHypothesisB_iff.mpr ⟨hX.1, hcard ▸ hX.2.1, ?_⟩
    intro S _ _ _ hS hnc
    exact signalizerMcBrideHypothesisA_of_isSectionOf hX ((isSectionOf_map_iff f hf X S).mpr hS) hnc

theorem isSigClass_hypBClass (p : ℕ) : IsSigClass p (hypBClass.{u} p) where
  mono := by
    intro H _ _ A X Y hYX _ hX
    have hX' : signalizerMcBrideHypothesisB p X := hX
    obtain ⟨hp, hcop, h⟩ := signalizerMcBrideHypothesisB_iff.mp hX'
    exact signalizerMcBrideHypothesisB_iff.mpr ⟨hp,
      hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hYX),
      fun S _ _ _ hS hnc => h S (isSectionOf_of_le hYX hS) hnc⟩
  map_iff := fun H K _ _ _ _ f hf A X => signalizerMcBrideHypothesisB_map_iff f hf
  quotient := by
    intro H _ _ A X N _ _ _ _ hX
    have hX' : signalizerMcBrideHypothesisB p X := hX
    obtain ⟨hp, hcop, h⟩ := signalizerMcBrideHypothesisB_iff.mp hX'
    exact signalizerMcBrideHypothesisB_iff.mpr ⟨hp,
      hcop.coprime_dvd_right (Subgroup.card_map_dvd X _),
      fun S _ _ _ hS hnc => h S (isSectionOf_of_isSectionOf_map _ X hS) hnc⟩
  extension := by
    intro H _ _ A X N _ _ _ hNX _ hN hQ
    have hN' : signalizerMcBrideHypothesisB p N := hN
    have hQ' : signalizerMcBrideHypothesisB p (X.map (QuotientGroup.mk' N)) := hQ
    refine signalizerMcBrideHypothesisB_iff.mpr ⟨hN'.1, ?_, ?_⟩
    · rw [← card_map_mk'_mul_card hNX]
      exact Nat.Coprime.mul_right hQ'.2.1 hN'.2.1
    · intro S _ _ _ hS hnc
      rcases isSectionOf_normal_or_quotient hNX hS with h | h
      · exact signalizerMcBrideHypothesisA_of_isSectionOf hN' h hnc
      · exact signalizerMcBrideHypothesisA_of_isSectionOf hQ' h hnc

theorem signalizerMcBrideHypothesisB_map_conj {G : Type*} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} (g : G) (h : signalizerMcBrideHypothesisB p X) :
    signalizerMcBrideHypothesisB p (X.map (MulAut.conj g).toMonoidHom) :=
  (signalizerMcBrideHypothesisB_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mp h

theorem signalizerMcBrideHypothesisB_of_isPGroup {G : Type*} [Group G] [Finite G] {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) {X : Subgroup G} (hX : IsPGroup r X) :
    signalizerMcBrideHypothesisB p X := by
  have := Fact.mk hr
  refine ⟨hp, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hX.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hr).mpr hrp.symm)
  · intro K L hKX hLK _ hsimple hnc
    exfalso
    have hQ : IsPGroup r (K ⧸ L.subgroupOf K) := (hX.to_le hKX).to_quotient _
    have : Group.IsNilpotent (K ⧸ L.subgroupOf K) := hQ.isNilpotent
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)

private theorem isSectionOf_prod {N M : Type*} [Group N] [Group M] {S : Type*} [Group S]
    [IsSimpleGroup S] (h : IsSectionOf S (N × M)) : IsSectionOf S N ∨ IsSectionOf S M := by
  rcases h.of_hom (MonoidHom.snd N M) with h | h
  · refine Or.inl (h.of_injective ((MonoidHom.fst N M).comp (MonoidHom.snd N M).ker.subtype) ?_)
    intro a b hab
    have ha : (a : N × M).2 = 1 := a.2
    have hb : (b : N × M).2 = 1 := b.2
    exact Subtype.ext (Prod.ext (by simpa using hab) (ha.trans hb.symm))
  · exact Or.inr h

theorem signalizerMcBrideHypothesisB_sup {G : Type*} [Group G] [Finite G] {p : ℕ}
    {N M : Subgroup G} (hcomm : ∀ x ∈ N, ∀ y ∈ M, x * y = y * x)
    (hN : signalizerMcBrideHypothesisB p N) (hM : signalizerMcBrideHypothesisB p M) :
    signalizerMcBrideHypothesisB p (N ⊔ M) := by
  let φ : N × M →* G := N.subtype.noncommCoprod M.subtype fun n m => hcomm n n.2 m m.2
  have hrange : φ.range = N ⊔ M :=
    (MonoidHom.noncommCoprod_range _ _ _).trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  let ψ : N × M →* ↥(N ⊔ M) := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp φ.rangeRestrict
  have hψ : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp φ.rangeRestrict_surjective
  refine signalizerMcBrideHypothesisB_iff.mpr ⟨hN.1, ?_, ?_⟩
  · have hdvd : Nat.card ↥(N ⊔ M) ∣ Nat.card N * Nat.card M := by
      simpa [Nat.card_prod] using Subgroup.card_dvd_of_surjective hψ
    exact (Nat.Coprime.mul_right hN.2.1 hM.2.1).coprime_dvd_right hdvd
  · intro S _ _ _ hS hnc
    rcases isSectionOf_prod (hS.trans (IsSectionOf.of_surjective ψ hψ)) with h | h
    · exact signalizerMcBrideHypothesisA_of_isSectionOf hN h hnc
    · exact signalizerMcBrideHypothesisA_of_isSectionOf hM h hnc

end CFSG.SignalizerFunctorTheorem.McBride
