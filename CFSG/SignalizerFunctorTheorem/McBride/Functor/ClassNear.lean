module

public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Class
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections
public import CFSG.SignalizerFunctorTheorem.NearModels.Main

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

@[expose] def nearClass (p : ℕ) : SigClass.{u} :=
  fun _ _ _ A X => NearASolvable p A X

private theorem isSolvable_inf_centralizer_of_le {H : Type*} [Group H] {A X Y : Subgroup H}
    (hYX : Y ≤ X) (hX : Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set H) : Subgroup H)) :
    Group.IsSolvable (Y ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) :=
  Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (inf_le_inf_right _ hYX))

private theorem map_inf_centralizer_of_injective {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) (A X : Subgroup H) :
    (X ⊓ Subgroup.centralizer (A : Set H)).map f =
      X.map f ⊓ Subgroup.centralizer (A.map f : Set K) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxX, hxC⟩, rfl⟩
    refine ⟨⟨x, hxX, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxC a ha]
  · rintro ⟨⟨x, hxX, rfl⟩, hy⟩
    refine ⟨x, ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hy (f a) ⟨a, ha, rfl⟩
    exact hf (by rw [map_mul, map_mul]; exact this)

private theorem isSolvable_inf_centralizer_map_iff {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Injective f) (A X : Subgroup H) :
    Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) ↔
      Group.IsSolvable (X.map f ⊓ Subgroup.centralizer (A.map f : Set K) : Subgroup K) := by
  let e : (X ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) ≃*
      (X.map f ⊓ Subgroup.centralizer (A.map f : Set K) : Subgroup K) :=
    ((X ⊓ Subgroup.centralizer (A : Set H)).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr (map_inf_centralizer_of_injective f hf A X))
  exact ⟨fun h => Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
    fun h => Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩

private theorem nearASolvable_map_iff {p : ℕ} {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) (A X : Subgroup H) :
    NearASolvable p A X ↔ NearASolvable p (A.map f) (X.map f) :=
  and_congr
    ⟨TransportA.nearPSolvable_of_mulEquiv (X.equivMapOfInjective f hf),
      TransportA.nearPSolvable_of_mulEquiv (X.equivMapOfInjective f hf).symm⟩
    (isSolvable_inf_centralizer_map_iff f hf A X)

private theorem card_dvd_of_isSectionOf {S X : Type*} [Group S] [Group X] [Finite X]
    (h : IsSectionOf S X) : Nat.card S ∣ Nat.card X := by
  obtain ⟨K, f, hf⟩ := h
  exact (Subgroup.card_dvd_of_surjective hf).trans (Subgroup.card_subgroup_dvd_card K)

private theorem card_eq_card_map_mul {H : Type*} [Group H] {X N : Subgroup H} [N.Normal]
    (hNX : N ≤ X) :
    Nat.card X = Nat.card (X.map (QuotientGroup.mk' N)) * Nat.card N := by
  have h := Subgroup.relIndex_mul_card (H := (QuotientGroup.mk' N).ker) (K := X)
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk', inf_of_le_left hNX] at h
  exact h.symm

private theorem nearASolvable_mono {p : ℕ} {H : Type u} [Group H] {A X Y : Subgroup H}
    (hYX : Y ≤ X) (h : NearASolvable p A X) : NearASolvable p A Y := by
  refine ⟨?_, isSolvable_inf_centralizer_of_le hYX h.2⟩
  obtain ⟨hcop, hsec⟩ := signalizerNearPSolvable_iff.1 h.1
  refine signalizerNearPSolvable_iff.2
    ⟨hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hYX), fun S _ _ hS hnc => ?_⟩
  exact hsec S (isSectionOf_of_le hYX hS) hnc

private theorem nearASolvable_quotient {p : ℕ} (hp : p.Prime) {H : Type u} [Group H]
    {A X N : Subgroup H} [N.Normal] (hA : IsElemAbelian p A)
    (hAX : A ≤ Subgroup.normalizer (X : Set H)) (hcop : Nat.Coprime p (Nat.card X))
    (h : NearASolvable p A X) :
    NearASolvable p (A.map (QuotientGroup.mk' N)) (X.map (QuotientGroup.mk' N)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, hsec⟩ := signalizerNearPSolvable_iff.1 h.1
    refine signalizerNearPSolvable_iff.2
      ⟨hcop.coprime_dvd_right (Subgroup.card_map_dvd X _), fun S _ _ hS hnc => ?_⟩
    exact hsec S (isSectionOf_of_isSectionOf_map _ X hS) hnc
  · have himage := CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image p hp
      (QuotientGroup.mk' N) A X
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA) hAX hcop
    have hsol := h.2
    rw [← himage]
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' N).subgroupMap (X ⊓ Subgroup.centralizer (A : Set H)))
      ((QuotientGroup.mk' N).subgroupMap_surjective _)

private theorem nearASolvable_extension {p : ℕ} {H : Type u} [Group H] {A X N : Subgroup H}
    [N.Normal] (hNX : N ≤ X) (hN : NearASolvable p A N)
    (hQ : NearASolvable p (A.map (QuotientGroup.mk' N)) (X.map (QuotientGroup.mk' N))) :
    NearASolvable p A X := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hNcop, hNsec⟩ := signalizerNearPSolvable_iff.1 hN.1
    obtain ⟨hQcop, hQsec⟩ := signalizerNearPSolvable_iff.1 hQ.1
    refine signalizerNearPSolvable_iff.2 ⟨?_, fun S _ _ hS hnc => ?_⟩
    · rw [card_eq_card_map_mul hNX]
      exact hQcop.mul_right hNcop
    · rcases isSectionOf_normal_or_quotient hNX hS with hS' | hS'
      · exact hNsec S hS' hnc
      · exact hQsec S hS' hnc
  · have hNsol := hN.2
    have hQsol := hQ.2
    have hmem : ∀ x : (X ⊓ Subgroup.centralizer (A : Set H) : Subgroup H),
        QuotientGroup.mk' N (x : H) ∈ X.map (QuotientGroup.mk' N) ⊓
          Subgroup.centralizer (A.map (QuotientGroup.mk' N) : Set (H ⧸ N)) := by
      intro x
      refine ⟨⟨x, x.2.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp x.2.2 a ha]
    let g := ((QuotientGroup.mk' N).comp
      (X ⊓ Subgroup.centralizer (A : Set H)).subtype).codRestrict _ hmem
    refine Group.isSolvable_of_ker_le_range
      (Subgroup.inclusion (inf_le_inf_right _ hNX)) g fun x hx => ?_
    have hxN : (x : H) ∈ N := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp this
    exact ⟨⟨x, hxN, x.2.2⟩, rfl⟩

theorem isSigClass_nearClass {p : ℕ} (hp : p.Prime) : IsSigClass p (nearClass.{u} p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H _ _ A X Y hYX _ h
    exact nearASolvable_mono hYX h
  · intro H K _ _ _ _ f hf A X
    exact nearASolvable_map_iff f hf A X
  · intro H _ _ A X N _ hA hAX hcop h
    exact nearASolvable_quotient hp hA hAX hcop h
  · intro H _ _ A X N _ _ _ hNX _ hN hQ
    exact nearASolvable_extension hNX hN hQ

theorem signalizerMcBrideHypothesisB_of_nearPSolvable
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X : Subgroup G} (h : signalizerNearPSolvable p X) :
    signalizerMcBrideHypothesisB p X := by
  have := Fact.mk hp
  obtain ⟨hcop, hmodel⟩ := signalizerNearPSolvable_iff.1 h
  refine signalizerMcBrideHypothesisB_iff.2 ⟨hp, hcop, fun S _ _ _ hS hnc => ?_⟩
  have hScop : Nat.Coprime p (Nat.card S) :=
    hcop.coprime_dvd_right (card_dvd_of_isSectionOf hS)
  have hmodS := hmodel S hS hnc
  refine ⟨hp, ‹_›, hnc, hScop, fun P hP => ?_, Or.inl ?_⟩
  · exact isCyclic_of_card_dvd_prime
      (NearModels.nearSimpleModel_card_pSubgroup_dvd hp hmodS hScop P hP)
  · refine signalizerNearPSolvable_iff.2 ⟨hScop, fun T _ _ hT hTnc => ?_⟩
    exact hmodel T (hT.trans hS) hTnc

theorem NearASolvable.hypothesisB
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A X : Subgroup G} (h : NearASolvable p A X) : signalizerMcBrideHypothesisB p X :=
  signalizerMcBrideHypothesisB_of_nearPSolvable hp h.1

theorem nearASolvable_of_isPGroup {G : Type*} [Group G] [Finite G] {p r : ℕ} (hr : r.Prime)
    (hp : p.Prime) (hrp : r ≠ p) {A X : Subgroup G} (hX : IsPGroup r X) :
    NearASolvable p A X := by
  have := Fact.mk hr
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card X) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hr).2 hrp.symm)
  refine ⟨⟨hcop, fun K L _ _ hsimple hnc => ?_⟩, ?_⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have := ((hX.to_subgroup K).to_quotient (L.subgroupOf K)).isNilpotent
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)
  · have := (hX.of_injective _
      (Subgroup.inclusion_injective (inf_le_left : X ⊓ Subgroup.centralizer (A : Set G) ≤ X))
        ).isNilpotent
    infer_instance

end CFSG.SignalizerFunctorTheorem.McBride
