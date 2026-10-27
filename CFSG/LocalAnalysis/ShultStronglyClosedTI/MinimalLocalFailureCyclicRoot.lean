module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem proper_pair_point_root
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let Q := minimalLocalFailurePairActionPointHull H z
    let K := minimalLocalFailureProperPairHull H z beta t
    Q ≤ H ∧ Q ≤ K ∧ (Q.subgroupOf H).Normal ∧ IsElemAbelian 2 Q ∧
      IsPGroup 2 Q ∧ 4 ≤ Nat.card Q ∧ z ∈ Q := by
  obtain ⟨hQH, hnormal, hQ, hQp, hzQ⟩ :=
    sylowAssemblyProper_normal_point_two_hull h hcomm hbeta ht hproper
  obtain ⟨s, hs, _, _, _, hfour, _⟩ :=
    minimalLocalFailureProperPair_four_group h hbeta ht
  have hVQ : Subgroup.closure ({z, s} : Set G) ≤
      minimalLocalFailurePairActionPointHull H z := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hzQ
    · have hxs : x = s := Set.mem_singleton_iff.mp hx
      rw [hxs]
      exact Subgroup.subset_closure hs
  have hcard := Nat.card_le_card_of_injective
    (Subgroup.inclusion hVQ) (Subgroup.inclusion_injective hVQ)
  rw [hfour] at hcard
  exact ⟨hQH, minimalLocalFailurePairActionPointHull_le_properPairHull h hbeta ht,
    hnormal, hQ, hQp, hcard, hzQ⟩

theorem proper_pair_involutions_in_intersection
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {x : G} (hx : x ∈ H ⊓ minimalLocalFailureProperPairHull H z beta t)
    (hxorder : orderOf x = 2) :
    x ∈ conjugacyWithin (H ⊓ minimalLocalFailureProperPairHull H z beta t) z := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  let zK : K := ⟨z, minimalLocalFailureProperPair_distinguished_mem H z beta t⟩
  let xK : K := ⟨x, hx.2⟩
  have hzorder : orderOf zK = 2 :=
    (Subgroup.orderOf_coe zK).symm.trans h.local_datum.distinguished_order
  have hxKorder : orderOf xK = 2 := (Subgroup.orderOf_coe xK).symm.trans hxorder
  have hzI : IsInvolution zK :=
    ⟨(orderOf_eq_prime_iff.mp hzorder).2, (orderOf_eq_prime_iff.mp hzorder).1⟩
  have hxI : IsInvolution xK :=
    ⟨(orderOf_eq_prime_iff.mp hxKorder).2, (orderOf_eq_prime_iff.mp hxKorder).1⟩
  obtain ⟨g, hg, heq⟩ :=
    (native_strong_embedding_of_order_conditions
      (minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper)).involutions_conjugate_in
      (show zK ∈ M from h.local_datum.distinguished_mem) hzI
      (show xK ∈ M from hx.1) hxI
  refine ⟨⟨(g : G), ⟨hg, g.property⟩⟩, ?_⟩
  exact congrArg Subtype.val heq

theorem proper_pair_point_root_classes
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let Q := minimalLocalFailurePairActionPointHull H z
    let M := H ⊓ minimalLocalFailureProperPairHull H z beta t
    (Q : Set G) \ {1} = conjugacyWithin H z ∧
      conjugacyWithin H z = conjugacyWithin M z ∧
      conjugacyWithin M z = {x : G | x ∈ M ∧ orderOf x = 2} := by
  obtain ⟨hQH, hQK, _, hQ, _, _, _⟩ := proper_pair_point_root h hcomm hbeta ht hproper
  let Q := minimalLocalFailurePairActionPointHull H z
  let M := H ⊓ minimalLocalFailureProperPairHull H z beta t
  have hMQ : ∀ x : G, x ∈ M → orderOf x = 2 → x ∈ conjugacyWithin M z :=
    fun _ hx hxorder => proper_pair_involutions_in_intersection h hbeta ht hproper hx hxorder
  have hMH : conjugacyWithin M z ⊆ conjugacyWithin H z := by
    rintro x ⟨g, rfl⟩
    exact ⟨⟨g, g.property.1⟩, rfl⟩
  have hHQ : conjugacyWithin H z ⊆ (Q : Set G) \ {1} := by
    intro x hx
    have hxclass : x ∈ involutionPointClass z := by
      obtain ⟨g, rfl⟩ := hx
      exact ⟨g, rfl⟩
    have hxorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hxclass
    refine ⟨Subgroup.subset_closure hx, ?_⟩
    intro hxone
    have hxone' : x = 1 := Set.mem_singleton_iff.mp hxone
    simp only [hxone', orderOf_one] at hxorder
    omega
  have hQI : (Q : Set G) \ {1} ⊆ {x : G | x ∈ M ∧ orderOf x = 2} := by
    rintro x ⟨hx, hxne⟩
    have hxone : x ≠ 1 := fun heq => hxne (Set.mem_singleton_iff.mpr heq)
    exact ⟨⟨hQH hx, hQK hx⟩, orderOf_eq_prime (hQ.2 x hx) hxone⟩
  have hIM : {x : G | x ∈ M ∧ orderOf x = 2} ⊆ conjugacyWithin M z :=
    fun x hx => hMQ x hx.1 hx.2
  have hMI : conjugacyWithin M z ⊆ {x : G | x ∈ M ∧ orderOf x = 2} :=
    fun x hx => hQI (hHQ (hMH hx))
  exact ⟨Set.Subset.antisymm (fun x hx => hMH (hIM (hQI hx))) hHQ,
    Set.Subset.antisymm (fun x hx => hIM (hQI (hHQ hx))) hMH,
    Set.Subset.antisymm hMI hIM⟩

theorem proper_pair_internal_elementary_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let M := H.subgroupOf K
    let V := (minimalLocalFailurePairActionPointHull H z).subgroupOf K
    V ≤ M ∧ (V.subgroupOf M).Normal ∧ IsElemAbelian 2 V ∧
      4 ≤ Nat.card V ∧ Subgroup.normalClosure (V : Set K) = ⊤ := by
  let Q := minimalLocalFailurePairActionPointHull H z
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  let V := Q.subgroupOf K
  obtain ⟨hQH, hQK, hQnormal, hQ, _, hcard, hzQ⟩ :=
    proper_pair_point_root h hcomm hbeta ht hproper
  have hVM : V ≤ M := fun _ hv => hQH hv
  have hVnormal : (V.subgroupOf M).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hVM).mpr
    intro v m hv hm
    exact hQnormal.conj_mem ⟨(v : G), hQH hv⟩ hv ⟨(m : G), hm⟩
  have hV : IsElemAbelian 2 V := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Q => (x : G))
        ((isMulCommutative_iff.mp hQ.1) (⟨(a : K), a.property⟩ : Q)
          (⟨(b : K), b.property⟩ : Q))
    · intro a ha
      exact Subtype.ext (hQ.2 (a : G) ha)
  have hVcard : 4 ≤ Nat.card V := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
    exact hcard
  let zK : K := ⟨z, minimalLocalFailureProperPair_distinguished_mem H z beta t⟩
  let N : Subgroup K := Subgroup.normalClosure (V : Set K)
  have hzN : zK ∈ N := Subgroup.subset_normalClosure (show zK ∈ V from hzQ)
  have hhull : involutionPointHull zK ≤ N := by
    rw [minimalLocalFailure_hull_eq_normalClosure]
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hzN
  rw [minimalLocalFailureProperPair_internal_hull_top h.local_datum h.central_sylow hbeta ht]
    at hhull
  exact ⟨hVM, hVnormal, hV, hVcard, top_unique hhull⟩

theorem proper_pair_full_odd_core_central
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    CFSG.oddCore K ≤ Subgroup.center K ∧
      minimalLocalFailureProperPairOddCore H z beta t ≤
        Subgroup.centralizer (K : Set G) := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let V := (minimalLocalFailurePairActionPointHull H z).subgroupOf K
  obtain ⟨hVM, hnormal, hV, hcard, hgen⟩ :=
    proper_pair_internal_elementary_hull h hcomm hbeta ht hproper
  have hcentral : CFSG.oddCore K ≤ Subgroup.center K :=
    oddCore_le_center_of_normal_elementary_hull (H.subgroupOf K) V
      (minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper)
      hVM hnormal hV hcard hgen
  refine ⟨hcentral, ?_⟩
  intro r hr
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
  apply Subgroup.mem_centralizer_iff.mpr
  intro k hk
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp (hcentral ha)) ⟨k, hk⟩)

end CFSG.ShultStronglyClosedTI.CyclicPair
