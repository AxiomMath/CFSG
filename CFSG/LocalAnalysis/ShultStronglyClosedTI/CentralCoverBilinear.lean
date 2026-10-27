module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ClassThreeCoverCommutators
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddActionRetraction
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

open scoped commutatorElement IsMulCommutative

namespace CFSG.ShultStronglyClosedTI

@[expose] def coverPreimageMap {E J : Type*} [Group E] [Group J]
    (η : E →* J) (H : Subgroup J) : H.comap η →* H :=
  (η.domRestrict (H.comap η)).codRestrict H (fun x => x.property)

@[simp]
theorem coverPreimageMap_coe {E J : Type*} [Group E] [Group J]
    (η : E →* J) (H : Subgroup J) (x : H.comap η) :
    (coverPreimageMap η H x : J) = η x.val := rfl

theorem coverPreimageMap_surjective {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (H : Subgroup J) :
    Function.Surjective (coverPreimageMap η H) := by
  intro y
  obtain ⟨x, hx⟩ := hη y.val
  exact ⟨⟨x, by change η x ∈ H; rw [hx]; exact y.property⟩, Subtype.ext hx⟩

@[expose] def centralCoverPreimageSylow {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (hp : IsPGroup 2 η.ker)
    (Q : Sylow 2 J) : Sylow 2 E :=
  Q.comapOfKerIsPGroup η hp (by rw [η.range_eq_top_of_surjective hη]; exact le_top)

@[simp]
theorem centralCoverPreimageSylow_coe {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (hp : IsPGroup 2 η.ker)
    (Q : Sylow 2 J) : (centralCoverPreimageSylow η hη hp Q : Subgroup E) =
      (Q : Subgroup J).comap η := rfl

theorem coverPreimageMap_ker_central {E J : Type*} [Group E] [Group J]
    (η : E →* J) (H : Subgroup J) (hc : η.ker ≤ Subgroup.center E) :
    (coverPreimageMap η H).ker ≤ Subgroup.center (H.comap η) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hxη : η x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact Subgroup.mem_center_iff.mp (hc hxη) y.val

theorem coverPreimageMap_ker_le_derived {E J : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group J] (η : E →* J) (hη : Function.Surjective η)
    (hp : IsPGroup 2 η.ker) (Q : Sylow 2 J) (hc : η.ker ≤ Subgroup.center E) :
    (coverPreimageMap η (Q : Subgroup J)).ker ≤ commutator ((Q : Subgroup J).comap η) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxη : η x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact central_element_mem_sylow_derived (centralCoverPreimageSylow η hη hp Q)
    x (hc hxη)

@[expose] def coverNormalizerAction {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J)) : T →* MulAut Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hT)

@[simp]
theorem coverNormalizerAction_coe {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J)) (t : T) (x : Q) :
    (coverNormalizerAction Q T hT t x : J) = t.val * x.val * t.val⁻¹ := rfl

theorem centralCover_preimage_normalizes {E J : Type*} [Group E] [Group J]
    (η : E →* J) (Q T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) :
    T.comap η ≤ Subgroup.normalizer (Q.comap η : Set E) :=
  (Subgroup.comap_mono hT).trans (Subgroup.le_normalizer_comap η)

@[expose] def centralCoverLiftAction {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (hc : η.ker ≤ Subgroup.center E)
    (Q T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) : T →* MulAut (Q.comap η) := by
  let a := coverNormalizerAction (Q.comap η) (T.comap η)
    (centralCover_preimage_normalizes η Q T hT)
  refine surjectiveHomLift (coverPreimageMap η T) (coverPreimageMap_surjective η hη T) a ?_
  intro t ht
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have htη : η t.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
  change t.val * x.val * t.val⁻¹ = x.val
  rw [← Subgroup.mem_center_iff.mp (hc htη) x.val, mul_inv_cancel_right]

theorem centralCoverLiftAction_of_lift {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (hc : η.ker ≤ Subgroup.center E)
    (Q T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) (t : T.comap η) (x : Q.comap η) :
    (centralCoverLiftAction η hη hc Q T hT (coverPreimageMap η T t) x : E) =
      t.val * x.val * t.val⁻¹ := by
  unfold centralCoverLiftAction
  dsimp only
  rw [surjectiveHomLift_apply]
  rfl

theorem centralCoverLiftAction_equivariant {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (hc : η.ker ≤ Subgroup.center E)
    (Q T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) (t : T) (x : Q.comap η) :
    coverPreimageMap η Q (centralCoverLiftAction η hη hc Q T hT t x) =
      coverNormalizerAction Q T hT t (coverPreimageMap η Q x) := by
  obtain ⟨s, rfl⟩ := coverPreimageMap_surjective η hη T t
  apply Subtype.ext
  simp only [coverPreimageMap_coe, coverNormalizerAction_coe, centralCoverLiftAction_of_lift]
  simp

theorem centralCoverLiftAction_fixes_kernel {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (hc : η.ker ≤ Subgroup.center E)
    (Q T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) (t : T)
    (x : (coverPreimageMap η Q).ker) :
    centralCoverLiftAction η hη hc Q T hT t x.val = x.val := by
  obtain ⟨s, rfl⟩ := coverPreimageMap_surjective η hη T t
  apply Subtype.ext
  rw [centralCoverLiftAction_of_lift]
  have hxη : η x.val.val = 1 := congrArg Subtype.val x.property
  rw [Subgroup.mem_center_iff.mp (hc hxη) s.val, mul_inv_cancel_right]

@[expose] def coverDerivedAction {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J)) : T →* Monoid.End (commutator Q) where
  toFun t := derivedHom (coverNormalizerAction Q T hT t).toMonoidHom
  map_one' := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change coverNormalizerAction Q T hT 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' t s := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change coverNormalizerAction Q T hT (t * s) x.val =
      coverNormalizerAction Q T hT t (coverNormalizerAction Q T hT s x.val)
    rw [map_mul]
    rfl

@[expose] def coverAbelianAction {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J)) : T →* Monoid.End (Abelianization Q) where
  toFun t := Abelianization.map (coverNormalizerAction Q T hT t).toMonoidHom
  map_one' := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
    change Abelianization.map _ (Abelianization.of y) = Abelianization.of y
    rw [Abelianization.map_of, map_one]
    rfl
  map_mul' t s := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
    change Abelianization.map _ (Abelianization.of y) = Abelianization.map _
      (Abelianization.map _ (Abelianization.of y))
    simp only [Abelianization.map_of, map_mul]
    rfl

@[expose] def CoverMixedInvariant {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J))
    (b : Additive (commutator Q) →+ Additive (Abelianization Q) →+ ZMod 2) : Prop :=
  ∀ (t : T) (w : commutator Q) (v : Abelianization Q),
    b (Additive.ofMul (coverDerivedAction Q T hT t w))
      (Additive.ofMul (coverAbelianAction Q T hT t v)) = b (Additive.ofMul w) (Additive.ofMul v)

@[expose] def CoverAbelianInvariant {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J))
    (b : Additive (Abelianization Q) →+ Additive (Abelianization Q) →+ ZMod 2) : Prop :=
  ∀ (t : T) (v w : Abelianization Q),
    b (Additive.ofMul (coverAbelianAction Q T hT t v))
      (Additive.ofMul (coverAbelianAction Q T hT t w)) = b (Additive.ofMul v) (Additive.ofMul w)


@[expose] def derivedAutomorphismAction {T G : Type*} [Monoid T] [Group G]
    (a : T →* MulAut G) : T →* Monoid.End (commutator G) where
  toFun t := derivedHom (a t).toMonoidHom
  map_one' := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change a 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' t s := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change a (t * s) x.val = a t (a s x.val)
    rw [map_mul]
    rfl

@[expose] def additiveEndAction {T G : Type*} [Monoid T] [Group G]
    (a : T →* Monoid.End G) : T →* AddMonoid.End (Additive G) where
  toFun t := MonoidHom.toAdditive (a t)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    change a 1 (Additive.toMul x) = Additive.toMul x
    rw [map_one]
    rfl
  map_mul' t s := by
    apply AddMonoidHom.ext
    intro x
    change a (t * s) (Additive.toMul x) = a t (a s (Additive.toMul x))
    rw [map_mul]
    rfl

theorem centralCoverMixedPairing_invariant {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ commutator G) (hc : f.ker ≤ Subgroup.center G)
    (hq : commutator H ≤ Subgroup.center H)
    (e : MulAut G) (a : MulAut H) (he : ∀ x, f (e x) = a (f x))
    (hfix : ∀ x ∈ f.ker, e x = x) (w : commutator H) (v : Abelianization H) :
    centralCoverMixedPairing f hf hk hc hq (derivedHom a.toMonoidHom w)
      (Abelianization.map a.toMonoidHom v) = centralCoverMixedPairing f hf hk hc hq w v := by
  obtain ⟨r, rfl⟩ := derivedHom_surjective f hf w
  obtain ⟨s, rfl⟩ := coverAbelianProjection_surjective f hf v
  have her : derivedHom a.toMonoidHom (derivedHom f r) =
      derivedHom f (derivedHom e.toMonoidHom r) := by
    apply Subtype.ext
    exact (he r.val).symm
  have hes : Abelianization.map a.toMonoidHom (coverAbelianProjection f s) =
      coverAbelianProjection f (e s) := by
    change Abelianization.map a.toMonoidHom (Abelianization.of (f s)) =
      Abelianization.of (f (e s))
    rw [Abelianization.map_of, he]
    rfl
  rw [her, hes]
  apply Subtype.ext
  rw [centralCoverMixedPairing_apply, centralCoverMixedPairing_apply]
  change ⁅e.toMonoidHom r.val, e.toMonoidHom s⁆ = ⁅r.val, s⁆
  rw [← map_commutatorElement e.toMonoidHom]
  exact hfix _ (centralCover_third_le_ker f hq
    (Subgroup.commutator_mem_commutator r.property (Subgroup.mem_top s)))

theorem centralCoverClassTwoPairing_equivariant {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    (hc : commutator G ≤ Subgroup.center G)
    (e : MulAut G) (a : MulAut H) (he : ∀ x, f (e x) = a (f x))
    (v w : Abelianization H) :
    centralCoverClassTwoPairing f hf hk hc (Abelianization.map a.toMonoidHom v)
      (Abelianization.map a.toMonoidHom w) =
      derivedHom e.toMonoidHom (centralCoverClassTwoPairing f hf hk hc v w) := by
  obtain ⟨r, rfl⟩ := coverAbelianProjection_surjective f hf v
  obtain ⟨s, rfl⟩ := coverAbelianProjection_surjective f hf w
  have heq (x : G) : Abelianization.map a.toMonoidHom (coverAbelianProjection f x) =
      coverAbelianProjection f (e x) := by
    change Abelianization.map a.toMonoidHom (Abelianization.of (f x)) =
      Abelianization.of (f (e x))
    rw [Abelianization.map_of, he]
    rfl
  rw [heq, heq]
  apply Subtype.ext
  rw [centralCoverClassTwoPairing_apply, derivedHom_coe, centralCoverClassTwoPairing_apply]
  exact (map_commutatorElement e.toMonoidHom _ _).symm

theorem centralCover_square_mem_derived {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    [IsElementaryAbelian 2 (Abelianization H)] (x : G) : x ^ 2 ∈ commutator G := by
  rw [← coverAbelianProjection_ker f hf hk]
  apply MonoidHom.mem_ker.mpr
  rw [map_pow]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Abelianization H)) _

theorem centralCover_mixed_obstruction {E J : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group J] (η : E →* J) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker)
    (Q : Sylow 2 J) (hq : commutator (Q : Subgroup J) ≤ Subgroup.center (Q : Subgroup J))
    [IsElementaryAbelian 2 (Abelianization (Q : Subgroup J))]
    (T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J))
    (hforms : ∀ b : Additive (commutator (Q : Subgroup J)) →+
      Additive (Abelianization (Q : Subgroup J)) →+ ZMod 2,
      CoverMixedInvariant (Q : Subgroup J) T hT b → b = 0) :
    commutator ((Q : Subgroup J).comap η) ≤ Subgroup.center ((Q : Subgroup J).comap η) := by
  let f := coverPreimageMap η (Q : Subgroup J)
  have hf := coverPreimageMap_surjective η hη (Q : Subgroup J)
  have hk := coverPreimageMap_ker_le_derived η hη hp Q hc
  have hfc := coverPreimageMap_ker_central η (Q : Subgroup J) hc
  have hthird := (centralCover_third_le_ker f hq).trans hfc
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := classThree_third_elementary hthird (centralCover_square_mem_derived f hf hk)
  let β := centralCoverMixedPairing f hf hk hfc hq
  have hinv (t : T) (w : commutator (Q : Subgroup J))
      (v : Abelianization (Q : Subgroup J)) :
      β (coverDerivedAction (Q : Subgroup J) T hT t w)
        (coverAbelianAction (Q : Subgroup J) T hT t v) = β w v := by
    apply centralCoverMixedPairing_invariant
    · exact centralCoverLiftAction_equivariant η hη hc (Q : Subgroup J) T hT t
    · intro x hx
      exact centralCoverLiftAction_fixes_kernel η hη hc (Q : Subgroup J) T hT t ⟨x, hx⟩
  have hzero (w : commutator (Q : Subgroup J)) (v : Abelianization (Q : Subgroup J)) :
      β w v = 1 := by
    apply Additive.toMul.injective
    apply binary_functionals_separate (Additive.ofMul (β w v))
    intro l
    let b := additivePairingComp (additivePairing β) l
    have hb : CoverMixedInvariant (Q : Subgroup J) T hT b := by
      intro t w v
      change l (Additive.ofMul (β _ _)) = l (Additive.ofMul (β w v))
      exact congrArg (fun z => l (Additive.ofMul z)) (hinv t w v)
    have hbzero := hforms b hb
    exact congrArg (fun b => b (Additive.ofMul w) (Additive.ofMul v)) hbzero
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  apply le_bot_iff.mp
  apply Subgroup.commutator_le.mpr
  intro r hr s _
  change ⁅r, s⁆ = 1
  have h := hzero (derivedHom f ⟨r, hr⟩) (coverAbelianProjection f s)
  exact (centralCoverMixedPairing_apply f hf hk hfc hq ⟨r, hr⟩ s).symm.trans
    (congrArg Subtype.val h)

theorem derivedHom_ker {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (derivedHom f).ker = f.ker.subgroupOf (commutator G) := by
  ext x
  change (derivedHom f x = 1) ↔ f x.val = 1
  exact Subtype.ext_iff

@[expose] def coverDerivedQuotientEquiv {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    (commutator G) ⧸ (derivedHom f).ker ≃* commutator H :=
  QuotientGroup.quotientKerEquivOfSurjective (derivedHom f) (derivedHom_surjective f hf)

@[expose] def centralCoverAbelianizationEquiv {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G) :
    Abelianization G ≃* Abelianization H :=
  (QuotientGroup.quotientMulEquivOfEq (coverAbelianProjection_ker f hf hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coverAbelianProjection f)
      (coverAbelianProjection_surjective f hf))

theorem derived_additiveHom_zero_of_commutators {G A : Type*} [Group G] [AddCommGroup A]
    (r : Additive (commutator G) →+ A)
    (hr : ∀ x y : G, r (Additive.ofMul ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩) = 0) (z : commutator G) :
    r (Additive.ofMul z) = 0 := by
  let j : (commutator G) →* Multiplicative A := MonoidHom.toAdditiveLeft.symm r
  have hD : commutator G ≤ j.ker.map (commutator G).subtype := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    refine Subgroup.mem_map.mpr ⟨⟨⁅x, y⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩, ?_, rfl⟩
    change r (Additive.ofMul ⟨⁅x, y⁆, _⟩) = 0
    exact hr x y
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp (hD z.property)
  have hcz' : c = z := Subtype.ext hcz
  rw [← hcz']
  exact hc

theorem elementary_subgroup_of_le {G : Type*} [Group G] {n : ℕ} {H K : Subgroup G}
    [IsElementaryAbelian n K] (h : H ≤ K) : IsElementaryAbelian n H :=
  CFSG.IsElementaryAbelian.of_le inferInstance h

theorem additive_inclusion_injective {G : Type*} [Group G] {H K : Subgroup G}
    (h : H ≤ K) : Function.Injective (MonoidHom.toAdditive (Subgroup.inclusion h)) := by
  intro x y hxy
  exact (Subgroup.inclusion_injective h) hxy

theorem coverPreimageMap_ker_eq_bot_iff {E J : Type*} [Group E] [Group J]
    (η : E →* J) (H : Subgroup J) : (coverPreimageMap η H).ker = ⊥ ↔ η.ker = ⊥ := by
  constructor
  · intro h
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    let xp : H.comap η := ⟨x, by change η x ∈ H; rw [hx]; exact H.one_mem⟩
    have hxk : xp ∈ (coverPreimageMap η H).ker := Subtype.ext hx
    have hxp : xp = 1 := by simpa [h] using hxk
    exact congrArg Subtype.val hxp
  · intro h
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    apply Subtype.ext
    have hxη : η x.val = 1 := congrArg Subtype.val hx
    have hxk : x.val ∈ η.ker := hxη
    simpa [h] using hxk

theorem centralCover_classTwo_abelian_obstruction {E J : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group J] (η : E →* J) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) (Q : Sylow 2 J)
    [IsElementaryAbelian 2 (Abelianization (Q : Subgroup J))]
    (T : Subgroup J) [Finite T] (hT : T ≤ Subgroup.normalizer (Q : Set J))
    (hodd : Odd (Nat.card T))
    (hforms : ∀ b : Additive (Abelianization (Q : Subgroup J)) →+
      Additive (Abelianization (Q : Subgroup J)) →+ ZMod 2,
      CoverAbelianInvariant (Q : Subgroup J) T hT b → b = 0)
    (hclass : commutator ((Q : Subgroup J).comap η) ≤
      Subgroup.center ((Q : Subgroup J).comap η)) : η.ker = ⊥ := by
  let f := coverPreimageMap η (Q : Subgroup J)
  have hf := coverPreimageMap_surjective η hη (Q : Subgroup J)
  have hk := coverPreimageMap_ker_le_derived η hη hp Q hc
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := classTwo_derived_elementary 2 hclass (centralCover_square_mem_derived f hf hk)
  let := elementary_subgroup_of_le (n := 2) hk
  let i := Subgroup.inclusion hk
  let ia := MonoidHom.toAdditive i
  let α := centralCoverLiftAction η hη hc (Q : Subgroup J) T hT
  let αd := derivedAutomorphismAction α
  let αa := additiveEndAction αd
  have hfixed (t : T) (c : Additive f.ker) : αa t (ia c) = ia c := by
    apply congrArg Additive.ofMul
    apply Subtype.ext
    exact centralCoverLiftAction_fixes_kernel η hη hc (Q : Subgroup J) T hT t
      (Additive.toMul c)
  obtain ⟨r, hr, hinv⟩ := exists_oddInvariant_retraction hodd αa ia
    (additive_inclusion_injective hk) hfixed
  let β := centralCoverClassTwoPairing f hf hk hclass
  have hβ (t : T) (v w : Abelianization (Q : Subgroup J)) :
      β (coverAbelianAction (Q : Subgroup J) T hT t v)
        (coverAbelianAction (Q : Subgroup J) T hT t w) = αd t (β v w) := by
    apply centralCoverClassTwoPairing_equivariant
    exact centralCoverLiftAction_equivariant η hη hc (Q : Subgroup J) T hT t
  have hz (v w : Abelianization (Q : Subgroup J)) : r (Additive.ofMul (β v w)) = 0 := by
    apply binary_functionals_separate
    intro l
    let b := additivePairingComp (additivePairingComp (additivePairing β) r) l
    have hb : CoverAbelianInvariant (Q : Subgroup J) T hT b := by
      intro t v w
      change l (r (Additive.ofMul (β _ _))) = l (r (Additive.ofMul (β v w)))
      have hinv' : r (Additive.ofMul (αd t (β v w))) = r (Additive.ofMul (β v w)) :=
        hinv t (Additive.ofMul (β v w))
      exact (congrArg (fun z => l (r (Additive.ofMul z))) (hβ t v w)).trans (congrArg l hinv')
    exact congrArg (fun b => b (Additive.ofMul v) (Additive.ofMul w)) (hforms b hb)
  have hcomm (x y : (Q : Subgroup J).comap η) : r (Additive.ofMul
      (⟨⁅x, y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)⟩ : commutator ((Q : Subgroup J).comap η))) = 0 := by
    have heq : β (coverAbelianProjection f x) (coverAbelianProjection f y) =
        ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
          (Subgroup.mem_top y)⟩ := Subtype.ext (centralCoverClassTwoPairing_apply f hf hk hclass x y)
    rw [← heq]
    exact hz _ _
  apply (coverPreimageMap_ker_eq_bot_iff η (Q : Subgroup J)).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  let c : Additive f.ker := Additive.ofMul ⟨x, hx⟩
  have hzero : c = 0 := (hr c).symm.trans (derived_additiveHom_zero_of_commutators r hcomm (i (Additive.toMul c)))
  exact congrArg (fun c : Additive f.ker => (Additive.toMul c).val) hzero

theorem central_two_cover_bilinear_Sylow_obstruction {E J : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] [Group J] [Finite J]
    (η : E →* J) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) (Q : Sylow 2 J)
    (hq : commutator (Q : Subgroup J) ≤ Subgroup.center (Q : Subgroup J))
    [IsElementaryAbelian 2 (commutator (Q : Subgroup J))]
    [IsElementaryAbelian 2 (Abelianization (Q : Subgroup J))]
    (T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) (hodd : Odd (Nat.card T))
    (hmixed : ∀ b : Additive (commutator (Q : Subgroup J)) →+
      Additive (Abelianization (Q : Subgroup J)) →+ ZMod 2,
      CoverMixedInvariant (Q : Subgroup J) T hT b → b = 0)
    (habelian : ∀ b : Additive (Abelianization (Q : Subgroup J)) →+
      Additive (Abelianization (Q : Subgroup J)) →+ ZMod 2,
      CoverAbelianInvariant (Q : Subgroup J) T hT b → b = 0) : η.ker = ⊥ := by
  exact centralCover_classTwo_abelian_obstruction η hη hc hp Q T hT hodd habelian
    (centralCover_mixed_obstruction η hη hc hp Q hq T hT hmixed)

end CFSG.ShultStronglyClosedTI
