module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.Replacement.ClassTwo
public import Mathlib.GroupTheory.Abelianization.Defs

public noncomputable section

open scoped commutatorElement IsMulCommutative

namespace CFSG.ShultStronglyClosedTI

theorem subgroup_commutative_of_le_center {G : Type*} [Group G]
    {H : Subgroup G} (hH : H ≤ Subgroup.center G) : IsMulCommutative H :=
  ⟨⟨fun x y => Subtype.ext ((Subgroup.mem_center_iff.mp (hH x.property) y.val).symm)⟩⟩

theorem classThree_derived_commutative {G : Type*} [Group G]
    (h : ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) :
    IsMulCommutative (commutator G) := by
  apply Subgroup.commutator_self_eq_bot_iff.mp
  have hr : ⁅⁅commutator G, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr h
  have hl : ⁅⁅(⊤ : Subgroup G), commutator G⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup G) (commutator G)]
    exact hr
  exact Subgroup.commutator_commutator_eq_bot_of_rotate hl hr

@[expose] def classThreeMixedPairing {G : Type*} [Group G]
    (h : ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) :
    letI := subgroup_commutative_of_le_center h
    (commutator G) →* G →* ↥⁅commutator G, (⊤ : Subgroup G)⁆ := by
  let := subgroup_commutative_of_le_center h
  have hmem (r : commutator G) (s : G) :
      ⁅r.val, s⁆ ∈ ⁅commutator G, (⊤ : Subgroup G)⁆ :=
    Subgroup.commutator_mem_commutator r.property (Subgroup.mem_top s)
  have hconj (r : commutator G) (s g : G) : g * ⁅r.val, s⁆ * g⁻¹ = ⁅r.val, s⁆ := by
    rw [Subgroup.mem_center_iff.mp (h (hmem r s)) g, mul_inv_cancel_right]
  have hr (r : commutator G) (s t : G) : ⁅r.val, s * t⁆ = ⁅r.val, s⁆ * ⁅r.val, t⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc, mul_assoc,
      ← mul_assoc s, hconj]
  have hl (r s : commutator G) (t : G) : ⁅(r * s).val, t⁆ = ⁅r.val, t⁆ * ⁅s.val, t⁆ := by
    change ⁅r.val * s.val, t⁆ = _
    rw [commutatorElement_mul_left_eq_conj_mul, hconj,
      Subgroup.mem_center_iff.mp (h (hmem r t))]
  exact MonoidHom.mk' (fun r => MonoidHom.mk' (fun s => ⟨⁅r.val, s⁆, hmem r s⟩)
    (fun s t => Subtype.ext (hr r s t)))
    (fun r s => MonoidHom.ext (fun t => Subtype.ext (hl r s t)))

@[simp]
theorem classThreeMixedPairing_coe {G : Type*} [Group G]
    (h : ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (r : commutator G) (s : G) :
    (classThreeMixedPairing h r s : G) = ⁅r.val, s⁆ := by
  rfl

@[expose] def surjectiveHomLift {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C)
    (hg : ∀ a ∈ f.ker, g a = 1) : B →* C :=
  f.liftOfSurjective hf ⟨g, fun a ha => MonoidHom.mem_ker.mpr (hg a ha)⟩

@[simp]
theorem surjectiveHomLift_apply {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C)
    (hg : ∀ a ∈ f.ker, g a = 1) (a : A) : surjectiveHomLift f hf g hg (f a) = g a := by
  exact MonoidHom.liftOfRightInverse_comp_apply f _
    (Function.rightInverse_surjInv hf) ⟨g, fun a ha => MonoidHom.mem_ker.mpr (hg a ha)⟩ a

@[expose] def surjectivePairingLift {A B U V C : Type*}
    [Group A] [Group B] [Group U] [Group V] [CommGroup C]
    (f : A →* U) (hf : Function.Surjective f)
    (g : B →* V) (hg : Function.Surjective g) (β : A →* B →* C)
    (hleft : ∀ a ∈ f.ker, ∀ b, β a b = 1)
    (hright : ∀ a, ∀ b ∈ g.ker, β a b = 1) : U →* V →* C := by
  let β₁ : A →* V →* C := MonoidHom.mk'
    (fun a => surjectiveHomLift g hg (β a) (hright a)) (by
      intro a a'
      ext v
      obtain ⟨b, rfl⟩ := hg v
      change surjectiveHomLift g hg (β (a * a')) _ (g b) =
        surjectiveHomLift g hg (β a) _ (g b) * surjectiveHomLift g hg (β a') _ (g b)
      simp only [surjectiveHomLift_apply, MonoidHom.map_mul₂])
  refine surjectiveHomLift f hf β₁ ?_
  intro a ha
  apply MonoidHom.ext
  intro v
  obtain ⟨b, rfl⟩ := hg v
  change surjectiveHomLift g hg (β a) (hright a) (g b) = 1
  rw [surjectiveHomLift_apply]
  exact hleft a ha b

@[simp]
theorem surjectivePairingLift_apply {A B U V C : Type*}
    [Group A] [Group B] [Group U] [Group V] [CommGroup C]
    (f : A →* U) (hf : Function.Surjective f)
    (g : B →* V) (hg : Function.Surjective g) (β : A →* B →* C)
    (hleft : ∀ a ∈ f.ker, ∀ b, β a b = 1)
    (hright : ∀ a, ∀ b ∈ g.ker, β a b = 1) (a : A) (b : B) :
    surjectivePairingLift f hf g hg β hleft hright (f a) (g b) = β a b := by
  unfold surjectivePairingLift
  dsimp only
  rw [surjectiveHomLift_apply]
  change surjectiveHomLift g hg (β a) (hright a) (g b) = β a b
  rw [surjectiveHomLift_apply]

@[expose] def derivedHom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    commutator G →* commutator H :=
  (f.domRestrict (commutator G)).codRestrict (commutator H) (fun x => by
    have hx : f x.val ∈ (commutator G).map f := Subgroup.mem_map.mpr ⟨x.val, x.property, rfl⟩
    change f x.val ∈ (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).map f at hx
    rw [Subgroup.map_commutator, Subgroup.map_top] at hx
    exact Subgroup.commutator_mono (by exact le_top) (by exact le_top) hx)

@[simp]
theorem derivedHom_coe {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x : commutator G) : (derivedHom f x : H) = f x.val := rfl

theorem derivedHom_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) : Function.Surjective (derivedHom f) := by
  intro y
  have hmap : (commutator G).map f = commutator H := by
    change (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).map f = _
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
    rfl
  have hy : y.val ∈ (commutator G).map f := hmap.symm ▸ y.property
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[expose] def coverAbelianProjection {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G →* Abelianization H := Abelianization.of.comp f

theorem coverAbelianProjection_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) : Function.Surjective (coverAbelianProjection f) := by
  intro v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator H) v
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, rfl⟩

theorem coverAbelianProjection_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G) :
    (coverAbelianProjection f).ker = commutator G := by
  have hmap : (commutator G).map f = commutator H := by
    change (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).map f = _
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
    rfl
  change (Abelianization.of.comp f).ker = _
  rw [← MonoidHom.comap_ker, Abelianization.ker_of, ← hmap, Subgroup.comap_map_eq,
    sup_eq_left.mpr hk]

theorem centralCover_third_le_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hclass : commutator H ≤ Subgroup.center H) :
    ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ f.ker := by
  apply Subgroup.commutator_le.mpr
  intro r hr s _
  change f ⁅r, s⁆ = 1
  rw [map_commutatorElement]
  have hfr := (derivedHom f ⟨r, hr⟩).property
  have hcomm : Commute (f r) (f s) :=
    (Subgroup.mem_center_iff.mp (hclass hfr) (f s)).symm
  exact hcomm.commutator_eq

theorem central_commutator_elementary {G : Type*} [Group G] (n : ℕ)
    (H K : Subgroup G) (hc : ⁅H, K⁆ ≤ Subgroup.center G)
    (hp : ∀ x ∈ H, ∀ y ∈ K, ⁅x, y⁆ ^ n = 1) : IsElementaryAbelian n ↥⁅H, K⁆ := by
  let := subgroup_commutative_of_le_center hc
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro z
  apply Subtype.ext
  have hz : z.val ∈ Subgroup.closure {g | ∃ x ∈ H, ∃ y ∈ K, ⁅x, y⁆ = g} := by
    rw [← Subgroup.commutator_def]
    exact z.property
  exact Subgroup.closure_induction
    (p := fun g _ => g ^ n = 1)
    (by rintro g ⟨x, hx, y, hy, rfl⟩; exact hp x hx y hy)
    (by simp)
    (by
      intro x y hx hy hxp hyp
      have hxy : Commute x y := (Subgroup.mem_center_iff.mp
        (hc (by simpa [← Subgroup.commutator_def] using hx)) y).symm
      rw [hxy.mul_pow, hxp, hyp, one_mul])
    (by intro x _ hx; simpa [inv_pow] using congrArg Inv.inv hx) hz

theorem classTwo_derived_elementary {G : Type*} [Group G] (n : ℕ)
    (hc : commutator G ≤ Subgroup.center G)
    (hp : ∀ x : G, x ^ n ∈ commutator G) : IsElementaryAbelian n (commutator G) := by
  apply central_commutator_elementary n (⊤ : Subgroup G) ⊤ hc
  intro x _ y _
  have hxy : ⁅x, y⁆ ∈ Subgroup.center G := hc
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hcx : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hxy x
  have hpowcomm : Commute (x ^ n) y := (Subgroup.mem_center_iff.mp (hc (hp x)) y).symm
  exact (hcx.commutatorElement_pow_left n).trans hpowcomm.commutator_eq

theorem classThree_third_elementary {G : Type*} [Group G]
    (hc : ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (hp : ∀ x : G, x ^ 2 ∈ commutator G) :
    IsElementaryAbelian 2 ↥⁅commutator G, (⊤ : Subgroup G)⁆ := by
  let := classThree_derived_commutative hc
  let := subgroup_commutative_of_le_center hc
  apply central_commutator_elementary 2 (commutator G) ⊤ hc
  intro x hx y _
  have hcomm : Commute x (y ^ 2) := by
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : commutator G) ⟨y ^ 2, hp y⟩)
  have h := map_pow (classThreeMixedPairing hc ⟨x, hx⟩) y 2
  have hz : classThreeMixedPairing hc ⟨x, hx⟩ (y ^ 2) = 1 :=
    Subtype.ext hcomm.commutator_eq
  exact (congrArg Subtype.val h).symm.trans (congrArg Subtype.val hz)

@[expose] def classTwoDerivedPairing {G : Type*} [Group G]
    (hc : commutator G ≤ Subgroup.center G) :
    letI := subgroup_commutative_of_le_center hc
    G →* G →* commutator G := by
  let := subgroup_commutative_of_le_center hc
  let β := GlaubermanReplacement.commutatorPairing hc
  exact MonoidHom.mk' (fun x => MonoidHom.mk'
    (fun y => ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩)
    (fun y z => Subtype.ext (congrArg (fun a : Subgroup.center G => (a : G))
      (map_mul (β x) y z))))
    (fun x y => MonoidHom.ext (fun z => Subtype.ext
      (congrArg (fun a : Subgroup.center G => (a : G)) (MonoidHom.map_mul₂ β x y z))))

@[simp]
theorem classTwoDerivedPairing_coe {G : Type*} [Group G]
    (hc : commutator G ≤ Subgroup.center G) (x y : G) :
    (classTwoDerivedPairing hc x y : G) = ⁅x, y⁆ := rfl

@[expose] def additivePairing {A B C : Type*} [Group A] [Group B] [CommGroup C]
    (β : A →* B →* C) : Additive A →+ Additive B →+ Additive C where
  toFun a := MonoidHom.toAdditive (β (Additive.toMul a))
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    change β 1 (Additive.toMul b) = 1
    simp
  map_add' a a' := by
    apply AddMonoidHom.ext
    intro b
    change β (Additive.toMul a * Additive.toMul a') (Additive.toMul b) =
      β (Additive.toMul a) (Additive.toMul b) * β (Additive.toMul a') (Additive.toMul b)
    exact MonoidHom.map_mul₂ β _ _ _

@[simp]
theorem additivePairing_apply {A B C : Type*} [Group A] [Group B] [CommGroup C]
    (β : A →* B →* C) (a : A) (b : B) :
    additivePairing β (Additive.ofMul a) (Additive.ofMul b) = Additive.ofMul (β a b) := rfl

@[expose] def additivePairingComp {A B C D : Type*}
    [AddGroup A] [AddGroup B] [AddCommGroup C] [AddCommGroup D]
    (β : A →+ B →+ C) (f : C →+ D) : A →+ B →+ D where
  toFun a := f.comp (β a)
  map_zero' := by ext b; simp
  map_add' a a' := by ext b; simp

@[simp]
theorem additivePairingComp_apply {A B C D : Type*}
    [AddGroup A] [AddGroup B] [AddCommGroup C] [AddCommGroup D]
    (β : A →+ B →+ C) (f : C →+ D) (a : A) (b : B) :
    additivePairingComp β f a b = f (β a b) := rfl

@[expose] def centralCoverMixedPairing {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ commutator G) (hc : f.ker ≤ Subgroup.center G)
    (hq : commutator H ≤ Subgroup.center H) :
    letI := subgroup_commutative_of_le_center ((centralCover_third_le_ker f hq).trans hc)
    commutator H →* Abelianization H →* ↥⁅commutator G, (⊤ : Subgroup G)⁆ := by
  have hthird := (centralCover_third_le_ker f hq).trans hc
  let := classThree_derived_commutative hthird
  let := subgroup_commutative_of_le_center hthird
  refine surjectivePairingLift (derivedHom f) (derivedHom_surjective f hf)
    (coverAbelianProjection f) (coverAbelianProjection_surjective f hf)
    (classThreeMixedPairing hthird) ?_ ?_
  · intro a ha b
    apply Subtype.ext
    have hfa : f a.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hcomm : Commute a.val b := (Subgroup.mem_center_iff.mp (hc hfa) b).symm
    exact hcomm.commutator_eq
  · intro a b hb
    apply Subtype.ext
    have hb' : b ∈ commutator G := (coverAbelianProjection_ker f hf hk) ▸ hb
    have hcomm : Commute a.val b := congrArg Subtype.val (mul_comm a ⟨b, hb'⟩)
    exact hcomm.commutator_eq

@[simp]
theorem centralCoverMixedPairing_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ commutator G) (hc : f.ker ≤ Subgroup.center G)
    (hq : commutator H ≤ Subgroup.center H) (a : commutator G) (b : G) :
    (centralCoverMixedPairing f hf hk hc hq (derivedHom f a)
      (coverAbelianProjection f b) : G) = ⁅a.val, b⁆ := by
  let := subgroup_commutative_of_le_center ((centralCover_third_le_ker f hq).trans hc)
  unfold centralCoverMixedPairing
  dsimp only
  rw [surjectivePairingLift_apply]
  rfl

@[expose] def centralCoverClassTwoPairing {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    (hc : commutator G ≤ Subgroup.center G) :
    letI := subgroup_commutative_of_le_center hc
    Abelianization H →* Abelianization H →* commutator G := by
  let := subgroup_commutative_of_le_center hc
  refine surjectivePairingLift (coverAbelianProjection f) (coverAbelianProjection_surjective f hf)
    (coverAbelianProjection f) (coverAbelianProjection_surjective f hf)
    (classTwoDerivedPairing hc) ?_ ?_
  · intro a ha b
    apply Subtype.ext
    have ha' : a ∈ commutator G := (coverAbelianProjection_ker f hf hk) ▸ ha
    have hcomm : Commute a b := (Subgroup.mem_center_iff.mp (hc ha') b).symm
    exact hcomm.commutator_eq
  · intro a b hb
    apply Subtype.ext
    have hb' : b ∈ commutator G := (coverAbelianProjection_ker f hf hk) ▸ hb
    have hcomm : Commute a b := Subgroup.mem_center_iff.mp (hc hb') a
    exact hcomm.commutator_eq

@[simp]
theorem centralCoverClassTwoPairing_apply {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    (hc : commutator G ≤ Subgroup.center G) (a b : G) :
    (centralCoverClassTwoPairing f hf hk hc (coverAbelianProjection f a)
      (coverAbelianProjection f b) : G) = ⁅a, b⁆ := by
  let := subgroup_commutative_of_le_center hc
  unfold centralCoverClassTwoPairing
  dsimp only
  rw [surjectivePairingLift_apply]
  rfl

end CFSG.ShultStronglyClosedTI
