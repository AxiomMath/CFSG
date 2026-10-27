module

public import CFSG.Monster.B.Geometry.ResidueBuilding
public import CFSG.Monster.B.Geometry.ProductModel

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}

theorem IsBuildingOn.comap {C D : Type*} {δ : D → D → W} {J : Set ι} {R' : Set D}
    (hB : IsBuildingOn cs δ J R') {R : Set C} {f : C → D} (hf : Set.BijOn f R R') :
    IsBuildingOn cs (fun x y => δ (f x) (f y)) J R where
  mem_parabolic x hx y hy := hB.mem_parabolic _ (hf.mapsTo hx) _ (hf.mapsTo hy)
  eq_one_iff x hx y hy :=
    (hB.eq_one_iff _ (hf.mapsTo hx) _ (hf.mapsTo hy)).trans (hf.injOn.eq_iff hx hy)
  mul_simple x hx y hy z hz j hj h :=
    hB.mul_simple _ (hf.mapsTo hx) _ (hf.mapsTo hy) _ (hf.mapsTo hz) j hj h
  exists_simple x hx y hy j hj := by
    obtain ⟨w, hw, h1, h2⟩ := hB.exists_simple _ (hf.mapsTo hx) _ (hf.mapsTo hy) j hj
    obtain ⟨z, hz, rfl⟩ := hf.surjOn hw
    exact ⟨z, hz, h1, h2⟩

theorem isBuildingOn_residue_comap {C D : Type*} {δ : D → D → W}
    (hδ : IsWeylDistanceBuilding cs δ) (J : Set ι) (a : D) {R : Set C} {f : C → D}
    (hf : Set.BijOn f R (residue cs δ J a)) :
    IsBuildingOn cs (fun x y => δ (f x) (f y)) J R :=
  (isBuildingOn_residue hδ J a).comap hf

theorem IsBuildingOn.mapWeyl {M' : CoxeterMatrix ι} {W' : Type*} [Group W']
    {cs' : CoxeterSystem M' W'} {φ : W ≃* W'} (hs : ∀ i, φ (cs.simple i) = cs'.simple i)
    (hl : ∀ w, cs'.length (φ w) = cs.length w) {C : Type*} {δ : C → C → W} {J : Set ι}
    {R : Set C} (hB : IsBuildingOn cs δ J R) : IsBuildingOn cs' (fun x y => φ (δ x y)) J R := by
  have hpar : ∀ w ∈ cs.parabolic J, φ w ∈ cs'.parabolic J := by
    have : cs.parabolic J ≤ (cs'.parabolic J).comap φ.toMonoidHom := by
      rw [cs.parabolic_le_iff]
      intro i hi
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hs]
      exact cs'.simple_mem_parabolic hi
    exact fun w hw => this hw
  have hsim : ∀ w i, φ w = cs'.simple i ↔ w = cs.simple i := fun w i => by
    rw [← hs, EquivLike.apply_eq_iff_eq]
  refine ⟨fun x hx y hy => hpar _ (hB.mem_parabolic x hx y hy), fun x hx y hy => ?_,
    fun x hx y hy z hz j hj e => ?_, fun x hx y hy j hj => ?_⟩
  · rw [MulEquiv.map_eq_one_iff]
    exact hB.eq_one_iff x hx y hy
  · rw [hsim] at e
    obtain ⟨h1, h2⟩ := hB.mul_simple x hx y hy z hz j hj e
    refine ⟨h1.imp (congrArg φ) fun h => by rw [h, map_mul, hs], fun h => ?_⟩
    rw [← hs, ← map_mul, hl, hl] at h
    rw [h2 h, map_mul, hs]
  · obtain ⟨z, hz, h1, h2⟩ := hB.exists_simple x hx y hy j hj
    exact ⟨z, hz, by rw [h1, hs], by rw [h2, map_mul, hs]⟩

section Gallery

variable {C : Type*} {δ : C → C → W} {J : Set ι} {R : Set C}

theorem isGallery_of_isStrictGallery (Y : ChamberSystem ι C)
    (hadj : ∀ a ∈ R, ∀ b ∈ R, ∀ j ∈ J, δ a b = cs.simple j → Y.adj j a b) :
    ∀ (γ : List (ι × C)) {x : C}, x ∈ R → IsStrictGallery cs δ x γ → (∀ p ∈ γ, p.2 ∈ R) →
      (∀ i ∈ galleryType γ, i ∈ J) → Y.IsGallery x γ
  | [], _, _, _, _, _ => trivial
  | p :: γ, x, hx, hγ, hR, hJ =>
    ⟨hadj x hx p.2 (hR p (by simp)) p.1 (hJ p.1 (by simp [galleryType])) hγ.1,
      isGallery_of_isStrictGallery Y hadj γ (hR p (by simp)) hγ.2
        (fun q hq => hR q (by simp [hq])) (fun i hi => hJ i (by simp [galleryType] at hi ⊢; tauto))⟩

theorem IsBuildingOn.exists_gallery (hB : IsBuildingOn cs δ J R) (Y : ChamberSystem ι C)
    (hadj : ∀ a ∈ R, ∀ b ∈ R, ∀ j ∈ J, δ a b = cs.simple j → Y.adj j a b) {x y : C}
    (hx : x ∈ R) (hy : y ∈ R) :
    ∃ γ : List (ι × C), Y.IsGallery x γ ∧ (∀ i ∈ galleryType γ, i ∈ J) ∧
      galleryEnd x γ = y ∧ ∀ p ∈ γ, p.2 ∈ R := by
  obtain ⟨ω, hω, hωe⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨γ, hγ, htype, hend, hR⟩ := hB.exists_strictGallery hx hy hω hωe.symm
  have hJ : ∀ i ∈ galleryType γ, i ∈ J := fun i hi =>
    mem_of_isReduced_of_mem_parabolic cs hω (hωe ▸ hB.mem_parabolic x hx y hy) (htype ▸ hi)
  exact ⟨γ, isGallery_of_isStrictGallery Y hadj γ hx hγ hR hJ, hJ, hend, hR⟩

end Gallery

namespace ChamberSystem

variable {C D : Type*}

theorem isResidueBuilding_of_bijOn (X : ChamberSystem ι C) {J : Set ι} {x : C}
    {δ : D → D → W} {R : Set D} (hB : IsBuildingOn cs δ J R) {ψ : D → C}
    (hψ : Set.BijOn ψ R (X.residue J x))
    (hadj : ∀ a ∈ R, ∀ b ∈ R, ∀ j ∈ J, X.adj j (ψ a) (ψ b) ↔ δ a b = 1 ∨ δ a b = cs.simple j) :
    X.IsResidueBuilding cs J x := by
  obtain ⟨a₀, -, -⟩ := hψ.surjOn (X.self_mem_residue J x)
  have : Nonempty D := ⟨a₀⟩
  have hinv := hψ.invOn_invFunOn
  have hbij : Set.BijOn (Function.invFunOn ψ R) (X.residue J x) R := hψ.symm hinv.symm
  refine ⟨fun y z => δ (Function.invFunOn ψ R y) (Function.invFunOn ψ R z), hB.comap hbij, ?_⟩
  intro y hy z hz j hj
  have h := hadj _ (hbij.mapsTo hy) _ (hbij.mapsTo hz) j hj
  rwa [hinv.2 hy, hinv.2 hz] at h

theorem IsResidueBuilding.of_mem_typeAut {X : ChamberSystem ι C} {J : Set ι} {x : C}
    (h : X.IsResidueBuilding cs J x) {g : Equiv.Perm C} (hg : g ∈ X.typeAut) :
    X.IsResidueBuilding cs J (g x) := by
  obtain ⟨δ, hB, hadj⟩ := h
  refine isResidueBuilding_of_bijOn X hB (ψ := g) ?_ fun a ha b hb j hj => ?_
  · rw [← image_residue_of_mem_typeAut hg J x]
    exact g.injective.injOn.bijOn_image
  · rw [mem_typeAut.mp hg j a b]
    exact hadj a ha b hb j hj

theorem IsResidueBuilding.mapWeyl {X : ChamberSystem ι C} {J : Set ι} {x : C}
    (h : X.IsResidueBuilding cs J x) {M' : CoxeterMatrix ι} {W' : Type*} [Group W']
    {cs' : CoxeterSystem M' W'} {φ : W ≃* W'} (hs : ∀ i, φ (cs.simple i) = cs'.simple i)
    (hl : ∀ w, cs'.length (φ w) = cs.length w) : X.IsResidueBuilding cs' J x := by
  obtain ⟨δ, hB, hadj⟩ := h
  refine ⟨fun a b => φ (δ a b), hB.mapWeyl hs hl, fun y hy z hz j hj => ?_⟩
  rw [hadj y hy z hz j hj, ← hs j, MulEquiv.map_eq_one_iff, EquivLike.apply_eq_iff_eq]

theorem IsResidueBuilding.mono {X : ChamberSystem ι C} {J K : Set ι} {x : C}
    (h : X.IsResidueBuilding cs K x) (hJK : J ⊆ K) : X.IsResidueBuilding cs J x := by
  obtain ⟨δ, hB, hadj⟩ := h
  have hsub : X.residue J x ⊆ X.residue K x := X.residue_mono hJK x
  have key : ∀ y ∈ X.residue J x, ∀ γ : List (ι × C), X.IsGallery y γ →
      (∀ i ∈ galleryType γ, i ∈ J) → δ y (galleryEnd y γ) ∈ cs.parabolic J := by
    intro y hy γ
    induction γ using List.reverseRecOn with
    | nil =>
      intro _ _
      rw [galleryEnd_nil, hB.eq_one_self (hsub hy)]
      exact one_mem _
    | append_singleton γ p ih =>
      intro hγ hJγ
      rw [isGallery_concat] at hγ
      have h1 := ih hγ.1 (fun i hi => hJγ i (by simp [galleryType_append, hi]))
      have hpJ : p.1 ∈ J := hJγ p.1 (by simp [galleryType_append])
      have hm : galleryEnd y γ ∈ X.residue J x :=
        mem_residue_trans hy (galleryEnd_mem_residue hγ.1
          (fun i hi => hJγ i (by simp [galleryType_append, hi])))
      have hp : p.2 ∈ X.residue J x := mem_residue_trans hm
        (X.residue_mono (Set.singleton_subset_iff.mpr hpJ) _ (mem_residue_singleton.mpr hγ.2))
      rw [galleryEnd_concat]
      rcases (hadj _ (hsub hm) _ (hsub hp) p.1 (hJK hpJ)).1 hγ.2 with e | e
      · rwa [← (hB.eq_one_iff _ (hsub hm) _ (hsub hp)).1 e]
      · rcases (hB.mul_simple y (hsub hy) _ (hsub hm) _ (hsub hp) p.1 (hJK hpJ) e).1 with e' | e'
        · rwa [e']
        · rw [e']
          exact mul_mem h1 (cs.simple_mem_parabolic hpJ)
  refine ⟨δ, ⟨fun y hy z hz => ?_, fun y hy z hz => hB.eq_one_iff y (hsub hy) z (hsub hz),
    fun y hy z hz w hw j hj e => hB.mul_simple y (hsub hy) z (hsub hz) w (hsub hw) j (hJK hj) e,
    fun y hy z hz j hj => ?_⟩, fun y hy z hz j hj => hadj y (hsub hy) z (hsub hz) j (hJK hj)⟩
  · have hz' : z ∈ X.residue J y := by rw [residue_eq_of_mem hy]; exact hz
    obtain ⟨γ, hγ, hJγ, rfl⟩ := hz'
    exact key y hy γ hγ hJγ
  · obtain ⟨w, hw, h1, h2⟩ := hB.exists_simple y (hsub hy) z (hsub hz) j (hJK hj)
    refine ⟨w, mem_residue_trans hz ?_, h1, h2⟩
    exact X.residue_mono (Set.singleton_subset_iff.mpr hj) _
      (mem_residue_singleton.mpr ((hadj z (hsub hz) w hw j (hJK hj)).2 (Or.inr h1)))

end ChamberSystem

section RankOne

variable (cs) in
open _root_.Classical in
@[expose] noncomputable def rankOneDist {Z : Type*} (z : ι) (s t : Z) : W :=
  if s = t then 1 else cs.simple z

variable (cs) in
@[expose] noncomputable def prodRankOneDist {D Z : Type*} (δ : D → D → W) (z : ι) (x y : D × Z) :
    W :=
  δ x.1 y.1 * rankOneDist cs z x.2 y.2

theorem rankOneDist_eq_one_iff {Z : Type*} {z : ι} {s t : Z} :
    rankOneDist cs z s t = 1 ↔ s = t := by
  classical
  rw [rankOneDist]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e (cs.simple_ne_one z), fun e => absurd e h⟩

theorem rankOneDist_of_eq {Z : Type*} {z : ι} {s t : Z} (h : s = t) : rankOneDist cs z s t = 1 :=
  rankOneDist_eq_one_iff.mpr h

theorem rankOneDist_of_ne {Z : Type*} {z : ι} {s t : Z} (h : s ≠ t) :
    rankOneDist cs z s t = cs.simple z := by
  classical
  rw [rankOneDist, ite_eq_right h]

theorem rankOneDist_mem {Z : Type*} (z : ι) (s t : Z) :
    rankOneDist cs z s t = 1 ∨ rankOneDist cs z s t = cs.simple z := by
  by_cases h : s = t
  · exact Or.inl (rankOneDist_of_eq h)
  · exact Or.inr (rankOneDist_of_ne h)

theorem mul_simple_not_mem_parabolic {J : Set ι} {w : W} (hw : w ∈ cs.parabolic J) {z : ι}
    (hz : z ∉ J) : w * cs.simple z ∉ cs.parabolic J := fun h => by
  have : cs.simple z ∈ cs.parabolic J := by
    have := mul_mem (inv_mem hw) h
    rwa [inv_mul_cancel_left] at this
  exact hz ((simple_mem_parabolic_iff cs).mp this)

variable {D Z : Type*} {δ : D → D → W} {J : Set ι} {R : Set D}

theorem prodRankOneDist_apply (z : ι) (x y : D × Z) :
    prodRankOneDist cs δ z x y = δ x.1 y.1 * rankOneDist cs z x.2 y.2 :=
  rfl

variable (hB : IsBuildingOn cs δ J R) {z : ι} (hz : z ∉ J)
include hB hz

theorem prodRankOneDist_eq_simple_iff {x y : D × Z} (hx : x.1 ∈ R) (hy : y.1 ∈ R) {j : ι}
    (hj : j ∈ J) :
    prodRankOneDist cs δ z x y = cs.simple j ↔ δ x.1 y.1 = cs.simple j ∧ x.2 = y.2 := by
  rw [prodRankOneDist_apply]
  constructor
  · intro h
    by_cases e : x.2 = y.2
    · rw [rankOneDist_of_eq e, mul_one] at h
      exact ⟨h, e⟩
    · exfalso
      rw [rankOneDist_of_ne e] at h
      apply mul_simple_not_mem_parabolic (hB.mem_parabolic _ hx _ hy) hz
      rw [h]
      exact cs.simple_mem_parabolic hj
  · rintro ⟨h, e⟩
    rw [rankOneDist_of_eq e, mul_one, h]

theorem prodRankOneDist_eq_simple_z_iff {x y : D × Z} (hx : x.1 ∈ R) (hy : y.1 ∈ R) :
    prodRankOneDist cs δ z x y = cs.simple z ↔ x.1 = y.1 ∧ x.2 ≠ y.2 := by
  rw [prodRankOneDist_apply]
  constructor
  · intro h
    by_cases e : x.2 = y.2
    · exfalso
      rw [rankOneDist_of_eq e, mul_one] at h
      exact hz ((simple_mem_parabolic_iff cs).mp (h ▸ hB.mem_parabolic _ hx _ hy))
    · rw [rankOneDist_of_ne e, mul_eq_right] at h
      exact ⟨(hB.eq_one_iff _ hx _ hy).mp h, e⟩
  · rintro ⟨h, e⟩
    rw [rankOneDist_of_ne e, (hB.eq_one_iff _ hx _ hy).mpr h, one_mul]

theorem prodRankOneDist_eq_one_iff {x y : D × Z} (hx : x.1 ∈ R) (hy : y.1 ∈ R) :
    prodRankOneDist cs δ z x y = 1 ↔ x = y := by
  rw [prodRankOneDist_apply]
  constructor
  · intro h
    by_cases e : x.2 = y.2
    · rw [rankOneDist_of_eq e, mul_one] at h
      exact Prod.ext ((hB.eq_one_iff _ hx _ hy).mp h) e
    · exfalso
      rw [rankOneDist_of_ne e, mul_eq_one_iff_eq_inv, cs.inv_simple] at h
      exact hz ((simple_mem_parabolic_iff cs).mp (h ▸ hB.mem_parabolic _ hx _ hy))
  · rintro rfl
    rw [rankOneDist_of_eq rfl, mul_one, hB.eq_one_self hx]

theorem prodRankOneDist_adj_iff {x y : D × Z} (hx : x.1 ∈ R) (hy : y.1 ∈ R) {j : ι} (hj : j ∈ J) :
    (prodRankOneDist cs δ z x y = 1 ∨ prodRankOneDist cs δ z x y = cs.simple j) ↔
      (δ x.1 y.1 = 1 ∨ δ x.1 y.1 = cs.simple j) ∧ x.2 = y.2 := by
  rw [prodRankOneDist_eq_one_iff hB hz hx hy, prodRankOneDist_eq_simple_iff hB hz hx hy hj]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨Or.inl (hB.eq_one_self hx), rfl⟩
    · exact ⟨Or.inr h1, h2⟩
  · rintro ⟨h1 | h1, h2⟩
    · exact Or.inl (Prod.ext ((hB.eq_one_iff _ hx _ hy).mp h1) h2)
    · exact Or.inr ⟨h1, h2⟩

theorem prodRankOneDist_adj_z_iff {x y : D × Z} (hx : x.1 ∈ R) (hy : y.1 ∈ R) :
    (prodRankOneDist cs δ z x y = 1 ∨ prodRankOneDist cs δ z x y = cs.simple z) ↔
      x.1 = y.1 := by
  rw [prodRankOneDist_eq_one_iff hB hz hx hy, prodRankOneDist_eq_simple_z_iff hB hz hx hy]
  constructor
  · rintro (rfl | ⟨h1, -⟩)
    · rfl
    · exact h1
  · intro h1
    by_cases h2 : x.2 = y.2
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr ⟨h1, h2⟩

theorem IsBuildingOn.prodRankOne (hM : ∀ j ∈ J, M j z = 2) (hZ : ∀ t : Z, ∃ t', t' ≠ t) :
    IsBuildingOn cs (prodRankOneDist cs δ z) (insert z J) (R ×ˢ (Set.univ : Set Z)) := by
  have hcomm := fun {w : W} (hw : w ∈ cs.parabolic J) => mul_simple_comm_of_mem_parabolic hM hw
  have hε : ∀ s t : Z, rankOneDist cs z s t ∈ cs.parabolic (insert z J) := fun s t => by
    rcases rankOneDist_mem (cs := cs) z s t with h | h <;> rw [h]
    · exact one_mem _
    · exact cs.simple_mem_parabolic (Set.mem_insert z J)
  have hεc : ∀ {w : W}, w ∈ cs.parabolic J → ∀ s t : Z,
      w * rankOneDist cs z s t = rankOneDist cs z s t * w := fun hw s t => by
    rcases rankOneDist_mem (cs := cs) z s t with h | h <;> rw [h]
    · rw [mul_one, one_mul]
    · exact hcomm hw
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => prodRankOneDist_eq_one_iff hB hz hx.1 hy.1,
    fun x hx y hy w hw j hj e => ?_, fun x hx y hy j hj => ?_⟩
  · exact mul_mem (cs.parabolic_mono (Set.subset_insert z J) (hB.mem_parabolic _ hx.1 _ hy.1))
      (hε _ _)
  · rw [prodRankOneDist_apply, prodRankOneDist_apply]
    rcases hj with rfl | hj
    · obtain ⟨e1, e2⟩ := (prodRankOneDist_eq_simple_z_iff hB hz hy.1 hw.1).mp e
      rw [← e1]
      by_cases hxy : x.2 = y.2
      · rw [rankOneDist_of_eq hxy, rankOneDist_of_ne (hxy ▸ e2), mul_one]
        exact ⟨Or.inr rfl, fun _ => rfl⟩
      · rw [rankOneDist_of_ne hxy]
        by_cases hxw : x.2 = w.2
        · rw [rankOneDist_of_eq hxw, mul_one, mul_assoc, cs.simple_mul_simple_self, mul_one]
          exact ⟨Or.inr rfl, fun _ => rfl⟩
        · rw [rankOneDist_of_ne hxw]
          refine ⟨Or.inl rfl, fun hl => ?_⟩
          exfalso
          rw [mul_assoc, cs.simple_mul_simple_self, mul_one,
            length_mul_simple_of_mem_parabolic hz (hB.mem_parabolic _ hx.1 _ hy.1)] at hl
          omega
    · obtain ⟨e1, e2⟩ := (prodRankOneDist_eq_simple_iff hB hz hy.1 hw.1 hj).mp e
      rw [← e2]
      obtain ⟨h1, h2⟩ := hB.mul_simple _ hx.1 _ hy.1 _ hw.1 j hj e1
      have hxy := hB.mem_parabolic _ hx.1 _ hy.1
      have hxys : δ x.1 y.1 * cs.simple j ∈ cs.parabolic J :=
        mul_mem hxy (cs.simple_mem_parabolic hj)
      refine ⟨h1.imp (fun e => by rw [e]) fun e => by
        rw [e, mul_assoc, mul_assoc, hεc (cs.simple_mem_parabolic hj)], fun hl => ?_⟩
      have hl' : cs.length (δ x.1 y.1 * cs.simple j) = cs.length (δ x.1 y.1) + 1 := by
        rcases rankOneDist_mem (cs := cs) z x.2 y.2 with h | h
        · rwa [h, mul_one] at hl
        · rw [h, mul_assoc, ← hcomm (cs.simple_mem_parabolic hj), ← mul_assoc,
            length_mul_simple_of_mem_parabolic hz hxys,
            length_mul_simple_of_mem_parabolic hz hxy] at hl
          omega
      rw [h2 hl', mul_assoc, mul_assoc, hεc (cs.simple_mem_parabolic hj)]
  · rcases hj with rfl | hj
    · by_cases hxy : x.2 = y.2
      · obtain ⟨t, ht⟩ := hZ y.2
        refine ⟨(y.1, t), ⟨hy.1, Set.mem_univ _⟩, ?_, ?_⟩
        · rw [prodRankOneDist_apply, hB.eq_one_self hy.1, one_mul, rankOneDist_of_ne (Ne.symm ht)]
        · rw [prodRankOneDist_apply, prodRankOneDist_apply, rankOneDist_of_eq hxy, mul_one,
            rankOneDist_of_ne (fun h => ht (h.symm.trans hxy))]
      · refine ⟨(y.1, x.2), ⟨hy.1, Set.mem_univ _⟩, ?_, ?_⟩
        · rw [prodRankOneDist_apply, hB.eq_one_self hy.1, one_mul,
            rankOneDist_of_ne (Ne.symm hxy)]
        · rw [prodRankOneDist_apply, prodRankOneDist_apply, rankOneDist_of_eq rfl, mul_one,
            rankOneDist_of_ne hxy, mul_assoc, cs.simple_mul_simple_self, mul_one]
    · obtain ⟨w, hw, h1, h2⟩ := hB.exists_simple _ hx.1 _ hy.1 j hj
      refine ⟨(w, y.2), ⟨hw, Set.mem_univ _⟩, ?_, ?_⟩
      · rw [prodRankOneDist_apply, h1, rankOneDist_of_eq rfl, mul_one]
      · rw [prodRankOneDist_apply, prodRankOneDist_apply, h2, mul_assoc, mul_assoc,
          hεc (cs.simple_mem_parabolic hj)]

end RankOne

end CFSG.Monster.B.Geometry
