module

public import CFSG.Monster.B.Geometry.ChamberCover
public import Mathlib.Algebra.Group.MinimalAxioms

public section

namespace CFSG.Monster.B.Geometry

namespace ChamberSystem

universe u v

variable {I : Type u} {C : Type v} (X : ChamberSystem I C) (c₀ : C)

@[expose] noncomputable def rep (a : X.Cover c₀) : List (I × C) := (Quotient.out a).1

variable {X c₀}

theorem isGallery_rep (a : X.Cover c₀) : X.IsGallery c₀ (X.rep c₀ a) := (Quotient.out a).2

@[simp] theorem cls_rep (a : X.Cover c₀) : X.cls c₀ (X.rep c₀ a) = a := by
  rw [cls_of_isGallery (isGallery_rep a)]
  exact Quotient.out_eq a

theorem galleryEnd_rep (a : X.Cover c₀) : galleryEnd c₀ (X.rep c₀ a) = X.coverProj c₀ a := by
  conv_rhs => rw [← cls_rep a]
  rw [coverProj_cls (isGallery_rep a)]

theorem isGallery_translate {h : Equiv.Perm C} (hh : h ∈ X.typeAut) {γ δ : List (I × C)}
    (hγ : X.IsGallery c₀ γ) (hend : galleryEnd c₀ γ = h c₀) (hδ : X.IsGallery c₀ δ) :
    X.IsGallery c₀ (γ ++ galleryMap h δ) := by
  refine hγ.append ?_
  rw [hend]
  exact (isMorphism_of_mem_typeAut hh).isGallery hδ

theorem galleryEnd_translate {h : Equiv.Perm C} {γ δ : List (I × C)}
    (hend : galleryEnd c₀ γ = h c₀) :
    galleryEnd c₀ (γ ++ galleryMap h δ) = h (galleryEnd c₀ δ) := by
  rw [galleryEnd_append, hend, galleryEnd_galleryMap]

theorem twoHomotopic_translate {h : Equiv.Perm C} (hh : h ∈ X.typeAut) {γ γ' δ δ' : List (I × C)}
    (hγγ : X.TwoHomotopic c₀ γ γ') (hend : galleryEnd c₀ γ = h c₀)
    (hδδ : X.TwoHomotopic c₀ δ δ') :
    X.TwoHomotopic c₀ (γ ++ galleryMap h δ) (γ' ++ galleryMap h δ') := by
  refine hγγ.append ?_
  rw [hend]
  exact hδδ.map (isMorphism_of_mem_typeAut hh)

variable (X c₀) in
@[ext] structure LiftPair where
  aut : X.typeAut
  cl : X.Cover c₀
  proj_eq : X.coverProj c₀ cl = (aut : Equiv.Perm C) c₀

variable (X c₀) in
@[expose] noncomputable def liftAct (z : X.LiftPair c₀) (d : X.Cover c₀) : X.Cover c₀ :=
  X.cls c₀ (X.rep c₀ z.cl ++ galleryMap (z.aut : Equiv.Perm C) (X.rep c₀ d))

theorem liftAct_cls (z : X.LiftPair c₀) {γ δ : List (I × C)} (hγ : X.IsGallery c₀ γ)
    (hz : z.cl = X.cls c₀ γ) (hδ : X.IsGallery c₀ δ) :
    X.liftAct c₀ z (X.cls c₀ δ) = X.cls c₀ (γ ++ galleryMap (z.aut : Equiv.Perm C) δ) := by
  refine cls_congr (twoHomotopic_translate z.aut.2 ?_ ?_ ?_)
  · rw [← cls_eq_iff (isGallery_rep _) hγ, cls_rep, hz]
  · rw [galleryEnd_rep, z.proj_eq]
  · rw [← cls_eq_iff (isGallery_rep _) hδ, cls_rep]

theorem coverProj_liftAct (z : X.LiftPair c₀) (d : X.Cover c₀) :
    X.coverProj c₀ (X.liftAct c₀ z d) = (z.aut : Equiv.Perm C) (X.coverProj c₀ d) := by
  have hend : galleryEnd c₀ (X.rep c₀ z.cl) = (z.aut : Equiv.Perm C) c₀ := by
    rw [galleryEnd_rep, z.proj_eq]
  rw [liftAct, coverProj_cls (isGallery_translate z.aut.2 (isGallery_rep _) hend
    (isGallery_rep _)), galleryEnd_translate hend, galleryEnd_rep]

noncomputable instance : Mul (X.LiftPair c₀) where
  mul z w := ⟨z.aut * w.aut, X.liftAct c₀ z w.cl, by
    rw [coverProj_liftAct, w.proj_eq]
    rfl⟩

noncomputable instance : One (X.LiftPair c₀) where
  one := ⟨1, X.coverBase c₀, by simp⟩

noncomputable instance : Inv (X.LiftPair c₀) where
  inv z := ⟨z.aut⁻¹, X.cls c₀ (galleryMap ((z.aut⁻¹ : X.typeAut) : Equiv.Perm C)
      (galleryReverse c₀ (X.rep c₀ z.cl))), by
    have hend : galleryEnd c₀ (X.rep c₀ z.cl) = (z.aut : Equiv.Perm C) c₀ := by
      rw [galleryEnd_rep, z.proj_eq]
    have hg := ((isMorphism_of_mem_typeAut (z.aut⁻¹).2).isGallery (isGallery_rep z.cl).reverse)
    have hbase : ((z.aut⁻¹ : X.typeAut) : Equiv.Perm C) (galleryEnd c₀ (X.rep c₀ z.cl)) = c₀ := by
      rw [hend]
      simp
    rw [hbase] at hg
    rw [coverProj_cls hg, galleryEnd_galleryMap' _ hbase, galleryEnd_galleryReverse]⟩

theorem mul_aut (z w : X.LiftPair c₀) : (z * w).aut = z.aut * w.aut := rfl
theorem mul_cl (z w : X.LiftPair c₀) : (z * w).cl = X.liftAct c₀ z w.cl := rfl
theorem one_aut : (1 : X.LiftPair c₀).aut = 1 := rfl
theorem one_cl : (1 : X.LiftPair c₀).cl = X.coverBase c₀ := rfl
theorem inv_aut (z : X.LiftPair c₀) : (z⁻¹).aut = z.aut⁻¹ := rfl

theorem liftAct_mul (z w : X.LiftPair c₀) (d : X.Cover c₀) :
    X.liftAct c₀ (z * w) d = X.liftAct c₀ z (X.liftAct c₀ w d) := by
  obtain ⟨γ, hγ, hz⟩ := exists_eq_cls z.cl
  obtain ⟨η, hη, hw⟩ := exists_eq_cls w.cl
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_cls d
  have hendγ : galleryEnd c₀ γ = (z.aut : Equiv.Perm C) c₀ := by
    rw [← coverProj_cls hγ, ← hz, z.proj_eq]
  have hendη : galleryEnd c₀ η = (w.aut : Equiv.Perm C) c₀ := by
    rw [← coverProj_cls hη, ← hw, w.proj_eq]
  have hηδ := isGallery_translate w.aut.2 hη hendη hδ
  have hzw : (z * w).cl = X.cls c₀ (γ ++ galleryMap (z.aut : Equiv.Perm C) η) := by
    rw [mul_cl, hw, liftAct_cls z hγ hz hη]
  have hγη := isGallery_translate z.aut.2 hγ hendγ hη
  rw [liftAct_cls (z * w) hγη hzw hδ, liftAct_cls w hη hw hδ, liftAct_cls z hγ hz hηδ,
    mul_aut, galleryMap_append, galleryMap_galleryMap, List.append_assoc]
  rfl

theorem one_liftAct (d : X.Cover c₀) : X.liftAct c₀ 1 d = d := by
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_cls d
  rw [liftAct_cls 1 (γ := []) trivial rfl hδ, one_aut]
  simp only [List.nil_append, Subgroup.coe_one]
  have : galleryMap (⇑(1 : Equiv.Perm C)) δ = δ := by
    simp
  rw [this]

theorem liftAct_coverBase (z : X.LiftPair c₀) : X.liftAct c₀ z (X.coverBase c₀) = z.cl := by
  obtain ⟨γ, hγ, hz⟩ := exists_eq_cls z.cl
  rw [coverBase, liftAct_cls z hγ hz (δ := []) (isGallery_nil c₀), galleryMap_nil,
    List.append_nil, hz]

noncomputable instance : Group (X.LiftPair c₀) :=
  Group.ofLeftAxioms
    (fun z w u => LiftPair.ext (mul_assoc _ _ _) (by
      change X.liftAct c₀ (z * w) u.cl = X.liftAct c₀ z (X.liftAct c₀ w u.cl)
      exact liftAct_mul z w u.cl))
    (fun z => LiftPair.ext (one_mul _) (one_liftAct z.cl))
    (fun z => LiftPair.ext (inv_mul_cancel _) (by
      change X.liftAct c₀ z⁻¹ z.cl = X.coverBase c₀
      obtain ⟨γ, hγ, hz⟩ := exists_eq_cls z.cl
      have hend : galleryEnd c₀ γ = (z.aut : Equiv.Perm C) c₀ := by
        rw [← coverProj_cls hγ, ← hz, z.proj_eq]
      have hrep : X.TwoHomotopic c₀ (X.rep c₀ z.cl) γ := by
        rw [← cls_eq_iff (isGallery_rep _) hγ, cls_rep, hz]
      have hbase : ((z.aut⁻¹ : X.typeAut) : Equiv.Perm C) (galleryEnd c₀ γ) = c₀ := by
        rw [hend]; simp
      have hinv : (z⁻¹).cl = X.cls c₀ (galleryMap ((z.aut⁻¹ : X.typeAut) : Equiv.Perm C)
          (galleryReverse c₀ γ)) := by
        change X.cls c₀ _ = _
        refine cls_congr ?_
        have := hrep.reverse.map (isMorphism_of_mem_typeAut (z.aut⁻¹).2)
        rw [hrep.galleryEnd_eq, hbase] at this
        exact this
      have hg := (isMorphism_of_mem_typeAut (z.aut⁻¹).2).isGallery hγ.reverse
      rw [hbase] at hg
      rw [hz, liftAct_cls z⁻¹ hg hinv hγ, inv_aut, ← galleryMap_append]
      have h2 : X.TwoHomotopic c₀ (galleryMap ((z.aut⁻¹ : X.typeAut) : Equiv.Perm C)
          (galleryReverse c₀ γ ++ γ)) [] := by
        have := (twoHomotopic_reverse_append hγ).map (isMorphism_of_mem_typeAut (z.aut⁻¹).2)
        rwa [hbase] at this
      rw [cls_congr h2]
      rfl))

noncomputable instance : MulAction (X.LiftPair c₀) (X.Cover c₀) where
  smul := X.liftAct c₀
  one_smul := one_liftAct
  mul_smul := liftAct_mul

theorem smul_def (z : X.LiftPair c₀) (d : X.Cover c₀) : z • d = X.liftAct c₀ z d := rfl

theorem smul_cls (z : X.LiftPair c₀) {γ δ : List (I × C)} (hγ : X.IsGallery c₀ γ)
    (hz : z.cl = X.cls c₀ γ) (hδ : X.IsGallery c₀ δ) :
    z • X.cls c₀ δ = X.cls c₀ (γ ++ galleryMap (z.aut : Equiv.Perm C) δ) :=
  liftAct_cls z hγ hz hδ

theorem mul_cl_cls (z w : X.LiftPair c₀) {γ η : List (I × C)} (hγ : X.IsGallery c₀ γ)
    (hz : z.cl = X.cls c₀ γ) (hη : X.IsGallery c₀ η) (hw : w.cl = X.cls c₀ η) :
    (z * w).cl = X.cls c₀ (γ ++ galleryMap (z.aut : Equiv.Perm C) η) := by
  rw [mul_cl, hw]
  exact liftAct_cls z hγ hz hη

theorem coverProj_smul (z : X.LiftPair c₀) (d : X.Cover c₀) :
    X.coverProj c₀ (z • d) = (z.aut : Equiv.Perm C) (X.coverProj c₀ d) :=
  coverProj_liftAct z d

theorem isMorphism_smul (z : X.LiftPair c₀) :
    IsMorphism (X.universalCover c₀) (X.universalCover c₀) (z • ·) := by
  intro i a b hab
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls a
  obtain ⟨γ, hγ, hz⟩ := exists_eq_cls z.cl
  have hend : galleryEnd c₀ γ = (z.aut : Equiv.Perm C) c₀ := by
    rw [← coverProj_cls hγ, ← hz, z.proj_eq]
  obtain ⟨y, hy, rfl⟩ := (universalCover_adj_cls_iff hα).mp hab
  have hαy : X.IsGallery c₀ (α ++ [(i, y)]) := (isGallery_concat _ _ _).mpr ⟨hα, hy⟩
  show (X.universalCover c₀).adj i (z • X.cls c₀ α) (z • X.cls c₀ (α ++ [(i, y)]))
  rw [smul_cls z hγ hz hα, smul_cls z hγ hz hαy]
  refine (universalCover_adj_cls_iff (isGallery_translate z.aut.2 hγ hend hα)).mpr
    ⟨(z.aut : Equiv.Perm C) y, ?_, ?_⟩
  · rw [galleryEnd_translate hend]
    exact (isMorphism_of_mem_typeAut z.aut.2) i _ _ hy
  · simp [galleryMap_append, List.append_assoc]

variable (X c₀) in
@[expose] noncomputable def liftPerm : X.LiftPair c₀ →* Equiv.Perm (X.Cover c₀) :=
  MulAction.toPermHom _ _

theorem liftPerm_apply (z : X.LiftPair c₀) (d : X.Cover c₀) : X.liftPerm c₀ z d = z • d := rfl

theorem liftPerm_mem_typeAut (z : X.LiftPair c₀) :
    X.liftPerm c₀ z ∈ (X.universalCover c₀).typeAut := by
  intro i a b
  refine ⟨fun h => ?_, isMorphism_smul z i a b⟩
  have := isMorphism_smul z⁻¹ i _ _ h
  simpa [liftPerm_apply, smul_smul] using this

variable (X c₀) in
@[expose] noncomputable def liftProj : X.LiftPair c₀ →* X.typeAut where
  toFun z := z.aut
  map_one' := rfl
  map_mul' _ _ := rfl

theorem liftProj_apply (z : X.LiftPair c₀) : X.liftProj c₀ z = z.aut := rfl

theorem mem_ker_liftProj_iff {z : X.LiftPair c₀} : z ∈ (X.liftProj c₀).ker ↔ z.aut = 1 :=
  MonoidHom.mem_ker

theorem smul_coverBase (z : X.LiftPair c₀) : z • X.coverBase c₀ = z.cl := liftAct_coverBase z

theorem eq_of_coverProj_comp_eq {f g : X.Cover c₀ → X.Cover c₀}
    (hf : IsMorphism (X.universalCover c₀) (X.universalCover c₀) f)
    (hg : IsMorphism (X.universalCover c₀) (X.universalCover c₀) g)
    (hfg : X.coverProj c₀ ∘ f = X.coverProj c₀ ∘ g) {a : X.Cover c₀} (ha : f a = g a) : f = g :=
  eq_of_comp_eq universalCover_connected (fun i d => (bijOn_coverProj_panel i d).injOn) hf hg
    (fun z => congrFun hfg z) ha

theorem liftPerm_injective (hX : X.Connected) : Function.Injective (X.liftPerm c₀) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : ∀ d, z • d = d := fun d => by
    have := congrArg (· d) hz
    simpa [liftPerm_apply] using this
  refine LiftPair.ext ?_ ?_
  · refine Subtype.ext (Equiv.ext fun c => ?_)
    obtain ⟨d, rfl⟩ := coverProj_surjective (c₀ := c₀) hX c
    have := congrArg (X.coverProj c₀) (hz' d)
    rw [coverProj_smul] at this
    exact this
  · rw [← smul_coverBase, hz']
    rfl

theorem exists_ker_eq_deck {g : Equiv.Perm (X.Cover c₀)} (hg : g ∈ (X.universalCover c₀).typeAut)
    (hgπ : ∀ d, X.coverProj c₀ (g d) = X.coverProj c₀ d) :
    ∃ z ∈ (X.liftProj c₀).ker, X.liftPerm c₀ z = g := by
  set z : X.LiftPair c₀ := ⟨1, g (X.coverBase c₀), by rw [hgπ]; simp⟩
  refine ⟨z, rfl, ?_⟩
  have := eq_of_coverProj_comp_eq (f := (z • ·)) (g := g) (isMorphism_smul z)
    (isMorphism_of_mem_typeAut hg) (by
      funext d
      simp only [Function.comp_apply, coverProj_smul, hgπ]
      rfl) (a := X.coverBase c₀) (smul_coverBase z)
  ext d
  exact congrFun this d

theorem coverProj_smul_of_mem_ker {z : X.LiftPair c₀} (hz : z ∈ (X.liftProj c₀).ker)
    (d : X.Cover c₀) : X.coverProj c₀ (z • d) = X.coverProj c₀ d := by
  rw [coverProj_smul, mem_ker_liftProj_iff.mp hz]
  rfl

theorem eq_one_of_mem_ker_of_smul_eq (hX : X.Connected) {z : X.LiftPair c₀}
    (hz : z ∈ (X.liftProj c₀).ker) {d : X.Cover c₀} (hd : z • d = d) : z = 1 := by
  have := eq_of_coverProj_comp_eq (f := (z • ·)) (g := id) (isMorphism_smul z) isMorphism_id
    (by funext e; exact coverProj_smul_of_mem_ker hz e) hd
  refine liftPerm_injective hX ?_
  ext e
  have h := congrFun this e
  simpa [liftPerm_apply] using h

theorem exists_ker_smul_eq {d d' : X.Cover c₀} (h : X.coverProj c₀ d = X.coverProj c₀ d') :
    ∃ z ∈ (X.liftProj c₀).ker, z • d = d' := by
  obtain ⟨α, hα, rfl⟩ := exists_eq_cls d
  obtain ⟨β, hβ, rfl⟩ := exists_eq_cls d'
  rw [coverProj_cls hα, coverProj_cls hβ] at h
  have hlam : X.IsGallery c₀ (β ++ galleryReverse c₀ α) := by
    refine hβ.append ?_
    rw [← h]
    exact hα.reverse
  have hlamend : galleryEnd c₀ (β ++ galleryReverse c₀ α) = c₀ := by
    rw [galleryEnd_append, ← h, galleryEnd_galleryReverse]
  set z : X.LiftPair c₀ := ⟨1, X.cls c₀ (β ++ galleryReverse c₀ α), by
    rw [coverProj_cls hlam, hlamend]; rfl⟩
  refine ⟨z, rfl, ?_⟩
  rw [smul_cls z hlam rfl hα]
  change X.cls c₀ (β ++ galleryReverse c₀ α ++ galleryMap (⇑(1 : Equiv.Perm C)) α) = _
  have h1 : galleryMap (⇑(1 : Equiv.Perm C)) α = α := by simp
  rw [h1, List.append_assoc]
  refine cls_congr ?_
  have h2 := twoHomotopic_reverse_append hα
  rw [h] at h2
  have := TwoHomotopic.append_left (x := c₀) β h2
  simpa using this

variable (X c₀) in
noncomputable abbrev pi2 : Subgroup (X.LiftPair c₀) := (X.liftProj c₀).ker

noncomputable def pi2Equiv : X.pi2 c₀ ≃ {a : X.Cover c₀ // X.coverProj c₀ a = c₀} where
  toFun z := ⟨z.1.cl, by rw [z.1.proj_eq, mem_ker_liftProj_iff.mp z.2]; rfl⟩
  invFun a := ⟨⟨1, a.1, by rw [a.2]; rfl⟩, rfl⟩
  left_inv z := by
    refine Subtype.ext (LiftPair.ext ?_ rfl)
    exact (mem_ker_liftProj_iff.mp z.2).symm
  right_inv a := rfl

theorem pi2_mul_cl (z w : X.pi2 c₀) {lam mu : List (I × C)} (hlam : X.IsGallery c₀ lam)
    (hz : z.1.cl = X.cls c₀ lam) (hmu : X.IsGallery c₀ mu) (hw : w.1.cl = X.cls c₀ mu) :
    (z * w).1.cl = X.cls c₀ (lam ++ mu) := by
  rw [Subgroup.coe_mul, mul_cl_cls z.1 w.1 hlam hz hmu hw, mem_ker_liftProj_iff.mp z.2]
  have h1 : galleryMap (⇑(1 : Equiv.Perm C)) mu = mu := by simp
  change X.cls c₀ (lam ++ galleryMap (⇑(1 : Equiv.Perm C)) mu) = _
  rw [h1]

variable (X c₀) in
noncomputable abbrev liftSubgroup (H : Subgroup X.typeAut) : Subgroup (X.LiftPair c₀) :=
  H.comap (X.liftProj c₀)

theorem liftProj_surjective (hX : X.Connected) : Function.Surjective (X.liftProj c₀) := by
  intro h
  obtain ⟨γ, hγ, hend⟩ := hX c₀ ((h : Equiv.Perm C) c₀)
  exact ⟨⟨h, X.cls c₀ γ, by rw [coverProj_cls hγ, hend]⟩, rfl⟩

theorem bijOn_liftProj_stabilizer (hX : X.Connected) (H : Subgroup X.typeAut) {J : Set I}
    {a : X.Cover c₀} (hR : IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) J a) :
    Set.BijOn (X.liftProj c₀)
      {z | z ∈ X.liftSubgroup c₀ H ∧
        (fun d : X.Cover c₀ => z • d) '' (X.universalCover c₀).residue J a =
          (X.universalCover c₀).residue J a}
      {h | h ∈ H ∧ (h : Equiv.Perm C) '' X.residue J (X.coverProj c₀ a) =
        X.residue J (X.coverProj c₀ a)} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨hzH, hzR⟩
    refine ⟨hzH, ?_⟩
    calc ((X.liftProj c₀ z : X.typeAut) : Equiv.Perm C) '' X.residue J (X.coverProj c₀ a)
        = ((X.liftProj c₀ z : X.typeAut) : Equiv.Perm C) ''
            (X.coverProj c₀ '' (X.universalCover c₀).residue J a) := by
          rw [hR.1.image_eq]
      _ = X.coverProj c₀ '' ((fun d : X.Cover c₀ => z • d) ''
            (X.universalCover c₀).residue J a) := by
          rw [Set.image_image, Set.image_image]
          exact Set.image_congr fun d _ => (coverProj_smul z d).symm
      _ = X.residue J (X.coverProj c₀ a) := by rw [hzR, hR.1.image_eq]
  · rintro z ⟨-, hzR⟩ w ⟨-, hwR⟩ hzw
    have hk : z⁻¹ * w ∈ (X.liftProj c₀).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzw, inv_mul_cancel]
    have haR : a ∈ (X.universalCover c₀).residue J a := self_mem_residue J a
    have h1 : (z⁻¹ * w) • a ∈ (X.universalCover c₀).residue J a := by
      have hwa : w • a ∈ (X.universalCover c₀).residue J a := hwR ▸ ⟨a, haR, rfl⟩
      obtain ⟨b, hb, hba⟩ := hzR.symm ▸ hwa
      rw [mul_smul, ← hba, inv_smul_smul]
      exact hb
    have h2 : (z⁻¹ * w) • a = a :=
      hR.1.injOn h1 haR (coverProj_smul_of_mem_ker hk a)
    have := eq_one_of_mem_ker_of_smul_eq hX hk h2
    rw [inv_mul_eq_one] at this
    exact this
  · rintro h ⟨hhH, hhR⟩
    obtain ⟨u, rfl⟩ := liftProj_surjective (c₀ := c₀) hX h
    have hua : ((X.liftProj c₀ u : X.typeAut) : Equiv.Perm C) (X.coverProj c₀ a) ∈
        X.residue J (X.coverProj c₀ a) := by
      rw [← hhR]
      exact ⟨_, self_mem_residue J _, rfl⟩
    obtain ⟨e, he, hπe⟩ := hR.1.surjOn hua
    have hfib : X.coverProj c₀ (u • a) = X.coverProj c₀ e := by
      rw [coverProj_smul, hπe]
      rfl
    obtain ⟨v, hv, hvu⟩ := exists_ker_smul_eq hfib
    refine ⟨v * u, ⟨?_, ?_⟩, ?_⟩
    · change X.liftProj c₀ (v * u) ∈ H
      rw [map_mul, MonoidHom.mem_ker.mp hv, one_mul]
      exact hhH
    · have hmem : X.liftPerm c₀ (v * u) ∈ (X.universalCover c₀).typeAut := liftPerm_mem_typeAut _
      have := image_residue_of_mem_typeAut hmem J a
      rw [liftPerm_apply, mul_smul, hvu] at this
      rw [residue_eq_of_mem he] at this
      exact this
    · rw [map_mul, MonoidHom.mem_ker.mp hv, one_mul]

theorem chamber_universal_cover_action_lifting (hX : X.Connected) (H : Subgroup X.typeAut) :
    (∀ z : X.LiftPair c₀, X.liftPerm c₀ z ∈ (X.universalCover c₀).typeAut) ∧
    Function.Injective (X.liftPerm c₀) ∧
    (∀ (z w : X.LiftPair c₀) (γ η : List (I × C)), X.IsGallery c₀ γ → z.cl = X.cls c₀ γ →
      X.IsGallery c₀ η → w.cl = X.cls c₀ η →
        (z * w).aut = z.aut * w.aut ∧
          (z * w).cl = X.cls c₀ (γ ++ galleryMap (z.aut : Equiv.Perm C) η)) ∧
    (∀ (z : X.LiftPair c₀) (γ δ : List (I × C)), X.IsGallery c₀ γ → z.cl = X.cls c₀ γ →
      X.IsGallery c₀ δ → z • X.cls c₀ δ = X.cls c₀ (γ ++ galleryMap (z.aut : Equiv.Perm C) δ)) ∧
    Set.SurjOn (X.liftProj c₀) (X.liftSubgroup c₀ H) H ∧
    (∀ (z : X.LiftPair c₀) (d : X.Cover c₀),
      X.coverProj c₀ (z • d) = (X.liftProj c₀ z : Equiv.Perm C) (X.coverProj c₀ d)) ∧
    X.pi2 c₀ ≤ X.liftSubgroup c₀ H ∧
    (∀ z ∈ X.liftSubgroup c₀ H, X.liftProj c₀ z = 1 ↔ z ∈ X.pi2 c₀) ∧
    (∀ g ∈ (X.universalCover c₀).typeAut, (∀ d, X.coverProj c₀ (g d) = X.coverProj c₀ d) →
      ∃ z ∈ X.pi2 c₀, X.liftPerm c₀ z = g) ∧
    (∀ z ∈ X.pi2 c₀, ∀ d : X.Cover c₀, X.coverProj c₀ (z • d) = X.coverProj c₀ d) ∧
    (∀ z ∈ X.pi2 c₀, ∀ d : X.Cover c₀, z • d = d → z = 1) ∧
    (∀ d d' : X.Cover c₀, X.coverProj c₀ d = X.coverProj c₀ d' → ∃ z ∈ X.pi2 c₀, z • d = d') ∧
    (∀ (J : Set I) (a : X.Cover c₀), IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) J a →
      Set.BijOn (X.liftProj c₀)
        {z | z ∈ X.liftSubgroup c₀ H ∧
          (fun d : X.Cover c₀ => z • d) '' (X.universalCover c₀).residue J a =
          (X.universalCover c₀).residue J a}
        {h | h ∈ H ∧ (h : Equiv.Perm C) '' X.residue J (X.coverProj c₀ a) =
          X.residue J (X.coverProj c₀ a)}) := by
  refine ⟨liftPerm_mem_typeAut, liftPerm_injective hX, fun z w γ η hγ hz hη hw =>
    ⟨rfl, mul_cl_cls z w hγ hz hη hw⟩, fun z γ δ hγ hz hδ => smul_cls z hγ hz hδ, ?_,
    coverProj_smul, fun z hz => ?_, fun z _ => MonoidHom.mem_ker.symm, fun g hg hgπ =>
    exists_ker_eq_deck hg hgπ, fun z hz d => coverProj_smul_of_mem_ker hz d,
    fun z hz d hd => eq_one_of_mem_ker_of_smul_eq hX hz hd, fun d d' h => exists_ker_smul_eq h,
    fun J a hR => bijOn_liftProj_stabilizer hX H hR⟩
  · intro h hh
    obtain ⟨u, hu⟩ := liftProj_surjective (c₀ := c₀) hX h
    exact ⟨u, by change X.liftProj c₀ u ∈ H; rw [hu]; exact hh, hu⟩
  · change X.liftProj c₀ z ∈ H
    rw [MonoidHom.mem_ker.mp hz]
    exact one_mem H

end ChamberSystem

end CFSG.Monster.B.Geometry
