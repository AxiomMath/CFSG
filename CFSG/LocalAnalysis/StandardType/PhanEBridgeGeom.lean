module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeTits

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.LieType.Chevalley.CosetBuilding CFSG.ClassicalInvolution.Phan

section Transport

variable {I : Type*} {C D : Type*}

theorem connected_of_equiv {X : ChamberSystem I C} {Y : ChamberSystem I D} (e : C ≃ D)
    (he : ∀ i x y, X.adj i x y ↔ Y.adj i (e x) (e y)) : Y.Connected → X.Connected := by
  intro hY x y
  have hm : IsMorphism Y X (e.symm : D → C) := by
    intro i a b hab
    rw [he i, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  obtain ⟨γ, hγ, hend⟩ := hY (e x) (e y)
  refine ⟨galleryMap (e.symm : D → C) γ, ?_, ?_⟩
  · simpa using hm.isGallery hγ
  · rw [galleryEnd_galleryMap' (e.symm : D → C) (e.symm_apply_apply x) γ, hend,
      e.symm_apply_apply]

theorem simplyTwoConnected_of_equiv {X : ChamberSystem I C} {Y : ChamberSystem I D} (e : C ≃ D)
    (he : ∀ i x y, X.adj i x y ↔ Y.adj i (e x) (e y)) :
    Y.SimplyTwoConnected → X.SimplyTwoConnected := by
  intro hY x γ hγ hend
  have hf : IsMorphism X Y (e : C → D) := fun i a b h => (he i a b).1 h
  have hg : IsMorphism Y X (e.symm : D → C) := by
    intro i a b hab
    rw [he i, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  have h1 : Y.IsGallery (e x) (galleryMap (e : C → D) γ) := hf.isGallery hγ
  have h2 : galleryEnd (e x) (galleryMap (e : C → D) γ) = e x := by
    rw [galleryEnd_galleryMap, hend]
  have h3 := (hY _ _ h1 h2).map hg
  rw [e.symm_apply_apply, galleryMap_galleryMap] at h3
  simpa using h3

end Transport

section Geom

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

structure PhanEConfig.Geom (c : PhanEConfig K f M G) [MulAction G c.C] where
  isom : ∀ (g : G) (x y : c.C), c.δ (g • x) (g • y) = c.δ x y
  comm_t : ∀ (g : G) (x : c.C), c.t (g • x) = g • c.t x
  c₀ : c.C
  c₀_op : c.δ c₀ (c.t c₀) = c.w₀
  transitive : ∀ x : c.C, c.δ x (c.t x) = c.w₀ → ∃ g : G, g • c₀ = x
  stab_base : ∀ g : G, g • c₀ = c₀ ↔ g ∈ c.S.torus
  stab_panel : ∀ (i : Fin n) (g : G),
    panelRel M.toCoxeterSystem c.δ i c₀ (g • c₀) ↔ g ∈ c.S.parab {i}
  good : c.S.Good

private theorem q2nPE_geom_mem (c : PhanEConfig K f M G) [MulAction G c.C] (d : c.Geom)
    (a : G) : c.δ (a • d.c₀) (c.t (a • d.c₀)) = c.w₀ := by
  rw [d.comm_t a d.c₀, d.isom a d.c₀ (c.t d.c₀)]
  exact d.c₀_op

private theorem q2nPE_geom_smul_eq (c : PhanEConfig K f M G) [MulAction G c.C] (d : c.Geom)
    {a b : G} (hab : a⁻¹ * b ∈ c.S.torus) : a • d.c₀ = b • d.c₀ := by
  have h : (a⁻¹ * b) • d.c₀ = d.c₀ := (d.stab_base (a⁻¹ * b)).mpr hab
  calc a • d.c₀ = a • ((a⁻¹ * b) • d.c₀) := by rw [h]
    _ = (a * (a⁻¹ * b)) • d.c₀ := (mul_smul a (a⁻¹ * b) d.c₀).symm
    _ = b • d.c₀ := by rw [show a * (a⁻¹ * b) = b by group]

private theorem q2nPE_geom_smul_conj (c : PhanEConfig K f M G) [MulAction G c.C] (d : c.Geom)
    (a b : G) : a • ((a⁻¹ * b) • d.c₀) = b • d.c₀ := by
  rw [← mul_smul]
  congr 1
  group

private noncomputable def q2nPE_geomFun (c : PhanEConfig K f M G) [MulAction G c.C]
    (d : c.Geom) : G ⧸ c.S.torus → ↥(flipOpSet c.δ c.w₀ c.t) :=
  fun q => Quotient.liftOn' q (fun a => (⟨a • d.c₀, q2nPE_geom_mem c d a⟩ :
      ↥(flipOpSet c.δ c.w₀ c.t)))
    (fun a b hab => Subtype.ext (q2nPE_geom_smul_eq c d (QuotientGroup.leftRel_apply.mp hab)))

private theorem q2nPE_geomFun_apply (c : PhanEConfig K f M G) [MulAction G c.C]
    (d : c.Geom) (a : G) :
    (q2nPE_geomFun c d (a : G ⧸ c.S.torus)).1 = a • d.c₀ := by
  simp only [q2nPE_geomFun, QuotientGroup.quotient_liftOn_mk]

private theorem q2nPE_geomFun_bijective (c : PhanEConfig K f M G) [MulAction G c.C]
    (d : c.Geom) : Function.Bijective (q2nPE_geomFun c d) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have h : a • d.c₀ = b • d.c₀ := by
      have hv := congrArg Subtype.val hxy
      rwa [q2nPE_geomFun_apply, q2nPE_geomFun_apply] at hv
    rw [QuotientGroup.eq]
    exact (d.stab_base (a⁻¹ * b)).mp (by
      rw [mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul])
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := d.transitive x hx
    exact ⟨(g : G ⧸ c.S.torus), Subtype.ext (by rw [q2nPE_geomFun_apply]; exact hg)⟩

private noncomputable def q2nPE_geomEquiv (c : PhanEConfig K f M G) [MulAction G c.C]
    (d : c.Geom) : G ⧸ c.S.torus ≃ ↥(flipOpSet c.δ c.w₀ c.t) :=
  Equiv.ofBijective (q2nPE_geomFun c d) (q2nPE_geomFun_bijective c d)

private theorem q2nPE_geomEquiv_apply (c : PhanEConfig K f M G) [MulAction G c.C]
    (d : c.Geom) (a : G) :
    (q2nPE_geomEquiv c d (a : G ⧸ c.S.torus)).1 = a • d.c₀ :=
  q2nPE_geomFun_apply c d a

private theorem q2nPE_panelRel_smul_forward (c : PhanEConfig K f M G) [MulAction G c.C]
    (d : c.Geom) (g : G) (i : Fin n) {p q : c.C}
    (h : panelRel M.toCoxeterSystem c.δ i p q) :
    panelRel M.toCoxeterSystem c.δ i (g • p) (g • q) := by
  unfold panelRel at h ⊢
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ (by rw [d.isom g u v]; exact huv)
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private theorem q2nPE_panelRel_smul (c : PhanEConfig K f M G) [MulAction G c.C] (d : c.Geom)
    (g : G) (i : Fin n) (p q : c.C) :
    panelRel M.toCoxeterSystem c.δ i (g • p) (g • q) ↔
      panelRel M.toCoxeterSystem c.δ i p q := by
  constructor
  · intro h
    have h' := q2nPE_panelRel_smul_forward c d g⁻¹ i (p := g • p) (q := g • q) h
    simpa using h'
  · exact q2nPE_panelRel_smul_forward c d g i

private theorem q2nPE_geom_adj_iff (c : PhanEConfig K f M G) [MulAction G c.C] (d : c.Geom)
    (i : Fin n) (x y : G ⧸ c.S.torus) :
    (phanSystemE c.S).adj i x y ↔
      (inducedSystemAll M.toCoxeterSystem c.δ (flipOpSet c.δ c.w₀ c.t)).adj i
        (q2nPE_geomEquiv c d x) (q2nPE_geomEquiv c d y) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [phanSystemE_adj_mk]
  have ha : (q2nPE_geomEquiv c d (a : G ⧸ c.S.torus)).1 = a • d.c₀ :=
    q2nPE_geomEquiv_apply c d a
  have hb : (q2nPE_geomEquiv c d (b : G ⧸ c.S.torus)).1 = b • d.c₀ :=
    q2nPE_geomEquiv_apply c d b
  have hmain : panelRel M.toCoxeterSystem c.δ i d.c₀ ((a⁻¹ * b) • d.c₀) ↔
      panelRel M.toCoxeterSystem c.δ i (a • d.c₀) (b • d.c₀) := by
    constructor
    · intro h
      have h1 := (q2nPE_panelRel_smul c d a i d.c₀ ((a⁻¹ * b) • d.c₀)).mpr h
      rwa [q2nPE_geom_smul_conj c d a b] at h1
    · intro h
      have h1 := (q2nPE_panelRel_smul c d a⁻¹ i (a • d.c₀) (b • d.c₀)).mpr h
      simpa [mul_smul] using h1
  rw [← d.stab_panel i (a⁻¹ * b)]
  change panelRel M.toCoxeterSystem c.δ i d.c₀ ((a⁻¹ * b) • d.c₀) ↔
    panelRel M.toCoxeterSystem c.δ i
      ((q2nPE_geomEquiv c d (a : G ⧸ c.S.torus)).1)
      ((q2nPE_geomEquiv c d (b : G ⧸ c.S.torus)).1)
  rw [ha, hb]
  exact hmain

theorem PhanEConfig.bridge_of_geom (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (c : PhanEConfig K f M G) [MulAction G c.C] (d : c.Geom) : c.Bridge := by
  intro hconn hsc
  refine universal_of_geometryE hK hq c.S d.good ?_ ?_
  · exact connected_of_equiv (q2nPE_geomEquiv c d)
      (fun i x y => q2nPE_geom_adj_iff c d i x y) hconn
  · exact simplyTwoConnected_of_equiv (q2nPE_geomEquiv c d)
      (fun i x y => q2nPE_geom_adj_iff c d i x y) hsc

end Geom

end CFSG.ClassicalInvolution.Phan.PhanE
