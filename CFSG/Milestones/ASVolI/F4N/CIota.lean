module

public import CFSG.Milestones.ASVolI.F4N.CModel
public import CFSG.Milestones.ASVolI.F45.TitsModel
public import CFSG.Milestones.ASVolI.F4N.A19

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType
  CFSG.Sporadic.Schreier.Tits CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F431
open scoped Pointwise

section Model


theorem burnsideF4nC_mem_titsH_iff (y : ↥titsD) :
    (y : Equiv.Perm (Fin 1755)) ∈ titsH ↔ y • (Sum.inl 0 : Vtx) = Sum.inl 0 := by
  obtain ⟨-, -, -, -, -, hPt, -, -, -⟩ := tits_geometry Certificates.certificate4190
  have h00 : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) := octGraph_adj_inl_inr.1 hPt.adj
  rw [← (xdatumD h00).stab1 y, smul_xv_iff', TitsGeo.mem_range_φ1_iff, toPermD_phiD]

theorem burnsideF4nC_mem_titsN_iff (y : ↥titsD) :
    (y : Equiv.Perm (Fin 1755)) ∈ titsN ↔ y • (Sum.inr 0 : Vtx) = Sum.inr 0 := by
  obtain ⟨-, -, -, -, -, hPt, -, -, -⟩ := tits_geometry Certificates.certificate4190
  have h00 : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) := octGraph_adj_inl_inr.1 hPt.adj
  rw [← (xdatumD h00).stab2 y, smul_lv_iff', TitsGeo.mem_range_φ2_iff, toPermD_phiD]

structure burnsideF4nC_ModelData {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z]
    (c : α.Completion Z) where
  Φ : ↥titsD →* c.G0
  e : c.Γ ≃ Vtx
  bij : Function.Bijective Φ
  exv : e c.xv = Sum.inl 0
  elv : e c.lv = Sum.inr 0
  equiv : ∀ (y : ↥titsD) (a : c.Γ), e (Φ y • a) = y • e a
  adj : ∀ a b, c.graph.Adj a b ↔ octGraph.Adj (e a) (e b)

theorem burnsideF4nC_model {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) : Nonempty (burnsideF4nC_ModelData (incl M₁ M₂)) := by
  haveI : Finite E := hyp.finite
  obtain ⟨θ, hθ1, hθ2⟩ := burnsideF45_tits_theta hyp
  obtain ⟨-, -, -, -, -, hPt, -, hLn, hpoly⟩ := tits_geometry Certificates.certificate4190
  have hsup : M₁ ⊔ M₂ = (⊤ : Subgroup E) := hyp.gen
  let θ' : ↥titsD ≃* ↥(⊤ : Subgroup E) :=
    (MulEquiv.subgroupCongr titsH_sup_N.symm).trans (θ.symm.trans (MulEquiv.subgroupCongr hsup))
  have hst1 : ∀ y : ↥titsD, ((θ' y : ↥(⊤ : Subgroup E)) : E) ∈ M₁ ↔
      (y : Equiv.Perm (Fin 1755)) ∈ titsH := by
    intro y
    have := hθ1 (θ.symm (MulEquiv.subgroupCongr titsH_sup_N.symm y))
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hst2 : ∀ y : ↥titsD, ((θ' y : ↥(⊤ : Subgroup E)) : E) ∈ M₂ ↔
      (y : Equiv.Perm (Fin 1755)) ∈ titsN := by
    intro y
    have := hθ2 (θ.symm (MulEquiv.subgroupCongr titsH_sup_N.symm y))
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hm : 3 ≤ GLKind.Tits.m := burnsideF45_three_le_m _
  have D := burnsideF45_xdatum_of_model hyp Nat.prime_two hm θ' (ΓM := octGraph)
    (v₁ := (Sum.inl 0 : Vtx)) (v₂ := Sum.inr 0)
    (fun y => (hst1 y).trans (burnsideF4nC_mem_titsH_iff y))
    (fun y => (hst2 y).trans (burnsideF4nC_mem_titsN_iff y))
    (fun y z => by rw [dsmul_inl, dsmul_inr]; exact Sum.inl_ne_inr)
    (fun y z => by rw [dsmul_inl, dsmul_inl]; exact fun h => h)
    (fun y z => by rw [dsmul_inr, dsmul_inr]; exact fun h => h) hPt.adj
  have f₁ : ∀ b, octGraph.Adj (Sum.inl 0) b →
      ∃ y : ↥titsD, y • (Sum.inl 0 : Vtx) = Sum.inl 0 ∧ y • (Sum.inr 0 : Vtx) = b :=
    fun b hb => (hPt.trans b hb).imp fun k hk => ⟨hk.1, hk.2.2⟩
  have f₂ : ∀ b, octGraph.Adj (Sum.inr 0) b →
      ∃ y : ↥titsD, y • (Sum.inr 0 : Vtx) = Sum.inr 0 ∧ y • (Sum.inl 0 : Vtx) = b :=
    fun b hb => hLn.flag hPt.adj.symm hb
  obtain ⟨e, he1, he2, heq, hadjE⟩ := D.exists_equiv (F45.cov_of_flags hpoly.connected f₁ f₂) f₁
  have hsurj : Function.Surjective (burnsideF45_Phi hyp θ') := by
    intro g
    have hg : g ∈ (burnsideF45_setting hyp Nat.prime_two hm).N := by
      show toE (incl M₁ M₂) g ∈ (⊤ : Subgroup E)
      exact Subgroup.mem_top _
    rw [D.N_eq] at hg
    exact hg
  exact ⟨⟨burnsideF45_Phi hyp θ', e, ⟨D.inj, hsurj⟩, he1, he2, heq, hadjE⟩⟩

section Generic

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] {c : α.Completion Z}

theorem burnsideF4nC_md_smul_eq_iff (Md : burnsideF4nC_ModelData c) (y : ↥titsD) (a b : c.Γ) :
    Md.Φ y • a = b ↔ y • Md.e a = Md.e b := by
  rw [← Md.equiv, Md.e.injective.eq_iff]

theorem burnsideF4nC_md_stv_xv (Md : burnsideF4nC_ModelData c) (y : ↥titsD) :
    Md.Φ y ∈ stv c c.xv ↔ (y : Equiv.Perm (Fin 1755)) ∈ titsH := by
  rw [MulAction.mem_stabilizer_iff, burnsideF4nC_md_smul_eq_iff, Md.exv,
    burnsideF4nC_mem_titsH_iff]

theorem burnsideF4nC_md_stv_lv (Md : burnsideF4nC_ModelData c) (y : ↥titsD) :
    Md.Φ y ∈ stv c c.lv ↔ (y : Equiv.Perm (Fin 1755)) ∈ titsN := by
  rw [MulAction.mem_stabilizer_iff, burnsideF4nC_md_smul_eq_iff, Md.elv,
    burnsideF4nC_mem_titsN_iff]

theorem burnsideF4nC_md_sq (Md : burnsideF4nC_ModelData c) (y : ↥titsD) :
    Md.Φ y * Md.Φ y = 1 ↔ (y : Equiv.Perm (Fin 1755)) * y = 1 := by
  rw [← map_mul, ← map_one Md.Φ, Md.bij.1.eq_iff, Subtype.ext_iff]
  rfl

@[expose] def burnsideF4nC_md_iso (Md : burnsideF4nC_ModelData c) : c.graph ≃g octGraph :=
  ⟨Md.e, fun {a b} => (Md.adj a b).symm⟩

theorem burnsideF4nC_md_dist (Md : burnsideF4nC_ModelData c) (a b : c.Γ) :
    octGraph.dist (Md.e a) (Md.e b) = c.graph.dist a b :=
  F45.iso_dist (burnsideF4nC_md_iso Md) a b

theorem burnsideF4nC_smul_inr_iff (y : ↥titsD) (v w : Fin 2925) :
    y • (Sum.inr v : Vtx) = Sum.inr w ↔ (y : Equiv.Perm (Fin 1755)) • titsLine v = titsLine w := by
  rw [dsmul_inr, Sum.inr.injEq]
  constructor
  · intro h
    rw [← h, titsLine_lineHom]
    rfl
  · intro h
    apply titsLine_injective
    rw [titsLine_lineHom]
    exact h

theorem burnsideF4nC_md_nbr_xv (Md : burnsideF4nC_ModelData c) {cc : c.Γ}
    (hcc : cc ∈ CosetGeom.nbrs c.xv) :
    ∃ v : Fin 2925, Md.e cc = Sum.inr v ∧ (0 : Fin 1755) ∈ titsLine v := by
  have h := (Md.adj c.xv cc).1 hcc
  rw [Md.exv] at h
  rcases hcv : Md.e cc with p | v
  · rw [hcv] at h
    exact h.elim
  · rw [hcv] at h
    exact ⟨v, rfl, octGraph_adj_inl_inr.1 h⟩

theorem burnsideF4nC_md_nbr_lv (Md : burnsideF4nC_ModelData c) {yy : c.Γ}
    (hyy : yy ∈ CosetGeom.nbrs c.lv) :
    ∃ q : Fin 1755, Md.e yy = Sum.inl q ∧ q ∈ titsLine 0 := by
  have h := (Md.adj c.lv yy).1 hyy
  rw [Md.elv] at h
  rcases hcv : Md.e yy with q | v
  · rw [hcv] at h
    exact ⟨q, rfl, octGraph_adj_inr_inl.1 h⟩
  · rw [hcv] at h
    exact h.elim

theorem burnsideF4nC_md_far_iff (Md : burnsideF4nC_ModelData c) (y : ↥titsD) :
    (∃ b, c.graph.dist c.xv b = 8 ∧ Md.Φ y • b = b) ↔
      ∃ p : Fin 1755, octGraph.dist (Sum.inl 0) (Sum.inl p) = 8 ∧
        (y : Equiv.Perm (Fin 1755)) p = p := by
  constructor
  · rintro ⟨b, hb, hyb⟩
    have hbt : CosetGeom.vtype b = false := by
      have h := (GPath.dist_even_iff (connected_graph c)
        (fun _ _ h => CosetGeom.vtype_ne_of_adj h) c.xv b).2 (by rw [hb]; decide)
      exact h.symm
    obtain ⟨g, hg⟩ := exists_smul_of_vtype_false (c := c) c.xv b rfl hbt
    obtain ⟨z, rfl⟩ := Md.bij.2 g
    have heb : Md.e b = Sum.inl ((z : Equiv.Perm (Fin 1755)) 0) := by
      rw [← hg, Md.equiv, Md.exv, dsmul_inl]
    refine ⟨(z : Equiv.Perm (Fin 1755)) 0, ?_, ?_⟩
    · rw [← heb, ← Md.exv, burnsideF4nC_md_dist]
      exact hb
    · have := (burnsideF4nC_md_smul_eq_iff Md y b b).1 hyb
      rw [heb, dsmul_inl] at this
      exact Sum.inl_injective this
  · rintro ⟨p, hp, hyp⟩
    refine ⟨Md.e.symm (Sum.inl p), ?_, ?_⟩
    · rw [← burnsideF4nC_md_dist, Md.exv, Equiv.apply_symm_apply]
      exact hp
    · rw [burnsideF4nC_md_smul_eq_iff, Equiv.apply_symm_apply, dsmul_inl, hyp]

theorem burnsideF4nC_md_ncard (Md : burnsideF4nC_ModelData c) (A : Set c.G0)
    (X : Set (Equiv.Perm (Fin 1755))) (hX : X ⊆ titsD)
    (hA : ∀ y : ↥titsD, Md.Φ y ∈ A ↔ (y : Equiv.Perm (Fin 1755)) ∈ X) : A.ncard = X.ncard := by
  have h1 : A = Md.Φ '' {y : ↥titsD | (y : Equiv.Perm (Fin 1755)) ∈ X} := by
    ext a
    constructor
    · intro ha
      obtain ⟨y, rfl⟩ := Md.bij.2 a
      exact ⟨y, (hA y).1 ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hA y).2 hy
  have h2 : (Subtype.val : ↥titsD → Equiv.Perm (Fin 1755)) ''
      {y : ↥titsD | (y : Equiv.Perm (Fin 1755)) ∈ X} = X := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hg
      exact ⟨⟨g, hX hg⟩, hg, rfl⟩
  rw [h1, Set.ncard_image_of_injective _ Md.bij.1]
  conv_rhs => rw [← h2]
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm

end Generic

section Sets

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Z : Type} [Group Z]

theorem burnsideF4nC_geod_iff (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {Gp : Subgroup E}
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) (c : Cpl M₁ M₂ Z) (hc : c.IsFaithful)
    (hs : c.IsSmall GLKind.Tits.m) {s : c.G0} (hsx : s ∈ stv c c.xv) (hss : s * s = 1)
    (hs1 : s ≠ 1) :
    (∃ q : GPath c.graph GLKind.Tits.m, q 0 = c.xv ∧ q.IsGeodesic ∧
        (q.stabPath : Subgroup c.G0) = Subgroup.zpowers s) ↔
      ∃ b, c.graph.dist c.xv b = 8 ∧ s • b = b := by
  constructor
  · rintro ⟨q, hq0, hqg, hqs⟩
    refine ⟨q GLKind.Tits.m, ?_, ?_⟩
    · have h : c.graph.dist (q 0) (q GLKind.Tits.m) = GLKind.Tits.m := hqg
      rw [hq0] at h
      exact h
    · have hsq : s ∈ (q.stabPath : Subgroup c.G0) := by
        rw [hqs]
        exact Subgroup.mem_zpowers s
      exact GPath.mem_stabPath_iff.mp hsq _ le_rfl
  · rintro ⟨b, hb, hsb⟩
    obtain ⟨r, hr, hrb⟩ := Facts46.exists_geod_path (c := c) (m := GLKind.Tits.m) hb
    exact burnsideF4nA_tits_geod h46 h45 ChF.nativeChartCompatibility hyp c hc hs hr
      (Subgroup.mem_inf.mpr ⟨hsx, MulAction.mem_stabilizer_iff.mpr (by rw [hrb]; exact hsb)⟩)
      hss hs1

@[expose] def burnsideF4nC_N1bar (v : Fin 2925) : Set (Equiv.Perm (Fin 1755)) :=
  {g | g ∈ titsH ∧ g * g = 1 ∧ g • titsLine 0 = titsLine v ∧ g • titsLine v = titsLine 0 ∧
    ∃ p : Fin 1755, octGraph.dist (Sum.inl 0) (Sum.inl p) = 8 ∧ g p = p}

@[expose] def burnsideF4nC_N2bar (q : Fin 1755) : Set (Equiv.Perm (Fin 1755)) :=
  {g | g ∈ titsN ∧ g * g = 1 ∧ g 0 = q ∧ g q = 0}

theorem burnsideF4nC_md_N1_iff (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {Gp : Subgroup E}
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) (c : Cpl M₁ M₂ Z) (hc : c.IsFaithful)
    (hs : c.IsSmall GLKind.Tits.m) (Md : burnsideF4nC_ModelData c) {cc : c.Γ} {v : Fin 2925}
    (hcv : Md.e cc = Sum.inr v) (hccl : cc ≠ c.lv) (yy : c.Γ) (y : ↥titsD) :
    Md.Φ y ∈ N1set c GLKind.Tits cc yy ↔ (y : Equiv.Perm (Fin 1755)) ∈ burnsideF4nC_N1bar v := by
  have hlc : Md.Φ y • c.lv = cc ↔ (y : Equiv.Perm (Fin 1755)) • titsLine 0 = titsLine v := by
    rw [burnsideF4nC_md_smul_eq_iff, Md.elv, hcv, burnsideF4nC_smul_inr_iff]
  have hcl : Md.Φ y • cc = c.lv ↔ (y : Equiv.Perm (Fin 1755)) • titsLine v = titsLine 0 := by
    rw [burnsideF4nC_md_smul_eq_iff, hcv, Md.elv, burnsideF4nC_smul_inr_iff]
  have hne : Md.Φ y • c.lv = cc → Md.Φ y ≠ 1 := fun h h1 => by
    rw [h1, one_smul] at h
    exact hccl h.symm
  unfold N1set
  rw [if_pos rfl]
  constructor
  · rintro ⟨hsx, ⟨hss, -, h1, h2⟩, hq⟩
    have hgeo := (burnsideF4nC_geod_iff h45 h46 hyp c hc hs hsx hss (hne h1)).1 hq
    exact ⟨(burnsideF4nC_md_stv_xv Md y).1 hsx, (burnsideF4nC_md_sq Md y).1 hss, hlc.1 h1,
      hcl.1 h2, (burnsideF4nC_md_far_iff Md y).1 hgeo⟩
  · rintro ⟨hH, hsq, h1, h2, hfar⟩
    have hsx := (burnsideF4nC_md_stv_xv Md y).2 hH
    have hss := (burnsideF4nC_md_sq Md y).2 hsq
    have h1' := hlc.2 h1
    refine ⟨hsx, ⟨hss, Ne.symm hccl, h1', hcl.2 h2⟩, ?_⟩
    exact (burnsideF4nC_geod_iff h45 h46 hyp c hc hs hsx hss (hne h1')).2
      ((burnsideF4nC_md_far_iff Md y).2 hfar)

theorem burnsideF4nC_md_N2_iff {α : RankTwoAmalgam.{0}} {c : α.Completion Z}
    (Md : burnsideF4nC_ModelData c) {yy : c.Γ} {q : Fin 1755} (hyq : Md.e yy = Sum.inl q)
    (hyx : yy ≠ c.xv) (cc y' : c.Γ) (y : ↥titsD) :
    Md.Φ y ∈ N2set c GLKind.Tits cc yy y' ↔ (y : Equiv.Perm (Fin 1755)) ∈ burnsideF4nC_N2bar q := by
  have h1 : Md.Φ y • c.xv = yy ↔ (y : Equiv.Perm (Fin 1755)) 0 = q := by
    rw [burnsideF4nC_md_smul_eq_iff, Md.exv, hyq, dsmul_inl, Sum.inl.injEq]
  have h2 : Md.Φ y • yy = c.xv ↔ (y : Equiv.Perm (Fin 1755)) q = 0 := by
    rw [burnsideF4nC_md_smul_eq_iff, Md.exv, hyq, dsmul_inl, Sum.inl.injEq]
  unfold N2set
  rw [if_pos rfl]
  show (Md.Φ y ∈ stv c c.lv ∧ HasCycle c (Md.Φ y) c.xv yy) ↔ _
  unfold HasCycle
  rw [burnsideF4nC_md_stv_lv, burnsideF4nC_md_sq, h1, h2]
  constructor
  · rintro ⟨hN, hsq, -, h1, h2⟩
    exact ⟨hN, hsq, h1, h2⟩
  · rintro ⟨hN, hsq, h1, h2⟩
    exact ⟨hN, hsq, Ne.symm hyx, h1, h2⟩

theorem burnsideF4nC_md_card_N1 (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {Gp : Subgroup E}
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) (c : Cpl M₁ M₂ Z) (hc : c.IsFaithful)
    (hs : c.IsSmall GLKind.Tits.m) (Md : burnsideF4nC_ModelData c) {cc : c.Γ}
    (hcc : cc ∈ CosetGeom.nbrs c.xv) (hccl : cc ≠ c.lv) (yy : c.Γ) :
    (N1set c GLKind.Tits cc yy).ncard = 2 ^ 4 := by
  obtain ⟨v, hcv, hv0⟩ := burnsideF4nC_md_nbr_xv Md hcc
  have hv : v ≠ 0 := by
    rintro rfl
    apply hccl
    apply Md.e.injective
    rw [hcv, Md.elv]
  rw [burnsideF4nC_md_ncard Md _ (burnsideF4nC_N1bar v) (fun g hg => titsH_le_titsD hg.1)
    (burnsideF4nC_md_N1_iff h45 h46 hyp c hc hs Md hcv hccl yy)]
  exact burnsideF4nC_card_N1 v hv0 hv

theorem burnsideF4nC_md_card_N2 {α : RankTwoAmalgam.{0}} {c : α.Completion Z}
    (Md : burnsideF4nC_ModelData c) {yy : c.Γ} (hyy : yy ∈ CosetGeom.nbrs c.lv)
    (hyx : yy ≠ c.xv) (cc y' : c.Γ) :
    (N2set c GLKind.Tits cc yy y').ncard = 2 ^ 6 := by
  obtain ⟨q, hyq, hq0⟩ := burnsideF4nC_md_nbr_lv Md hyy
  have hq : q ≠ 0 := by
    rintro rfl
    apply hyx
    apply Md.e.injective
    rw [hyq, Md.exv]
  rw [burnsideF4nC_md_ncard Md _ (burnsideF4nC_N2bar q) (fun g hg => titsN_le_titsD hg.1)
    (burnsideF4nC_md_N2_iff Md hyq hyx cc y')]
  exact burnsideF4nC_card_N2 q hq0 hq

theorem burnsideF4nC_md_J_le {α : RankTwoAmalgam.{0}} {c : α.Completion Z}
    (Md : burnsideF4nC_ModelData c) :
    (titsJ.subgroupOf titsD).map Md.Φ ≤ pCoreOf 2 (stv c c.xv) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJn, -, -, -, -⟩ :=
    AT_Tits_local_stabilizers_and_normal_cores
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact (burnsideF4nC_md_stv_xv Md w).2 (titsJ_le_titsH hw)
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hw, hwn⟩ := hn
    obtain ⟨z, hz⟩ := Md.bij.2 (g : c.G0)
    have hzH : (z : Equiv.Perm (Fin 1755)) ∈ titsH := (burnsideF4nC_md_stv_xv Md z).1 (hz ▸ g.2)
    have hwJ : (w : Equiv.Perm (Fin 1755)) ∈ titsJ := hw
    have hc := hJn.conj_mem ⟨(w : Equiv.Perm (Fin 1755)), titsJ_le_titsH hwJ⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hwJ) ⟨(z : Equiv.Perm (Fin 1755)), hzH⟩
    rw [Subgroup.mem_subgroupOf] at hc
    refine ⟨z * w * z⁻¹, hc, ?_⟩
    rw [map_mul, map_mul, map_inv, hz, hwn]
    rfl
  · have hJ : IsPGroup 2 titsJ := IsPGroup.of_card (n := 9) (by rw [titsQJ_facts.2.2.2]; norm_num)
    exact (hJ.comap_of_injective titsD.subtype titsD.subtype_injective).map Md.Φ

theorem burnsideF4nC_md_K_le {α : RankTwoAmalgam.{0}} {c : α.Completion Z}
    (Md : burnsideF4nC_ModelData c) :
    (titsK.subgroupOf titsD).map Md.Φ ≤ pCoreOf 2 (stv c c.lv) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hKn, -, -, -⟩ :=
    AT_Tits_local_stabilizers_and_normal_cores
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact (burnsideF4nC_md_stv_lv Md w).2 (titsK_le_titsN hw)
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hw, hwn⟩ := hn
    obtain ⟨z, hz⟩ := Md.bij.2 (g : c.G0)
    have hzN : (z : Equiv.Perm (Fin 1755)) ∈ titsN := (burnsideF4nC_md_stv_lv Md z).1 (hz ▸ g.2)
    have hwK : (w : Equiv.Perm (Fin 1755)) ∈ titsK := hw
    have hc := hKn.conj_mem ⟨(w : Equiv.Perm (Fin 1755)), titsK_le_titsN hwK⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hwK) ⟨(z : Equiv.Perm (Fin 1755)), hzN⟩
    rw [Subgroup.mem_subgroupOf] at hc
    refine ⟨z * w * z⁻¹, hc, ?_⟩
    rw [map_mul, map_mul, map_inv, hz, hwn]
    rfl
  · have hK : IsPGroup 2 titsK := IsPGroup.of_card (n := 10) (by rw [titsQK_facts.2.2.2]; norm_num)
    exact (hK.comap_of_injective titsD.subtype titsD.subtype_injective).map Md.Φ

theorem burnsideF4nC_md_trans (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {Gp : Subgroup E}
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) (c : Cpl M₁ M₂ Z) (hc : c.IsFaithful)
    (hs : c.IsSmall GLKind.Tits.m) (Md : burnsideF4nC_ModelData c) {cc : c.Γ}
    (hcc : cc ∈ CosetGeom.nbrs c.xv) (hccl : cc ≠ c.lv) (yy : c.Γ) :
    ∀ s ∈ N1set c GLKind.Tits cc yy, ∀ s' ∈ N1set c GLKind.Tits cc yy,
      ∃ g ∈ pCoreOf 2 (stv c c.xv) ⊓ pCoreOf 2 (stv c c.lv), g * s * g⁻¹ = s' := by
  obtain ⟨v, hcv, hv0⟩ := burnsideF4nC_md_nbr_xv Md hcc
  have hv : v ≠ 0 := by
    rintro rfl
    apply hccl
    apply Md.e.injective
    rw [hcv, Md.elv]
  intro s hsN s' hs'N
  obtain ⟨h, rfl⟩ := Md.bij.2 s
  obtain ⟨h', rfl⟩ := Md.bij.2 s'
  have hh := (burnsideF4nC_md_N1_iff h45 h46 hyp c hc hs Md hcv hccl yy h).1 hsN
  have hh' := (burnsideF4nC_md_N1_iff h45 h46 hyp c hc hs Md hcv hccl yy h').1 hs'N
  obtain ⟨u, hu, hconj⟩ := burnsideF4nC_trans_N1 v hv0 hv hh hh'
  have huD : u ∈ titsD := titsH_le_titsD (titsJ_le_titsH hu.1)
  refine ⟨Md.Φ ⟨u, huD⟩, ⟨burnsideF4nC_md_J_le Md ⟨⟨u, huD⟩, hu.1, rfl⟩,
    burnsideF4nC_md_K_le Md ⟨⟨u, huD⟩, hu.2, rfl⟩⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hconj

end Sets

section IotaQ

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF4nC_iota_Qu (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) (u : (incl M₁ M₂).Γ) :
    Qu 2 ⊤ (incl M₁ M₂) u = pCoreOf 2 (stv (incl M₁ M₂) u) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hm : 3 ≤ GLKind.Tits.m := burnsideF45_three_le_m _
  have hN : (burnsideF45_setting hyp hp hm).N = ⊤ := by
    show (⊤ : Subgroup E).comap (toE (incl M₁ M₂)) = ⊤
    rw [Subgroup.comap_top]
  refine (burnsideF45_Qu_eq_Qbar hyp hp hm u).trans ?_
  show pCoreOf 2 ((burnsideF45_setting hyp hp hm).N ⊓ stv (incl M₁ M₂) u) = _
  rw [hN, top_inf_eq]

end IotaQ

end Model

end CFSG.ASVolI
