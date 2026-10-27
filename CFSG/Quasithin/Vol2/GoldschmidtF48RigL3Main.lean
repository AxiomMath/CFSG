module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigL3Torus
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigL3Faith
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigXfer
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigCent

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.F45.PgGeom CFSG.Quasithin.H13.F431.F48L3
  CFSG.Quasithin.H13.F431.F48Rig

namespace F48L3

theorem exists_l3_data (f : ℕ) (hm : F431ModelFacts .PSL 3 f) (D : Type) [Group D]
    (hD : LieModel D .PSL 3 2 f) (A : LieAmalgamExt D) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = 2 ^ f)
      (Φ : projectiveSL 3 F →*
        (A.setting (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL)).ι.G0)
      (v₁ v₂ : Pt F ⊕ Ln F),
      XDatum (A.setting (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL)) Φ (Gr F) v₁ v₂ ∧
      ((v₁ = Sum.inl p0 ∧ v₂ = Sum.inr l0) ∨ (v₁ = Sum.inr l0 ∧ v₂ = Sum.inl p0)) ∧
      ∀ k : (A.setting (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL)).ι.G0,
        (∀ y, k * Φ y = Φ y * k) → k = 1 := by
  obtain ⟨F, hFf, hFfin, hFchar, E, hFcard, hcases⟩ := L3.l3Amalgam_borel hD A
  have hgen := f431Generation_psl3 f D hD A
  have hcen := (hm D hD).2
  have hb := Borel252.L3.borelData_L3 (F := F)
  have hcent := fun k hk => centralizer_inn_trivial A (hm D hD).1 (polyNumber .PSL)
    (three_le_polyNumber .PSL) hcen hgen E k hk
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨F, hFf, hFfin, hFchar, hFcard, _, _, _,
      F45.xdatum_of_inn A (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL) E hgen
        hcen h1 h2 hb.core₁ hb.core₂ (PgGeom.Gr F) (Sum.inl (PgGeom.p0 : PgGeom.Pt F))
        (Sum.inr (PgGeom.l0 : PgGeom.Ln F))
        (fun y => by
          rw [Sum.smul_inl, Sum.inl.injEq]
          exact F45.smul_p0_iff_normalizer y)
        (fun y => by
          rw [Sum.smul_inr, Sum.inr.injEq]
          exact F45.smul_l0_iff_normalizer y)
        (fun y z => by
          rw [Sum.smul_inl, Sum.smul_inr]
          exact Sum.inl_ne_inr)
        (fun y z => by
          rw [Sum.smul_inl, Sum.smul_inl]
          exact fun h => h)
        (fun y z => by
          rw [Sum.smul_inr, Sum.smul_inr]
          exact fun h => h)
        (F45.incGraph_adj_inl_inr.mpr PgGeom.inc_p0_l0),
      Or.inl ⟨rfl, rfl⟩, hcent⟩
  · exact ⟨F, hFf, hFfin, hFchar, hFcard, _, _, _,
      F45.xdatum_of_inn A (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL) E hgen
        hcen h1 h2 hb.core₂ hb.core₁ (PgGeom.Gr F) (Sum.inr (PgGeom.l0 : PgGeom.Ln F))
        (Sum.inl (PgGeom.p0 : PgGeom.Pt F))
        (fun y => by
          rw [Sum.smul_inr, Sum.inr.injEq]
          exact F45.smul_l0_iff_normalizer y)
        (fun y => by
          rw [Sum.smul_inl, Sum.inl.injEq]
          exact F45.smul_p0_iff_normalizer y)
        (fun y z => by
          rw [Sum.smul_inr, Sum.smul_inl]
          exact Sum.inr_ne_inl)
        (fun y z => by
          rw [Sum.smul_inr, Sum.smul_inr]
          exact fun h => h)
        (fun y z => by
          rw [Sum.smul_inl, Sum.smul_inl]
          exact fun h => h)
        (F45.incGraph_adj_inr_inl.mpr PgGeom.inc_p0_l0),
      Or.inr ⟨rfl, rfl⟩, hcent⟩

theorem l3_equiv {S : LieSetting} {F : Type} [Field F] [Finite F] [CharP F 2]
    {Φ : projectiveSL 3 F →* S.ι.G0} {v₁ v₂ : Pt F ⊕ Ln F} (D : XDatum S Φ (Gr F) v₁ v₂)
    (hlab : (v₁ = Sum.inl p0 ∧ v₂ = Sum.inr l0) ∨ (v₁ = Sum.inr l0 ∧ v₂ = Sum.inl p0)) :
    ∃ e : S.ι.Γ ≃ Pt F ⊕ Ln F, e S.ι.xv = v₁ ∧ e S.ι.lv = v₂ ∧
      (∀ y a, e (Φ y • a) = y • e a) ∧
      ∀ a b, S.ι.graph.Adj a b ↔ (Gr F).Adj (e a) (e b) := by
  rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have f₁ := modelBase_p0.flag three_p0 D.adj12
    have f₂ := modelBase_l0.flag three_l0 D.adj12.symm
    exact D.exists_equiv (cov_of_flags isGenPolygon_gr.connected f₁ f₂) f₁
  · have f₁ := modelBase_l0.flag three_l0 D.adj12
    have f₂ := modelBase_p0.flag three_p0 D.adj12.symm
    exact D.exists_equiv (cov_of_flags isGenPolygon_gr.connected f₁ f₂) f₁

end F48L3

theorem cartanFPF_psl3 (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .PSL 3 f) (D : Type) [Group D]
    (hD : LieModel D .PSL 3 2 f) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL)).CartanFPF := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, Φ, v₁, v₂, X, hlab, -⟩ := F48L3.exists_l3_data f hm D hD A
  have hq : 2 < Nat.card F := by
    rw [hFcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hb := Borel252.L3.borelData_L3 (F := F)
  obtain ⟨e, he1, he2, heq, hadj⟩ := F48L3.l3_equiv X hlab
  rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h, L₁, L₂, L, hL₁, hL₂, hne, hL, hp, h1, h2, h3, hc⟩ := exists_cartan_pt hq
    refine F48Rig.cartanFPF_of_model X e he1 heq hadj (Fin257.L3.V1 : Subgroup (projectiveSL 3 F))
      (by rw [F45.stabilizer_inl_p0]; exact hb.core₁) (Sum.inr L) (Sum.inr L₁) (Sum.inr L₂)
      ((ppAxioms.dist_inl_inr_eq_three _ _).mpr hL) (F45.incGraph_adj_inl_inr.mpr hL₁)
      (F45.incGraph_adj_inl_inr.mpr hL₂) (fun h => hne (Sum.inr.inj h)) h ?_ ?_ ?_ ?_ hc
    · rw [Sum.smul_inl, hp]
    · rw [Sum.smul_inr, h3]
    · rw [Sum.smul_inr, h1]
    · rw [Sum.smul_inr, h2]
  · obtain ⟨h, P₁, P₂, P, hP₁, hP₂, hne, hP, hl, h1, h2, h3, hc⟩ := exists_cartan_ln hq
    refine F48Rig.cartanFPF_of_model X e he1 heq hadj (Fin257.L3.V2 : Subgroup (projectiveSL 3 F))
      (by rw [F45.stabilizer_inr_l0]; exact hb.core₂) (Sum.inl P) (Sum.inl P₁) (Sum.inl P₂)
      ((ppAxioms.dist_inr_inl_eq_three _ _).mpr hP) (F45.incGraph_adj_inr_inl.mpr hP₁)
      (F45.incGraph_adj_inr_inl.mpr hP₂) (fun h => hne (Sum.inl.inj h)) h ?_ ?_ ?_ ?_ hc
    · rw [Sum.smul_inr, hl]
    · rw [Sum.smul_inl, h3]
    · rw [Sum.smul_inl, h1]
    · rw [Sum.smul_inl, h2]

theorem faithfulOnType_psl3 (f : ℕ) (hm : F431ModelFacts .PSL 3 f) (D : Type) [Group D]
    (hD : LieModel D .PSL 3 2 f) (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL)).FaithfulOnType s := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, Φ, v₁, v₂, X, hlab, hcent⟩ :=
    F48L3.exists_l3_data f hm D hD A
  obtain ⟨e, he1, he2, heq, -⟩ := F48L3.l3_equiv X hlab
  have hlabτ : Sum.isLeft v₁ ≠ Sum.isLeft v₂ := by
    rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  refine F48Rig.faithfulOnType_of_model X e he1 he2 heq Sum.isLeft (fun y w => ?_) hlabτ s hcent ?_
  · cases w <;> simp [Sum.smul_inl, Sum.smul_inr]
  · intro y hy
    rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases s
    · refine eq_one_of_smul_pt fun p => ?_
      have := hy (Sum.inl p) rfl
      rw [Sum.smul_inl] at this
      exact Sum.inl.inj this
    · refine eq_one_of_smul_ln fun L => ?_
      have := hy (Sum.inr L) rfl
      rw [Sum.smul_inr] at this
      exact Sum.inr.inj this
    · refine eq_one_of_smul_ln fun L => ?_
      have := hy (Sum.inr L) rfl
      rw [Sum.smul_inr] at this
      exact Sum.inr.inj this
    · refine eq_one_of_smul_pt fun p => ?_
      have := hy (Sum.inl p) rfl
      rw [Sum.smul_inl] at this
      exact Sum.inl.inj this

end CFSG.Quasithin.H13.F431
