module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Main
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSpTorus
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSpFaith
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigXfer

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.Open
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.SpGeom
  CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.F431.F48Rig

namespace F48Sp

theorem two_lt_card_of_ctx {D : Type} [Group D] {f : ℕ} (hf : 2 ≤ f)
    (hD : LieModel D .PSp 2 2 f) (hcen : Subgroup.center D = ⊥) (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) {F : Type} [Field F] [Finite F]
    [CharP F 2] (Φ : antiSp F →* ↥A.K) (hΦ : Function.Injective Φ)
    (hΦr : ∀ k : ↥A.K, k ∈ Φ.range ↔ (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range) :
    2 < Nat.card F := by
  obtain ⟨-, F₀, h₀f, h₀fin, h₀ch, hcard₀, ⟨e⟩⟩ := exists_equiv_antiSp hD
  have hK : ∀ d : D, (MulAut.conj d : MulAut D) ∈ A.K := fun d => hgen ⟨d, rfl⟩
  have hinj : Function.Injective ((MulAut.conj : D →* MulAut D).codRestrict A.K hK) := by
    intro a b hab
    have h1 : (MulAut.conj a : MulAut D) = MulAut.conj b := congrArg Subtype.val hab
    have hc : b⁻¹ * a ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 := congrArg (fun φ : MulAut D => φ y)
        (show (MulAut.conj (b⁻¹ * a) : MulAut D) = 1 by rw [map_mul, map_inv, h1, inv_mul_cancel])
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (b⁻¹ * a) = (b⁻¹ * a * y * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [h3]
        _ = (b⁻¹ * a) * y := by group
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have hrange : Φ.range = ((MulAut.conj : D →* MulAut D).codRestrict A.K hK).range := by
    ext k
    rw [hΦr]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, Subtype.ext hd⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, rfl⟩
  have h1 : Nat.card (antiSp F) = Nat.card (antiSp F₀) :=
    calc Nat.card (antiSp F) = Nat.card Φ.range :=
          Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv
      _ = Nat.card ((MulAut.conj : D →* MulAut D).codRestrict A.K hK).range := by rw [hrange]
      _ = Nat.card D := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      _ = Nat.card (antiSp F₀) := Nat.card_congr e.toEquiv
  by_contra hle
  have hF2 : Nat.card F = 2 := by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  rw [card_antiSp hF2, card_antiSp hcard₀] at h1
  have hq : 4 ≤ 2 ^ f := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : 256 ≤ (2 ^ f) ^ 4 := calc 256 = 4 ^ 4 := by norm_num
    _ ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : 16 ≤ (2 ^ f) ^ 2 := calc 16 = 4 ^ 2 := by norm_num
    _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
  have h5 : 256 * (15 * 255) ≤ (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) :=
    Nat.mul_le_mul h4 (Nat.mul_le_mul (by omega) (by omega))
  omega

theorem exists_sp_data (f : ℕ) (hm : F431ModelFacts .PSp 2 f) (D : Type) [Group D]
    (hD : LieModel D .PSp 2 2 f) (A : LieAmalgamExt D) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      (2 ≤ f → 2 < Nat.card F) ∧
      ∃ (Φ : antiSp F →*
        (A.setting (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp)).ι.G0)
      (v₁ v₂ : Pt F ⊕ Ln F) (Q : Subgroup (antiSp F)),
      XDatum (A.setting (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp)) Φ (Gr F) v₁ v₂ ∧
      pCoreOf 2 (MulAction.stabilizer (antiSp F) v₁) = Q ∧
      ((v₁ = Sum.inl pt0 ∧ v₂ = Sum.inr ln0 ∧ Q = radA2 F) ∨
        (v₁ = Sum.inr ln0 ∧ v₂ = Sum.inl pt0 ∧ Q = radA1 F)) ∧
      ∀ k : (A.setting (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp)).ι.G0,
        (∀ y, k * Φ y = Φ y * k) → k = 1 := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, ψ, k₀, R, i, hP, hDd, hN, hRi, hψ, hΦr⟩ :=
    F45.exists_f45Ctx hD A
  have hF := F45.spGeomFacts (F := F)
  have hcard : 2 ≤ f → 2 < Nat.card F := fun hf =>
    two_lt_card_of_ctx hf hD (hm D hD).2 A (f431Generation_psp f D hD A) Φ hP.inj hΦr
  have hst_p : MulAction.stabilizer (antiSp F) (Sum.inl (pt0 : Pt F) : Pt F ⊕ Ln F) =
      Subgroup.normalizer (radA2 F : Set (antiSp F)) := by
    ext y
    rw [MulAction.mem_stabilizer_iff]
    exact hF.stab_p y
  have hst_l : MulAction.stabilizer (antiSp F) (Sum.inr (ln0 : Ln F) : Pt F ⊕ Ln F) =
      Subgroup.normalizer (radA1 F : Set (antiSp F)) := by
    ext y
    rw [MulAction.mem_stabilizer_iff]
    exact hF.stab_l y
  have hcent : ∀ k : (A.setting (hm D hD).1 (polyNumber .PSp)
      (three_le_polyNumber .PSp)).ι.G0,
      (∀ y, k * phiG0 A (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp) Φ y =
        phiG0 A (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp) Φ y * k) → k = 1 := by
    intro k hk
    exact Subtype.ext (hP.cen k.1 fun x => mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val (hk x)))
  rcases hRi with ⟨hR, -⟩ | ⟨hR, -⟩
  · subst hR
    have X := F45.xdatum_of_ctx A (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp) Φ ψ k₀
      (Rrad F) hP hN hψ hΦr (Gr F) (Sum.inr (ln0 : Ln F)) (Sum.inl (pt0 : Pt F)) hF.stab_l
      hF.stab_p (fun y z => (hF.disj z y).symm) hF.noadj_l hF.noadj_p hF.adj.symm
    refine ⟨F, hFf, hFfin, hFchar, hcard, _, _, _, radA1 F, X, ?_, Or.inr ⟨rfl, rfl, rfl⟩, hcent⟩
    rw [hst_l]
    exact hDd.borel.core₁
  · subst hR
    have X := F45.xdatum_of_ctx A (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp) Φ ψ k₀
      ![radA2 F, radA1 F] hP hN hψ hΦr (Gr F) (Sum.inl (pt0 : Pt F)) (Sum.inr (ln0 : Ln F))
      hF.stab_p hF.stab_l hF.disj hF.noadj_p hF.noadj_l hF.adj
    refine ⟨F, hFf, hFfin, hFchar, hcard, _, _, _, radA2 F, X, ?_, Or.inl ⟨rfl, rfl, rfl⟩, hcent⟩
    rw [hst_p]
    exact hDd.borel.core₁


theorem sp_equiv {S : LieSetting} {F : Type} [Field F] [Finite F] [CharP F 2]
    {Φ : antiSp F →* S.ι.G0} {v₁ v₂ : Pt F ⊕ Ln F} (D : XDatum S Φ (Gr F) v₁ v₂)
    (hlab : (v₁ = Sum.inl pt0 ∧ v₂ = Sum.inr ln0) ∨ (v₁ = Sum.inr ln0 ∧ v₂ = Sum.inl pt0)) :
    ∃ e : S.ι.Γ ≃ Pt F ⊕ Ln F, e S.ι.xv = v₁ ∧ e S.ι.lv = v₂ ∧
      (∀ y a, e (Φ y • a) = y • e a) ∧
      ∀ a b, S.ι.graph.Adj a b ↔ (Gr F).Adj (e a) (e b) := by
  rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have f₁ := modelBase_pt0.flag three_pt0 D.adj12
    have f₂ := modelBase_ln0.flag three_ln0 D.adj12.symm
    exact D.exists_equiv (cov_of_flags isGenPolygon_gr.connected f₁ f₂) f₁
  · have f₁ := modelBase_ln0.flag three_ln0 D.adj12
    have f₂ := modelBase_pt0.flag three_pt0 D.adj12.symm
    exact D.exists_equiv (cov_of_flags isGenPolygon_gr.connected f₁ f₂) f₁

end F48Sp

theorem cartanFPF_psp (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .PSp 2 f) (D : Type) [Group D]
    (hD : LieModel D .PSp 2 2 f) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp)).CartanFPF := by
  obtain ⟨F, hFf, hFfin, hFchar, hq, Φ, v₁, v₂, Q, X, hQ, hlab, -⟩ :=
    F48Sp.exists_sp_data f hm D hD A
  have hq := hq hf
  obtain ⟨e, he1, he2, heq, hadj⟩ := F48Sp.sp_equiv X
    (hlab.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩))
  rcases hlab with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨h, L₁, L₂, P, hL₁, hL₂, hne, hP, hp, h1, h2, h3, hc⟩ := F48Sp.exists_cartan_pt hq
    refine F48Rig.cartanFPF_of_model X e he1 heq hadj (radA2 F) hQ (Sum.inl P) (Sum.inr L₁)
      (Sum.inr L₂) hP (incGraph_adj_inl_inr.mpr hL₁) (incGraph_adj_inl_inr.mpr hL₂)
      (fun h => hne (Sum.inr.inj h)) h ?_ ?_ ?_ ?_ hc
    · rw [Sum.smul_inl, hp]
    · rw [Sum.smul_inl, h3]
    · rw [Sum.smul_inr, h1]
    · rw [Sum.smul_inr, h2]
  · obtain ⟨h, P₁, P₂, L, hP₁, hP₂, hne, hL, hl, h1, h2, h3, hc⟩ := F48Sp.exists_cartan_ln hq
    refine F48Rig.cartanFPF_of_model X e he1 heq hadj (radA1 F) hQ (Sum.inr L) (Sum.inl P₁)
      (Sum.inl P₂) hL (incGraph_adj_inr_inl.mpr hP₁) (incGraph_adj_inr_inl.mpr hP₂)
      (fun h => hne (Sum.inl.inj h)) h ?_ ?_ ?_ ?_ hc
    · rw [Sum.smul_inr, hl]
    · rw [Sum.smul_inr, h3]
    · rw [Sum.smul_inl, h1]
    · rw [Sum.smul_inl, h2]

theorem faithfulOnType_psp (f : ℕ) (hm : F431ModelFacts .PSp 2 f) (D : Type) [Group D]
    (hD : LieModel D .PSp 2 2 f) (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .PSp) (three_le_polyNumber .PSp)).FaithfulOnType s := by
  obtain ⟨F, hFf, hFfin, hFchar, -, Φ, v₁, v₂, Q, X, -, hlab, hcent⟩ :=
    F48Sp.exists_sp_data f hm D hD A
  obtain ⟨e, he1, he2, heq, -⟩ := F48Sp.sp_equiv X
    (hlab.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩))
  have hlabτ : Sum.isLeft v₁ ≠ Sum.isLeft v₂ := by
    rcases hlab with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> simp
  refine F48Rig.faithfulOnType_of_model X e he1 he2 heq Sum.isLeft (fun y w => ?_) hlabτ s hcent ?_
  · cases w <;> simp [Sum.smul_inl, Sum.smul_inr]
  · intro y hy
    rcases hlab with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> cases s
    · refine F48Sp.eq_one_of_smul_pt fun p => ?_
      have := hy (Sum.inl p) rfl
      rw [Sum.smul_inl] at this
      exact Sum.inl.inj this
    · refine F48Sp.eq_one_of_smul_ln fun L => ?_
      have := hy (Sum.inr L) rfl
      rw [Sum.smul_inr] at this
      exact Sum.inr.inj this
    · refine F48Sp.eq_one_of_smul_ln fun L => ?_
      have := hy (Sum.inr L) rfl
      rw [Sum.smul_inr] at this
      exact Sum.inr.inj this
    · refine F48Sp.eq_one_of_smul_pt fun p => ?_
      have := hy (Sum.inl p) rfl
      rw [Sum.smul_inl] at this
      exact Sum.inl.inj this

end CFSG.Quasithin.H13.F431
