module

public import CFSG.Monster.B.TwoA.Unitary.CliqueKernel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem exists_mulEquiv_of_forall_iff {α β G : Type*} [Group G] [MulAction G β]
    [FaithfulSMul G β] (H : Subgroup (Equiv.Perm α)) (e : α ≃ β)
    (h : ∀ σ : Equiv.Perm α, σ ∈ H ↔ ∃ g : G, ∀ a, e (σ a) = g • e a) :
    ∃ θ : H ≃* G, ∀ (σ : H) (a : α), e ((σ : Equiv.Perm α) a) = θ σ • e a := by
  choose f hf using fun σ : H => (h σ).1 σ.2
  have key : ∀ g g' : G, (∀ a, g • e a = g' • e a) → g = g' := fun g g' hg =>
    eq_of_smul_eq_smul fun b => by
      obtain ⟨a, rfl⟩ := e.surjective b
      exact hg a
  let θ : H →* G :=
    { toFun := f
      map_one' := key _ _ fun a => by
        rw [← hf, one_smul]
        rfl
      map_mul' := fun σ τ => key _ _ fun a => by
        rw [← hf, mul_smul, ← hf, ← hf]
        rfl }
  have hinj : Function.Injective θ := fun σ τ hστ => Subtype.ext (Equiv.ext fun a =>
    e.injective (by rw [hf, hf]; exact congrArg (· • e a) hστ))
  have hsurj : Function.Surjective θ := fun g => by
    let σ : Equiv.Perm α := (e.trans (MulAction.toPerm g)).trans e.symm
    have hσ : σ ∈ H := (h σ).2 ⟨g, fun a => by simp [σ]⟩
    refine ⟨⟨σ, hσ⟩, key _ _ fun a => ?_⟩
    change f ⟨σ, hσ⟩ • e a = g • e a
    rw [← hf]
    simp [σ]
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, hsurj⟩, fun σ a => hf σ a⟩

theorem natCard_SL3 : Nat.card SL(3, F4) = 60480 := by
  rw [Matrix.card_SL_field, F4.card, Fin.prod_univ_three]
  rfl

theorem rootsOfUnity_three_eq_top : rootsOfUnity 3 F4 = ⊤ := by
  ext u
  simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
  have h := pow_card_eq_one (G := F4ˣ) (x := u)
  rwa [Fintype.card_units, F4.card] at h

theorem natCard_center_SL3 : Nat.card (Subgroup.center SL(3, F4)) = 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  have e : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  rw [e, rootsOfUnity_three_eq_top, Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_units, F4.card]

theorem natCard_PSL3 : Nat.card PSL(3, F4) = 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3, F4))
  rw [natCard_SL3, natCard_center_SL3] at h
  change Nat.card (SL(3, F4) ⧸ Subgroup.center SL(3, F4)) = 20160
  omega

theorem psl_smul_mk (A : SL(3, F4)) {w : Fin 3 → F4} (hw : w ≠ 0) :
    (A : PSL(3, F4)) • Projectivization.mk F4 w hw =
      Projectivization.mk F4 ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ w)
        (by rw [← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def]
            exact (smul_ne_zero_iff_ne A).mpr hw) := by
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk]
  congr 1

theorem hypA_rep_ne_zero {p : IsoPt} (hp : p ∈ planePts W0) : hypA p.1.rep ≠ 0 := fun h =>
  rep_ne_zero p (by rw [eq_lift3_of_mem_W0 hp, h]; exact ofHyp_zero)

theorem lift3_rep_ne_zero (q : ℙ F4 (Fin 3 → F4)) : lift3 q.rep ≠ 0 := fun h =>
  q.rep_nonzero (lift3_eq_zero_iff.1 h)

theorem ne_zero_of_lift3 {w : Fin 3 → F4} (hw : lift3 w ≠ 0) : w ≠ 0 := fun h =>
  hw (by rw [h]; exact ofHyp_zero)

@[expose] noncomputable def e0 : planePts W0 ≃ ℙ F4 (Fin 3 → F4) where
  toFun p := Projectivization.mk F4 (hypA p.1.1.rep) (hypA_rep_ne_zero p.2)
  invFun q := ⟨pt (lift3 q.rep) (lift3_rep_ne_zero q) (herm_lift3 _ _),
    (pt_mem_planePts _ _).2 (lift3_mem_W0 _)⟩
  left_inv p := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F4 (hypA p.1.1.rep)
      (hypA_rep_ne_zero p.2)
    refine Subtype.ext ?_
    dsimp only
    conv_rhs => rw [← pt_rep p.1]
    refine (pt_eq_pt_iff _ _ _ _).2 ⟨(a : F4), ?_⟩
    rw [← ha, Units.smul_def, ← lift3_smul, ← eq_lift3_of_mem_W0 p.2]
  right_inv q := by
    dsimp only
    obtain ⟨a, ha⟩ := rep_pt (lift3_rep_ne_zero q) (herm_lift3 q.rep q.rep)
    conv_rhs => rw [← Projectivization.mk_rep q]
    refine (Projectivization.mk_eq_mk_iff F4 _ _ _ _).2 ⟨a, ?_⟩
    rw [← ha, Units.smul_def, Units.smul_def, lift3_smul, hypA_ofHyp]

theorem e0_eq_mk (p : planePts W0) (w : Fin 3 → F4) (hw : lift3 w ≠ 0)
    (h : p.1 = pt (lift3 w) hw (herm_lift3 w w)) :
    e0 p = Projectivization.mk F4 w (ne_zero_of_lift3 hw) := by
  change Projectivization.mk F4 (hypA p.1.1.rep) _ = _
  obtain ⟨a, ha⟩ := rep_pt hw (herm_lift3 w w)
  refine (Projectivization.mk_eq_mk_iff F4 _ _ _ _).2 ⟨a, ?_⟩
  rw [h, ← ha, Units.smul_def, Units.smul_def, lift3_smul, hypA_ofHyp]

@[expose] noncomputable def blockSL (k : SU frobeniusF4 6)
    (h : (hyp ((k : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).toBlocks₂₁ = 0) : SL(3, F4) :=
  ⟨(hyp ((k : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).toBlocks₁₁,
    det_blockA_eq_one (isIsometry_of_mem k) (det_of_mem k) h⟩

theorem e0_smul (k : SU frobeniusF4 6)
    (h : (hyp ((k : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).toBlocks₂₁ = 0)
    (q : planePts W0) (hq : k • q.1 ∈ planePts W0) :
    e0 ⟨k • q.1, hq⟩ = (blockSL k h : PSL(3, F4)) • e0 q := by
  obtain ⟨w, hw, hqw⟩ := planePts_W0_eq q.1 q.2
  set M := ((k : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hAw : lift3 ((hyp M).toBlocks₁₁ *ᵥ w) ≠ 0 := by
    rw [← mulVec_lift3_of_mapsTo h]
    exact (smul_ne_zero_iff_ne k).mpr hw
  have hk : k • q.1 = pt (lift3 ((hyp M).toBlocks₁₁ *ᵥ w)) hAw (herm_lift3 _ _) := by
    rw [hqw, smul_pt]
    congr 1
    rw [smul_def, mulVec_lift3_of_mapsTo h]
  rw [e0_eq_mk _ _ hAw hk, e0_eq_mk q w hw hqw, psl_smul_mk]
  rfl

theorem smulSub_W0_of_toBlocks₂₁ {k : SU frobeniusF4 6}
    (h : (hyp ((k : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).toBlocks₂₁ = 0) :
    smulSub k W0 = W0 := by
  have hle : smulSub k W0 ≤ W0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mapsTo_W0_iff _).2 h v hv
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_smulSub])

theorem mk_mem_stabL_of_smulSub {h : SU frobeniusF4 6} {W : Submodule F4 V}
    (hW : smulSub h W = W) : (h : ProjSU) ∈ stabL W := by
  intro p
  rw [projAct_mk]
  conv_lhs => rw [← hW]
  exact smul_mem_planePts h W p

theorem map_bar_mul (M N : Matrix (Fin 3) (Fin 3) F4) :
    (M * N).map bar = M.map bar * N.map bar := by
  have := Matrix.map_mul (L := M) (M := N) (f := barHom)
  rw [coe_barHom] at this
  exact this

theorem map_bar_map_bar (M : Matrix (Fin 3) (Fin 3) F4) : (M.map bar).map bar = M := by
  ext i j
  exact bar_bar _

theorem coe_inv_mul_SL (A : SL(3, F4)) :
    ((A⁻¹ : SL(3, F4)) : Matrix (Fin 3) (Fin 3) F4) * (A : Matrix (Fin 3) (Fin 3) F4) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] def leviMat (A : SL(3, F4)) : Matrix (Fin 6) (Fin 6) F4 :=
  ofHypMat (fromBlocks (A : Matrix (Fin 3) (Fin 3) F4) 0 0
    ((((A⁻¹ : SL(3, F4)) : Matrix (Fin 3) (Fin 3) F4).map bar)ᵀ))

theorem hyp_leviMat (A : SL(3, F4)) :
    hyp (leviMat A) = fromBlocks (A : Matrix (Fin 3) (Fin 3) F4) 0 0
      ((((A⁻¹ : SL(3, F4)) : Matrix (Fin 3) (Fin 3) F4).map bar)ᵀ) :=
  hyp_ofHypMat _

theorem det_leviMat (A : SL(3, F4)) : (leviMat A).det = 1 := by
  rw [← det_hyp, hyp_leviMat, det_fromBlocks_zero₂₁, det_transpose, det_map_bar,
    (A⁻¹ : SL(3, F4)).2, A.2, bar_one, one_mul]

theorem isIsometry_leviMat (A : SL(3, F4)) : IsIsometry (leviMat A) := by
  rw [isIsometry_iff_hyp, hyp_leviMat, fromBlocks_isometry_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← transpose_mul, ← map_bar_mul, coe_inv_mul_SL, map_bar_one, transpose_one]
  · rw [transpose_map, transpose_transpose, map_bar_map_bar, coe_inv_mul_SL]
  · rw [Matrix.mul_zero, Matrix.map_zero _ bar_zero, transpose_zero, Matrix.zero_mul, add_zero]

@[expose] noncomputable def leviSU (A : SL(3, F4)) : SU frobeniusF4 6 :=
  mkSU (leviMat A) (det_leviMat A) (isIsometry_leviMat A)

theorem toBlocks₂₁_leviSU (A : SL(3, F4)) :
    (hyp (((leviSU A : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).toBlocks₂₁ =
      0 := by
  show (hyp (leviMat A)).toBlocks₂₁ = 0
  rw [hyp_leviMat, toBlocks_fromBlocks₂₁]

theorem blockSL_leviSU (A : SL(3, F4)) : blockSL (leviSU A) (toBlocks₂₁_leviSU A) = A := by
  refine Subtype.ext ?_
  change (hyp (leviMat A)).toBlocks₁₁ = _
  rw [hyp_leviMat, toBlocks_fromBlocks₁₁]

@[expose] noncomputable def shiftEquiv (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    planePts (smulSub g X) ≃ planePts X where
  toFun p := ⟨g⁻¹ • p.1, by rw [← smul_mem_planePts g, smul_inv_smul]; exact p.2⟩
  invFun p := ⟨g • p.1, (smul_mem_planePts g X p.1).2 p.2⟩
  left_inv p := Subtype.ext (smul_inv_smul g p.1)
  right_inv p := Subtype.ext (inv_smul_smul g p.1)

@[expose] noncomputable def eW (g : SU frobeniusF4 6) :
    planePts (smulSub g W0) ≃ ℙ F4 (Fin 3 → F4) :=
  (shiftEquiv g W0).trans e0

theorem conj_toBlocks₂₁ {g h : SU frobeniusF4 6} (hx : (h : ProjSU) ∈ stabL (smulSub g W0)) :
    (hyp (((g⁻¹ * h * g : SU frobeniusF4 6) : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4)).toBlocks₂₁ = 0 := by
  rw [← mapsTo_W0_iff]
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0, mulVec_zero]
    exact Submodule.zero_mem _
  have hvi : herm v v = 0 := isTotIso_W0 v hv v hv
  have h1 : g • pt v hv0 hvi ∈ planePts (smulSub g W0) :=
    (smul_mem_planePts g W0 _).2 ((pt_mem_planePts hv0 hvi).2 hv)
  have h2 := (hx (g • pt v hv0 hvi)).2 h1
  rw [projAct_mk] at h2
  have h3 : (g⁻¹ * h * g) • pt v hv0 hvi ∈ planePts W0 := by
    rw [mul_smul, mul_smul, ← smul_mem_planePts g W0, smul_inv_smul]
    exact h2
  rw [smul_pt, pt_mem_planePts] at h3
  rwa [smul_def] at h3

theorem mem_range_restrL_iff (g : SU frobeniusF4 6) (σ : Equiv.Perm (planePts (smulSub g W0))) :
    σ ∈ (restrL (smulSub g W0)).range ↔
      ∃ A : PSL(3, F4), ∀ p, eW g (σ p) = A • eW g p := by
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H h =>
      have hk := conj_toBlocks₂₁ hx
      refine ⟨blockSL _ hk, fun p => ?_⟩
      have hq : (g⁻¹ * h * g) • ((shiftEquiv g W0 p : planePts W0) : IsoPt) ∈ planePts W0 := by
        change (g⁻¹ * h * g) • (g⁻¹ • p.1) ∈ planePts W0
        rw [mul_smul, mul_smul, smul_inv_smul, ← smul_mem_planePts g W0, smul_inv_smul]
        exact (hx p.1).2 p.2
      rw [eW, Equiv.trans_apply, Equiv.trans_apply, ← e0_smul _ hk _ hq]
      congr 1
      refine Subtype.ext ?_
      change g⁻¹ • projAct (h : ProjSU) p.1 = (g⁻¹ * h * g) • (g⁻¹ • p.1)
      rw [projAct_mk, mul_smul, mul_smul, smul_inv_smul]
  · rintro ⟨A, hA⟩
    obtain ⟨A', rfl⟩ := QuotientGroup.mk_surjective A
    have hW : smulSub (g * leviSU A' * g⁻¹) (smulSub g W0) = smulSub g W0 := by
      rw [← smulSub_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, smulSub_mul,
        smulSub_W0_of_toBlocks₂₁ (toBlocks₂₁_leviSU A')]
    have hx := mk_mem_stabL_of_smulSub hW
    refine ⟨⟨_, hx⟩, Equiv.ext fun p => (eW g).injective ?_⟩
    rw [hA p]
    have hq : leviSU A' • ((shiftEquiv g W0 p : planePts W0) : IsoPt) ∈ planePts W0 := by
      have h0 := (smul_mem_planePts (leviSU A') W0 _).2 (shiftEquiv g W0 p).2
      rwa [smulSub_W0_of_toBlocks₂₁ (toBlocks₂₁_leviSU A')] at h0
    have e1 := e0_smul _ (toBlocks₂₁_leviSU A') _ hq
    rw [blockSL_leviSU] at e1
    rw [eW, Equiv.trans_apply, Equiv.trans_apply, ← e1]
    congr 1
    refine Subtype.ext ?_
    change g⁻¹ • projAct ((g * leviSU A' * g⁻¹ : SU frobeniusF4 6) : ProjSU) p.1 =
      leviSU A' • (g⁻¹ • p.1)
    rw [projAct_mk, mul_smul, mul_smul, inv_smul_smul]

theorem exists_levi_mulEquiv {W : Submodule F4 V} (hW : IsMaxIso W) :
    ∃ (e : planePts W ≃ ℙ F4 (Fin 3 → F4)) (θ : (restrL W).range ≃* PSL(3, F4)),
      ∀ (σ : (restrL W).range) (p : planePts W),
        e ((σ : Equiv.Perm (planePts W)) p) = θ σ • e p := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_of_forall_iff (restrL (smulSub g W0)).range (eW g)
    (mem_range_restrL_iff g)
  exact ⟨eW g, θ, hθ⟩

theorem natCard_range_restrL {W : Submodule F4 V} (hW : IsMaxIso W) :
    Nat.card (restrL W).range = 20160 := by
  obtain ⟨-, θ, -⟩ := exists_levi_mulEquiv hW
  rw [Nat.card_congr θ.toEquiv, natCard_PSL3]

end CFSG.Monster.B.TwoA.Unitary.Clique
