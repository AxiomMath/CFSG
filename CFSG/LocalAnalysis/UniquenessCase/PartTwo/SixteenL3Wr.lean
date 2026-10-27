module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Quasithin.Background.HL3WrMParam
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

section Transport

private noncomputable def s16b_slMap {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K) :
    ↥(StatedSL d (ZMod 2)) →* ↥(StatedSL d K) :=
  ((Matrix.GeneralLinearGroup.map e.toRingHom).comp (StatedSL d (ZMod 2)).subtype).codRestrict _
    fun g => by
      apply Subgroup.subset_closure
      have hg : ((g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det (g : GL (Fin d) (ZMod 2)) = 1 :=
          Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      show (e.toRingHom.mapMatrix ((g : GL (Fin d) (ZMod 2)) :
        Matrix (Fin d) (Fin d) (ZMod 2))).det = 1
      rw [← RingHom.map_det, hg, map_one]

private theorem s16b_slMap_val {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K)
    (g : ↥(StatedSL d (ZMod 2))) :
    (((s16b_slMap e g : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)).map e := rfl

private theorem s16b_slMap_surjective {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K) :
    Function.Surjective (s16b_slMap (d := d) e) := by
  intro g
  have hm : ∀ g' : ↥(StatedSL d K),
      ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map e.symm ∈
        {A : Matrix (Fin d) (Fin d) (ZMod 2) | A.det = 1} := fun g' => by
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (g' : GL (Fin d) K)) = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  refine ⟨⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom (g : GL (Fin d) K),
    Subgroup.subset_closure (hm g)⟩, Subtype.ext (Units.ext ?_)⟩
  show (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map e.symm).map e =
    ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  ext i j
  simp

private theorem s16b_tensorAct_mul (d : ℕ) (K : Type) [Field K]
    (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (x y : Multiplicative (Matrix (Fin d) (Fin d) K)) :
    tensorAct d K γ (x * y) = tensorAct d K γ x * tensorAct d K γ y := by
  unfold tensorAct
  rw [toAdd_mul, Matrix.mul_add, Matrix.add_mul, ofAdd_add]

private theorem s16b_tensorAct_one_left (d : ℕ) (K : Type) [Field K]
    (x : Multiplicative (Matrix (Fin d) (Fin d) K)) : tensorAct d K 1 x = x := by
  unfold tensorAct
  simp

private theorem s16b_tensorAct_mul_act (d : ℕ) (K : Type) [Field K]
    (γ δ : ↥(StatedSL d K) × ↥(StatedSL d K)) (x : Multiplicative (Matrix (Fin d) (Fin d) K)) :
    tensorAct d K (γ * δ) x = tensorAct d K γ (tensorAct d K δ x) := by
  unfold tensorAct
  simp [Matrix.mul_assoc, Matrix.transpose_mul]

private theorem s16b_tensorAct_one_right (d : ℕ) (K : Type) [Field K]
    (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) : tensorAct d K γ 1 = 1 := by
  unfold tensorAct
  simp

theorem tensorNat_isActionModel (d : ℕ) (K : Type) [Field K] :
    (FFModel.tensorNat d K).IsActionModel where
  act_mul γ x y := s16b_tensorAct_mul d K γ x y
  act_one x := s16b_tensorAct_one_left d K x
  act_mul_act γ δ x := s16b_tensorAct_mul_act d K γ δ x
  sec_inv _ _ _ := trivial
  ker_inv γ m hm := by
    have h1 : m = 1 := Subgroup.mem_bot.1 hm
    subst h1
    exact Subgroup.mem_bot.2 (s16b_tensorAct_one_right d K γ)
  ker_le := bot_le

private abbrev s16b_TM (d : ℕ) (K : Type) [Field K] : Type :=
  Multiplicative (Matrix (Fin d) (Fin d) K)

private noncomputable def s16b_secMap {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K) :
    ↥(FFModel.tensorNat d (ZMod 2)).sec →* ↥(FFModel.tensorNat d K).sec where
  toFun m := ⟨Multiplicative.ofAdd
    ((Multiplicative.toAdd (show s16b_TM d (ZMod 2) from m.1)).map e), Subgroup.mem_top _⟩
  map_one' := Subtype.ext (by
    show Multiplicative.ofAdd ((0 : Matrix (Fin d) (Fin d) (ZMod 2)).map e) = 1
    rw [Matrix.map_zero _ (map_zero e)]
    rfl)
  map_mul' a b := Subtype.ext (by
    show Multiplicative.ofAdd
      ((Multiplicative.toAdd (show s16b_TM d (ZMod 2) from a.1) +
        Multiplicative.toAdd (show s16b_TM d (ZMod 2) from b.1)).map e) = _
    rw [Matrix.map_add _ (map_add e)]
    rfl)

private theorem s16b_secMap_val {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K)
    (m : ↥(FFModel.tensorNat d (ZMod 2)).sec) :
    ((s16b_secMap e m : ↥(FFModel.tensorNat d K).sec) : (FFModel.tensorNat d K).Amb) =
      Multiplicative.ofAdd ((Multiplicative.toAdd (show s16b_TM d (ZMod 2) from m.1)).map e) :=
  rfl

private theorem s16b_secMap_surjective {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K) :
    Function.Surjective (s16b_secMap (d := d) e) := by
  intro n
  refine ⟨⟨Multiplicative.ofAdd
    ((Multiplicative.toAdd (show s16b_TM d K from n.1)).map e.symm), Subgroup.mem_top _⟩,
    Subtype.ext ?_⟩
  rw [s16b_secMap_val]
  show Multiplicative.ofAdd
    (((Multiplicative.toAdd (show s16b_TM d K from n.1)).map e.symm).map e) =
      (show s16b_TM d K from n.1)
  ext i j
  simp

private theorem s16b_secMap_act {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K)
    (σ : ↥(StatedSL d (ZMod 2)) × ↥(StatedSL d (ZMod 2))) (m : s16b_TM d (ZMod 2)) :
    Multiplicative.ofAdd ((Multiplicative.toAdd (tensorAct d (ZMod 2) σ m)).map e) =
      tensorAct d K ((s16b_slMap e).prodMap (s16b_slMap e) σ)
        (Multiplicative.ofAdd ((Multiplicative.toAdd m).map e)) := by
  have hm : ∀ A B : Matrix (Fin d) (Fin d) (ZMod 2), (A * B).map e = A.map e * B.map e :=
    fun A B => Matrix.map_mul (f := e.toRingHom)
  unfold tensorAct
  simp only [toAdd_ofAdd, MonoidHom.coe_prodMap, Prod.map_fst, Prod.map_snd, s16b_slMap_val]
  rw [hm, hm, Matrix.transpose_map]

private theorem s16b_map_eq_one_iff {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K)
    (x : s16b_TM d (ZMod 2)) :
    (Multiplicative.ofAdd ((Multiplicative.toAdd x).map e) : s16b_TM d K) = 1 ↔ x = 1 := by
  rw [ofAdd_eq_one, ← toAdd_eq_zero]
  constructor
  · intro h
    refine Matrix.map_injective e.injective ?_
    show (Multiplicative.toAdd x).map e = (0 : Matrix (Fin d) (Fin d) (ZMod 2)).map e
    rw [h, Matrix.map_zero _ (map_zero e)]
  · intro h
    rw [h]
    exact Matrix.map_zero _ (map_zero e)

private theorem s16b_secMap_ker {d : ℕ} {K : Type} [Field K] (e : ZMod 2 ≃+* K)
    (m : ↥(FFModel.tensorNat d (ZMod 2)).sec) :
    ((s16b_secMap e m : ↥(FFModel.tensorNat d K).sec) : (FFModel.tensorNat d K).Amb) ∈
        (FFModel.tensorNat d K).ker ↔
      (m : (FFModel.tensorNat d (ZMod 2)).Amb) ∈ (FFModel.tensorNat d (ZMod 2)).ker := by
  have h1 := s16b_map_eq_one_iff (K := K) e (show s16b_TM d (ZMod 2) from m.1)
  show _ ∈ (⊥ : Subgroup (FFModel.tensorNat d K).Amb) ↔
    _ ∈ (⊥ : Subgroup (FFModel.tensorNat d (ZMod 2)).Amb)
  rw [Subgroup.mem_bot, Subgroup.mem_bot, s16b_secMap_val]
  exact h1

theorem tensorNat_realizes_zmod_two {d : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} (h : (FFModel.tensorNat d K).Realizes H U Z) :
    (FFModel.tensorNat d (ZMod 2)).Realizes H U Z := by
  obtain ⟨π, hπ⟩ := h
  haveI := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hF
  have hθ : Function.Surjective ((s16b_slMap (d := d) e).prodMap (s16b_slMap (d := d) e)) := by
    rw [MonoidHom.coe_prodMap]
    exact (s16b_slMap_surjective e).prodMap (s16b_slMap_surjective e)
  exact ⟨π.comp ((s16b_slMap e).prodMap (s16b_slMap e)),
    FFModel.RealizesVia.of_surjHom (tensorNat_isActionModel d (ZMod 2)) hπ
      ((s16b_slMap e).prodMap (s16b_slMap e)) hθ (s16b_secMap e) (s16b_secMap_surjective e)
      (fun σ m hm => s16b_secMap_act e σ m.1) (fun m => s16b_secMap_ker e m)⟩

private noncomputable def s16b_trans {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    ↥(StatedSL d (ZMod 2)) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j (1 : ZMod 2))
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero),
    CFSG.Open.StatedAPI.mem_statedSL_iff.2 (by
      show (Matrix.transvection i j (1 : ZMod 2)).det = 1
      exact Matrix.det_transvection_of_ne i j hij 1)⟩

private theorem s16b_trans_val {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    (((s16b_trans hij : ↥(StatedSL d (ZMod 2))) : GL (Fin d) (ZMod 2)) :
      Matrix (Fin d) (Fin d) (ZMod 2)) = Matrix.transvection i j (1 : ZMod 2) := rfl

private theorem s16b_tensorAct_trans {d : ℕ} {i j : Fin d} (hij : i ≠ j) (k : Fin d) :
    tensorAct d (ZMod 2) (s16b_trans hij, 1)
        (Multiplicative.ofAdd (Matrix.single j k (1 : ZMod 2))) *
      (Multiplicative.ofAdd (Matrix.single j k (1 : ZMod 2)))⁻¹ =
    Multiplicative.ofAdd (Matrix.single i k (1 : ZMod 2)) := by
  unfold tensorAct
  simp only [toAdd_ofAdd, s16b_trans_val, Matrix.transvection, Subgroup.coe_one, Prod.snd_one,
    Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul,
    Matrix.single_mul_single_same, one_mul]
  rw [← ofAdd_neg, ← ofAdd_add]
  congr 1
  abel

theorem commSub_top_eq_top_of_tensorNat {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : (FFModel.tensorNat 3 (ZMod 2)).Realizes H ⊤ ⊥) : commSub ⊤ H = ⊤ := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.tensorNat 3 (ZMod 2)) rfl hπ
  have hone : E.symm (1 : ↥(FFModel.tensorNat 3 (ZMod 2)).sec) = 1 := map_one _
  have hunit : ∀ i k : Fin 3,
      E.symm ⟨(Multiplicative.ofAdd (Matrix.single i k (1 : ZMod 2)) : s16b_TM 3 (ZMod 2)),
        trivial⟩ ∈ commSub ⊤ H := by
    intro i k
    have hij : i ≠ i + 1 := by revert i; decide
    let γ : (FFModel.tensorNat 3 (ZMod 2)).Gam := (s16b_trans hij, 1)
    set v : V := E.symm ⟨(Multiplicative.ofAdd (Matrix.single (i + 1) k (1 : ZMod 2)) :
      s16b_TM 3 (ZMod 2)), trivial⟩ with hv
    have hmem : ((π γ : ↥H) : MulAut V) v * v⁻¹ ∈ commSub ⊤ H :=
      Subgroup.subset_closure ⟨_, (π γ).2, v, trivial, rfl⟩
    have hEv : E v = ⟨(Multiplicative.ofAdd (Matrix.single (i + 1) k (1 : ZMod 2)) :
        s16b_TM 3 (ZMod 2)), trivial⟩ := E.apply_symm_apply _
    have key : E (((π γ : ↥H) : MulAut V) v * v⁻¹) =
        ⟨(Multiplicative.ofAdd (Matrix.single i k (1 : ZMod 2)) : s16b_TM 3 (ZMod 2)),
          trivial⟩ := by
      rw [map_mul, map_inv]
      refine Subtype.ext ?_
      show ((E (((π γ : ↥H) : MulAut V) v) :
          ↥(FFModel.tensorNat 3 (ZMod 2)).sec) : (FFModel.tensorNat 3 (ZMod 2)).Amb) *
        ((E v : ↥(FFModel.tensorNat 3 (ZMod 2)).sec) : (FFModel.tensorNat 3 (ZMod 2)).Amb)⁻¹ = _
      rw [hE γ v, hEv]
      exact s16b_tensorAct_trans hij k
    rw [← E.symm_apply_eq.2 key.symm] at hmem
    exact hmem
  have hall : ∀ Y : Matrix (Fin 3) (Fin 3) (ZMod 2),
      E.symm ⟨(Multiplicative.ofAdd Y : s16b_TM 3 (ZMod 2)), trivial⟩ ∈ commSub ⊤ H := by
    intro Y
    induction Y using Matrix.induction_on' with
    | h_zero =>
      have : (⟨(Multiplicative.ofAdd (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) : s16b_TM 3 (ZMod 2)),
          trivial⟩ : ↥(FFModel.tensorNat 3 (ZMod 2)).sec) = 1 := rfl
      rw [this, hone]
      exact Subgroup.one_mem _
    | h_add p q hp hq =>
      have : (⟨(Multiplicative.ofAdd (p + q) : s16b_TM 3 (ZMod 2)), trivial⟩ :
          ↥(FFModel.tensorNat 3 (ZMod 2)).sec) =
          ⟨(Multiplicative.ofAdd p : s16b_TM 3 (ZMod 2)), trivial⟩ *
            ⟨(Multiplicative.ofAdd q : s16b_TM 3 (ZMod 2)), trivial⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ hp hq
    | h_std_basis i k x =>
      have hx : x = 0 ∨ x = 1 := by revert x; decide
      rcases hx with rfl | rfl
      · have : (⟨(Multiplicative.ofAdd (Matrix.single i k (0 : ZMod 2)) : s16b_TM 3 (ZMod 2)),
            trivial⟩ : ↥(FFModel.tensorNat 3 (ZMod 2)).sec) = 1 := by
          refine Subtype.ext ?_
          show Multiplicative.ofAdd (Matrix.single i k (0 : ZMod 2)) = 1
          rw [Matrix.single_zero]
          rfl
        rw [this, hone]
        exact Subgroup.one_mem _
      · exact hunit i k
  refine eq_top_iff.2 fun v _ => ?_
  have hEv : E v = ⟨(Multiplicative.ofAdd
      (Multiplicative.toAdd (show s16b_TM 3 (ZMod 2) from (E v).1)) : s16b_TM 3 (ZMod 2)),
      trivial⟩ := Subtype.ext rfl
  have := hall (Multiplicative.toAdd (show s16b_TM 3 (ZMod 2) from (E v).1))
  rwa [← hEv, MulEquiv.symm_apply_apply] at this

end Transport

section Finite

variable {G : Type} [Group G] [Finite G]

theorem Mbar_le_normalizer_lBar_of_tensor (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h151 : Hyp151 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥)
    (hT : (FFModel.tensorNat 3 (ZMod 2)).Realizes (barSub V₀ V hV L) ⊤ ⊥) :
    Mbar D.M V₀ V hV ≤
      normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  have hW : wTil V₀ V hV L = ⊤ := commSub_top_eq_top_of_tensorNat hT
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h151.hyp125.pairFacts.le_normalizer h151.hyp125.pairFacts.le_normalizer₀
  have hnB : ∀ g ∈ D.M, g ∈ nBar D.M V₀ V hV L := by
    intro g hg
    by_contra hn
    obtain ⟨-, hc⟩ := h151.commute g hg hn
    rw [hW, commSub_eq_bot_iff] at hc
    have hbot : barSub V₀ V hV (conjSubgroup L g) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      refine Subgroup.mem_bot.2 (MulEquiv.ext fun u => ?_)
      exact hc (Subgroup.mem_top u) x hx
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hg) L] at hbot
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).1 hbot)
  intro φ hφ
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  obtain ⟨-, hh, hnorm⟩ := (mem_preBarSub D.M V₀ V hV _).1 (hnB g hgM)
  exact hnorm

theorem R16_58_m_holds (D : Data G) : R16_58_m D := by
  intro V₀ V L hV hS h7
  obtain ⟨K, _, hfin, hK, hmodel⟩ := h7.2.1
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hT := tensorNat_realizes_zmod_two hK2 hmodel
  have hnorm := Mbar_le_normalizer_lBar_of_tensor D hV hS.setting.hyp151 hS.ne_bot hT
  have h3 : 3 ≤ E3.mParam (Mbar D.M V₀ V hV) :=
    CFSG.Quasithin.H.L3Wr.H44_L3Wreath_mParam hT hnorm
  exact (hS.setting.hyp16.hyp125.pairFacts.mBarGT_iff_lt_mBar 2).2 h3

end Finite

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
