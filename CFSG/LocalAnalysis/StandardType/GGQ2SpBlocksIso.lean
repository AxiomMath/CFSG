module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

section

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
  (m : ℕ)

private theorem glFixing_one {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] :
    glFixing (1 : Matrix ι ι F) = ⊥ := by
  ext g
  rw [Subgroup.mem_bot]
  change ((g : GL ι F) : Matrix ι ι F) * 1 = 1 ↔ g = 1
  rw [mul_one]
  constructor
  · intro h
    exact Units.ext h
  · intro h
    rw [h]
    rfl

private theorem comap_bot_subtype {G : Type} [Group G] {H : Subgroup G} :
    (⊥ : Subgroup G).comap H.subtype = ⊥ := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_bot, Subgroup.mem_bot]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    rw [h]
    rfl

private theorem levi_empty {K : Type} [Field K] (m : ℕ) :
    levi (K := K) m (∅ : Finset (Fin m)) = ⊥ := by
  rw [levi, planeIdem_empty, sub_zero, glFixing_one, comap_bot_subtype]

theorem blockGroup_zero_empty : blockGroup ζ m (PlaneRaw.Code.zero ∅) = ⊥ := by
  show levi (K := K) m (∅ : Finset (Fin m)) = ⊥
  exact levi_empty m

theorem blockGroup_extension_zero : blockGroup ζ m (PlaneRaw.Code.extension 0) = ⊥ := by
  show levi (K := K) m (PlaneRaw.Code.extSupport (0 : PlaneRaw.V m)) ⊓
      Subgroup.centralizer ({tau ζ m 0} : Set ↥(StatedSp m K)) = ⊥
  rw [show PlaneRaw.Code.extSupport (0 : PlaneRaw.V m) = ∅ by
        simp [PlaneRaw.Code.extSupport], levi_empty]
  simp

end

variable {K : Type} [Field K]

private def tauMat (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u : PlaneRaw.V m) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  ((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K)

private def zeroKeyVec (m : ℕ) (S : Finset (Fin m)) : PlaneRaw.V m :=
  fun i => if i ∈ S then 0 else 1

private theorem extSupport_zeroKeyVec (m : ℕ) (S : Finset (Fin m)) :
    PlaneRaw.Code.extSupport (zeroKeyVec m S) = Sᶜ := by
  ext i
  rw [PlaneRaw.mem_extSupport]
  by_cases h : i ∈ S <;> simp [zeroKeyVec, h]

private theorem tau_pow_three (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (m : ℕ) (u : PlaneRaw.V m) : tau ζ m u ^ 3 = 1 := by
  have h3 : (3 : ℕ) • u = 0 := by
    funext i
    show (3 : ℕ) • (u i) = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← tau_nsmul ζ m 3 u, h3, tau_zero]

private theorem tauGL_pow_three (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (m : ℕ) (u : PlaneRaw.V m) :
    (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K)) ^ 3 = 1 := by
  have h := congrArg (fun x : ↥(StatedSp m K) => ((x : GL (Fin m ⊕ Fin m) K)))
    (tau_pow_three ζ m u)
  simpa [Subgroup.coe_pow] using h

private theorem tauGL_orderOf_odd (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (m : ℕ) (u : PlaneRaw.V m) :
    Odd (orderOf (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K))) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (tauGL_pow_three ζ m u))

private theorem tauMat_mul_planeIdem_comm
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (u : PlaneRaw.V m) (S : Finset (Fin m)) :
    tauMat ζ m u * planeIdem m S = planeIdem m S * tauMat ζ m u :=
  tau_mul_planeIdem_comm ζ m u S

private theorem tauMat_mul_self_add_extSupport [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (m : ℕ) (u : PlaneRaw.V m) :
    tauMat ζ m u * tauMat ζ m u + tauMat ζ m u =
      planeIdem m (PlaneRaw.Code.extSupport u) :=
  tau_mul_self_add hK hζ u

private theorem extSupport_nonempty {m : ℕ} {e : PlaneRaw.V m} (he : e ≠ 0) :
    (PlaneRaw.Code.extSupport e).Nonempty := by
  by_contra h
  apply he
  funext i
  by_contra hi
  exact h ⟨i, by simpa using hi⟩

private theorem tauMat_zeroKeyVec_mul_planeIdem
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (S : Finset (Fin m)) :
    tauMat ζ m (zeroKeyVec m S) * planeIdem m S = planeIdem m S := by
  show (((tau ζ m (zeroKeyVec m S) : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * planeIdem m S = planeIdem m S
  rw [coe_tau, planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
  congr 1
  funext j
  by_cases hj : j ∈ S <;> simp [zeroKeyVec, hj]

private theorem planeIdem_eq_one_add_tauMat_zeroKeyVec [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (m : ℕ) (S : Finset (Fin m)) :
    (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      1 + tauMat ζ m (zeroKeyVec m S) +
        tauMat ζ m (zeroKeyVec m S) * tauMat ζ m (zeroKeyVec m S) := by
  have h := tauMat_mul_self_add_extSupport (ζ := ζ) hK hζ m (zeroKeyVec m S)
  rw [extSupport_zeroKeyVec, planeIdem_compl] at h
  calc (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      = 1 - (1 - planeIdem m S) := by abel
    _ = 1 - (tauMat ζ m (zeroKeyVec m S) * tauMat ζ m (zeroKeyVec m S) +
          tauMat ζ m (zeroKeyVec m S)) := by rw [← h]
    _ = 1 + (tauMat ζ m (zeroKeyVec m S) * tauMat ζ m (zeroKeyVec m S) +
          tauMat ζ m (zeroKeyVec m S)) := by
        rw [sub_eq_add_neg, neg_eq_self_of_charTwo]
    _ = 1 + tauMat ζ m (zeroKeyVec m S) +
          tauMat ζ m (zeroKeyVec m S) * tauMat ζ m (zeroKeyVec m S) := by abel

private def sumSupportEquiv (m : ℕ) (S : Finset (Fin m)) :
    {x : Fin m ⊕ Fin m // Sum.elim id id x ∈ S} ≃ S ⊕ S where
  toFun x :=
    match x with
    | ⟨Sum.inl i, h⟩ => Sum.inl ⟨i, h⟩
    | ⟨Sum.inr i, h⟩ => Sum.inr ⟨i, h⟩
  invFun y :=
    match y with
    | Sum.inl i => ⟨Sum.inl i.1, i.2⟩
    | Sum.inr i => ⟨Sum.inr i.1, i.2⟩
  left_inv x := by rcases x with ⟨i | i, h⟩ <;> rfl
  right_inv y := by rcases y with i | i <;> rfl

private theorem finrank_range_planeIdem (K : Type) [Field K] (m : ℕ)
    (S : Finset (Fin m)) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (planeIdem (K := K) m S))) =
      2 * S.card := by
  classical
  have htoLin : Matrix.toLin' (planeIdem (K := K) m S) =
      Matrix.mulVecLin (planeIdem (K := K) m S) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.mulVecLin_apply]
  rw [htoLin]
  have hrank : Module.finrank K (LinearMap.range (Matrix.mulVecLin (planeIdem m S))) =
      (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).rank := rfl
  rw [hrank, planeIdem, Matrix.rank_diagonal, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun x : Fin m ⊕ Fin m =>
      (if Sum.elim id id x ∈ S then (1 : K) else 0) ≠ 0) =
      Finset.univ.filter fun x : Fin m ⊕ Fin m => Sum.elim id id x ∈ S := by
    apply Finset.filter_congr
    intro x _
    by_cases hx : Sum.elim id id x ∈ S <;> simp [hx]
  rw [hfilter, ← Fintype.card_subtype,
    Fintype.card_congr (sumSupportEquiv m S), Fintype.card_sum]
  simp [Fintype.card_coe, two_mul]

private theorem zeroAlg_mul_planeIdem_mem_span
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (m : ℕ) (S : Finset (Fin m)) :
    ∀ a ∈ Algebra.adjoin K (Units.val '' ({((tau ζ m (zeroKeyVec m S) : ↥(StatedSp m K)) :
        GL (Fin m ⊕ Fin m) K)} : Set (GL (Fin m ⊕ Fin m) K))),
      a * planeIdem m S ∈
        Submodule.span K ({planeIdem m S} : Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) := by
  classical
  intro a ha
  have hbε : tauMat ζ m (zeroKeyVec m S) * planeIdem m S = planeIdem m S :=
    tauMat_zeroKeyVec_mul_planeIdem ζ m S
  refine Algebra.adjoin_induction
    (p := fun x _ => x * planeIdem m S ∈
      Submodule.span K ({planeIdem m S} : Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)))
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    change tauMat ζ m (zeroKeyVec m S) * planeIdem m S ∈
      Submodule.span K ({planeIdem m S} : Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    rw [hbε]
    exact Submodule.subset_span (by simp)
  · intro r
    have h : (algebraMap K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) r) * planeIdem m S =
        r • planeIdem m S := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    rw [h]
    exact Submodule.smul_mem _ r (Submodule.subset_span (by simp))
  · intro x y _ _ hx hy
    rw [Matrix.add_mul]
    exact Submodule.add_mem _ hx hy
  · intro x y _ _ hx hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    rw [Matrix.mul_assoc, ← hc, Matrix.mul_smul]
    exact Submodule.smul_mem _ c hx

private def extEps {K : Type} [Field K] (m : ℕ) (e : PlaneRaw.V m) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  planeIdem m (PlaneRaw.Code.extSupport e)

private def extB {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) : GL (Fin m ⊕ Fin m) K :=
  (tau ζ m e : ↥(StatedSp m K))

private def extAlg {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) : Subalgebra K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
  Algebra.adjoin K (Units.val '' ({extB ζ m e} : Set (GL (Fin m ⊕ Fin m) K)))

private def extV {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) : Submodule K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
  Submodule.span K ({extEps m e, tauMat ζ m e * extEps m e} :
    Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))

private theorem centralizer_tau_extB {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) :
    Subgroup.centralizer ({tau ζ m e} : Set ↥(StatedSp m K)) =
      (Subgroup.centralizer ({extB ζ m e} : Set (GL (Fin m ⊕ Fin m) K))).comap
        (StatedSp m K).subtype := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    change ((g : GL (Fin m ⊕ Fin m) K)) * ((tau ζ m e : ↥(StatedSp m K)) :
        GL (Fin m ⊕ Fin m) K) =
      ((tau ζ m e : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K)
    have h' := congrArg (fun x : ↥(StatedSp m K) => ((x : GL (Fin m ⊕ Fin m) K))) h
    simpa only [Subgroup.coe_mul] using h'
  · intro h
    apply Subtype.ext
    change (StatedSp m K).subtype g * extB ζ m e =
      extB ζ m e * (StatedSp m K).subtype g
    exact h

private theorem blockGroup_extension_eq {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) :
    blockGroup ζ m (PlaneRaw.Code.extension e) =
      glBlockCentralizer (StatedSp m K).subtype ({extB ζ m e} :
        Set (GL (Fin m ⊕ Fin m) K)) (extEps m e) := by
  show levi (K := K) m (PlaneRaw.Code.extSupport e) ⊓
      Subgroup.centralizer ({tau ζ m e} : Set ↥(StatedSp m K)) = _
  rw [glBlockCentralizer, Subgroup.comap_inf, centralizer_tau_extB]
  exact inf_comm _ _

private theorem tauMat_extEps_mul_self {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) :
    (tauMat ζ m e * extEps m e) * (tauMat ζ m e * extEps m e) =
      tauMat ζ m e * (tauMat ζ m e * extEps m e) := by
  have hcomm : tauMat ζ m e * extEps m e = extEps m e * tauMat ζ m e :=
    tauMat_mul_planeIdem_comm ζ m e _
  have hεid : extEps (K := K) m e * extEps (K := K) m e = extEps (K := K) m e :=
    (isIdempotentElem_planeIdem (K := K) m (PlaneRaw.Code.extSupport e)).eq
  calc (tauMat ζ m e * extEps m e) * (tauMat ζ m e * extEps m e)
      = tauMat ζ m e * (extEps m e * (tauMat ζ m e * extEps m e)) :=
          Matrix.mul_assoc _ _ _
    _ = tauMat ζ m e * ((extEps m e * tauMat ζ m e) * extEps m e) := by
          rw [Matrix.mul_assoc]
    _ = tauMat ζ m e * ((tauMat ζ m e * extEps m e) * extEps m e) := by rw [← hcomm]
    _ = tauMat ζ m e * (tauMat ζ m e * (extEps m e * extEps m e)) := by
          rw [Matrix.mul_assoc]
    _ = tauMat ζ m e * (tauMat ζ m e * extEps m e) := by rw [hεid]

private theorem tauMat_ext_sq [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) (e : PlaneRaw.V m) :
    tauMat ζ m e * tauMat ζ m e = tauMat ζ m e + extEps m e := by
  have hsq : tauMat ζ m e * tauMat ζ m e + tauMat ζ m e = extEps m e :=
    tauMat_mul_self_add_extSupport (ζ := ζ) hK hζ m e
  calc tauMat ζ m e * tauMat ζ m e
      = (tauMat ζ m e * tauMat ζ m e + tauMat ζ m e) + tauMat ζ m e := by
          rw [add_assoc, add_self_eq_zero_of_charTwo, add_zero]
    _ = tauMat ζ m e + extEps m e := by rw [hsq, add_comm]

private theorem tauMat_ext_sq_mul [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) (e : PlaneRaw.V m) :
    tauMat ζ m e * (tauMat ζ m e * extEps m e) =
      tauMat ζ m e * extEps m e + extEps m e := by
  have hεid : extEps (K := K) m e * extEps (K := K) m e = extEps (K := K) m e :=
    (isIdempotentElem_planeIdem (K := K) m (PlaneRaw.Code.extSupport e)).eq
  rw [← Matrix.mul_assoc, tauMat_ext_sq hK hζ m e, Matrix.add_mul, hεid]

private theorem extB_mul_extEps_ne {K : Type} [Field K]
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) {e : PlaneRaw.V m} (he : e ≠ 0) :
    (extB ζ m e : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * extEps m e ≠ extEps m e := by
  classical
  intro h
  obtain ⟨j, hj⟩ := extSupport_nonempty he
  have hh : (((tau ζ m e : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        planeIdem m (PlaneRaw.Code.extSupport e) =
      planeIdem m (PlaneRaw.Code.extSupport e) := h
  rw [coe_tau, planeIdem_eq_planeMat, WitSpNs.planeMat_mul] at hh
  have hf := WitSpNs.planeMat_injective hh
  have hblock : ((ζ (Multiplicative.ofAdd (e j)) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrFun hf j
    simpa [hj] using this
  have hsl : ζ (Multiplicative.ofAdd (e j)) = 1 := Subtype.ext (by simpa using hblock)
  have h1 : Multiplicative.ofAdd (e j) = 1 := by
    apply hζ
    simpa using hsl
  have h0 : e j = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  exact (PlaneRaw.mem_extSupport e j).mp hj h0

private theorem extV_stable [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) (e : PlaneRaw.V m) :
    ∀ a ∈ extAlg ζ m e, ∀ v ∈ extV ζ m e, a * v ∈ extV ζ m e := by
  classical
  have hbbε := tauMat_ext_sq_mul hK hζ m e
  intro a ha
  refine Algebra.adjoin_induction
    (p := fun x _ => ∀ v ∈ extV ζ m e, x * v ∈ extV ζ m e) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    intro v hv
    change tauMat ζ m e * v ∈ extV ζ m e
    refine Submodule.span_induction
      (p := fun v _ => tauMat ζ m e * v ∈ extV ζ m e) ?_ ?_ ?_ ?_ hv
    · intro w hw
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [hbbε]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
    · rw [Matrix.mul_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [Matrix.mul_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [Matrix.mul_smul]
      exact Submodule.smul_mem _ c hx
  · intro r v hv
    have h : (algebraMap K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) r) * v = r • v := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    rw [h]
    exact Submodule.smul_mem _ r hv
  · intro x y _ _ hx hy v hv
    rw [Matrix.add_mul]
    exact Submodule.add_mem _ (hx v hv) (hy v hv)
  · intro x y _ _ hx hy v hv
    rw [Matrix.mul_assoc]
    exact hx _ (hy v hv)

private theorem finrank_extV_le_two {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (e : PlaneRaw.V m) :
    Module.finrank K (extV ζ m e) ≤ 2 := by
  classical
  change Module.finrank K (Submodule.span K
    ({extEps m e, tauMat ζ m e * extEps m e} :
      Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))) ≤ 2
  refine (finrank_span_le_card (R := K)
    (s := ({extEps m e, tauMat ζ m e * extEps m e} :
      Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)))).trans ?_
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  exact (Finset.card_insert_le _ _).trans (by simp)

private theorem blockDegree_le_finrank_extV [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) (e : PlaneRaw.V m) :
    blockDegree (extAlg ζ m e) (extEps m e) ≤ Module.finrank K (extV ζ m e) := by
  classical
  rw [blockDegree]
  refine Submodule.finrank_mono ?_
  rintro x ⟨a, ha, hx⟩
  rw [← hx, LinearMap.mulRight_apply]
  exact extV_stable (ζ := ζ) hK hζ m e a ha (extEps m e)
    (Submodule.subset_span (by simp))

private theorem extPair_sq [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) (e : PlaneRaw.V m) :
    (extEps m e + tauMat ζ m e * extEps m e) *
      (extEps m e + tauMat ζ m e * extEps m e) = tauMat ζ m e * extEps m e := by
  have hεid : IsIdempotentElem (extEps (K := K) m e) :=
    isIdempotentElem_planeIdem (K := K) m (PlaneRaw.Code.extSupport e)
  have hcomm : extEps m e * tauMat ζ m e = tauMat ζ m e * extEps m e :=
    (tauMat_mul_planeIdem_comm ζ m e _).symm
  have hcross1 : extEps m e * (tauMat ζ m e * extEps m e) =
      tauMat ζ m e * extEps m e := by
    calc extEps m e * (tauMat ζ m e * extEps m e)
        = (extEps m e * tauMat ζ m e) * extEps m e := (Matrix.mul_assoc _ _ _).symm
      _ = (tauMat ζ m e * extEps m e) * extEps m e := by rw [hcomm]
      _ = tauMat ζ m e * (extEps m e * extEps m e) := Matrix.mul_assoc _ _ _
      _ = tauMat ζ m e * extEps m e := by rw [hεid.eq]
  have hcross2 : (tauMat ζ m e * extEps m e) * extEps m e =
      tauMat ζ m e * extEps m e := by
    rw [Matrix.mul_assoc, hεid.eq]
  have hb2 := tauMat_ext_sq_mul hK hζ m e
  calc (extEps m e + tauMat ζ m e * extEps m e) *
        (extEps m e + tauMat ζ m e * extEps m e)
      = extEps m e * extEps m e + extEps m e * (tauMat ζ m e * extEps m e) +
          ((tauMat ζ m e * extEps m e) * extEps m e +
            (tauMat ζ m e * extEps m e) * (tauMat ζ m e * extEps m e)) := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    _ = extEps m e + tauMat ζ m e * extEps m e +
          ((tauMat ζ m e * extEps m e) + (tauMat ζ m e * extEps m e +
            extEps m e)) := by
          rw [hεid.eq, hcross1, hcross2, tauMat_extEps_mul_self ζ m e, hb2]
    _ = tauMat ζ m e * extEps m e := by
          have hε2 : extEps (K := K) m e + extEps (K := K) m e = 0 :=
            add_self_eq_zero_of_charTwo _
          have hb2' : (tauMat ζ m e * extEps m e) + (tauMat ζ m e * extEps m e) = 0 :=
            add_self_eq_zero_of_charTwo _
          calc extEps m e + tauMat ζ m e * extEps m e +
                ((tauMat ζ m e * extEps m e) + (tauMat ζ m e * extEps m e +
                  extEps m e))
              = (extEps m e + extEps m e) +
                  ((tauMat ζ m e * extEps m e) + (tauMat ζ m e * extEps m e)) +
                    tauMat ζ m e * extEps m e := by abel
            _ = 0 + 0 + tauMat ζ m e * extEps m e := by rw [hε2, hb2']
            _ = tauMat ζ m e * extEps m e := by abel

variable [Finite K] [CharP K 2]
  (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)

theorem nonempty_blockGroup_zero_mulEquiv (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {S : Finset (Fin m)} (hS : S.Nonempty) :
    Nonempty (↥(blockGroup ζ m (PlaneRaw.Code.zero S)) ≃* ↥(StatedSp S.card K)) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let u₀ : PlaneRaw.V m := zeroKeyVec m S
  let b : GL (Fin m ⊕ Fin m) K := (tau ζ m u₀ : ↥(StatedSp m K))
  let ε : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := planeIdem m S
  let A : Subalgebra K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin m ⊕ Fin m) K)))
  have hbSp : b ∈ StatedSp m K := (tau ζ m u₀).2
  have hodd : Odd (orderOf b) := tauGL_orderOf_odd ζ m u₀
  have hbε : (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * ε = ε :=
    tauMat_zeroKeyVec_mul_planeIdem ζ m S
  have hεid : IsIdempotentElem ε := isIdempotentElem_planeIdem m S
  have hne : ε ≠ 0 := planeIdem_ne_zero hS
  have hsq : ε = 1 + tauMat ζ m u₀ + tauMat ζ m u₀ * tauMat ζ m u₀ :=
    planeIdem_eq_one_add_tauMat_zeroKeyVec (ζ := ζ) hK hζ m S
  have hmemV : ∀ a ∈ A, a * ε ∈ Submodule.span K ({ε} : Set
      (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) := by
    intro a ha
    exact zeroAlg_mul_planeIdem_mem_span (ζ := ζ) m S a ha
  have hAdj : IsPrimAdjIdemIn (RingHom.id K)
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) A ε := by
    refine ⟨?_, hεid, hne, formAdj_planeIdem m S, ?_⟩
    · have hb : tauMat ζ m u₀ ∈ A := Algebra.subset_adjoin ⟨b, by simp, rfl⟩
      rw [hsq]
      exact A.add_mem (A.add_mem A.one_mem hb) (A.mul_mem hb hb)
    · intro e' he' hidem hfix hprod
      have hmem : e' ∈ Submodule.span K ({ε} : Set
          (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) := by
        have h := hmemV e' he'
        rwa [hprod] at h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hcross : (c • ε) * (c • ε) = (c * c) • ε := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hεid.eq]
      have hidem' : (c • ε) * (c • ε) = c • ε := by
        rw [hc]
        exact hidem.eq
      have hcc : (c * c) • ε = c • ε := by
        rw [← hcross, hidem']
      have hzero : (c * c - c) • ε = 0 := by
        rw [sub_smul, hcc, sub_self]
      have hc2 : c * c = c := by
        rcases smul_eq_zero.mp hzero with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 hne
      rcases eq_zero_or_eq_one hK c with h0 | h1
      · left
        rw [← hc, h0, zero_smul]
      · right
        rw [← hc, h1, one_smul]
  have hle : levi (K := K) m S ≤ (Subgroup.centralizer
      ({b} : Set (GL (Fin m ⊕ Fin m) K))).comap (StatedSp m K).subtype := by
    intro g hg
    rw [Subgroup.mem_comap]
    have hgSp : ((g : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) ∈ StatedSp m K := g.2
    have hfix : (((g : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 - ε) = 1 - ε := hg
    have hcomm := commute_of_block hfix
      (one_sub_planeIdem_mul_of_mem hgSp hfix)
      (tauMat_mul_planeIdem_comm ζ m u₀ S) (by rw [one_mul]; exact hbε.symm)
      (by rw [mul_one, one_mul])
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    change (((g : GL (Fin m ⊕ Fin m) K)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        tauMat ζ m u₀ =
      tauMat ζ m u₀ * (((g : GL (Fin m ⊕ Fin m) K)) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    exact hcomm
  have hEq : blockGroup ζ m (PlaneRaw.Code.zero S) =
      glBlockCentralizer (StatedSp m K).subtype ({b} : Set (GL (Fin m ⊕ Fin m) K)) ε := by
    show levi (K := K) m S = _
    ext g
    constructor
    · intro hg
      exact ⟨hle hg, hg⟩
    · intro hg
      exact hg.2
  obtain ⟨n₁, hn₁, ⟨iso⟩⟩ :=
    ClassicalBlocks.blockGroup_iso_Sp_one (K := K) b hbSp hodd hAdj hbε
  have hrank : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 2 * S.card :=
    finrank_range_planeIdem K m S
  have hn : n₁ = S.card := by
    rw [hrank] at hn₁
    omega
  refine ⟨(MulEquiv.subgroupCongr hEq).trans ?_⟩
  exact hn ▸ iso

private theorem isPrimIdemIn_ext (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (m : ℕ) {e : PlaneRaw.V m} (he : e ≠ 0) :
    IsPrimIdemIn (extAlg ζ m e) (extEps m e) := by
  classical
  have hT : (PlaneRaw.Code.extSupport e).Nonempty := extSupport_nonempty he
  have hεid : IsIdempotentElem (extEps (K := K) m e) :=
    isIdempotentElem_planeIdem (K := K) m (PlaneRaw.Code.extSupport e)
  have hne : extEps (K := K) m e ≠ 0 := planeIdem_ne_zero hT
  have hsq : tauMat ζ m e * tauMat ζ m e + tauMat ζ m e = extEps m e :=
    tauMat_mul_self_add_extSupport (ζ := ζ) hK hζ m e
  have hbε : (extB ζ m e : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * extEps m e ≠
      extEps m e := extB_mul_extEps_ne hζ m he
  have hbidem : ¬ IsIdempotentElem (tauMat ζ m e * extEps m e) := by
    intro hid
    have h1 : tauMat ζ m e * (tauMat ζ m e * extEps m e) = tauMat ζ m e * extEps m e :=
      (tauMat_extEps_mul_self ζ m e).symm.trans hid.eq
    have hinv : (((extB ζ m e)⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * tauMat ζ m e = 1 := by
      change (((extB ζ m e)⁻¹ : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((extB ζ m e : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : tauMat ζ m e * extEps m e = extEps m e := by
      have h3 := congrArg (fun x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K =>
        (((extB ζ m e)⁻¹ : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * x) h1
      simp only [← Matrix.mul_assoc, hinv, Matrix.one_mul] at h3
      exact h3
    exact hbε h2
  have hsq2 : (extEps m e + tauMat ζ m e * extEps m e) *
      (extEps m e + tauMat ζ m e * extEps m e) = tauMat ζ m e * extEps m e :=
    extPair_sq hK hζ m e
  refine ⟨?_, hεid, hne, ?_⟩
  · have hb : tauMat ζ m e ∈ extAlg ζ m e :=
      Algebra.subset_adjoin ⟨extB ζ m e, by simp, rfl⟩
    rw [show extEps m e = tauMat ζ m e * tauMat ζ m e + tauMat ζ m e from hsq.symm]
    exact (extAlg ζ m e).add_mem ((extAlg ζ m e).mul_mem hb hb) hb
  · intro e' he' hidem hprod
    have hmemV : e' ∈ extV ζ m e := by
      have h := extV_stable (ζ := ζ) hK hζ m e e' he' (extEps m e)
        (Submodule.subset_span (by simp))
      rwa [hprod] at h
    obtain ⟨β, γ, hβγ⟩ := Submodule.mem_span_pair.mp hmemV
    have hβγ' : e' = β • extEps m e + γ • (tauMat ζ m e * extEps m e) := hβγ.symm
    rcases eq_zero_or_eq_one hK β with hβ | hβ <;>
      rcases eq_zero_or_eq_one hK γ with hγ | hγ
    · left
      rw [hβγ', hβ, hγ, zero_smul, zero_smul, add_zero]
    · exfalso
      have heq : e' = tauMat ζ m e * extEps m e := by
        rw [hβγ', hβ, hγ, zero_smul, one_smul, zero_add]
      exact hbidem (by rw [← heq]; exact hidem)
    · right
      rw [hβγ', hβ, hγ, zero_smul, one_smul, add_zero]
    · exfalso
      have heq : e' = extEps m e + tauMat ζ m e * extEps m e := by
        rw [hβγ', hβ, hγ, one_smul, one_smul]
      have hidem' : (extEps m e + tauMat ζ m e * extEps m e) *
          (extEps m e + tauMat ζ m e * extEps m e) =
            extEps m e + tauMat ζ m e * extEps m e := by
        rw [← heq]
        exact hidem.eq
      rw [hsq2] at hidem'
      have hzero : extEps (K := K) m e = 0 := by
        have h4 : extEps (K := K) m e + tauMat ζ m e * extEps (K := K) m e =
            0 + tauMat ζ m e * extEps (K := K) m e := by
          rw [zero_add]
          exact hidem'.symm
        exact add_right_cancel h4
      exact hne hzero

theorem exists_blockGroup_extension_mulEquiv (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V m} (he : e ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = 2 ^ 2 ∧
      Nonempty (↥(blockGroup ζ m (PlaneRaw.Code.extension e)) ≃*
        ↥(ClassicalBlocks.GUFull (PlaneRaw.Code.extSupport e).card 2 E)) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let b : GL (Fin m ⊕ Fin m) K := extB ζ m e
  let ε : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := extEps m e
  have hbSp : b ∈ StatedSp m K := (tau ζ m e).2
  have hodd : Odd (orderOf b) := tauGL_orderOf_odd ζ m e
  have hPrim : IsPrimIdemIn (extAlg ζ m e) ε := isPrimIdemIn_ext hK hζ m he
  have hPrimAdj : IsPrimAdjIdemIn (RingHom.id K)
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (extAlg ζ m e) ε := by
    refine ⟨hPrim.1, hPrim.2.1, hPrim.2.2.1, formAdj_planeIdem m (PlaneRaw.Code.extSupport e), ?_⟩
    intro e' he' hidem _ hprod
    exact hPrim.2.2.2 e' he' hidem hprod
  have hbε : (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * ε ≠ ε :=
    extB_mul_extEps_ne hζ m he
  have hEq : blockGroup ζ m (PlaneRaw.Code.extension e) =
      glBlockCentralizer (StatedSp m K).subtype ({b} :
        Set (GL (Fin m ⊕ Fin m) K)) ε := blockGroup_extension_eq ζ m e
  obtain ⟨d, m', E, hEfield, hEfin, hd1, hcard, hrank, hdeg, ⟨iso⟩⟩ :=
    ClassicalBlocks.blockGroup_iso_Sp_unitary (K := K) b hbSp hodd hPrimAdj hPrim hbε
  let : Field E := hEfield
  let : Fintype E := hEfin
  have : Finite E := Finite.of_fintype E
  have hrank2 : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) =
      2 * (PlaneRaw.Code.extSupport e).card :=
    finrank_range_planeIdem K m (PlaneRaw.Code.extSupport e)
  have hdeg2 : 2 * d ≤ 2 := by
    have hb := blockDegree_le_finrank_extV hK hζ m e
    change blockDegree (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin m ⊕ Fin m) K)))) ε ≤
        Module.finrank K (extV ζ m e) at hb
    rw [hdeg] at hb
    exact hb.trans (finrank_extV_le_two ζ m e)
  have hd : d = 1 := by omega
  have hm' : m' = (PlaneRaw.Code.extSupport e).card := by
    have h2 : 2 * m' = 2 * (PlaneRaw.Code.extSupport e).card := by
      rw [hd] at hrank
      norm_num at hrank
      rw [hrank, hrank2]
    omega
  have hcardK : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK]
  have hcardE : Nat.card E = 2 ^ 2 := by
    have h4 : Fintype.card E = 4 := by
      rw [hcard, hd, hcardK]
      norm_num
    rw [Nat.card_eq_fintype_card, h4]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow
    Nat.prime_two hcardE
  subst hm'
  subst hd
  rw [hcardK, pow_one] at iso
  refine ⟨E, inferInstance, inferInstance, inferInstance, hcardE, ?_⟩
  exact ⟨(MulEquiv.subgroupCongr hEq).trans iso⟩
