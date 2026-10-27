module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V} {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
  {I₁ I₂ : Subgroup (Vtil V₀ V hV)}
  {π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L)}
  {π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)}

private theorem s16k_quadPlus_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L)
    (v : Fin 4 ⊕ Fin 4 → K) :
    StatedQuadPlus 4 L (φ ∘ v) = φ (StatedQuadPlus 4 K v) := by
  simp only [StatedQuadPlus, Function.comp_apply, map_sum, map_mul]

private noncomputable def s16k_glCongrStatedOmega {K L : Type} [Field K] [Field L]
    (φ : K ≃+* L) :
    ↥(StatedOmega (StatedQuadPlus 4 K)) ≃* ↥(StatedOmega (StatedQuadPlus 4 L)) :=
  (MulEquiv.subgroupMap
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 4 ⊕ Fin 4) φ)
      (StatedOmega (StatedQuadPlus 4 K))).trans
    (MulEquiv.subgroupCongr
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega
        (QK := StatedQuadPlus 4 K) (QL := StatedQuadPlus 4 L) φ (s16k_quadPlus_map φ)))

private noncomputable def s16k_ringEquiv {K L : Type} [Field K] [Field L] [Finite K] [Finite L]
    (h : Nat.card K = Nat.card L) : K ≃+* L := by
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite L
  exact FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h)

private noncomputable def s16k_coordEquiv {K L : Type} [Field K] [Field L] (ψ : L ≃+* K) :
    Multiplicative (Fin 4 ⊕ Fin 4 → L) ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K) where
  toFun v := Multiplicative.ofAdd (ψ ∘ Multiplicative.toAdd v)
  invFun v := Multiplicative.ofAdd (ψ.symm ∘ Multiplicative.toAdd v)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [map_add]

private theorem s16k_coordEquiv_natAct {K L : Type} [Field K] [Field L] (ψ : L ≃+* K)
    (y : ↥(StatedOmega (StatedQuadPlus 4 L)))
    (v : Multiplicative (Fin 4 ⊕ Fin 4 → L)) :
    s16k_coordEquiv ψ (natAct (StatedOmega (StatedQuadPlus 4 L)) y v) =
      natAct (StatedOmega (StatedQuadPlus 4 K)) (s16k_glCongrStatedOmega ψ y)
        (s16k_coordEquiv ψ v) := by
  apply Multiplicative.toAdd.injective
  funext i
  have hcoe : (((s16k_glCongrStatedOmega ψ y : ↥(StatedOmega (StatedQuadPlus 4 K))) :
      Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      (((y : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) L) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L).map ψ) := by
    rw [show ((s16k_glCongrStatedOmega ψ y : ↥(StatedOmega (StatedQuadPlus 4 K))) :
        Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) =
        CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 4 ⊕ Fin 4) ψ
          (y : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) L) from rfl,
      CFSG.Adapters.RankTwoModelTransports.glCongr_coe]
  show ψ (Matrix.mulVec ((y : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) L) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) (Multiplicative.toAdd v) i) =
    Matrix.mulVec ((((s16k_glCongrStatedOmega ψ y : ↥(StatedOmega (StatedQuadPlus 4 K))) :
      Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K))
      (ψ ∘ Multiplicative.toAdd v) i
  rw [hcoe]
  exact RingHom.map_mulVec (ψ : L →+* K)
    ((y : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) L) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L)
    (Multiplicative.toAdd v) i

private theorem s16k_twistIso_transport {K L : Type} [Field K] [Field L] [Finite K] [Finite L]
    (ψ : L ≃+* K) {β : MulAut ↥(StatedOmega (StatedQuadPlus 4 L))} (hβ : S16kTwistIso 1 β) :
    S16kTwistIso 1
      ((s16k_glCongrStatedOmega ψ).symm.trans (β.trans (s16k_glCongrStatedOmega ψ))) := by
  obtain ⟨T₂, hT₂⟩ := hβ
  let ψvec := s16k_coordEquiv ψ
  refine ⟨(ψvec.symm.trans (T₂.trans ψvec)), fun x v => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w, ψvec w = v := ⟨ψvec.symm v, ψvec.apply_symm_apply v⟩
  have h1 : ψvec.symm
      (natAct (StatedOmega (StatedQuadPlus 4 K)) x (ψvec w)) =
      natAct (StatedOmega (StatedQuadPlus 4 L)) ((s16k_glCongrStatedOmega ψ).symm x) w := by
    have h := s16k_coordEquiv_natAct ψ ((s16k_glCongrStatedOmega ψ).symm x) w
    rw [MulEquiv.apply_symm_apply] at h
    calc ψvec.symm (natAct (StatedOmega (StatedQuadPlus 4 K)) x (ψvec w))
        = ψvec.symm (ψvec (natAct (StatedOmega (StatedQuadPlus 4 L))
            ((s16k_glCongrStatedOmega ψ).symm x) w)) := by rw [h]
      _ = natAct (StatedOmega (StatedQuadPlus 4 L))
            ((s16k_glCongrStatedOmega ψ).symm x) w := ψvec.symm_apply_apply _
  have h2 : T₂ (natAct (StatedOmega (StatedQuadPlus 4 L))
        ((s16k_glCongrStatedOmega ψ).symm x) w) =
      natAct (StatedOmega (StatedQuadPlus 4 L))
        (β ((s16k_glCongrStatedOmega ψ).symm x)) (T₂ w) := hT₂ _ _
  have h3 := s16k_coordEquiv_natAct ψ (β ((s16k_glCongrStatedOmega ψ).symm x)) (T₂ w)
  calc ψvec (T₂ (ψvec.symm (natAct (StatedOmega (StatedQuadPlus 4 K)) x (ψvec w))))
      = ψvec (T₂ (natAct (StatedOmega (StatedQuadPlus 4 L))
          ((s16k_glCongrStatedOmega ψ).symm x) w)) := by rw [h1]
    _ = ψvec (natAct (StatedOmega (StatedQuadPlus 4 L))
          (β ((s16k_glCongrStatedOmega ψ).symm x)) (T₂ w)) := by rw [h2]
    _ = natAct (StatedOmega (StatedQuadPlus 4 K))
          (s16k_glCongrStatedOmega ψ (β ((s16k_glCongrStatedOmega ψ).symm x)))
          (ψvec (T₂ w)) := h3
    _ = natAct (StatedOmega (StatedQuadPlus 4 K))
          ((s16k_glCongrStatedOmega ψ).symm.trans
            (β.trans (s16k_glCongrStatedOmega ψ)) x)
          ((ψvec.symm.trans (T₂.trans ψvec)) (ψvec w)) := by
      have hθ : ((s16k_glCongrStatedOmega ψ).symm.trans
            (β.trans (s16k_glCongrStatedOmega ψ)) x) =
          s16k_glCongrStatedOmega ψ (β ((s16k_glCongrStatedOmega ψ).symm x)) := rfl
      have hw : ((ψvec.symm.trans (T₂.trans ψvec)) (ψvec w)) = ψvec (T₂ w) := by
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hθ, hw]

private theorem s16k_map_fixV_le {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {s : MulAut V} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    (fixV H).map s.toMonoidHom ≤ fixV H := by
  rintro w ⟨v, hv, rfl⟩
  refine mem_fixV.2 fun x hx => ?_
  have hconj : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  have hxt : s⁻¹ * x * s ∈ H :=
    (Subgroup.mem_normalizer_iff.1 hs (s⁻¹ * x * s)).2 (hconj.symm ▸ hx)
  have h1 : x * s = s * (s⁻¹ * x * s) := by group
  calc x (s v) = (x * s) v := rfl
    _ = (s * (s⁻¹ * x * s)) v := by rw [h1]
    _ = s ((s⁻¹ * x * s) v) := rfl
    _ = s v := by rw [hv (s⁻¹ * x * s) hxt]

private theorem s16k_map_fixV_eq {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {s : MulAut V} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    (fixV H).map s.toMonoidHom = fixV H := by
  refine le_antisymm (s16k_map_fixV_le hs) ?_
  have hsin : s⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut V)) := Subgroup.inv_mem _ hs
  have hcomp : ((fixV H).map s⁻¹.toMonoidHom).map s.toMonoidHom = fixV H := by
    rw [Subgroup.map_map]
    have hone : s.toMonoidHom.comp s⁻¹.toMonoidHom = MonoidHom.id V := by ext v; simp
    rw [hone, Subgroup.map_id]
  calc fixV H = ((fixV H).map s⁻¹.toMonoidHom).map s.toMonoidHom := hcomp.symm
    _ ≤ (fixV H).map s.toMonoidHom := Subgroup.map_mono (s16k_map_fixV_le hsin)

private theorem s16k_secMapNat {K : Type} [Field K] [Finite K]
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedOmega (StatedQuadPlus 4 K)) →* ↥H}
    (hR : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).RealizesVia H U Z π) :
    ∃ f : ↥U →* Multiplicative (Fin 4 ⊕ Fin 4 → K),
      Function.Surjective f ∧ (∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K))) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        f ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          natAct (StatedOmega (StatedQuadPlus 4 K)) γ (f u) := by
  obtain ⟨f, hfs, hfk, hfi⟩ :=
    CFSG.Quasithin.FFC.RealizesVia.secMap
      (D := FFModel.nat (StatedOmega (StatedQuadPlus 4 K))) rfl hR
  have hsec : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).sec = ⊤ := rfl
  let qe : ↥(FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).sec ≃*
      Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    (MulEquiv.subgroupCongr hsec).trans
      (Subgroup.topEquiv (G := Multiplicative (Fin 4 ⊕ Fin 4 → K)))
  let f' : ↥U →* Multiplicative (Fin 4 ⊕ Fin 4 → K) := qe.toMonoidHom.comp f
  have hqe : ∀ x : ↥(FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).sec, qe x = x.1 :=
    fun x => rfl
  have hfs' : Function.Surjective f' := qe.surjective.comp hfs
  have hfk' : ∀ u : ↥U, f' u = 1 ↔ (u : V) ∈ Z := by
    intro u
    show qe (f u) = 1 ↔ (u : V) ∈ Z
    rw [MulEquiv.map_eq_one_iff]
    exact hfk u
  have hfi' : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K))) (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      f' ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
        natAct (StatedOmega (StatedQuadPlus 4 K)) γ (f' u) := by
    intro γ u hu
    change qe (f ⟨_, hu⟩) = natAct (StatedOmega (StatedQuadPlus 4 K)) γ (qe (f u))
    rw [hqe, hqe]
    exact hfi γ u hu
  exact ⟨f', hfs', hfk', hfi'⟩

private theorem s16k_injective_of_realizes {K : Type} [Field K] [Finite K]
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedOmega (StatedQuadPlus 4 K)) →* ↥H}
    (hR : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).RealizesVia H U Z π) :
    Function.Injective π := by
  obtain ⟨f, hfs, hfk, hfi⟩ := s16k_secMapNat hR
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply CFSG.Quasithin.FFModel.nat_faithful (StatedOmega (StatedQuadPlus 4 K)) γ
  intro m _
  obtain ⟨u, rfl⟩ := hfs m
  have hπ1 : ((π γ : ↥H) : MulAut V) = 1 := by rw [hγ]; rfl
  have hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := by rw [hπ1]; exact u.2
  have h2 : natAct (StatedOmega (StatedQuadPlus 4 K)) γ (f u) = f u := by
    have hsub : (⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ : ↥U) = u := by
      apply Subtype.ext
      change ((π γ : ↥H) : MulAut V) (u : V) = (u : V)
      rw [hπ1]
      rfl
    have h1 := hfi γ u hu
    rw [hsub] at h1
    exact h1.symm
  show natAct (StatedOmega (StatedQuadPlus 4 K)) γ (f u) * (f u)⁻¹ ∈
    (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).ker
  rw [h2, mul_inv_cancel]
  exact Subgroup.one_mem _

private theorem s16k_twistIso_of_realizes {K : Type} [Field K] [Finite K]
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedOmega (StatedQuadPlus 4 K)) →* ↥H}
    (hR : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).RealizesVia H U Z π)
    {t : MulAut V} (hZt : Z.map t.toMonoidHom = Z)
    (hU : U.map t.toMonoidHom = U)
    (α : MulAut ↥(StatedOmega (StatedQuadPlus 4 K)))
    (hα : ∀ x, (π (α x) : MulAut V) = t * (π x : MulAut V) * t⁻¹) :
    S16kTwistIso 1 α := by
  classical
  obtain ⟨f, hfs, hfk, hfi⟩ := s16k_secMapNat hR
  have hZt_le : Z.map t.toMonoidHom ≤ Z := hZt.le
  let tU : ↥U ≃* ↥U := (MulEquiv.subgroupMap t U).trans (MulEquiv.subgroupCongr hU)
  have htU_coe : ∀ u : ↥U, ((tU u : ↥U) : V) = t (u : V) := fun u => rfl
  have htUinv_coe : ∀ u : ↥U, ((tU⁻¹ u : ↥U) : V) = t⁻¹ (u : V) := fun u => rfl
  have hZtinv : Z.map t⁻¹.toMonoidHom = Z := by
    have h := congrArg (fun W : Subgroup V => W.map t⁻¹.toMonoidHom) hZt
    rw [Subgroup.map_map,
      show t⁻¹.toMonoidHom.comp t.toMonoidHom = MonoidHom.id V from by ext v; simp,
      Subgroup.map_id] at h
    exact h.symm
  have hker_eq : Z.subgroupOf U = f.ker := by
    ext u
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hfk u).symm
  have hmap : (Z.subgroupOf U).map tU.toMonoidHom = Z.subgroupOf U := by
    ext u
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      have hvu' : (u : V) = t (v : V) := by
        rw [← hvu]
        exact htU_coe v
      rw [hvu']
      exact hZt_le (Subgroup.mem_map.2 ⟨(v : V), hv, rfl⟩)
    · intro hu
      rw [Subgroup.mem_subgroupOf] at hu
      refine ⟨tU⁻¹ u, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf, htUinv_coe]
        rw [← hZtinv]
        exact Subgroup.mem_map.2 ⟨(u : V), hu, rfl⟩
      · simp
  let βq : (↥U ⧸ Z.subgroupOf U) ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have hβqmk : ∀ u : ↥U, βq (QuotientGroup.mk u) = f u := by
    intro u
    change (QuotientGroup.quotientKerEquivOfSurjective f hfs)
      ((QuotientGroup.quotientMulEquivOfEq hker_eq) (QuotientGroup.mk u)) = f u
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk (φ := f) u
  let tq : (↥U ⧸ Z.subgroupOf U) ≃* (↥U ⧸ Z.subgroupOf U) :=
    QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) tU hmap
  have htqmk : ∀ u : ↥U, tq (QuotientGroup.mk u) = QuotientGroup.mk (tU u) :=
    fun u => rfl
  let T : Multiplicative (Fin 4 ⊕ Fin 4 → K) ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    (βq.symm.trans tq).trans βq
  have hTf : ∀ u : ↥U, T (f u) = f (tU u) := by
    intro u
    rw [← hβqmk u]
    change βq (tq (βq.symm (βq (QuotientGroup.mk u)))) = f (tU u)
    rw [MulEquiv.symm_apply_apply, htqmk u, hβqmk (tU u)]
  refine ⟨T, fun x v => ?_⟩
  obtain ⟨u, rfl⟩ := hfs v
  have hu : ((π x : ↥H) : MulAut V) (u : V) ∈ U := hR.2.2.2.1 (π x) u u.2
  have hαmem : ((π (α x) : ↥H) : MulAut V) ((tU u : ↥U) : V) ∈ U :=
    hR.2.2.2.1 (π (α x)) (tU u) (tU u).2
  have hkey : ((tU ⟨((π x : ↥H) : MulAut V) (u : V), hu⟩ : ↥U) : V) =
      ((π (α x) : ↥H) : MulAut V) ((tU u : ↥U) : V) := by
    show t (((π x : ↥H) : MulAut V) (u : V)) =
      ((π (α x) : ↥H) : MulAut V) (t (u : V))
    rw [hα x]
    simp [MulAut.mul_apply]
  have hsub : (tU ⟨((π x : ↥H) : MulAut V) (u : V), hu⟩ : ↥U) =
      ⟨((π (α x) : ↥H) : MulAut V) ((tU u : ↥U) : V), hαmem⟩ := Subtype.ext hkey
  calc T (natAct (StatedOmega (StatedQuadPlus 4 K)) x (f u))
      = T (f ⟨((π x : ↥H) : MulAut V) (u : V), hu⟩) := by rw [hfi x u hu]
    _ = f (tU ⟨((π x : ↥H) : MulAut V) (u : V), hu⟩) := hTf _
    _ = f ⟨((π (α x) : ↥H) : MulAut V) ((tU u : ↥U) : V), hαmem⟩ := by rw [hsub]
    _ = natAct (StatedOmega (StatedQuadPlus 4 K)) (α x) (f (tU u)) := hfi (α x) (tU u) hαmem
    _ = natAct (StatedOmega (StatedQuadPlus 4 K)) (α x) (T (f u)) := by rw [hTf u]


theorem s16k_tri8_inner (hOut : S16kOmega8OutInner) (h : S16gRowCtx D V₀ V L hV)
    (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) {t : MulAut (Vtil V₀ V hV)}
    (ht : t ∈ Mbar D.M V₀ V hV) (hI₁ : I₁.map t.toMonoidHom = I₁)
    (hI₂ : I₂.map t.toMonoidHom = I₂) :
    ∃ l ∈ lBar V₀ V hV L, ∀ x ∈ lBar V₀ V hV L, t * x * t⁻¹ = l * x * l⁻¹ := by
  classical
  have hinj₁ : Function.Injective π₁ := s16k_injective_of_realizes hc.real₁
  have hinj₂ : Function.Injective π₂ := s16k_injective_of_realizes hc.real₂
  let e₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) ≃* ↥(lBar V₀ V hV L) :=
    MulEquiv.ofBijective π₁ ⟨hinj₁, hc.real₁.1⟩
  let e₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) ≃* ↥(lBar V₀ V hV L) :=
    MulEquiv.ofBijective π₂ ⟨hinj₂, hc.real₂.1⟩
  have htH : t ∈ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    h.mBar_le_normalizer ht
  have hZt : (fixV (lBar V₀ V hV L)).map t.toMonoidHom = fixV (lBar V₀ V hV L) :=
    s16k_map_fixV_eq htH
  have htHmap : (lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom = lBar V₀ V hV L := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      exact (Subgroup.mem_normalizer_iff.1 htH y).1 hy
    · intro hx
      refine ⟨t⁻¹ * x * t, ?_, ?_⟩
      · have hconj : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        exact (Subgroup.mem_normalizer_iff.1 htH (t⁻¹ * x * t)).2 (hconj.symm ▸ hx)
      · show MulAut.conj t (t⁻¹ * x * t) = x
        rw [MulAut.conj_apply]
        group
  let tL : MulAut ↥(lBar V₀ V hV L) :=
    (MulEquiv.subgroupMap (MulAut.conj t) (lBar V₀ V hV L)).trans
      (MulEquiv.subgroupCongr htHmap)
  have htL : ∀ y : ↥(lBar V₀ V hV L),
      ((tL y : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) =
        t * (y : MulAut (Vtil V₀ V hV)) * t⁻¹ := fun y => rfl
  let α : MulAut ↥(StatedOmega (StatedQuadPlus 4 K₁)) := (e₁.trans tL).trans e₁.symm
  let α₂ : MulAut ↥(StatedOmega (StatedQuadPlus 4 K₂)) := (e₂.trans tL).trans e₂.symm
  have hα₁ : ∀ x, (π₁ (α x) : MulAut (Vtil V₀ V hV)) =
      t * (π₁ x : MulAut (Vtil V₀ V hV)) * t⁻¹ := by
    intro x
    have h1 : e₁ (α x) = tL (e₁ x) := by
      show e₁ ((e₁.trans tL).trans e₁.symm x) = tL (e₁ x)
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [show π₁ (α x) = e₁ (α x) from rfl, h1]
    exact htL (e₁ x)
  have hα₂ : ∀ x, (π₂ (α₂ x) : MulAut (Vtil V₀ V hV)) =
      t * (π₂ x : MulAut (Vtil V₀ V hV)) * t⁻¹ := by
    intro x
    have h1 : e₂ (α₂ x) = tL (e₂ x) := by
      show e₂ ((e₂.trans tL).trans e₂.symm x) = tL (e₂ x)
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [show π₂ (α₂ x) = e₂ (α₂ x) from rfl, h1]
    exact htL (e₂ x)
  have hTwistα : S16kTwistIso 1 α :=
    s16k_twistIso_of_realizes hc.real₁ hZt hI₁ α hα₁
  have hTwistα₂ : S16kTwistIso 1 α₂ :=
    s16k_twistIso_of_realizes hc.real₂ hZt hI₂ α₂ hα₂
  let ψ : K₂ ≃+* K₁ := s16k_ringEquiv (hc.card₂.trans hc.card₁.symm)
  let Ψ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) ≃* ↥(StatedOmega (StatedQuadPlus 4 K₁)) :=
    s16k_glCongrStatedOmega ψ
  let e₂' : ↥(StatedOmega (StatedQuadPlus 4 K₁)) ≃* ↥(lBar V₀ V hV L) := Ψ.symm.trans e₂
  let θ : MulAut ↥(StatedOmega (StatedQuadPlus 4 K₁)) := e₁.trans e₂'.symm
  have hθα : Ψ.symm.trans (α₂.trans Ψ) = θ * α * θ⁻¹ := by
    refine MulEquiv.ext fun x => ?_
    change Ψ (α₂ (Ψ.symm x)) = θ (α (θ.symm x))
    dsimp only [α, α₂, θ, e₂']
    simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have hTwistθα : S16kTwistIso 1 (θ * α * θ⁻¹) := by
    rw [← hθα]
    exact s16k_twistIso_transport ψ hTwistα₂
  have hNotTwistθ : ¬ S16kTwistIso 1 θ := by
    rintro ⟨T, hT⟩
    apply hc.ne
    let A : Multiplicative (Fin 4 ⊕ Fin 4 → K₁) ≃*
        Multiplicative (Fin 4 ⊕ Fin 4 → K₂) := T.trans (s16k_coordEquiv ψ).symm
    refine ⟨A, fun m => ?_, fun m => ?_, fun γ₁ γ₂ hγ m => ?_⟩
    · exact ⟨fun _ => trivial, fun _ => trivial⟩
    · exact (MulEquiv.map_eq_one_iff A).symm
    · let γ₁' : ↥(StatedOmega (StatedQuadPlus 4 K₁)) := γ₁
      let γ₂' : ↥(StatedOmega (StatedQuadPlus 4 K₂)) := γ₂
      have hψvec : ∀ (y : ↥(StatedOmega (StatedQuadPlus 4 K₁)))
          (v : Multiplicative (Fin 4 ⊕ Fin 4 → K₂)),
          natAct (StatedOmega (StatedQuadPlus 4 K₂)) (Ψ.symm y) v =
            (s16k_coordEquiv ψ).symm
              (natAct (StatedOmega (StatedQuadPlus 4 K₁)) y ((s16k_coordEquiv ψ) v)) := by
        intro y v
        have h := s16k_coordEquiv_natAct ψ (Ψ.symm y) v
        rw [MulEquiv.apply_symm_apply] at h
        rw [← MulEquiv.symm_apply_apply (s16k_coordEquiv ψ)
          (natAct (StatedOmega (StatedQuadPlus 4 K₂)) (Ψ.symm y) v), h]
      have hγ' : γ₂' = Ψ.symm (θ γ₁') := by
        have h1 : θ γ₁' = Ψ γ₂' := by
          have h2 : e₁ γ₁' = e₂ γ₂' := by
            change π₁ γ₁' = π₂ γ₂'
            exact hγ
          change e₂'.symm (e₁ γ₁') = Ψ γ₂'
          rw [show e₂'.symm = e₂.symm.trans Ψ from rfl, MulEquiv.trans_apply, h2]
          simp
        exact ((Ψ.symm_apply_eq).2 h1).symm
      show (s16k_coordEquiv ψ).symm (T (natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ₁' m)) =
        natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂' ((s16k_coordEquiv ψ).symm (T m))
      change (s16k_coordEquiv ψ).symm (T (natAct (StatedOmega (StatedQuadPlus 4 K₁))
          ((1 : MulAut ↥(StatedOmega (StatedQuadPlus 4 K₁))) γ₁') m)) =
        natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂' ((s16k_coordEquiv ψ).symm (T m))
      rw [hT γ₁' m, hγ', hψvec (θ γ₁') ((s16k_coordEquiv ψ).symm (T m)),
        MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := hOut K₁ hc.card₁ α θ hTwistα hTwistθα hNotTwistθ
  refine ⟨e₁ g, (e₁ g).2, fun x' hx' => ?_⟩
  set y : ↥(lBar V₀ V hV L) := ⟨x', hx'⟩ with hy
  change t * (↑y : MulAut (Vtil V₀ V hV)) * t⁻¹ =
    ↑(e₁ g) * (↑y : MulAut (Vtil V₀ V hV)) * (↑(e₁ g))⁻¹
  rw [show y = e₁ (e₁.symm y) from (e₁.apply_symm_apply y).symm]
  calc t * (↑(e₁ (e₁.symm y)) : MulAut (Vtil V₀ V hV)) * t⁻¹ =
        ↑(e₁ (α (e₁.symm y))) := (hα₁ (e₁.symm y)).symm
    _ = ↑(e₁ (g * (e₁.symm y) * g⁻¹)) := by rw [hg (e₁.symm y)]
    _ = ↑(e₁ g) * ↑(e₁ (e₁.symm y)) * (↑(e₁ g))⁻¹ := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
