module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

private theorem Ctx.layerT_transport (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T)
    {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = Nat.card Z)
    (φΩ : ↥(Rt M (LB M Q B) t) →* GL (Fin 3 ⊕ Fin 3) K')
    (hφΩ : φΩ.range = StatedOmega (StatedQuadPlus 3 K'))
    (hSA : SectionAct K' (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φΩ
      (fun g => (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K'))) :
    ∃ (θ : K ≃+* K') (Ψ : ↥T ≃+ (Fin 3 ⊕ Fin 3 → K')),
      (∀ (c : K) (w : ↥T), Ψ (c • w) = θ c • Ψ w) ∧
      (∀ (r : ↥(Rt M (LB M Q B) t))
        (hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈
          bar M Q (H0 M Z)), ∀ w ∈ T, φ ⟨_, hr⟩ w ∈ T) ∧
      ∀ (r : ↥(Rt M (LB M Q B) t))
        (hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈
          bar M Q (H0 M Z)) (w w' : ↥T), (w' : M₀.E) = φ ⟨_, hr⟩ w →
        Ψ w' = (φΩ r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ Ψ w := by
  classical
  obtain ⟨hRV, hZVn, ψ, hψ⟩ := hSA
  haveI := hZVn
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  have hVH : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans hRH)
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q Z0 :=
    (mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) := hVH hsbar
  have ha₀V : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
    Subgroup.mem_subgroupOf.mpr hsbar
  have ha₀1 : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  have hs2 : s ^ 2 ∈ Q := by
    have h := sq_eq_one_bar hc hs hZc hZ0 (QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩) hsbar
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hTset : (T : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    rw [← hT _ ha₀V ha₀1, range_opm_eq_image M₀ s (φ ⟨_, hsH⟩) hZQ (fun x hx => hQM s hsM x hx)
      (fun x hx => hφπ ⟨s, hsM⟩ hsH x hx) hs2, hZV G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ]
  have hπT : ∀ v ∈ Vt M (LB M Q B) B Z t, M₀.π v ∈ T := fun v hv => by
    have : M₀.π v ∈ (T : Set M₀.E) := by rw [hTset]; exact ⟨v, hv, rfl⟩
    exact this
  have hTπ : ∀ w ∈ T, ∃ v ∈ Vt M (LB M Q B) B Z t, M₀.π v = w := fun w hw => by
    have : w ∈ (T : Set M₀.E) := hw
    rw [hTset] at this
    exact this
  have hTVt : T = hc.VtSub hM t := by
    ext e
    rw [hc.mem_VtSub hM t, M₀.mem_img]
    constructor
    · intro he
      obtain ⟨v, hv, rfl⟩ := hTπ e he
      exact ⟨v, hv, hVQ hv, rfl⟩
    · rintro ⟨v, hv, -, rfl⟩
      exact hπT v hv
  subst hTVt
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(hc.VtSub hM t) ≃+ (Fin 3 ⊕ Fin 3 → K'),
      ∀ (v : ↥(Vt M (LB M Q B) B Z t)) (h : M₀.π v ∈ hc.VtSub hM t),
        Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) :=
    exists_addEquiv_imgSub M₀ hVQ (fun c _ he => hc.smul_mem_img_Vt hM t c he) ψ
  have hact : ∀ (r : ↥(Rt M (LB M Q B) t))
      (hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈ bar M Q (H0 M Z))
      (v : G), v ∈ Vt M (LB M Q B) B Z t →
        φ ⟨_, hr⟩ (M₀.π v) = M₀.π ((r : G) * v * (r : G)⁻¹) := fun r hr v hv =>
    (hφπ ⟨(r : G), hc.Rt_le_M t r.2⟩ hr v (hVQ hv)).symm
  have hRT : ∀ (r : ↥(Rt M (LB M Q B) t))
      (hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈ bar M Q (H0 M Z)),
      ∀ w ∈ hc.VtSub hM t, φ ⟨_, hr⟩ w ∈ hc.VtSub hM t := by
    intro r hr w hw
    obtain ⟨v, hv, rfl⟩ := hTπ w hw
    rw [hact r hr v hv]
    exact hπT _ ((Subgroup.mem_normalizer_iff.mp (hRV r.2) v).mp hv)
  have hint : ∀ (r : ↥(Rt M (LB M Q B) t))
      (hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈ bar M Q (H0 M Z))
      (w w' : ↥(hc.VtSub hM t)), (w' : M₀.E) = φ ⟨_, hr⟩ w →
        Ψ w' = (φΩ r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ Ψ w := by
    intro r hr w w' hw'
    obtain ⟨v, hv, hvw⟩ := hTπ w w.2
    have hrv : (r : G) * v * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hRV r.2) v).mp hv
    have e1 : w = ⟨M₀.π v, hπT v hv⟩ := Subtype.ext hvw.symm
    have e2 : w' = ⟨M₀.π ((r : G) * v * (r : G)⁻¹), hπT _ hrv⟩ := by
      apply Subtype.ext
      rw [hw', e1]
      exact hact r hr v hv
    have e3 : Ψ ⟨M₀.π ((r : G) * v * (r : G)⁻¹), hπT _ hrv⟩ =
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨_, hrv⟩)) := hΨ ⟨_, hrv⟩ _
    have e4 : Ψ ⟨M₀.π v, hπT v hv⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hv⟩)) :=
      hΨ ⟨v, hv⟩ _
    rw [e1, e2, e3, e4]
    exact hψ r ⟨v, hv⟩ ⟨_, hrv⟩ rfl
  have hcard : Nat.card K = Nat.card K' := hM.card.trans hK'.symm
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_of_scalar_commutant hcard
    (addCommutantScalar_statedOmegaPlus (K := K') (m := 3) (by norm_num)) Ψ (by
      intro c A hA v
      rw [← hφΩ] at hA
      obtain ⟨r, rfl⟩ := hA
      have hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈
          bar M Q (H0 M Z) :=
        bar_mono' hRH (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr r.2))
      obtain ⟨u, rfl⟩ : ∃ u, v = Ψ u := ⟨Ψ.symm v, (Ψ.apply_symm_apply v).symm⟩
      show Ψ (c • Ψ.symm ((φΩ r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ Ψ u)) =
        (φΩ r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ Ψ (c • Ψ.symm (Ψ u))
      have h1 : Ψ.symm ((φΩ r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ Ψ u) =
          ⟨φ ⟨_, hr⟩ u, hRT r hr u u.2⟩ := by
        apply Ψ.injective
        rw [AddEquiv.apply_symm_apply]
        exact (hint r hr u _ rfl).symm
      have h2 : c • (⟨φ ⟨_, hr⟩ u, hRT r hr u u.2⟩ : ↥(hc.VtSub hM t)) =
          ⟨φ ⟨_, hr⟩ ((c • u : ↥(hc.VtSub hM t)) : M₀.E), hRT r hr _ (c • u).2⟩ := by
        apply Subtype.ext
        simp
      rw [h1, h2, AddEquiv.symm_apply_apply]
      exact hint r hr (c • u) _ rfl)
  exact ⟨θ, Ψ, hθ, hRT, hint⟩

theorem Ctx.smul_of_comm_layerT (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T)
    {x : ↥(bar M Q (H0 M Z))} (hxT : ∀ w ∈ T, φ x w ∈ T)
    (hxR : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ T, φ x (φ r w) = φ r (φ x w)) :
    ∃ c : K, ∀ w ∈ T, φ x w = c • w := by
  classical
  obtain ⟨K', _, _, hK', φΩ, hφΩ, -, hSA⟩ := hp3
  obtain ⟨θ, Ψ, hθ, hRT, hint⟩ :=
    hc.layerT_transport hZcard hZc hZV hs hZ0 M₀ hM φ hφπ T hT hK' φΩ hφΩ hSA
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  let F : (Fin 3 ⊕ Fin 3 → K') →+ (Fin 3 ⊕ Fin 3 → K') :=
    { toFun := fun v => Ψ ⟨φ x (Ψ.symm v), hxT _ (Ψ.symm v).2⟩
      map_zero' := by
        have e : (⟨φ x ((Ψ.symm 0 : ↥T) : M₀.E), hxT _ (Ψ.symm 0).2⟩ : ↥T) = 0 := by
          apply Subtype.ext
          simp
        rw [e, map_zero]
      map_add' := fun v v' => by
        have e : (⟨φ x ((Ψ.symm (v + v') : ↥T) : M₀.E), hxT _ (Ψ.symm (v + v')).2⟩ : ↥T) =
            ⟨φ x (Ψ.symm v), hxT _ (Ψ.symm v).2⟩ + ⟨φ x (Ψ.symm v'), hxT _ (Ψ.symm v').2⟩ := by
          apply Subtype.ext
          simp
        rw [e, map_add] }
  have hF : ∀ v, F v = Ψ ⟨φ x (Ψ.symm v), hxT _ (Ψ.symm v).2⟩ := fun v => rfl
  obtain ⟨c', hc'⟩ := addCommutantScalar_statedOmegaPlus (K := K') (m := 3) (by norm_num) F (by
    intro A hA v
    rw [← hφΩ] at hA
    obtain ⟨r, rfl⟩ := hA
    have hr : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ ∈
        bar M Q (H0 M Z) :=
      bar_mono' hRH (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr r.2))
    have hrR : (⟨_, hr⟩ : ↥(bar M Q (H0 M Z))) ∈
        (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr r.2))
    set w := Ψ.symm v with hw
    have h1 : Ψ.symm ((φΩ r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ v) =
        ⟨φ ⟨_, hr⟩ w, hRT r hr w w.2⟩ := by
      apply Ψ.injective
      rw [AddEquiv.apply_symm_apply, hint r hr w ⟨φ ⟨_, hr⟩ w, hRT r hr w w.2⟩ rfl, hw,
        AddEquiv.apply_symm_apply]
    rw [hF, hF, h1]
    have h2 : (⟨φ x (φ ⟨_, hr⟩ w), hxT _ (hRT r hr w w.2)⟩ : ↥T) =
        ⟨φ ⟨_, hr⟩ (φ x w), hRT r hr _ (hxT _ w.2)⟩ :=
      Subtype.ext (hxR _ hrR w w.2)
    simp only
    rw [h2]
    exact hint r hr ⟨φ x w, hxT _ w.2⟩ _ rfl)
  refine ⟨θ.symm c', fun w hw => ?_⟩
  have h1 : Ψ ⟨φ x w, hxT w hw⟩ = c' • Ψ ⟨w, hw⟩ := by
    have := hc' (Ψ ⟨w, hw⟩)
    rw [hF, AddEquiv.symm_apply_apply] at this
    exact this
  have h2 : Ψ ⟨φ x w, hxT w hw⟩ = Ψ (θ.symm c' • (⟨w, hw⟩ : ↥T)) := by
    rw [h1, hθ, RingEquiv.apply_symm_apply]
  have h3 := congrArg Subtype.val (Ψ.injective h2)
  simpa using h3

theorem Ctx.eq_one_of_smul_layerT (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T)
    {r : ↥(bar M Q (H0 M Z))} (hr : r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))
    {c : K} (hrc : ∀ w ∈ T, φ r w = c • w) : c = 1 := by
  classical
  obtain ⟨K', _, _, hK', φΩ, hφΩ, -, hSA⟩ := hp3
  obtain ⟨θ, Ψ, hθ, hRT, hint⟩ :=
    hc.layerT_transport hZcard hZc hZV hs hZ0 M₀ hM φ hφπ T hT hK' φΩ hφΩ hSA
  obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hr)
  have hyR : (y : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hy
  set r₁ : ↥(Rt M (LB M Q B) t) := ⟨(y : G), hyR⟩ with hr₁
  have hr₁H : QuotientGroup.mk' (Q.subgroupOf M) ⟨(r₁ : G), hc.Rt_le_M t r₁.2⟩ ∈
      bar M Q (H0 M Z) := by
    have e : (⟨(r₁ : G), hc.Rt_le_M t r₁.2⟩ : ↥M) = y := Subtype.ext rfl
    rw [e, hyr]
    exact r.2
  have hrr : (⟨_, hr₁H⟩ : ↥(bar M Q (H0 M Z))) = r := by
    apply Subtype.ext
    have e : (⟨(r₁ : G), hc.Rt_le_M t r₁.2⟩ : ↥M) = y := Subtype.ext rfl
    show QuotientGroup.mk' (Q.subgroupOf M) ⟨(r₁ : G), hc.Rt_le_M t r₁.2⟩ = (r : Mbar M Q)
    rw [e, hyr]
  have hmat : ∀ v, (φΩ r₁ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ v = θ c • v := by
    intro v
    set w := Ψ.symm v with hw
    have hcw : (c • w : ↥T) = ⟨φ ⟨_, hr₁H⟩ w, hRT r₁ hr₁H w w.2⟩ := by
      apply Subtype.ext
      show c • (w : M₀.E) = φ ⟨_, hr₁H⟩ (w : M₀.E)
      rw [hrr, hrc w w.2]
    have h1 := hint r₁ hr₁H w ⟨φ ⟨_, hr₁H⟩ w, hRT r₁ hr₁H w w.2⟩ rfl
    rw [← hcw, hθ, hw, AddEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hmem : φΩ r₁ ∈ StatedOmega (StatedQuadPlus 3 K') := hφΩ ▸ ⟨r₁, rfl⟩
  set v₀ : Fin 3 ⊕ Fin 3 → K' := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 with hv₀
  have hpres := mem_statedOmega_preserves (Q := CFSG.LieType.Universal.Spin.quadPlus 3 K')
    (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K') hmem v₀
  have hQv₀ : CFSG.LieType.Universal.Spin.quadPlus 3 K' v₀ = 1 := by
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply, Fin.sum_univ_three, hv₀]
    simp [Pi.single_apply]
  rw [hmat, QuadraticMap.map_smul, hQv₀, smul_eq_mul, mul_one] at hpres
  obtain ⟨e', -, he, -⟩ := hc.hyp.cp
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'.trans he)
  have hθc : θ c = 1 := by
    have h2 : (θ c - 1) ^ 2 = 0 := by
      rw [sub_pow_char, one_pow, sq, hpres, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  rw [← θ.map_one] at hθc
  exact θ.injective hθc

end CFSG.RankThree.GF2n.Stroth80
