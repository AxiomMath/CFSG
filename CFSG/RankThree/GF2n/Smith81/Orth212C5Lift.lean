module

public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIBasic
public import CFSG.RankThree.GF2n.Smith81.Orth212C7

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.OrthC5

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {x : G}

theorem mem_normalizer_X (hs : Sit M Q Z X x) {m : G} (hmx : m * x * m⁻¹ = x) :
    m ∈ Subgroup.normalizer (X : Set G) := by
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have h1 : x ∈ conjSubgroup (m * g₀) Z := by
    rw [conjSubgroup_mul, ← hg₀, mem_conjSubgroup]
    have : m⁻¹ * x * m = x := by
      calc m⁻¹ * x * m = m⁻¹ * (m * x * m⁻¹) * m := by rw [hmx]
        _ = x := by group
    rw [this]
    exact hs.mem
  have h2 : x ∈ conjSubgroup g₀ Z := hg₀ ▸ hs.mem
  have h3 := conjSubgroup_eq_of_mem_ne_one hs.hyp hs.ne_one h1 h2
  rw [conjSubgroup_mul, ← hg₀] at h3
  exact conjSubgroup_eq_self_iff.mp h3

theorem conj_mem_D (hs : Sit M Q Z X x) {m : G} (hmM : m ∈ M) (hmx : m * x * m⁻¹ = x) {d : G}
    (hd : d ∈ Q ⊓ QB X) : m * d * m⁻¹ ∈ Q ⊓ QB X :=
  ⟨conj_mem_Q hs.hyp hmM hd.1, hs.normalizer_QB (mem_normalizer_X hs hmx) hd.2⟩

theorem exists_lift (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (h7 : Orth212C7CondStatement) (hD : Q ⊓ QB X ≠ ⊥)
    {g g' : Matrix (Fin 2) (Fin 2) C.K} {o o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hx : ActsAsTensor Q Z C.M₀ C.φ x g o) {s : G} (hsM : s ∈ M)
    (hsa : ActsAsTensor Q Z C.M₀ C.φ s g' o')
    (hcomm : ∀ p, orthTensor g o (orthTensor g' o' p) = orthTensor g' o' (orthTensor g o p)) :
    ∀ d ∈ Q ⊓ QB X, ∃ d' ∈ Q ⊓ QB X,
      C.φ (C.M₀.π d') = orthTensor g' o' (C.φ (C.M₀.π d)) := by
  have H := hc.ctx.hyp
  have hxM : x ∈ M := hs.memM
  have hxx : x * x = 1 := hs.x_sq
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hQs : ∀ y ∈ Q, s * y * s⁻¹ ∈ Q := fun y hy => conj_mem_Q H hsM hy
  have hQs' : ∀ y ∈ Q, s⁻¹ * y * s ∈ Q := fun y hy => by
    simpa using conj_mem_Q H (M.inv_mem hsM) hy
  have hQx : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun y hy => conj_mem_Q H hxM hy
  have hm₀M : x⁻¹ * (s * x * s⁻¹) ∈ M :=
    M.mul_mem (M.inv_mem hxM) (M.mul_mem (M.mul_mem hsM hxM) (M.inv_mem hsM))
  have hm₀Q : x⁻¹ * (s * x * s⁻¹) ∈ Q := by
    refine mem_Q_of_pi_conj_eq (M₀ := C.M₀) H hm₀M fun y hy => ?_
    apply C.φ.injective
    have hy₁ := hQs' y hy
    have hy₃ := hQx _ hy₁
    have ha := hQs _ hy₃
    have e1 : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    have hφa : C.φ (C.M₀.π (s * (x * (s⁻¹ * y * s) * x⁻¹) * s⁻¹)) =
        C.φ (C.M₀.π (x * y * x⁻¹)) := by
      calc C.φ (C.M₀.π (s * (x * (s⁻¹ * y * s) * x⁻¹) * s⁻¹))
          = orthTensor g' o' (C.φ (C.M₀.π (x * (s⁻¹ * y * s) * x⁻¹))) := hsa _ hy₃
        _ = orthTensor g' o' (orthTensor g o (C.φ (C.M₀.π (s⁻¹ * y * s)))) := by
          rw [hx _ hy₁]
        _ = orthTensor g o (orthTensor g' o' (C.φ (C.M₀.π (s⁻¹ * y * s)))) := (hcomm _).symm
        _ = orthTensor g o (C.φ (C.M₀.π (s * (s⁻¹ * y * s) * s⁻¹))) := by rw [hsa _ hy₁]
        _ = orthTensor g o (C.φ (C.M₀.π y)) := by rw [e1]
        _ = C.φ (C.M₀.π (x * y * x⁻¹)) := (hx y hy).symm
    have e2 : x⁻¹ * (s * x * s⁻¹) * y * (x⁻¹ * (s * x * s⁻¹))⁻¹ =
        x⁻¹ * (s * (x * (s⁻¹ * y * s) * x⁻¹) * s⁻¹) * x := by group
    have e3 : x * (x * y * x⁻¹) * x⁻¹ = y := by
      calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
        _ = y := by rw [hxx]; group
    rw [e2]
    have e4 : x⁻¹ * (s * (x * (s⁻¹ * y * s) * x⁻¹) * s⁻¹) * x =
        x * (s * (x * (s⁻¹ * y * s) * x⁻¹) * s⁻¹) * x⁻¹ := by rw [hxinv]
    rw [e4, hx _ ha, hφa, ← hx _ (hQx y hy), e3]
  obtain ⟨q', hq', e⟩ := h7 G M Q Z B hc X x hs hD s _ hm₀Q (by group)
  have hq'M : q' ∈ M := H.Q_normal.1 hq'
  have hmM : q'⁻¹ * s ∈ M := M.mul_mem (M.inv_mem hq'M) hsM
  have hmx : q'⁻¹ * s * x * (q'⁻¹ * s)⁻¹ = x := by
    calc q'⁻¹ * s * x * (q'⁻¹ * s)⁻¹ = q'⁻¹ * (s * x * s⁻¹) * q' := by group
      _ = q'⁻¹ * (q' * x * q'⁻¹) * q' := by rw [e]
      _ = x := by group
  intro d hd
  refine ⟨q'⁻¹ * s * d * (q'⁻¹ * s)⁻¹, conj_mem_D hs hmM hmx hd, ?_⟩
  have hw := hQs d hd.1
  have e5 : q'⁻¹ * s * d * (q'⁻¹ * s)⁻¹ = q'⁻¹ * (s * d * s⁻¹) * q'⁻¹⁻¹ := by group
  have := (ActsAsTensor.of_mem (M₀ := C.M₀) (φ := C.φ) (Q.inv_mem hq')) _ hw
  rw [orthTensor_one_id] at this
  rw [e5, this, hsa d hd.1]

theorem phi_pi_mem_Rsp (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (h4 : Orth212C4CondStatement) (h28 : Smith28OrthStatement)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hx : ActsAsTensor Q Z C.M₀ C.φ x g o) {d : G} (hd : d ∈ Q ⊓ QB X) :
    C.φ (C.M₀.π d) ∈ OrthCaseI.Rsp C g o := by
  have H := hc.ctx.hyp
  have hxM : x ∈ M := hs.memM
  have hxc : ∀ z ∈ Z, x * z * x⁻¹ = z := hs.x_cent (smith_1_12 hs)
  obtain ⟨T, hTπ, -, hTB⟩ := C.hD.linear_of_centralizes hxM hxc
  have hB : C.M₀.B.Nondegenerate := orth212C7_nondegenerate_of_alt C.M₀.alt C.M₀.nondeg
  have hperp := orth212C7_perp_ker_eq_range hB T.toLinearMap hTB
  have hmem : C.M₀.π d ∈ C.M₀.B.orthogonal (LinearMap.ker (T.toLinearMap - LinearMap.id)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro e he
    have hTe : T e = e := by simpa [sub_eq_zero] using he
    obtain ⟨w, hw, hwe⟩ := C.M₀.π_surj e
    have hwxQ : ⁅w, x⁆ ∈ Q := comm_mem_Q H hxM hw
    have hxwQ : x * w * x⁻¹ ∈ Q := conj_mem_Q H hxM hw
    have hπwx : C.M₀.π ⁅w, x⁆ = 0 := by
      have e1 : ⁅w, x⁆ = w * (x * w * x⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e1, C.M₀.π_mul w hw _ (Q.inv_mem hxwQ), Tim79.QuadModel.pi_inv C.M₀ hxwQ, hTπ w hw,
        hwe, hTe, add_neg_cancel]
    have hwxZ : ⁅w, x⁆ ∈ Z := (C.M₀.π_ker ⁅w, x⁆ hwxQ).mp hπwx
    have hθ : ⁅w, x⁆ = 1 := orth212C7_theta_zero h4 h28 hc hs hwxZ
    have hwx : w * x = x * w := commutatorElement_eq_one_iff_mul_comm.mp hθ
    have hwc : w ∈ Q ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨hw, Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hwx.symm⟩
    have hdw : d * w = w * d := (smith_1_13 hs).2.2.2.2 d hd w hwc
    have hwd : ⁅w, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hdw.symm
    have h0 := (GM.comm_eq_one_iff C.hD hw hd.1).mp hwd
    rw [hwe] at h0
    exact h0
  rw [hperp] at hmem
  obtain ⟨e', he'⟩ := LinearMap.mem_range.mp hmem
  obtain ⟨y, hy, rfl⟩ := C.M₀.π_surj e'
  have hTy : C.φ (C.M₀.π (x * y * x⁻¹)) = orthTensor g o (C.φ (C.M₀.π y)) := hx y hy
  have h1 : T (C.M₀.π y) - C.M₀.π y = C.M₀.π d := by simpa using he'
  refine ⟨C.φ (C.M₀.π y), ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, orthTensorLin_apply]
  calc orthTensor g o (C.φ (C.M₀.π y)) - C.φ (C.M₀.π y)
      = C.φ (C.M₀.π (x * y * x⁻¹)) - C.φ (C.M₀.π y) := by rw [hTy]
    _ = C.φ (T (C.M₀.π y) - C.M₀.π y) := by rw [hTπ y hy, map_sub]
    _ = C.φ (C.M₀.π d) := by rw [h1]

theorem sup_eq_of_image (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hx : ActsAsTensor Q Z C.M₀ C.φ x g o)
    (h1 : ∀ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) ∈ OrthCaseI.Rsp C g o)
    (h2 : ∀ r ∈ OrthCaseI.Rsp C g o, ∃ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) = r) :
    (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
  have H := hc.ctx.hyp
  rw [OrthCaseI.comm_sup_eq_preimSub hc C hs hx]
  apply le_antisymm
  · refine sup_le (fun d hd => ?_) (fun z hz => ?_)
    · exact OrthDT.mem_preimSub.mpr ⟨hd.1, h1 d hd⟩
    · refine OrthDT.mem_preimSub.mpr ⟨H.Z_normal.1 hz, ?_⟩
      rw [(C.M₀.π_ker z (H.Z_normal.1 hz)).mpr hz, map_zero]
      exact (OrthCaseI.Rsp C g o).zero_mem
  · intro y hy
    obtain ⟨hyQ, hyR⟩ := OrthDT.mem_preimSub.mp hy
    obtain ⟨d, hd, hdy⟩ := h2 _ hyR
    have hπ : C.M₀.π d = C.M₀.π y := C.φ.injective hdy
    have hz : d⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff C.M₀ hd.1 hyQ).mp hπ
    have : y = d * (d⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hd hz

theorem exists_phi_pi_ne_zero (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x) (hD : Q ⊓ QB X ≠ ⊥) :
    ∃ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) ≠ 0 := by
  obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  refine ⟨d, d.2, fun h0 => hd1 ?_⟩
  have hπ : C.M₀.π d = 0 := (map_eq_zero_iff C.φ C.φ.injective).mp h0
  have hdZ : (d : G) ∈ Z := (C.M₀.π_ker d d.2.1).mp hπ
  have hm : (d : G) ∈ Z ⊓ QB X := ⟨hdZ, d.2.2⟩
  rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hm
  exact Subtype.ext hm

end CFSG.RankThree.GF2n.Smith81.OrthC5
