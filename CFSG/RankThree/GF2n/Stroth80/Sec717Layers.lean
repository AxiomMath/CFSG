module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerOps
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

structure Sec717LayerData {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [Group X]
    (B : LinearMap.BilinForm K E) (φ : X →* (E ≃ₗ[K] E)) (V Nb Rb : Subgroup X)
    (T : Submodule K E) : Prop where
  nondeg : B.Nondegenerate
  refl : B.IsRefl
  isom : ∀ x u v, B (φ x u) (φ x v) = B u v
  inj : Function.Injective φ
  V_ne : ∃ a ∈ V, a ≠ 1
  range_V : ∀ a ∈ V, a ≠ 1 → LinearMap.range (opm (φ a)) = T
  ker_V : ∀ a ∈ V, a ≠ 1 → LinearMap.ker (opm (φ a)) = B.orthogonal T
  T_le : T ≤ B.orthogonal T
  Nb_low : ∀ n ∈ Nb, IsLayerLowering T (B.orthogonal T) (opm (φ n))
  V_corner : ∀ v ∈ V, IsLayerCorner T (B.orthogonal T) (opm (φ v))
  corner_mem : ∀ n ∈ Nb, IsLayerCorner T (B.orthogonal T) (opm (φ n)) → n ∈ V
  Rb_T : ∀ r ∈ Rb, ∀ w ∈ T, φ r w ∈ T
  Rb_P : ∀ r ∈ Rb, ∀ w ∈ B.orthogonal T, φ r w ∈ B.orthogonal T
  Rb_fix : ∀ r ∈ Rb, (∀ w ∈ T, φ r w = w) → r ∈ Nb
  finrank_T : Module.finrank K T = 6
  finrank_P : Module.finrank K (B.orthogonal T) = 14
  finrank_E : Module.finrank K E = 20

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem quadModel_isom_of_act {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) (hQH : Q ≤ H0 M Z) :
    ∀ x u v, M₀.B (φ x u) (φ x v) = M₀.B u v := by
  intro x u v
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  have hyx : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ x.2
  have hxy : x = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyx⟩ := Subtype.ext hy.symm
  have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hyx
  obtain ⟨a, haQ, rfl⟩ := M₀.π_surj u
  obtain ⟨b, hbQ, rfl⟩ := M₀.π_surj v
  have hyaQ := hQM y y.2 a haQ
  have hybQ := hQM y y.2 b hbQ
  rw [hxy, ← hφπ y hyx a haQ, ← hφπ y hyx b hbQ, ← M₀.comm_eq _ hyaQ _ hybQ,
    ← M₀.comm_eq _ haQ _ hbQ]
  have e : ⁅(y : G) * a * (y : G)⁻¹, (y : G) * b * (y : G)⁻¹⁆ = (y : G) * ⁅a, b⁆ * (y : G)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hz : ⁅a, b⁆ ∈ Z := M₀.comm_mem a haQ b hbQ
  have hc : ⁅a, b⁆ * (y : G) = (y : G) * ⁅a, b⁆ :=
    Subgroup.mem_centralizer_iff.mp hyH.2 _ hz
  have e2 : (y : G) * ⁅a, b⁆ * (y : G)⁻¹ = ⁅a, b⁆ := by
    rw [← hc]
    group
  rw [e, e2]

theorem quadModel_act_injective {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (H : StrothHyp M Q Z) (hM : GlobalModelData M Q Z γ M₀)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x)) (hQH : Q ≤ H0 M Z) :
    Function.Injective φ := by
  obtain ⟨φ₀, hφ₀π, hφ₀ker, -⟩ := exists_actionHom_H0 H hM
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  have hyx : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ x.2
  have hxy : x = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyx⟩ := Subtype.ext hy.symm
  have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hyx
  have h1 : φ₀ ⟨(y : G), hyH⟩ = 1 := by
    ext e
    obtain ⟨a, haQ, rfl⟩ := M₀.π_surj e
    rw [← hφ₀π ⟨(y : G), hyH⟩ a haQ, hφπ y hyx a haQ, ← hxy, hx]
  have hyQ : (y : G) ∈ Q := (hφ₀ker _).mp h1
  apply Subtype.ext
  show (x : Mbar M Q) = 1
  rw [← hy]
  exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyQ)

theorem Ctx.sec717LayerData (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZNc : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {L : Subgroup G} (hL : Sec717L hc t Z0 L) (hLn : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    Sec717LayerData M₀.B φ ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) T := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  have hVH : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans hRH)
  have Bs := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL hLn
  obtain ⟨hnd, hrefl, -⟩ := quadModel_form_facts M₀
  have hisom := quadModel_isom_of_act M₀ hQM φ hφπ hQH
  have hinj := quadModel_act_injective hc.hyp hM φ hφπ hQH
  obtain ⟨Tt, hTtR, hTtrank, hTtN, hTtR'⟩ :=
    Ctx.move_Tt_facts hZV hZc hZcard hc hs hp3 hZ0 M₀ hM.card φ hφπ
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q Z0 :=
    (mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) := hVH hsbar
  set a₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsH⟩ with ha₀
  have ha₀V : a₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hsbar
  have ha₀1 : a₀ ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  have hT1 : Tt 1 = T := by
    have h := hTtR 1 a₀ ha₀V ha₀1
    simp only [one_mul, inv_one, mul_one] at h
    rw [← h, hT a₀ ha₀V ha₀1]
  have hTa₀ : LinearMap.range (opm (φ a₀)) = T := hT a₀ ha₀V ha₀1
  have hs2 : s ^ 2 ∈ Q := by
    have h := sq_eq_one_bar hc hs hZc hZ0 (QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩) hsbar
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hTset : (T : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
    rw [← hTa₀, range_opm_eq_image M₀ s (φ a₀) hZQ (fun x hx => hQM s hsM x hx)
      (fun x hx => hφπ ⟨s, hsM⟩ hsH x hx) hs2, hZV G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ]
  have hπVt : ∀ v ∈ Vt M (LB M Q B) B Z t, M₀.π v ∈ T := fun v hv => by
    have : M₀.π v ∈ (T : Set M₀.E) := by rw [hTset]; exact ⟨v, hv, rfl⟩
    exact this
  have hNfix : ∀ x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ T, φ x w = w :=
    fun x hx w hw => hTtN x hx w (hT1 ▸ hw)
  have hker : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.ker (opm (φ a)) = M₀.B.orthogonal T := by
    intro a ha ha1
    rw [ker_opm_eq_orthogonal_range M₀.B hnd hrefl (φ a) (hisom a), hT a ha ha1]
  have hTle : T ≤ M₀.B.orthogonal T := by
    intro w hw
    rw [← hker a₀ ha₀V ha₀1, LinearMap.mem_ker, opm_apply, sub_eq_zero]
    exact hNfix a₀ (Bs.LN (Bs.VL ha₀V)) w hw
  have hmid : ∀ x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ e ∈ M₀.B.orthogonal T, opm (φ x) e ∈ T := by
    intro x hx e he
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
    have hkx : QuotientGroup.mk' (Q.subgroupOf M) k ∈ bar M Q (H0 M Z) := hk ▸ x.2
    have hxk : x = ⟨QuotientGroup.mk' (Q.subgroupOf M) k, hkx⟩ := Subtype.ext hk.symm
    have hkN : (k : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN k).mp (hk ▸ Subgroup.mem_subgroupOf.mp hx)
    obtain ⟨a, haQ, rfl⟩ := M₀.π_surj e
    have haW : a ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      refine Subgroup.mem_inf.mpr ⟨haQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hvQ : v ∈ Q := hVtQ hv
      have hB : M₀.B (M₀.π v) (M₀.π a) = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp he) _ (hπVt v hv)
      rw [← M₀.comm_eq v hvQ a haQ] at hB
      have h1 : ⁅v, a⁆ = 1 := hM.reg.inj _ (M₀.comm_mem v hvQ a haQ) hB
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hka : ⁅(k : G), a⁆ ∈ Vt M (LB M Q B) B Z t := sec7_N_comm_W_le_V h52a hA hc hs _ hkN a haW
    have hkaQ : (k : G) * a * (k : G)⁻¹ ∈ Q := hQM k k.2 a haQ
    have e1 : (k : G) * a * (k : G)⁻¹ = ⁅(k : G), a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [hxk, opm_apply, ← hφπ k hkx a haQ, e1, M₀.π_mul _ (hVtQ hka) _ haQ, add_sub_cancel_right]
    exact hπVt _ hka
  have hNlow : ∀ x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      IsLayerLowering T (M₀.B.orthogonal T) (opm (φ x)) := by
    intro x hx
    refine ⟨fun e => ?_, hmid x hx, fun w hw => ?_⟩
    · rw [opm_apply]
      exact sub_mem_orthogonal_of_fixes M₀.B (φ x) (hisom x) T (hNfix x hx) e
    · rw [opm_apply, hNfix x hx w hw, sub_self]
  have hVcorner : ∀ v ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
      IsLayerCorner T (M₀.B.orthogonal T) (opm (φ v)) := by
    intro v hv
    by_cases hv1 : v = 1
    · subst hv1
      refine ⟨fun e => ?_, fun e _ => ?_⟩ <;> simp [opm_apply]
    · refine ⟨fun e => ?_, fun e he => ?_⟩
      · rw [← hT v hv hv1]
        exact LinearMap.mem_range_self _ e
      · rw [← hker v hv hv1] at he
        exact LinearMap.mem_ker.mp he
  have hRV : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        r * a * r⁻¹ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
    intro r hr a ha
    have hrK := Bs.RK hr
    rw [Bs.K_eq] at hrK
    exact (Subgroup.mem_normalizer_iff.mp hrK a).mp ha
  have hRT : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ T, φ r w ∈ T := by
    intro r hr w hw
    rw [← hTa₀] at hw
    obtain ⟨e, rfl⟩ := hw
    have hconj : r * a₀ * r⁻¹ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := hRV r hr a₀ ha₀V
    have hconj1 : r * a₀ * r⁻¹ ≠ 1 := by
      intro h
      apply ha₀1
      have : a₀ = r⁻¹ * (r * a₀ * r⁻¹) * r := by group
      rw [this, h]
      group
    have h1 : φ r (opm (φ a₀) e) = opm (φ (r * a₀ * r⁻¹)) (φ r e) := by
      rw [opm_conj, phi_inv_apply_phi]
    rw [h1, ← hT _ hconj hconj1]
    exact LinearMap.mem_range_self _ _
  have hRP : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ M₀.B.orthogonal T, φ r w ∈ M₀.B.orthogonal T := by
    intro r hr w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hu' : φ r⁻¹ u ∈ T := hRT r⁻¹ (Subgroup.inv_mem _ hr) u hu
    have e : u = φ r (φ r⁻¹ u) := (phi_apply_inv_apply φ r u).symm
    rw [e, hisom]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) _ hu'
  have hn10 : n = 10 := by
    have hcN78 := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (by norm_num) (Or.inl hp3)
    unfold Conc78 at hcN78
    rcases hcN78 with ⟨-, h10, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
    · exact h10
    all_goals omega
  have hq : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  haveI := Fintype.ofFinite K
  haveI : Finite M₀.E := Module.finite_of_finite K
  haveI : Fintype M₀.E := Fintype.ofFinite _
  have hfinE : Module.finrank K M₀.E = 20 := by
    have himg := natCard_image_pi M₀ (W := Q) le_rfl hZQ
    have huniv : M₀.π '' (Q : Set G) = Set.univ := by
      ext e
      simp only [Set.mem_image, SetLike.mem_coe, Set.mem_univ, iff_true]
      exact M₀.π_surj e
    rw [huniv, Nat.card_univ, hs.toSec5.width, hn10] at himg
    have hE : Nat.card M₀.E * Nat.card Z = Nat.card Z ^ 20 * Nat.card Z := by
      rw [himg]
      ring
    have hE' := Nat.eq_of_mul_eq_mul_right Nat.card_pos hE
    have h6 := Module.card_eq_pow_finrank (K := K) (V := M₀.E)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := K), hE', hM.card] at h6
    exact (Nat.pow_right_injective hq h6).symm
  have hfinT : Module.finrank K T = 6 := by
    rw [← hT1]
    exact hTtrank 1
  refine
    { nondeg := hnd
      refl := hrefl
      isom := hisom
      inj := hinj
      V_ne := ⟨a₀, ha₀V, ha₀1⟩
      range_V := hT
      ker_V := hker
      T_le := hTle
      Nb_low := hNlow
      V_corner := hVcorner
      corner_mem := fun x hx hcorner => ?_
      Rb_T := hRT
      Rb_P := hRP
      Rb_fix := fun r hr hfix => hTtR' r hr (fun w hw => hfix w (hT1 ▸ hw))
      finrank_T := hfinT
      finrank_P := ?_
      finrank_E := hfinE }
  · refine Bs.ZN x hx fun y hy => ?_
    have h1 := commutator_eq_one_of_corner hTle (hNlow y hy) hcorner
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_one φ] at h1
    have h2 := hinj h1
    have h3 : y * x = x * y := by
      have : y * x * y⁻¹ * x⁻¹ * (x * y) = x * y := by rw [h2, one_mul]
      calc y * x = y * x * y⁻¹ * x⁻¹ * (x * y) := by group
        _ = x * y := this
    exact h3.symm
  · rw [LinearMap.BilinForm.finrank_orthogonal hnd, hfinE, hfinT]

end CFSG.RankThree.GF2n.Stroth80
