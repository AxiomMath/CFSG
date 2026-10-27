module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM2B
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95COrth

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Setup

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}

variable (M₀) in
theorem isQuadSpace_quadModel : IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩

structure SetupW (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    extends SetupV hc t M₀ φ where
  hVsq : ∀ v ∈ Vt M (LB M Q B) B Z t, v * v = 1

namespace SetupW

variable (S : SetupW hc t M₀ φ)

@[expose] noncomputable def Wsub : Submodule K M₀.E :=
  imgSub M₀ (Wt Q (Vt M (LB M Q B) B Z t))
    (fun c e he => smul_mem_img_Wt M₀ S.glob.reg (hc.Vt_le_Q t) c he)

@[expose] noncomputable def Vsub : Submodule K M₀.E :=
  imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c e he => hc.smul_mem_img_Vt S.glob t c he)

@[expose] noncomputable def VW : Submodule K ↥S.Wsub := S.Vsub.comap S.Wsub.subtype

abbrev Wq : Type := ↥S.Wsub ⧸ S.VW

@[expose] noncomputable def mkW : ↥S.Wsub →ₗ[K] S.Wq := S.VW.mkQ

theorem mem_Wsub {e : M₀.E} : e ∈ S.Wsub ↔ e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := Iff.rfl

theorem mem_Vsub {e : M₀.E} : e ∈ S.Vsub ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := Iff.rfl

theorem mkW_surjective : Function.Surjective S.mkW := Submodule.Quotient.mk_surjective _

theorem mkW_eq_zero_iff {w : S.Wsub} : S.mkW w = 0 ↔ (w : M₀.E) ∈ S.Vsub :=
  Submodule.Quotient.mk_eq_zero _

theorem mkW_eq_iff {w w' : S.Wsub} :
    S.mkW w = S.mkW w' ↔ (w : M₀.E) - w' ∈ S.Vsub := by
  rw [← sub_eq_zero, ← map_sub, mkW_eq_zero_iff]
  rfl

instance : Module.Finite K S.Wq := inferInstanceAs (Module.Finite K (↥S.Wsub ⧸ S.VW))

theorem B_Wsub_Vsub {w v : M₀.E} (hw : w ∈ S.Wsub) (hv : v ∈ S.Vsub) : M₀.B w v = 0 :=
  (mem_img_Wt_iff M₀ S.glob.reg (hc.Vt_le_Q t)).mp hw v hv

theorem B_Vsub_Wsub {w v : M₀.E} (hw : w ∈ S.Wsub) (hv : v ∈ S.Vsub) : M₀.B v w = 0 := by
  rw [(isQuadSpace_quadModel M₀).B_neg w v, S.B_Wsub_Vsub hw hv, neg_zero]

theorem Qf_Vsub {v : M₀.E} (hv : v ∈ S.Vsub) : M₀.Qf v = 0 := by
  obtain ⟨x, hxV, hxQ, rfl⟩ := S.mem_Vsub.mp hv
  rw [← M₀.sq_eq x hxQ, pow_two, S.hVsq x hxV]
  exact S.glob.reg.one

theorem Wsub_eq_orth : S.Wsub = M₀.B.orthogonal S.Vsub := by
  ext w
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hw v hv
    exact S.B_Vsub_Wsub hw hv
  · intro h
    refine S.mem_Wsub.mpr ((mem_img_Wt_iff M₀ S.glob.reg (hc.Vt_le_Q t)).mpr fun v hv => ?_)
    rw [(isQuadSpace_quadModel M₀).B_neg v w]
    have : M₀.B v w = 0 := h v hv
    rw [this, neg_zero]

theorem orth_Wsub : M₀.B.orthogonal S.Wsub = S.Vsub := by
  rw [S.Wsub_eq_orth]
  exact LinearMap.BilinForm.orthogonal_orthogonal (isQuadSpace_quadModel M₀).nondegenerate
    (LinearMap.BilinForm.IsAlt.isRefl M₀.alt) S.Vsub

@[expose] noncomputable def actWsub (r : ↥(Rt M (LB M Q B) t)) : S.Wsub →ₗ[K] S.Wsub :=
  LinearMap.restrict ((actM φ (r : G) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
    (fun w hw => S.actM_mem_W r.2 hw)

@[expose] noncomputable def actWq (r : ↥(Rt M (LB M Q B) t)) : S.Wq →ₗ[K] S.Wq :=
  S.VW.mapQ S.VW (S.actWsub r) (fun w hw => S.actM_mem_V r.2 hw)

theorem actWq_one : S.actWq 1 = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun w => ?_)
  show S.mkW (S.actWsub 1 w) = S.mkW w
  congr 1
  apply Subtype.ext
  show actM φ (((1 : ↥(Rt M (LB M Q B) t)) : ↥(Rt M (LB M Q B) t)) : G) w = w
  rw [Subgroup.coe_one, actM_one]
  rfl

theorem actWq_mul (r s : ↥(Rt M (LB M Q B) t)) : S.actWq (r * s) = S.actWq r ∘ₗ S.actWq s := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun w => ?_)
  show S.mkW (S.actWsub (r * s) w) = S.mkW (S.actWsub r (S.actWsub s w))
  congr 1
  apply Subtype.ext
  show actM φ ((r * s : ↥(Rt M (LB M Q B) t)) : G) w = actM φ (r : G) (actM φ (s : G) w)
  rw [Subgroup.coe_mul, actM_mul (hc.Rt_le_H0 t r.2) (hc.Rt_le_H0 t s.2)]
  rfl

@[expose] noncomputable def ActR (r : ↥(Rt M (LB M Q B) t)) : S.Wq ≃ₗ[K] S.Wq :=
  LinearEquiv.ofLinear (S.actWq r) (S.actWq r⁻¹)
    (by rw [← S.actWq_mul, mul_inv_cancel, S.actWq_one])
    (by rw [← S.actWq_mul, inv_mul_cancel, S.actWq_one])

@[expose] noncomputable def ActRhom : ↥(Rt M (LB M Q B) t) →* (S.Wq ≃ₗ[K] S.Wq) where
  toFun := S.ActR
  map_one' := LinearEquiv.ext fun x => by
    show S.actWq 1 x = x
    rw [S.actWq_one]
    rfl
  map_mul' r s := LinearEquiv.ext fun x => by
    show S.actWq (r * s) x = S.actWq r (S.actWq s x)
    rw [S.actWq_mul]
    rfl

theorem ActR_eq_one_of_rho_eq_one {r : ↥(Rt M (LB M Q B) t)} (hr : S.vd.ρ r = 1) :
    S.ActR r = 1 := by
  have hrN : (r : G) ∈ hc.CN t :=
    S.mem_CN_of_rhoV_eq_one r.2 (by rw [rhoV_of_mem S.vd r.2]; exact hr)
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  show S.mkW (S.actWsub r w) = S.mkW w
  rw [mkW_eq_iff]
  exact S.actM_sub_mem_V hrN w.2

@[expose] noncomputable def Act : SL(2, K) × SL(2, K) →* (S.Wq ≃ₗ[K] S.Wq) :=
  S.vd.ρ.liftOfSurjective S.vd.ρ_surj
    ⟨S.ActRhom, fun r hr =>
      MonoidHom.mem_ker.mpr (S.ActR_eq_one_of_rho_eq_one (MonoidHom.mem_ker.mp hr))⟩

theorem Act_rho (r : ↥(Rt M (LB M Q B) t)) : S.Act (S.vd.ρ r) = S.ActR r :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem Act_rho_mk (r : ↥(Rt M (LB M Q B) t)) (w : S.Wsub) :
    S.Act (S.vd.ρ r) (S.mkW w) = S.mkW (S.actWsub r w) := by
  rw [S.Act_rho]
  rfl

@[expose] noncomputable def BW : S.Wsub →ₗ[K] S.Wsub →ₗ[K] K :=
  M₀.B.compl₁₂ S.Wsub.subtype S.Wsub.subtype

@[expose] noncomputable def bwq : S.Wq →ₗ[K] S.Wq →ₗ[K] K :=
  LinearMap.liftQ₂ S.VW S.VW S.BW
    (fun v hv => LinearMap.mem_ker.mpr (LinearMap.ext fun w => S.B_Vsub_Wsub w.2 hv))
    (fun v hv => LinearMap.mem_ker.mpr (LinearMap.ext fun w => S.B_Wsub_Vsub w.2 hv))

theorem bwq_mk (w w' : S.Wsub) : S.bwq (S.mkW w) (S.mkW w') = M₀.B (w : M₀.E) (w' : M₀.E) :=
  rfl

theorem qf_congr {a b : S.Wsub} (h : (a : M₀.E) - b ∈ S.Vsub) :
    M₀.Qf (a : M₀.E) = M₀.Qf (b : M₀.E) := by
  have hab : (a : M₀.E) = b + ((a : M₀.E) - b) := by abel
  rw [hab, M₀.Qf_add, S.Qf_Vsub h, S.B_Wsub_Vsub b.2 h]
  ring

@[expose] noncomputable def qwq : S.Wq → K :=
  Quotient.lift (s := Submodule.quotientRel S.VW) (fun w : S.Wsub => M₀.Qf (w : M₀.E))
    (fun _ _ hab => S.qf_congr ((Submodule.quotientRel_def S.VW).mp hab))

theorem qwq_mk (w : S.Wsub) : S.qwq (S.mkW w) = M₀.Qf (w : M₀.E) := rfl

include S in
theorem qf_actM {g : G} (hg : g ∈ H0 M Z) (e : M₀.E) : M₀.Qf (actM φ g e) = M₀.Qf e := by
  rw [actM_of_mem hg]
  exact S.hφQf ⟨g, hg⟩ e

theorem bwq_alt (x : S.Wq) : S.bwq x x = 0 := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  exact M₀.alt (w : M₀.E)

theorem bwq_nondeg (x : S.Wq) (h : ∀ y, S.bwq x y = 0) : x = 0 := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  rw [mkW_eq_zero_iff, ← S.orth_Wsub, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have h2 : M₀.B (w : M₀.E) n = 0 := h (S.mkW ⟨n, hn⟩)
  show M₀.B n (w : M₀.E) = 0
  rw [(isQuadSpace_quadModel M₀).B_neg (w : M₀.E) n, h2, neg_zero]

theorem Act_bwq (γ : SL(2, K) × SL(2, K)) (x y : S.Wq) :
    S.bwq (S.Act γ x) (S.Act γ y) = S.bwq x y := by
  obtain ⟨r, rfl⟩ := S.vd.ρ_surj γ
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  obtain ⟨w', rfl⟩ := S.mkW_surjective y
  rw [S.Act_rho_mk, S.Act_rho_mk, bwq_mk, bwq_mk]
  exact (isQuadSpace_quadModel M₀).B_iso (actM φ (r : G)) (S.qf_actM (hc.Rt_le_H0 t r.2)) w w'

theorem qwq_smul (c : K) (x : S.Wq) : S.qwq (c • x) = c ^ 2 * S.qwq x := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  rw [← map_smul]
  exact M₀.Qf_smul c (w : M₀.E)

theorem qwq_add (x y : S.Wq) : S.qwq (x + y) = S.qwq x + S.qwq y + S.bwq x y := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  obtain ⟨w', rfl⟩ := S.mkW_surjective y
  rw [← map_add]
  exact M₀.Qf_add (w : M₀.E) (w' : M₀.E)

theorem Act_qwq (γ : SL(2, K) × SL(2, K)) (x : S.Wq) : S.qwq (S.Act γ x) = S.qwq x := by
  obtain ⟨r, rfl⟩ := S.vd.ρ_surj γ
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  rw [S.Act_rho_mk, qwq_mk, qwq_mk]
  exact S.qf_actM (hc.Rt_le_H0 t r.2) (w : M₀.E)

end SetupW

end Setup

end HS9

end CFSG.RankThree.GF2n.Stroth80
