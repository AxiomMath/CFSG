module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1
public import CFSG.RankThree.GF2n.Stroth80.Sec12LBFlag
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat
public import CFSG.RankThree.GF2n.Stroth80.Sec92Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Setup

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
  {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]

structure Setup95 (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (Y₁ Y₂ : Type) [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂] where
  glob : GlobalModelData M Q Z γ M₀
  hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)
  hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q
  hφQf : ∀ (m : H0 M Z) (e : M₀.E), M₀.Qf (φ m e) = M₀.Qf e
  hWV : ∀ s ∈ hc.CN t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t
  ht : t ∈ LB M Q B
  desc : ModDesc95 hc t M₀ φ Y₁ Y₂

open _root_.Classical in
@[expose] noncomputable def actM (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (g : G) :
    M₀.E ≃ₗ[K] M₀.E :=
  if hg : g ∈ H0 M Z then φ ⟨g, hg⟩ else 1

open _root_.Classical in
@[expose] noncomputable def rhoM (D : ModDesc95 hc t M₀ φ Y₁ Y₂) (g : G) :
    SL(2, K) × SL(2, K) :=
  if hg : g ∈ Rt M (LB M Q B) t then D.ρ ⟨g, hg⟩ else 1

theorem actM_of_mem {g : G} (hg : g ∈ H0 M Z) : actM φ g = φ ⟨g, hg⟩ := dif_pos hg

theorem actM_one : actM φ (1 : G) = 1 := by
  rw [actM_of_mem (H0 M Z).one_mem]
  exact map_one φ

theorem actM_mul {g h : G} (hg : g ∈ H0 M Z) (hh : h ∈ H0 M Z) :
    actM φ (g * h) = actM φ g * actM φ h := by
  rw [actM_of_mem hg, actM_of_mem hh, actM_of_mem ((H0 M Z).mul_mem hg hh)]
  exact map_mul φ ⟨g, hg⟩ ⟨h, hh⟩

theorem actM_inv {g : G} (hg : g ∈ H0 M Z) : actM φ g⁻¹ = (actM φ g)⁻¹ := by
  rw [actM_of_mem hg, actM_of_mem ((H0 M Z).inv_mem hg)]
  exact map_inv φ ⟨g, hg⟩

theorem rhoM_of_mem (D : ModDesc95 hc t M₀ φ Y₁ Y₂) {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    rhoM D g = D.ρ ⟨g, hg⟩ := dif_pos hg

theorem rhoM_one (D : ModDesc95 hc t M₀ φ Y₁ Y₂) : rhoM D (1 : G) = 1 := by
  rw [rhoM_of_mem D (Rt M (LB M Q B) t).one_mem]
  exact map_one D.ρ

theorem rhoM_mul (D : ModDesc95 hc t M₀ φ Y₁ Y₂) {g h : G} (hg : g ∈ Rt M (LB M Q B) t)
    (hh : h ∈ Rt M (LB M Q B) t) : rhoM D (g * h) = rhoM D g * rhoM D h := by
  rw [rhoM_of_mem D hg, rhoM_of_mem D hh, rhoM_of_mem D ((Rt M (LB M Q B) t).mul_mem hg hh)]
  exact map_mul D.ρ ⟨g, hg⟩ ⟨h, hh⟩

theorem rhoM_inv (D : ModDesc95 hc t M₀ φ Y₁ Y₂) {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    rhoM D g⁻¹ = (rhoM D g)⁻¹ := by
  rw [rhoM_of_mem D hg, rhoM_of_mem D ((Rt M (LB M Q B) t).inv_mem hg)]
  exact map_inv D.ρ ⟨g, hg⟩

theorem actM_conj_apply {g n : G} (hg : g ∈ H0 M Z) (hn : n ∈ H0 M Z) (e : M₀.E) :
    actM φ (g * n * g⁻¹) (actM φ g e) = actM φ g (actM φ n e) := by
  rw [actM_mul ((H0 M Z).mul_mem hg hn) ((H0 M Z).inv_mem hg), actM_mul hg hn, actM_inv hg]
  show (actM φ g) ((actM φ n) ((actM φ g)⁻¹ ((actM φ g) e))) = (actM φ g) ((actM φ n) e)
  rw [show (actM φ g)⁻¹ ((actM φ g) e) = e from (actM φ g).symm_apply_apply e]

namespace Setup95

variable (S : Setup95 hc t M₀ φ Y₁ Y₂)

include S

theorem pi_conj {g : G} (hg : g ∈ H0 M Z) {x : G} (hx : x ∈ Q) :
    M₀.π (g * x * g⁻¹) = actM φ g (M₀.π x) := by
  rw [actM_of_mem hg]
  exact S.hφπ ⟨g, hg⟩ x hx

theorem actM_eq_one_of_mem_Q {q : G} (hq : q ∈ Q) : actM φ q = 1 := by
  rw [actM_of_mem (hc.Q_le_H0 hq)]
  exact (S.hφQ _).mpr hq

theorem pi_eq_zero_iff {x : G} (hx : x ∈ Q) : M₀.π x = 0 ↔ x ∈ Z := M₀.π_ker x hx

@[expose] noncomputable def Wsub : Submodule K M₀.E :=
  imgSub M₀ (Wt Q (Vt M (LB M Q B) B Z t))
    (fun c e he => smul_mem_img_Wt M₀ S.glob.reg (hc.Vt_le_Q t) c he)

theorem exists_sec : ∃ s : (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] M₀.E,
    ∀ y, s y ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) ∧ S.desc.cW (s y) = y := by
  let f : S.Wsub →ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂) := S.desc.cW.comp S.Wsub.subtype
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨w, hw, hcw⟩ := S.desc.cW_surj y
    exact ⟨⟨w, hw⟩, hcw⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f hf
  refine ⟨S.Wsub.subtype.comp g, fun y => ⟨(g y).2, ?_⟩⟩
  have := LinearMap.congr_fun hg y
  simpa [f] using this

@[expose] noncomputable def sec : (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] M₀.E :=
  Classical.choose S.exists_sec

theorem sec_mem (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    S.sec y ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) :=
  (Classical.choose_spec S.exists_sec y).1

theorem cW_sec (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) : S.desc.cW (S.sec y) = y :=
  (Classical.choose_spec S.exists_sec y).2

@[expose] noncomputable def theta (n : G) :
    (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  S.desc.cV ∘ₗ (((actM φ n : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) ∘ₗ S.sec

theorem theta_eq (n : G) (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    S.theta n y = S.desc.cV (actM φ n (S.sec y) - S.sec y) := by
  simp [theta]

theorem actM_fix_V {n : G} (hn : n ∈ hc.CN t) {e : M₀.E}
    (he : e ∈ M₀.img (Vt M (LB M Q B) B Z t)) : actM φ n e = e := by
  obtain ⟨v, hvV, hvQ, rfl⟩ := he
  have hnH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hn)
  have hcomm : ⁅n, v⁆ ∈ Z := (Ctx.mem_CN.mp hn).2 v hvV
  have hcommQ : ⁅n, v⁆ ∈ Q := hc.Z_le_Q hcomm
  have e1 : n * v * n⁻¹ = ⁅n, v⁆ * v := by simp only [commutatorElement_def]; group
  rw [← S.pi_conj hnH hvQ, e1, M₀.π_mul _ hcommQ _ hvQ, (S.pi_eq_zero_iff hcommQ).mpr hcomm,
    zero_add]

theorem actM_sub_mem_V {n : G} (hn : n ∈ hc.CN t) {e : M₀.E}
    (he : e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t))) :
    actM φ n e - e ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
  obtain ⟨x, hxW, hxQ, rfl⟩ := he
  have hnH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hn)
  have hcomm : ⁅n, x⁆ ∈ Vt M (LB M Q B) B Z t := S.hWV n hn x hxW
  have hcommQ : ⁅n, x⁆ ∈ Q := hc.Vt_le_Q t hcomm
  have e1 : n * x * n⁻¹ = ⁅n, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [← S.pi_conj hnH hxQ, e1, M₀.π_mul _ hcommQ _ hxQ]
  have : M₀.π ⁅n, x⁆ + M₀.π x - M₀.π x = M₀.π ⁅n, x⁆ := by abel
  rw [this]
  exact M₀.pi_mem_img hcomm hcommQ

theorem theta_apply {n : G} (hn : n ∈ hc.CN t) {w : M₀.E}
    (hw : w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t))) :
    S.theta n (S.desc.cW w) = S.desc.cV (actM φ n w - w) := by
  have h1 : w - S.sec (S.desc.cW w) ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
    have hmem : w - S.sec (S.desc.cW w) ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) :=
      (M₀.img (Wt Q (Vt M (LB M Q B) B Z t))).sub_mem hw (S.sec_mem _)
    rw [← S.desc.cW_ker _ hmem, map_sub, S.cW_sec, sub_self]
  have h2 := S.actM_fix_V hn h1
  rw [map_sub] at h2
  rw [theta_eq]
  congr 1
  have h3 := (sub_eq_sub_iff_sub_eq_sub.mp h2).symm
  exact h3

theorem theta_one : S.theta 1 = 0 := by
  refine LinearMap.ext fun y => ?_
  rw [theta_eq, actM_one]
  simp

theorem theta_mul {n m : G} (hn : n ∈ hc.CN t) (hm : m ∈ hc.CN t) :
    S.theta (n * m) = S.theta n + S.theta m := by
  refine LinearMap.ext fun y => ?_
  have hnH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hn)
  have hmH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hm)
  have hwW := S.sec_mem y
  have h1 := S.actM_sub_mem_V hm hwW
  have h2 := S.actM_fix_V hn h1
  rw [map_sub] at h2
  rw [LinearMap.add_apply, theta_eq, theta_eq, theta_eq, actM_mul hnH hmH, ← map_add]
  congr 1
  have h3 : (actM φ n * actM φ m) (S.sec y) = actM φ n (actM φ m (S.sec y)) := rfl
  rw [h3]
  calc actM φ n (actM φ m (S.sec y)) - S.sec y
      = (actM φ n (actM φ m (S.sec y)) - actM φ n (S.sec y)) + (actM φ n (S.sec y) - S.sec y) := by
        abel
    _ = (actM φ m (S.sec y) - S.sec y) + (actM φ n (S.sec y) - S.sec y) := by rw [h2]
    _ = (actM φ n (S.sec y) - S.sec y) + (actM φ m (S.sec y) - S.sec y) := add_comm _ _

theorem actM_mem_W {g : G} (hg : g ∈ Rt M (LB M Q B) t) {w : M₀.E}
    (hw : w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t))) :
    actM φ g w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := by
  obtain ⟨x, hxW, hxQ, rfl⟩ := hw
  have hgH := hc.Rt_le_H0 t hg
  rw [← S.pi_conj hgH hxQ]
  have hx' := sec9_conj_mem_Wt hc S.ht hg hxW
  exact M₀.pi_mem_img hx' hx'.1

theorem actM_mem_V {g : G} (hg : g ∈ Rt M (LB M Q B) t) {e : M₀.E}
    (he : e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    actM φ g e ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
  obtain ⟨x, hxV, hxQ, rfl⟩ := he
  have hgH := hc.Rt_le_H0 t hg
  rw [← S.pi_conj hgH hxQ]
  have hx' : g * x * g⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt S.ht hg) x).mp hxV
  exact M₀.pi_mem_img hx' (hc.Vt_le_Q t hx')

theorem theta_conj {n g : G} (hn : n ∈ hc.CN t) (hg : g ∈ Rt M (LB M Q B) t)
    (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    S.theta (g * n * g⁻¹) (M1.actW ((rhoM S.desc g).1 : Matrix (Fin 2) (Fin 2) K)
        ((rhoM S.desc g).2 : Matrix (Fin 2) (Fin 2) K) y) =
      ((rhoM S.desc g).1 : Matrix (Fin 2) (Fin 2) K) * S.theta n y *
        ((rhoM S.desc g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have hgH := hc.Rt_le_H0 t hg
  have hnH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hn)
  have hgnN : g * n * g⁻¹ ∈ hc.CN t := hc.CN_conj_mem S.ht hg hn
  have hwW := S.sec_mem y
  have hgw : actM φ g (S.sec y) ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := S.actM_mem_W hg hwW
  have hact := S.desc.cW_act ⟨g, hg⟩ (S.sec y) hwW
  have harg : M1.actW ((rhoM S.desc g).1 : Matrix (Fin 2) (Fin 2) K)
      ((rhoM S.desc g).2 : Matrix (Fin 2) (Fin 2) K) y = S.desc.cW (actM φ g (S.sec y)) := by
    rw [actM_of_mem hgH, rhoM_of_mem S.desc hg]
    have e1 : M1.actW ((S.desc.ρ ⟨g, hg⟩).1 : Matrix (Fin 2) (Fin 2) K)
        ((S.desc.ρ ⟨g, hg⟩).2 : Matrix (Fin 2) (Fin 2) K) (S.desc.cW (S.sec y)) =
        S.desc.cW ((φ ⟨g, hgH⟩) (S.sec y)) := hact.symm
    rw [S.cW_sec y] at e1
    exact e1
  have hV := S.actM_sub_mem_V hn hwW
  have hcv := S.desc.cV_act ⟨g, hg⟩ _ hV
  rw [harg, S.theta_apply hgnN hgw, actM_conj_apply hgH hnH, ← map_sub, theta_eq,
    rhoM_of_mem S.desc hg]
  rw [actM_of_mem hgH]
  exact hcv

theorem theta_comm {n g : G} (hn : n ∈ hc.CN t) (hg : g ∈ Rt M (LB M Q B) t)
    (hcomm : ⁅g, n⁆ ∈ Q) (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    S.theta n (M1.actW ((rhoM S.desc g).1 : Matrix (Fin 2) (Fin 2) K)
        ((rhoM S.desc g).2 : Matrix (Fin 2) (Fin 2) K) y) =
      ((rhoM S.desc g).1 : Matrix (Fin 2) (Fin 2) K) * S.theta n y *
        ((rhoM S.desc g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have hnH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hn)
  have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by simp only [commutatorElement_def]; group
  have h1 : actM φ (g * n * g⁻¹) = actM φ n := by
    rw [e, actM_mul (hc.Q_le_H0 hcomm) hnH, S.actM_eq_one_of_mem_Q hcomm, one_mul]
  have hth : S.theta (g * n * g⁻¹) = S.theta n := by
    unfold theta
    rw [h1]
  have := S.theta_conj hn hg y
  rwa [hth] at this

theorem rhoM_eq_one_of_fix [CharP K 2] {g : G} (hg : g ∈ Rt M (LB M Q B) t)
    (hfix : ∀ e ∈ M₀.img (Vt M (LB M Q B) B Z t), actM φ g e = e) : rhoM S.desc g = 1 := by
  have hgH := hc.Rt_le_H0 t hg
  have hX : ∀ X : Matrix (Fin 2) (Fin 2) K,
      ((rhoM S.desc g).1 : Matrix (Fin 2) (Fin 2) K) * X *
        ((rhoM S.desc g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
    intro X
    obtain ⟨e, he, rfl⟩ := S.desc.cV_surj X
    have h1 := S.desc.cV_act ⟨g, hg⟩ e he
    have h' : (φ ⟨g, hgH⟩) e = e := by rw [← actM_of_mem hgH]; exact hfix e he
    rw [rhoM_of_mem S.desc hg]
    rw [h'] at h1
    exact h1.symm
  obtain ⟨h1, h2⟩ := M1.eq_one_of_act_eq_self _ _ hX
  exact Prod.ext h1 h2

theorem rhoM_eq_one_of_mem_CN [CharP K 2] {n : G} (hn : n ∈ hc.CN t) : rhoM S.desc n = 1 :=
  S.rhoM_eq_one_of_fix (sec9_CN_le_Rt hc t hn) (fun _ he => S.actM_fix_V hn he)

theorem mem_CN_of_rhoM_eq_one {g : G} (hg : g ∈ Rt M (LB M Q B) t) (h1 : rhoM S.desc g = 1) :
    g ∈ hc.CN t := by
  refine Ctx.mem_CN.mpr ⟨hg, fun v hv => ?_⟩
  have hgH := hc.Rt_le_H0 t hg
  have hgM : g ∈ M := hc.Rt_le_M t hg
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have he : M₀.π v ∈ M₀.img (Vt M (LB M Q B) B Z t) := M₀.pi_mem_img hv hvQ
  have hge := S.actM_mem_V hg he
  have hcv := S.desc.cV_act ⟨g, hg⟩ _ he
  rw [rhoM_of_mem S.desc hg] at h1
  rw [h1] at hcv
  simp only [Prod.fst_one, Prod.snd_one, Matrix.SpecialLinearGroup.coe_one, one_mul,
    Matrix.transpose_one, mul_one] at hcv
  have hcv' : S.desc.cV (φ ⟨g, hgH⟩ (M₀.π v)) = S.desc.cV (M₀.π v) := hcv
  rw [← actM_of_mem hgH] at hcv'
  have hdiff : actM φ g (M₀.π v) - M₀.π v ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    (M₀.img (Vt M (LB M Q B) B Z t)).sub_mem hge he
  have hz : S.desc.cV (actM φ g (M₀.π v) - M₀.π v) = 0 := by rw [map_sub, hcv', sub_self]
  have h0 := S.desc.cV_inj _ hdiff hz
  have hfixv : actM φ g (M₀.π v) = M₀.π v := sub_eq_zero.mp h0
  have hcommQ : ⁅g, v⁆ ∈ Q := by
    have h2 : g * v * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) v).mp hvQ
    rw [commutatorElement_def]
    exact Q.mul_mem h2 (Q.inv_mem hvQ)
  have hg2 : g * v * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) v).mp hvQ
  have e1 : ⁅g, v⁆ = (g * v * g⁻¹) * v⁻¹ := commutatorElement_def g v
  refine (M₀.π_ker _ hcommQ).mp ?_
  rw [e1, M₀.π_mul _ hg2 _ (Q.inv_mem hvQ), S.pi_conj hgH hvQ, hfixv, M₀.pi_inv hvQ,
    add_neg_cancel]

theorem rhoM_LB_unip [CharP K 2] {l : G} (hl : l ∈ LB M Q B) :
    ∃ s s' : K, ((rhoM S.desc l).1 : Matrix (Fin 2) (Fin 2) K) = M1.uMat s ∧
      ((rhoM S.desc l).2 : Matrix (Fin 2) (Fin 2) K) = M1.uMat s' := by
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) S.ht hl
  have hlH := hc.Rt_le_H0 t hlR
  obtain ⟨b, hb0, hB, hcb⟩ := S.desc.point
  have hfix := (hc.LB_act_fix_line S.glob hB hl
    (T := ((actM φ l : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E))
    (fun x hx => S.pi_conj hlH hx)).1
  have hbV : b ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    M₀.img_mono (hc.B_le_Vt S.ht) ((hB b).mpr ⟨1, (one_smul K b).symm⟩)
  have h1 := S.desc.cV_act ⟨l, hlR⟩ b hbV
  have h' : (φ ⟨l, hlH⟩) b = b := by rw [← actM_of_mem hlH]; exact hfix
  rw [h', hcb] at h1
  have hE : ((rhoM S.desc l).1 : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 0 1 *
      ((rhoM S.desc l).2 : Matrix (Fin 2) (Fin 2) K)ᵀ = Matrix.single 0 0 1 := by
    rw [rhoM_of_mem S.desc hlR]
    exact h1.symm
  have hll : l * l ∈ Q := by
    have := hc.sq_mem_Q_of_mem_LB hl
    rwa [pow_two] at this
  have hllR : l * l ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).mul_mem hlR hlR
  have h2 : rhoM S.desc (l * l) = 1 :=
    S.rhoM_eq_one_of_fix hllR (fun e _ => by rw [S.actM_eq_one_of_mem_Q hll]; rfl)
  rw [rhoM_mul S.desc hlR hlR] at h2
  have h3 : ((rhoM S.desc l).1 : Matrix (Fin 2) (Fin 2) K) * ((rhoM S.desc l).1 : Matrix _ _ K) =
      1 := by
    have := congrArg Prod.fst h2
    simpa using congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) this
  exact M1.exists_uMat_of_fix _ _ hE h3

theorem rhoM_LB_surj [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    (s s' : K) :
    ∃ l ∈ LB M Q B, ((rhoM S.desc l).1 : Matrix (Fin 2) (Fin 2) K) = M1.uMat s ∧
      ((rhoM S.desc l).2 : Matrix (Fin 2) (Fin 2) K) = M1.uMat s' := by
  classical
  have hLR : ∀ l : ↥(LB M Q B), (l : G) ∈ Rt M (LB M Q B) t := fun l =>
    le_Rt (M := M) (LB M Q B) S.ht l.2
  let e1 : G → K := fun l => ((rhoM S.desc l).1 : Matrix (Fin 2) (Fin 2) K) 0 1
  let e2 : G → K := fun l => ((rhoM S.desc l).2 : Matrix (Fin 2) (Fin 2) K) 0 1
  have hent : ∀ l : ↥(LB M Q B), ((rhoM S.desc l).1 : Matrix (Fin 2) (Fin 2) K) = M1.uMat (e1 l) ∧
      ((rhoM S.desc l).2 : Matrix (Fin 2) (Fin 2) K) = M1.uMat (e2 l) := by
    intro l
    obtain ⟨a, b, ha, hb⟩ := S.rhoM_LB_unip l.2
    have h1 : e1 l = a := by simp [e1, ha, M1.uMat]
    have h2 : e2 l = b := by simp [e2, hb, M1.uMat]
    rw [h1, h2]
    exact ⟨ha, hb⟩
  have hone : ∀ l : ↥(LB M Q B), rhoM S.desc l = 1 ↔ e1 l = 0 ∧ e2 l = 0 := by
    intro l
    constructor
    · intro h
      simp [e1, e2, h]
    · rintro ⟨h1, h2⟩
      have a1 := (hent l).1
      have a2 := (hent l).2
      rw [h1, M1.uMat_zero] at a1
      rw [h2, M1.uMat_zero] at a2
      exact Prod.ext (Subtype.ext a1) (Subtype.ext a2)
  let ψ : ↥(LB M Q B) →* Multiplicative (K × K) :=
    { toFun := fun l => Multiplicative.ofAdd (e1 l, e2 l)
      map_one' := by
        have := (hone 1).mp (rhoM_one S.desc)
        show Multiplicative.ofAdd (e1 ((1 : ↥(LB M Q B)) : G), e2 ((1 : ↥(LB M Q B)) : G)) = 1
        rw [this.1, this.2]
        rfl
      map_mul' := by
        intro l₁ l₂
        have hm := rhoM_mul S.desc (hLR l₁) (hLR l₂)
        obtain ⟨a1, a2⟩ := hent l₁
        obtain ⟨b1, b2⟩ := hent l₂
        have m1 : ((rhoM S.desc ((l₁ * l₂ : ↥(LB M Q B)) : G)).1 : Matrix (Fin 2) (Fin 2) K) =
            M1.uMat (e1 l₁ + e1 l₂) := by
          rw [Subgroup.coe_mul, hm, Prod.fst_mul, Matrix.SpecialLinearGroup.coe_mul, a1, b1,
            M1.uMat_mul]
        have m2 : ((rhoM S.desc ((l₁ * l₂ : ↥(LB M Q B)) : G)).2 : Matrix (Fin 2) (Fin 2) K) =
            M1.uMat (e2 l₁ + e2 l₂) := by
          rw [Subgroup.coe_mul, hm, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul, a2, b2,
            M1.uMat_mul]
        show Multiplicative.ofAdd (e1 ((l₁ * l₂ : ↥(LB M Q B)) : G),
          e2 ((l₁ * l₂ : ↥(LB M Q B)) : G)) = _
        have e1' : e1 ((l₁ * l₂ : ↥(LB M Q B)) : G) = e1 l₁ + e1 l₂ := by
          show ((rhoM S.desc ((l₁ * l₂ : ↥(LB M Q B)) : G)).1 : Matrix (Fin 2) (Fin 2) K) 0 1 = _
          rw [m1]
          rfl
        have e2' : e2 ((l₁ * l₂ : ↥(LB M Q B)) : G) = e2 l₁ + e2 l₂ := by
          show ((rhoM S.desc ((l₁ * l₂ : ↥(LB M Q B)) : G)).2 : Matrix (Fin 2) (Fin 2) K) 0 1 = _
          rw [m2]
          rfl
        rw [e1', e2']
        rfl }
  have hker : ψ.ker = (hc.CN t).subgroupOf (LB M Q B) := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (e1 l, e2 l) = 0 := ofAdd_eq_one.mp h
      exact S.mem_CN_of_rhoM_eq_one (hLR l)
        ((hone l).mpr ⟨(Prod.ext_iff.mp h').1, (Prod.ext_iff.mp h').2⟩)
    · intro h
      have := (hone l).mp (S.rhoM_eq_one_of_mem_CN h)
      show Multiplicative.ofAdd (e1 l, e2 l) = 1
      rw [this.1, this.2]
      rfl
  have hcard : Nat.card ψ.range = Nat.card (Multiplicative (K × K)) := by
    rw [← Subgroup.index_ker, hker]
    change (hc.CN t).relIndex (LB M Q B) = _
    rw [relIndex_LB_CN h34 hs, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, S.glob.card,
      pow_two]
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  have hmem : Multiplicative.ofAdd (s, s') ∈ ψ.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨l, hl⟩ := hmem
  have hl' : (e1 l, e2 l) = (s, s') := Multiplicative.ofAdd.injective hl
  have hs1 : e1 l = s := (Prod.ext_iff.mp hl').1
  have hs2 : e2 l = s' := (Prod.ext_iff.mp hl').2
  refine ⟨l, l.2, ?_, ?_⟩
  · rw [(hent l).1, hs1]
  · rw [(hent l).2, hs2]

theorem theta_comm_LB [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t) {x : G}
    (hx : x ∈ hc.CN t) (hxL : x ∈ LB M Q B) (s s' : K) (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    S.theta x (M1.actW (M1.uMat s) (M1.uMat s') y) =
      M1.uMat s * S.theta x y * (M1.uMat s')ᵀ := by
  obtain ⟨l, hl, h1, h2⟩ := S.rhoM_LB_surj h34 hs s s'
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) S.ht hl
  have hcomm : ⁅l, x⁆ ∈ Q := hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hl hxL)
  have := S.theta_comm hx hlR hcomm y
  rwa [h1, h2] at this
end Setup95

end Setup

end HS9

end CFSG.RankThree.GF2n.Stroth80
