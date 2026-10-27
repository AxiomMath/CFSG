module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1C
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DGeo
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DLin

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Lemmas

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
  {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]

@[expose] noncomputable def V2 (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (s : G) : Submodule K M₀.E :=
  LinearMap.range (((actM φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)

namespace Setup95

variable (S : Setup95 hc t M₀ φ Y₁ Y₂)

include S

theorem actM_invol {s : G} (hs : s ∈ H0 M Z) (hss : s * s ∈ Q) (e : M₀.E) :
    actM φ s (actM φ s e) = e := by
  have h := S.actM_eq_one_of_mem_Q hss
  rw [actM_mul hs hs] at h
  exact congrArg (fun T : M₀.E ≃ₗ[K] M₀.E => T e) h

theorem actM_isom {s : G} (hs : s ∈ H0 M Z) (e : M₀.E) : M₀.Qf (actM φ s e) = M₀.Qf e := by
  rw [actM_of_mem hs]
  exact S.hφQf ⟨s, hs⟩ e

theorem selfAdj {s : G} (hs : s ∈ H0 M Z) (hss : s * s ∈ Q) (e e' : M₀.E) :
    M₀.B ((((actM φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e) e' =
      M₀.B e ((((actM φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e') :=
  selfAdj_sub_one95 ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩ (actM φ s) (S.actM_isom hs)
    (S.actM_invol hs hss) e e'

theorem V2_le_W {s : G} (hsN : s ∈ hc.CN t) (hss : s * s ∈ Q) {e : M₀.E} (he : e ∈ V2 φ s) :
    e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := by
  have hsH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hsN)
  obtain ⟨u, rfl⟩ := he
  rw [mem_img_Wt_iff M₀ S.glob.reg (hc.Vt_le_Q t)]
  intro v hv
  rw [S.selfAdj hsH hss]
  have h0 : ((((actM φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) v) = 0 := by
    simp [S.actM_fix_V hsN hv]
  rw [h0, map_zero]

theorem B_V2_ker {s : G} (hsH : s ∈ H0 M Z) (hss : s * s ∈ Q) {e e' : M₀.E} (he : e ∈ V2 φ s)
    (he' : actM φ s e' = e') : M₀.B e e' = 0 := by
  obtain ⟨u, rfl⟩ := he
  rw [S.selfAdj hsH hss]
  have h0 : ((((actM φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) e') = 0 := by
    simp [he']
  rw [h0, map_zero]

theorem conj_LB_eq_of_line {g₁ g₂ : G} (hg₁ : g₁ ∈ Rt M (LB M Q B) t)
    (hg₂ : g₂ ∈ Rt M (LB M Q B) t) {κ : K} (hκ : κ ≠ 0) {b : M₀.E} (hb0 : b ≠ 0)
    (hB : ∀ e, e ∈ M₀.img B ↔ ∃ c : K, e = c • b)
    (h : actM φ g₁ b = κ • actM φ g₂ b) :
    conjSubgroup g₁ (LB M Q B) = conjSubgroup g₂ (LB M Q B) := by
  have hg₁M := hc.Rt_le_M t hg₁
  have hg₂M := hc.Rt_le_M t hg₂
  have hg₁H := hc.Rt_le_H0 t hg₁
  have hg₂H := hc.Rt_le_H0 t hg₂
  have hC₁ : Ctx M Q Z (conjSubgroup g₁ B) := hc.conj_of_mem hg₁M
  have hC₂ : Ctx M Q Z (conjSubgroup g₂ B) := hc.conj_of_mem hg₂M
  obtain ⟨b₁, hb₁B, hb₁Q, hb₁⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  obtain ⟨b₂, hb₂B, hb₂Q, hb₂⟩ : κ • b ∈ M₀.img B := (hB (κ • b)).mpr ⟨κ, rfl⟩
  have ha : g₁ * b₁ * g₁⁻¹ ∈ conjSubgroup g₁ B := conj_mem95 g₁ hb₁B
  have ha' : g₂ * b₂ * g₂⁻¹ ∈ conjSubgroup g₂ B := conj_mem95 g₂ hb₂B
  have hpi : M₀.π (g₁ * b₁ * g₁⁻¹) = M₀.π (g₂ * b₂ * g₂⁻¹) := by
    rw [S.pi_conj hg₁H hb₁Q, S.pi_conj hg₂H hb₂Q, hb₁, hb₂, h, map_smul]
  have hne : M₀.π (g₁ * b₁ * g₁⁻¹) ≠ 0 := by
    rw [S.pi_conj hg₁H hb₁Q, hb₁]
    exact fun h0 => hb0 ((LinearEquiv.map_eq_zero_iff _).mp h0)
  have h1 : conjSubgroup g₂ B ≤ Z ⊔ conjSubgroup g₁ B :=
    le_sup_of_common_pi95 S.glob hC₁ hC₂ ha ha' hpi hne
  have h2 : conjSubgroup g₁ B ≤ Z ⊔ conjSubgroup g₂ B :=
    le_sup_of_common_pi95 S.glob hC₂ hC₁ ha' ha hpi.symm (hpi ▸ hne)
  have hEq : conjSubgroup g₁ B ⊔ Z = conjSubgroup g₂ B ⊔ Z :=
    le_antisymm (sup_le (h2.trans (le_of_eq (sup_comm _ _))) le_sup_right)
      (sup_le (h1.trans (le_of_eq (sup_comm _ _))) le_sup_right)
  exact hc.conj_LB_eq_of_conj_BZ hg₁M hg₂M hEq


theorem theta_pure_of_conj [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    {s₂ r : G} (hs₂N : s₂ ∈ hc.CN t) (hs₂L : s₂ ∈ LB M Q B) (hrR : r ∈ Rt M (LB M Q B) t)
    (hs₂r : s₂ ∈ LB M Q (conjSubgroup r B))
    (hγ : ((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    ∃ a : Y₂ →ₗ[K] K, S.theta s₂ = M1.pureMap a := by
  have hrM := hc.Rt_le_M t hrR
  have hcA : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) S.ht
  have hB : ∀ (s s' : K) (y : M1.Wd K Y₁ Y₂),
      S.theta s₂ (M1.actW (M1.uMat s) (M1.uMat s') y) =
        M1.uMat s * S.theta s₂ y * (M1.uMat s')ᵀ :=
    fun s s' y => S.theta_comm_LB h34 hs hs₂N hs₂L s s' y
  have hC : ∀ (s' : K) (y : M1.Wd K Y₁ Y₂),
      S.theta s₂ (M1.actW (1 : Matrix (Fin 2) (Fin 2) K)
          (1 + s' • M1.nilMat (((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 0 0)
            (((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 1 0)) y) =
        S.theta s₂ y * (1 + s' • M1.nilMat (((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 0 0)
            (((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 1 0))ᵀ := by
    intro s' y
    obtain ⟨l, hlL, h1, h2⟩ := S.rhoM_LB_surj h34 hs 0 s'
    have hlR : l ∈ Rt M (LB M Q B) t := hLR hlL
    have hl'L : r * l * r⁻¹ ∈ LB M Q (conjSubgroup r B) := by
      rw [hc.LB_conj hrM]
      exact conj_mem95 r hlL
    have hl'R : r * l * r⁻¹ ∈ Rt M (LB M Q B) t :=
      (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hrR hlR)
        ((Rt M (LB M Q B) t).inv_mem hrR)
    have hcomm : ⁅r * l * r⁻¹, s₂⁆ ∈ Q :=
      hcA.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hl'L hs₂r)
    have hρ : rhoM S.desc (r * l * r⁻¹) = rhoM S.desc r * rhoM S.desc l * (rhoM S.desc r)⁻¹ := by
      rw [rhoM_mul S.desc ((Rt M (LB M Q B) t).mul_mem hrR hlR) ((Rt M (LB M Q B) t).inv_mem hrR),
        rhoM_mul S.desc hrR hlR, rhoM_inv S.desc hrR]
    have h1' : ((rhoM S.desc (r * l * r⁻¹)).1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [hρ]
      simp only [Prod.fst_mul, Prod.fst_inv, Matrix.SpecialLinearGroup.coe_mul, h1, M1.uMat_zero,
        Matrix.mul_one]
      exact coe_mul_inv_SL _
    have h2' : ((rhoM S.desc (r * l * r⁻¹)).2 : Matrix (Fin 2) (Fin 2) K) =
        1 + s' • M1.nilMat (((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 0 0)
          (((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 1 0) := by
      rw [hρ]
      simp only [Prod.snd_mul, Prod.snd_inv, Matrix.SpecialLinearGroup.coe_mul, h2]
      exact M1.conj_uMat _ s'
    have := S.theta_comm hs₂N hl'R hcomm y
    rw [h1', h2', Matrix.one_mul] at this
    exact this
  obtain ⟨h1, a, ha⟩ := M1.eqv_D (S.theta s₂) _ _ hγ hB hC
  refine ⟨a, LinearMap.ext fun y => ?_⟩
  have hy : y = (y.1, 0) + (0, y.2) := by simp
  rw [hy, map_add, map_add, h1, ha]
  simp [M1.pureMap_apply]

theorem exists_pure_in_N1 [CharP K 2] (hq4 : 4 ≤ Nat.card K) (h34 : Stroth34Statement) {n : ℕ}
    (hs : Sec9Hyp hc n t) {x₀ : G} (hx₀N : x₀ ∈ hc.CN t) (hx₀L : x₀ ∈ LB M Q B) :
    ∃ a b : Y₂ →ₗ[K] K, (∀ w : Fin 2 → Y₂,
      S.theta x₀ (0, w) = !![a (w 0) + b (w 1), a (w 1); 0, 0]) ∧
      ∃ d ∈ N1 hc t, S.theta d = M1.pureMap a := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hB : ∀ (s s' : K) (y : M1.Wd K Y₁ Y₂), S.theta x₀ (M1.actW (M1.uMat s) (M1.uMat s') y) =
      M1.uMat s * S.theta x₀ y * (M1.uMat s')ᵀ :=
    fun s s' y => S.theta_comm_LB h34 hs hx₀N hx₀L s s' y
  have hq4' : 4 ≤ Fintype.card K := by
    rw [Fintype.card_eq_nat_card]
    exact hq4
  obtain ⟨a, b, hab, hsum⟩ := M1.torus_avg hq4' (S.theta x₀) hB
  refine ⟨a, b, hab, ?_⟩
  obtain ⟨p, hp0, hBp, hcp⟩ := S.desc.point
  have hpV : p ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    M₀.img_mono (hc.B_le_Vt S.ht) ((hBp p).mpr ⟨1, (one_smul K p).symm⟩)
  have hlift : ∀ μ : Kˣ, ∃ g ∈ Rt M (LB M Q B) t, rhoM S.desc g = (1, M1.tSL μ) := by
    intro μ
    obtain ⟨g, hg⟩ := S.desc.ρ_surj (1, M1.tSL μ)
    exact ⟨(g : G), g.2, by rw [rhoM_of_mem S.desc g.2]; exact hg⟩
  choose g hgR hgρ using hlift
  have hfix : ∀ μ : Kˣ, actM φ (g μ) p = (μ : K) • p := by
    intro μ
    have hgH := hc.Rt_le_H0 t (hgR μ)
    have h1 := S.desc.cV_act ⟨g μ, hgR μ⟩ p hpV
    have hρ' : S.desc.ρ ⟨g μ, hgR μ⟩ = (1, M1.tSL μ) :=
      (rhoM_of_mem S.desc (hgR μ)).symm.trans (hgρ μ)
    rw [hρ', hcp] at h1
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, M1.coe_tSL] at h1
    have h2 : S.desc.cV (φ ⟨g μ, hgH⟩ p) = S.desc.cV ((μ : K) • p) := by
      rw [map_smul, hcp, ← M1.tMat_unit_smul]
      exact h1
    rw [← actM_of_mem hgH] at h2
    have hmem : actM φ (g μ) p - (μ : K) • p ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      (M₀.img (Vt M (LB M Q B) B Z t)).sub_mem (S.actM_mem_V (hgR μ) hpV)
        (hc.smul_mem_img_Vt S.glob t _ hpV)
    exact sub_eq_zero.mp (S.desc.cV_inj _ hmem (by rw [map_sub, h2, sub_self]))
  have hnorm : ∀ μ : Kˣ, conjSubgroup (g μ) (LB M Q B) = LB M Q B := by
    intro μ
    have := S.conj_LB_eq_of_line (hgR μ) (Rt M (LB M Q B) t).one_mem μ.ne_zero hp0 hBp
      (by rw [hfix μ, actM_one]; rfl)
    rwa [conjSubgroup_one] at this
  have hN1N : ∀ {d : G}, d ∈ N1 hc t → d ∈ hc.CN t := fun hd => (Subgroup.mem_inf.mp hd).2
  have hmemN1 : ∀ μ : Kˣ, g μ * x₀ * (g μ)⁻¹ ∈ N1 hc t := by
    intro μ
    refine Subgroup.mem_inf.mpr ⟨?_, hc.CN_conj_mem S.ht (hgR μ) hx₀N⟩
    have := conj_mem95 (g μ) hx₀L
    rwa [hnorm μ] at this
  have hθμ : ∀ (μ : Kˣ) (y : M1.Wd K Y₁ Y₂), S.theta (g μ * x₀ * (g μ)⁻¹) y =
      S.theta x₀ (M1.actW 1 (M1.tMat (((μ⁻¹ : Kˣ) : K))) y) * M1.tMat (μ : K) := by
    intro μ y
    have h1 := S.theta_conj hx₀N (hgR μ) (M1.actW 1 (M1.tMat (((μ⁻¹ : Kˣ) : K))) y)
    rw [hgρ μ] at h1
    have e1 : M1.actW ((((1 : SL(2, K)), M1.tSL μ) : SL(2, K) × SL(2, K)).1 :
        Matrix (Fin 2) (Fin 2) K) ((((1 : SL(2, K)), M1.tSL μ) : SL(2, K) × SL(2, K)).2 :
        Matrix (Fin 2) (Fin 2) K) (M1.actW 1 (M1.tMat (((μ⁻¹ : Kˣ) : K))) y) = y := by
      simp only [Matrix.SpecialLinearGroup.coe_one, M1.coe_tSL]
      rw [← actW_mul, Matrix.one_mul, M1.tMat_mul_inv]
      exact actW_one_one y
    rw [e1] at h1
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, M1.coe_tSL,
      M1.tMat_transpose] at h1
    exact h1
  let T1 : AddSubmonoid (M1.Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {f | ∃ d ∈ N1 hc t, S.theta d = f}
      add_mem' := by
        rintro _ _ ⟨d₁, hd₁, rfl⟩ ⟨d₂, hd₂, rfl⟩
        exact ⟨d₁ * d₂, (N1 hc t).mul_mem hd₁ hd₂, S.theta_mul (hN1N hd₁) (hN1N hd₂)⟩
      zero_mem' := ⟨1, (N1 hc t).one_mem, S.theta_one⟩ }
  have hsumT : ∑ μ : Kˣ, S.theta (g μ * x₀ * (g μ)⁻¹) ∈ T1 :=
    AddSubmonoid.sum_mem _ fun μ _ => ⟨_, hmemN1 μ, rfl⟩
  obtain ⟨d, hd, hdθ⟩ := hsumT
  refine ⟨d, hd, ?_⟩
  rw [hdθ]
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply]
  simp only [hθμ]
  exact hsum y


theorem mem_LB_conj_of_pure [CharP K 2] {d r : G} (hdN1 : d ∈ N1 hc t) {a : Y₂ →ₗ[K] K}
    (hθ : S.theta d = M1.pureMap a) (hrR : r ∈ Rt M (LB M Q B) t)
    (hg10 : ((rhoM S.desc r).1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hK : ∀ m ∈ hc.CN t, S.theta m = 0 → m ∈ LB M Q B) : d ∈ LB M Q (conjSubgroup r B) := by
  have hrM := hc.Rt_le_M t hrR
  have hdN : d ∈ hc.CN t := (Subgroup.mem_inf.mp hdN1).2
  have hdL : d ∈ LB M Q B := (Subgroup.mem_inf.mp hdN1).1
  obtain ⟨p, hp0, hBp, hcp⟩ := S.desc.point
  have hpV : p ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    M₀.img_mono (hc.B_le_Vt S.ht) ((hBp p).mpr ⟨1, (one_smul K p).symm⟩)
  obtain ⟨g', hg'⟩ := S.desc.ρ_surj (1, (rhoM S.desc r).2)
  have hg'R : (g' : G) ∈ Rt M (LB M Q B) t := g'.2
  have hg'ρ : rhoM S.desc g' = (1, (rhoM S.desc r).2) := by
    rw [rhoM_of_mem S.desc g'.2]
    exact hg'
  set κ : K := ((rhoM S.desc r).1 : Matrix (Fin 2) (Fin 2) K) 0 0 with hκdef
  have hκ : κ ≠ 0 := by
    have hdet := (rhoM S.desc r).1.det_coe
    rw [Matrix.det_fin_two, hg10] at hdet
    intro h0
    rw [hκdef] at h0
    rw [h0] at hdet
    simp at hdet
  have hrp : actM φ r p = κ • actM φ (g' : G) p := by
    have hrH := hc.Rt_le_H0 t hrR
    have hg'H := hc.Rt_le_H0 t hg'R
    have h1 := S.desc.cV_act ⟨r, hrR⟩ p hpV
    have h2 := S.desc.cV_act ⟨(g' : G), hg'R⟩ p hpV
    have hρr : S.desc.ρ ⟨r, hrR⟩ = rhoM S.desc r := (rhoM_of_mem S.desc hrR).symm
    have hρg : S.desc.ρ ⟨(g' : G), hg'R⟩ = (1, (rhoM S.desc r).2) :=
      (rhoM_of_mem S.desc hg'R).symm.trans hg'ρ
    rw [hρr, hcp] at h1
    rw [hρg, hcp] at h2
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at h2
    have hgE : ((rhoM S.desc r).1 : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 0 1 =
        κ • Matrix.single 0 0 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, hg10, hκdef]
    rw [hgE, Matrix.smul_mul] at h1
    have h3 : S.desc.cV (actM φ r p) = S.desc.cV (κ • actM φ (g' : G) p) := by
      rw [map_smul, actM_of_mem hrH, actM_of_mem hg'H]
      have h1' : S.desc.cV (φ ⟨r, hrH⟩ p) =
          κ • (Matrix.single 0 0 1 * ((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ) := h1
      have h2' : S.desc.cV (φ ⟨(g' : G), hg'H⟩ p) =
          Matrix.single 0 0 1 * ((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := h2
      rw [h1', h2']
    have hmem : actM φ r p - κ • actM φ (g' : G) p ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      (M₀.img (Vt M (LB M Q B) B Z t)).sub_mem (S.actM_mem_V hrR hpV)
        (hc.smul_mem_img_Vt S.glob t _ (S.actM_mem_V hg'R hpV))
    exact sub_eq_zero.mp (S.desc.cV_inj _ hmem (by rw [map_sub, h3, sub_self]))
  have hline := S.conj_LB_eq_of_line hrR hg'R hκ hp0 hBp hrp
  rw [hc.LB_conj hrM, hline, mem_conjSubgroup]
  have hg'iR : (g' : G)⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hg'R
  have hconjN : (g' : G)⁻¹ * d * (g' : G) ∈ hc.CN t := by
    have := hc.CN_conj_mem S.ht hg'iR hdN
    rwa [inv_inv] at this
  have hθconj : S.theta ((g' : G)⁻¹ * d * (g' : G)) = S.theta d := by
    refine LinearMap.ext fun y' => ?_
    set h : SL(2, K) := (rhoM S.desc r).2 with hhdef
    have key := S.theta_conj hdN hg'iR
      (M1.actW (1 : Matrix (Fin 2) (Fin 2) K) (h : Matrix (Fin 2) (Fin 2) K) y')
    rw [rhoM_inv S.desc hg'R, hg'ρ, inv_inv] at key
    have e1 : M1.actW ((((1 : SL(2, K)), h)⁻¹ : SL(2, K) × SL(2, K)).1 : Matrix (Fin 2) (Fin 2) K)
        ((((1 : SL(2, K)), h)⁻¹ : SL(2, K) × SL(2, K)).2 : Matrix (Fin 2) (Fin 2) K)
        (M1.actW 1 (h : Matrix (Fin 2) (Fin 2) K) y') = y' := by
      simp only [Prod.inv_mk, inv_one, Matrix.SpecialLinearGroup.coe_one]
      rw [← actW_mul, Matrix.one_mul, coe_inv_mul_SL h]
      exact actW_one_one y'
    rw [e1] at key
    rw [key]
    simp only [Prod.inv_mk, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    rw [hθ, M1.pureMap_equiv, Matrix.mul_assoc, ← Matrix.transpose_mul, coe_inv_mul_SL h,
      Matrix.transpose_one, Matrix.mul_one]
  have hmN : (g' : G)⁻¹ * d * (g' : G) * d⁻¹ ∈ hc.CN t :=
    (hc.CN t).mul_mem hconjN ((hc.CN t).inv_mem hdN)
  have hmd : (g' : G)⁻¹ * d * (g' : G) = ((g' : G)⁻¹ * d * (g' : G) * d⁻¹) * d := by group
  have hθm : S.theta ((g' : G)⁻¹ * d * (g' : G) * d⁻¹) = 0 := by
    have h4 := S.theta_mul hmN hdN
    rw [← hmd, hθconj] at h4
    exact add_eq_right.mp h4.symm
  have hmL := hK _ hmN hθm
  rw [hmd]
  exact (LB M Q B).mul_mem hmL hdL

theorem finite_Y2 : Module.Finite K Y₂ := by
  haveI : Module.Finite K S.Wsub := inferInstance
  let f : S.Wsub →ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂) := S.desc.cW.comp S.Wsub.subtype
  have hf : Function.Surjective f := fun y => by
    obtain ⟨w, hw, h⟩ := S.desc.cW_surj y
    exact ⟨⟨w, hw⟩, h⟩
  haveI : Module.Finite K ((Fin 2 → Y₁) × (Fin 2 → Y₂)) := Module.Finite.of_surjective f hf
  let ι : Y₂ →ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂) :=
    (LinearMap.inr K (Fin 2 → Y₁) (Fin 2 → Y₂)) ∘ₗ (LinearMap.single K (fun _ : Fin 2 => Y₂) 0)
  have hι : Function.Injective ι := by
    intro y₁ y₂ h
    have := congrArg (fun p => p.2 0) h
    simpa [ι] using this
  exact Module.Finite.of_injective ι hι

theorem core_A [CharP K 2] (hq4 : 4 ≤ Nat.card K) (h34 : Stroth34Statement) {n : ℕ}
    (hs : Sec9Hyp hc n t) (hK : ∀ m ∈ hc.CN t, S.theta m = 0 → m ∈ LB M Q B)
    {s₂ x₀ r : G} (hs₂ : s₂ ∈ N1 hc t) (hx₀ : x₀ ∈ N1 hc t) (hrR : r ∈ Rt M (LB M Q B) t)
    (hs₂r : s₂ ∈ LB M Q (conjSubgroup r B))
    (hg10 : ((rhoM S.desc r).1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hh10 : ((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (hP : ∃ e ∈ V2 φ s₂, S.desc.cV (actM φ x₀ e - e) = Matrix.single 0 1 1) :
    ∃ d ∈ N1 hc t, d ∈ LB M Q (conjSubgroup r B) ∧ ∃ e ∈ V2 φ s₂, actM φ d e ≠ e := by
  classical
  haveI := S.finite_Y2
  have hs₂N : s₂ ∈ hc.CN t := (Subgroup.mem_inf.mp hs₂).2
  have hs₂L : s₂ ∈ LB M Q B := (Subgroup.mem_inf.mp hs₂).1
  have hx₀N : x₀ ∈ hc.CN t := (Subgroup.mem_inf.mp hx₀).2
  have hx₀L : x₀ ∈ LB M Q B := (Subgroup.mem_inf.mp hx₀).1
  have hs₂H : s₂ ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hs₂N)
  have hss : s₂ * s₂ ∈ Q := by
    have := hc.sq_mem_Q_of_mem_LB hs₂L
    rwa [pow_two] at this
  obtain ⟨aₜ, hθs⟩ := S.theta_pure_of_conj h34 hs hs₂N hs₂L hrR hs₂r hh10
  obtain ⟨a, b, hab, d, hdN1, hdθ⟩ := S.exists_pure_in_N1 hq4 h34 hs hx₀N hx₀L
  have hdN : d ∈ hc.CN t := (Subgroup.mem_inf.mp hdN1).2
  let X₂ : Set (M1.Wd K Y₁ Y₂) := {x | ∃ e ∈ V2 φ s₂, x = S.desc.cW e}
  have hort : ∀ x ∈ X₂, ∀ x' : M1.Wd K Y₁ Y₂, M1.pureMap aₜ x' = 0 →
      M1.formW S.desc.β₁ S.desc.β₂ x x' = 0 := by
    rintro _ ⟨e, he, rfl⟩ x' hx'
    have heW := S.V2_le_W hs₂N hss he
    have he'W := S.sec_mem x'
    have hθ0 : S.theta s₂ x' = 0 := by rw [hθs]; exact hx'
    rw [S.theta_eq] at hθ0
    have hdiffV := S.actM_sub_mem_V hs₂N he'W
    have hfix : actM φ s₂ (S.sec x') = S.sec x' := sub_eq_zero.mp (S.desc.cV_inj _ hdiffV hθ0)
    have hB0 := S.B_V2_ker hs₂H hss he hfix
    have hform := S.desc.form e heW (S.sec x') he'W
    rw [S.cW_sec] at hform
    rw [← hform]
    exact hB0
  have hP' : ∃ x₁ ∈ X₂, S.theta x₀ x₁ = !![(0 : K), 1; 0, 0] := by
    obtain ⟨e, he, hecv⟩ := hP
    refine ⟨S.desc.cW e, ⟨e, he, rfl⟩, ?_⟩
    rw [S.theta_apply hx₀N (S.V2_le_W hs₂N hss he), hecv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
  obtain ⟨x₂, ⟨e₂, he₂, rfl⟩, hx₂⟩ := M1.pure_ne_zero S.desc.β₁ S.desc.β₂ S.desc.β₁_nd
    S.desc.β₂_nd aₜ X₂ hort a b (S.theta x₀) hab hP'
  refine ⟨d, hdN1, S.mem_LB_conj_of_pure hdN1 hdθ hrR hg10 hK, e₂, he₂, ?_⟩
  intro hfix
  apply hx₂
  rw [← hdθ, S.theta_apply hdN (S.V2_le_W hs₂N hss he₂), hfix, sub_self, map_zero]
end Setup95

end Lemmas

end HS9

end CFSG.RankThree.GF2n.Stroth80
