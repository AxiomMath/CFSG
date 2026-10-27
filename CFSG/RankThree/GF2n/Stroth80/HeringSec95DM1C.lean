module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1B
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DComm
public import CFSG.RankThree.GF2n.Stroth80.Sec92SplitN

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

namespace Setup95

variable (S : Setup95 hc t M₀ φ Y₁ Y₂)

include S

theorem pi_comm {m x : G} (hm : m ∈ H0 M Z) (hx : x ∈ Q) :
    M₀.π ⁅m, x⁆ = actM φ m (M₀.π x) - M₀.π x := by
  have h1 : m * x * m⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm.1) x).mp hx
  have e1 : ⁅m, x⁆ = (m * x * m⁻¹) * x⁻¹ := commutatorElement_def m x
  rw [e1, M₀.π_mul _ h1 _ (Q.inv_mem hx), S.pi_conj hm hx, M₀.pi_inv hx, sub_eq_add_neg]

theorem exists_pre_of_mem_img_comm {S' : Subgroup G} (hS'Q : S' ≤ Q) {a : G} (ha : a ∈ H0 M Z)
    (haa : a * a ∈ Q) {e : M₀.E} (he : e ∈ M₀.img (⁅S', Subgroup.zpowers a⁆ ⊔ Z)) :
    ∃ w ∈ M₀.img S', actM φ a w - w = e := by
  classical
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hT2 : φ ⟨a, ha⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have := S.actM_eq_one_of_mem_Q haa
    rw [actM_of_mem ((H0 M Z).mul_mem ha ha)] at this
    exact this
  have hTk : ∀ k : ℤ, φ ⟨a, ha⟩ ^ k = 1 ∨ φ ⟨a, ha⟩ ^ k = φ ⟨a, ha⟩ := by
    intro k
    have h2 : φ ⟨a, ha⟩ ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hT2]
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zpow_zero]
    · right
      rw [hk, zpow_one]
  let R : AddSubgroup M₀.E := (M₀.img S').map
    (((actM φ a : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1).toAddMonoidHom
  have hle : ⁅S', Subgroup.zpowers a⁆ ⊔ Z ≤ M₀.lift R := by
    refine sup_le ?_ (fun z hz => ⟨hZQ hz, ?_⟩)
    · rw [Subgroup.commutator_le]
      intro y hy g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hyQ : y ∈ Q := hS'Q hy
      have hakH : a ^ k ∈ H0 M Z := (H0 M Z).zpow_mem ha k
      have hq1 : a ^ k * y⁻¹ * (a ^ k)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hakH.1) y⁻¹).mp (Q.inv_mem hyQ)
      have e1 : ⁅y, a ^ k⁆ = y * (a ^ k * y⁻¹ * (a ^ k)⁻¹) := by
        rw [commutatorElement_def]; group
      refine ⟨by rw [e1]; exact Q.mul_mem hyQ hq1, ?_⟩
      rw [e1, M₀.π_mul _ hyQ _ hq1, S.pi_conj hakH (Q.inv_mem hyQ), M₀.pi_inv hyQ,
        actM_of_mem hakH]
      have hpow : φ ⟨a ^ k, hakH⟩ = φ ⟨a, ha⟩ ^ k := by
        rw [← map_zpow]
        rfl
      rw [hpow]
      have hπy : M₀.π y ∈ M₀.img S' := M₀.pi_mem_img hy hyQ
      rcases hTk k with h1 | h1
      · rw [h1]
        simp only [LinearEquiv.coe_one, id_eq, map_neg]
        have : M₀.π y + -M₀.π y = 0 := add_neg_cancel _
        rw [this]
        exact R.zero_mem
      · rw [h1]
        have hmem : (φ ⟨a, ha⟩ (M₀.π y) - M₀.π y) ∈ R := by
          refine AddSubgroup.mem_map.mpr ⟨M₀.π y, hπy, ?_⟩
          show ((actM φ a : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) (M₀.π y) - M₀.π y = _
          rw [actM_of_mem ha]
          rfl
        have := R.neg_mem hmem
        simp only [map_neg, neg_sub] at this ⊢
        have e2 : M₀.π y + -(φ ⟨a, ha⟩) (M₀.π y) = M₀.π y - (φ ⟨a, ha⟩) (M₀.π y) := by abel
        rw [e2]
        exact this
    · rw [(M₀.π_ker z (hZQ hz)).mpr hz]
      exact R.zero_mem
  obtain ⟨x, hx, hxQ, rfl⟩ := he
  obtain ⟨w, hw, hwe⟩ := AddSubgroup.mem_map.mp (hle hx).2
  refine ⟨w, hw, ?_⟩
  simpa using hwe

theorem theta_eq_zero_iff {m : G} (hm : m ∈ hc.CN t) :
    S.theta m = 0 ↔ ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅m, x⁆ ∈ Z := by
  have hmH := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hm)
  constructor
  · intro h0 x hx
    have hxW : M₀.π x ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := M₀.pi_mem_img hx hx.1
    have h1 := S.theta_apply hm hxW
    rw [h0, LinearMap.zero_apply] at h1
    have hV := S.actM_sub_mem_V hm hxW
    have h2 := S.desc.cV_inj _ hV h1.symm
    have hcommQ : ⁅m, x⁆ ∈ Q := by
      have h3 : m * x * m⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp
          (hc.hyp.Q_normal.2 (hc.Rt_le_M t (sec9_CN_le_Rt hc t hm))) x).mp hx.1
      rw [commutatorElement_def]
      exact Q.mul_mem h3 (Q.inv_mem hx.1)
    refine (M₀.π_ker _ hcommQ).mp ?_
    rw [S.pi_comm hmH hx.1]
    exact h2
  · intro h
    refine LinearMap.ext fun y => ?_
    rw [theta_eq]
    obtain ⟨x, hxW, hxQ, hx⟩ := S.sec_mem y
    rw [← hx, ← S.pi_comm hmH hxQ, (M₀.π_ker _ (hc.Z_le_Q (h x hxW))).mpr (h x hxW), map_zero]
    rfl


end Setup95

theorem actW_mul (g₁ g₂ h₁ h₂ : Matrix (Fin 2) (Fin 2) K) (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    M1.actW (g₁ * g₂) (h₁ * h₂) y = M1.actW g₁ h₁ (M1.actW g₂ h₂ y) :=
  Prod.ext (M1.smulVec_mul g₁ g₂ y.1) (M1.smulVec_mul h₁ h₂ y.2)

theorem actW_one_one (y : (Fin 2 → Y₁) × (Fin 2 → Y₂)) :
    M1.actW (1 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K) y = y :=
  Prod.ext (M1.smulVec_one y.1) (M1.smulVec_one y.2)

theorem coe_inv_mul_SL (a : SL(2, K)) :
    ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv_SL (a : SL(2, K)) :
    (a : Matrix (Fin 2) (Fin 2) K) * ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] def EqvAt (D : ModDesc95 hc t M₀ φ Y₁ Y₂)
    (f : (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] Matrix (Fin 2) (Fin 2) K) (g : G) : Prop :=
  ∀ y, f (M1.actW ((rhoM D g).1 : Matrix (Fin 2) (Fin 2) K)
      ((rhoM D g).2 : Matrix (Fin 2) (Fin 2) K) y) =
    ((rhoM D g).1 : Matrix (Fin 2) (Fin 2) K) * f y *
      ((rhoM D g).2 : Matrix (Fin 2) (Fin 2) K)ᵀ

namespace EqvAt

variable (D : ModDesc95 hc t M₀ φ Y₁ Y₂)
  (f : (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] Matrix (Fin 2) (Fin 2) K)

theorem one : EqvAt D f 1 := by
  intro y
  rw [rhoM_one]
  simp [actW_one_one]

theorem mul {g h : G} (hg : g ∈ Rt M (LB M Q B) t) (hh : h ∈ Rt M (LB M Q B) t)
    (h₁ : EqvAt D f g) (h₂ : EqvAt D f h) : EqvAt D f (g * h) := by
  intro y
  rw [rhoM_mul D hg hh]
  simp only [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [actW_mul, h₁, h₂, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem inv {g : G} (hg : g ∈ Rt M (LB M Q B) t) (h₁ : EqvAt D f g) : EqvAt D f g⁻¹ := by
  intro y
  rw [rhoM_inv D hg]
  simp only [Prod.fst_inv, Prod.snd_inv]
  set a := (rhoM D g).1 with ha
  set b := (rhoM D g).2 with hb
  set y' := M1.actW ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
    ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) y with hy'
  have hback : M1.actW (a : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K) y' = y := by
    rw [hy', ← actW_mul, coe_mul_inv_SL a, coe_mul_inv_SL b]
    exact actW_one_one y
  have h2 : f y = (a : Matrix (Fin 2) (Fin 2) K) * f y' * (b : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    have := h₁ y'
    rwa [hback] at this
  have hbt : (b : Matrix (Fin 2) (Fin 2) K)ᵀ * ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, coe_inv_mul_SL b, Matrix.transpose_one]
  rw [h2]
  calc f y' = ((a⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (a : Matrix (Fin 2) (Fin 2) K) *
        f y' * ((b : Matrix (Fin 2) (Fin 2) K)ᵀ *
          ((b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
        rw [coe_inv_mul_SL a, hbt, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end EqvAt

theorem eqvAt_of_sup (D : ModDesc95 hc t M₀ φ Y₁ Y₂)
    (f : (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] Matrix (Fin 2) (Fin 2) K) {H₁ H₂ : Subgroup G}
    (h₁R : H₁ ≤ Rt M (LB M Q B) t) (h₂R : H₂ ≤ Rt M (LB M Q B) t)
    (hf₁ : ∀ g ∈ H₁, EqvAt D f g) (hf₂ : ∀ g ∈ H₂, EqvAt D f g) :
    ∀ g ∈ H₁ ⊔ H₂, EqvAt D f g := by
  intro g hg
  have hsub : H₁ ⊔ H₂ ≤ Rt M (LB M Q B) t := sup_le h₁R h₂R
  rw [Subgroup.sup_eq_closure] at hg
  have hcl : Subgroup.closure ((H₁ : Set G) ∪ (H₂ : Set G)) ≤ Rt M (LB M Q B) t := by
    rw [← Subgroup.sup_eq_closure]
    exact hsub
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hf₁ x hx
    · exact hf₂ x hx
  | one => exact EqvAt.one D f
  | mul x y hx hy ih₁ ih₂ => exact EqvAt.mul D f (hcl hx) (hcl hy) ih₁ ih₂
  | inv x hx ih => exact EqvAt.inv D f (hcl hx) ih

theorem eq_zero_of_eqvAt (D : ModDesc95 hc t M₀ φ Y₁ Y₂)
    (f : (Fin 2 → Y₁) × (Fin 2 → Y₂) →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hf : ∀ g ∈ Rt M (LB M Q B) t, EqvAt D f g) : f = 0 := by
  refine M1.eqv_all_zero f fun g h y => ?_
  obtain ⟨r, hr⟩ := D.ρ_surj (g, h)
  have := hf r r.2 y
  rw [rhoM_of_mem D r.2] at this
  have h' : D.ρ ⟨(r : G), r.2⟩ = (g, h) := hr
  rw [h'] at this
  exact this


namespace Setup95

variable (S : Setup95 hc t M₀ φ Y₁ Y₂)

include S

theorem mem_Z0_of_theta_eq_zero (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {n : ℕ} (hs : Sec9Hyp hc n t) {r' : G} (hr' : Sec7A hc t r') {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {m : G} (hm : m ∈ hc.CN t)
    (hθ : S.theta m = 0) : m ∈ Z0 := by
  have hrM : r' ∈ M := hc.Rt_le_M t hr'.mem
  have hcA : Ctx M Q Z (conjSubgroup r' B) := hc.conj_of_mem hrM
  have hLB_R : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) S.ht
  have hLA_R : LB M Q (conjSubgroup r' B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem S.ht hr'.mem
  have hmW := (S.theta_eq_zero_iff hm).mp hθ
  refine Split92.mem_centre_of_mem_N h34 h311a h311bComm h311bCard hs hr' hZ0 ?_ hm hmW
  intro m' hm' hm'W
  obtain ⟨hdec, -, -⟩ := CN_eq_mul95 h34 h311a (sec9NComm_of_311b h34 h311bComm) hs hr'
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec m' hm'
  have haN : a ∈ hc.CN t := (Subgroup.mem_inf.mp ha).2
  have hbN : b ∈ hc.CN t := (Subgroup.mem_inf.mp hb).2
  have hθab : S.theta (a * b) = 0 := (S.theta_eq_zero_iff hm').mpr hm'W
  rw [S.theta_mul haN hbN] at hθab
  have hba : S.theta b = - S.theta a := eq_neg_of_add_eq_zero_right hθab
  have hEqB : ∀ g ∈ LB M Q B, EqvAt S.desc (S.theta a) g := by
    intro g hg y
    have hcomm : ⁅g, a⁆ ∈ Q :=
      hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hg (Subgroup.mem_inf.mp ha).1)
    exact S.theta_comm haN (hLB_R hg) hcomm y
  have hEqA : ∀ g ∈ LB M Q (conjSubgroup r' B), EqvAt S.desc (S.theta a) g := by
    intro g hg y
    have hcomm : ⁅g, b⁆ ∈ Q :=
      hcA.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hg (Subgroup.mem_inf.mp hb).1)
    have := S.theta_comm hbN (hLA_R hg) hcomm y
    rw [hba] at this
    simpa [LinearMap.neg_apply, Matrix.mul_neg, Matrix.neg_mul] using this
  have hall := eqvAt_of_sup S.desc (S.theta a) hLB_R hLA_R hEqB hEqA
  have hgen : ∀ g ∈ Rt M (LB M Q B) t, EqvAt S.desc (S.theta a) g := by
    intro g hg
    apply hall
    rw [← hr'.gen]
    exact hg
  have h0 : S.theta a = 0 := eq_zero_of_eqvAt S.desc _ hgen
  have h0' : S.theta b = 0 := by rw [hba, h0, neg_zero]
  exact ⟨a, ha, (S.theta_eq_zero_iff haN).mp h0, b, hb, (S.theta_eq_zero_iff hbN).mp h0', rfl⟩

end Setup95
end Lemmas

end HS9

end CFSG.RankThree.GF2n.Stroth80
