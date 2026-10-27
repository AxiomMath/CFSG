module

import CFSG.RankThree.GF2n.Stroth80.Sec310ClConj
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauSetup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem act_sub_mem_of_not_mem_range {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {T : M₀.E ≃ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e) {b : M₀.E}
    (hbW : b ∉ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) {A : AddSubgroup M₀.E}
    (hperp : ∀ f, M₀.B f b = 0 → T f - f ∈ A) (e : M₀.E) : T e - e ∈ A := by
  obtain ⟨f₀, hf₀, hf₀b⟩ := exists_fixed_not_perp M₀ (T := (T : M₀.E →ₗ[K] M₀.E)) hT hT2 hbW
  have hf₀' : T f₀ = f₀ := hf₀
  set c : K := M₀.B e b / M₀.B f₀ b with hc_def
  have hef : M₀.B (e - c • f₀) b = 0 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hc_def,
      div_mul_cancel₀ _ hf₀b, sub_self]
  have h2 : T e - e = T (e - c • f₀) - (e - c • f₀) := by
    simp only [map_sub, map_smul, hf₀']
    abel
  rw [h2]
  exact hperp _ hef

private theorem act_fix_of_not_mem_range {K : Type} [Field K] {E : Type} [AddCommGroup E]
    [Module K E] {T S : E ≃ₗ[K] E} {b : E}
    (hbW : b ∉ LinearMap.range ((T : E →ₗ[K] E) - 1)) (hST : ∀ e, S (T e) = T (S e))
    (hS : ∀ e, ∃ c : K, S (T e - e) - (T e - e) = c • b) (e : E) : S (T e - e) = T e - e := by
  obtain ⟨c, hc'⟩ := hS e
  have hmem : S (T e - e) - (T e - e) ∈ LinearMap.range ((T : E →ₗ[K] E) - 1) := by
    refine ⟨S e - e, ?_⟩
    have e1 : ((T : E →ₗ[K] E) - 1) (S e - e) = T (S e) - T e - (S e - e) := by
      simp only [LinearMap.sub_apply, map_sub, Module.End.one_apply, LinearEquiv.coe_coe]
      abel
    rw [e1, ← hST e, map_sub]
    abel
  have hc0 : c = 0 := by
    by_contra hc0
    apply hbW
    have h4 : c • b ∈ LinearMap.range ((T : E →ₗ[K] E) - 1) := hc' ▸ hmem
    have h5 := Submodule.smul_mem _ c⁻¹ h4
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h5
  rw [hc0, zero_smul, sub_eq_zero] at hc'
  exact hc'

private theorem Ctx.act_sub_mem_img_of_perp (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {b : M₀.E} (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {t : G} (ht : t ∈ LB M Q B) {f : M₀.E} (hf : M₀.B f b = 0) :
    φ ⟨t, hc.LB_le_H0 ht⟩ f - f ∈ M₀.img (Q ⊓ QB B) := by
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj f
  have hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = φ ⟨t, hc.LB_le_H0 ht⟩ (M₀.π x) :=
    fun x hx => hφπ ⟨t, hc.LB_le_H0 ht⟩ x hx
  have hyC : y ∈ Subgroup.centralizer (B : Set G) := (hcent y hyQ).mpr hf
  have hd : ⁅t, y⁆ ∈ Q ⊓ QB B := hc.comm_mem_inf_of_mem_LB ht ⟨hyQ, hyC⟩
  have hdQ : ⁅t, y⁆ ∈ Q := (Subgroup.mem_inf.mp hd).1
  have hkd : ⁅t, y⁆ * y = t * y * t⁻¹ := by
    rw [commutatorElement_def]
    group
  have h2 := M₀.π_mul _ hdQ _ hyQ
  rw [hkd, hT y hyQ] at h2
  have h3 : M₀.π ⁅t, y⁆ = φ ⟨t, hc.LB_le_H0 ht⟩ (M₀.π y) - M₀.π y :=
    eq_sub_of_add_eq h2.symm
  rw [← h3]
  exact M₀.pi_mem_img hd hdQ

private theorem Ctx.act_comm_of_mem_LB (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) {s t : G} (hs : s ∈ LB M Q B)
    (ht : t ∈ LB M Q B) (e : M₀.E) :
    φ ⟨s, hc.LB_le_H0 hs⟩ (φ ⟨t, hc.LB_le_H0 ht⟩ e) =
      φ ⟨t, hc.LB_le_H0 ht⟩ (φ ⟨s, hc.LB_le_H0 hs⟩ e) := by
  have h1 : φ ⁅(⟨s, hc.LB_le_H0 hs⟩ : ↥(H0 M Z)), ⟨t, hc.LB_le_H0 ht⟩⁆ = 1 := by
    rw [hφker]
    show ⁅s, t⁆ ∈ Q
    exact Subgroup.commutator_le.mp hc.commutator_LB_le_Q _ hs _ ht
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) h1
  simpa [LinearEquiv.mul_apply] using this

private theorem Ctx.exists_smul_of_fixed_LB (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {w : M₀.E}
    (hw : w ∈ M₀.img (Q ⊓ QB B))
    (hfix : ∀ (l : G) (hl : l ∈ LB M Q B), φ ⟨l, hc.LB_le_H0 hl⟩ w = w) :
    ∃ s : K, w = s • b := by
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj w
  have hyQB : y ∈ Q ⊓ QB B := (M₀.mem_img_iff (le_inf hc.Z_le_Q hc.Z_le_QB.1) hyQ).mp hw
  have hyBZ : y ∈ B ⊔ Z := by
    refine hc.mem_sup_of_comm_LB_mem_Z' hyQB fun l hl => ?_
    have hQn : l * y * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.LB_le_M hl)) y).mp hyQ
    have hT : M₀.π (l * y * l⁻¹) = φ ⟨l, hc.LB_le_H0 hl⟩ (M₀.π y) :=
      hφπ ⟨l, hc.LB_le_H0 hl⟩ y hyQ
    have h1 : ⁅l, y⁆ ∈ Z := (M₀.comm_mem_iff hyQ hQn).mpr (hT.trans (hfix l hl))
    rw [← commutatorElement_inv l y]
    exact Z.inv_mem h1
  have himg : M₀.img (B ⊔ Z) = M₀.img B := by
    rw [quadModel_img_sup M₀ hc.le hc.Z_le_Q, quadModel_img_center_eq_bot M₀ hc.Z_le_Q,
      sup_bot_eq]
  have hmem := M₀.pi_mem_img hyBZ hyQ
  rw [himg] at hmem
  exact (hB _).mp hmem

theorem Ctx.mem_range_act_sub_one_of_mem_LB (hc : Ctx M Q Z B) {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) (e : M₀.E), M₀.Qf (φ m e) = M₀.Qf e) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {i : G} (hi : i ∈ LB M Q B) (hiQ : i ∉ Q) :
    b ∈ LinearMap.range ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1) := by
  by_contra hbW
  have hDW : ∀ e, φ ⟨i, hc.LB_le_H0 hi⟩ e - e ∈ M₀.img (Q ⊓ QB B) :=
    act_sub_mem_of_not_mem_range M₀ (hφiso _) (fun e => hc.act_sq_eq_of_mem_LB hφker hi e)
      hbW fun f hf => hc.act_sub_mem_img_of_perp hφπ hcent hi hf
  have hW0 : ∀ (l : G) (hl : l ∈ LB M Q B) (e : M₀.E),
      φ ⟨l, hc.LB_le_H0 hl⟩ (φ ⟨i, hc.LB_le_H0 hi⟩ e - e) = φ ⟨i, hc.LB_le_H0 hi⟩ e - e := by
    intro l hl e
    refine act_fix_of_not_mem_range hbW (fun e => hc.act_comm_of_mem_LB hφker hl hi e)
      (fun e => ?_) e
    exact (hc.LB_act_fix_line hD hB hl (T := (φ ⟨l, hc.LB_le_H0 hl⟩ : M₀.E →ₗ[K] M₀.E))
      (fun x hx => hφπ ⟨l, hc.LB_le_H0 hl⟩ x hx)).2 _ (hDW e)
  obtain ⟨e, he⟩ : ∃ e, φ ⟨i, hc.LB_le_H0 hi⟩ e ≠ e := by
    by_contra hall
    apply hiQ
    refine (hφker ⟨i, hc.LB_le_H0 hi⟩).mp (LinearEquiv.ext fun e => ?_)
    simpa using not_exists_not.mp hall e
  obtain ⟨s, hs⟩ := hc.exists_smul_of_fixed_LB hφπ hB (hDW e) fun l hl => hW0 l hl e
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hs
    exact he hs
  apply hbW
  refine ⟨s⁻¹ • e, ?_⟩
  have h1 : ((φ ⟨i, hc.LB_le_H0 hi⟩ : M₀.E →ₗ[K] M₀.E) - 1) (s⁻¹ • e) =
      s⁻¹ • (φ ⟨i, hc.LB_le_H0 hi⟩ e - e) := by
    simp only [LinearMap.sub_apply, map_smul, Module.End.one_apply, LinearEquiv.coe_coe,
      smul_sub]
  rw [h1, hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end CFSG.RankThree.GF2n.Stroth80
