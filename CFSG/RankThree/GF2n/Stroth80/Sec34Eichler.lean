module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec57D

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Eichler

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem eichler_of_isometry (M₀ : Tim79.QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) {b : M₀.E} (hb0 : b ≠ 0)
    (hTb : T b = b) (hr : ∀ y, M₀.B y b = 0 → ∃ c : K, T y = y + c • b) :
    ∃ v : M₀.E, M₀.B v b = 0 ∧
      ∀ y, T y = y + M₀.B y b • v + M₀.B y v • b + (M₀.Qf v * M₀.B y b) • b := by
  obtain ⟨f, hfb⟩ : ∃ f : M₀.E, M₀.B f b = 1 := by
    obtain ⟨f₀, hf₀⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
    exact ⟨(M₀.B f₀ b)⁻¹ • f₀, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]⟩
  obtain ⟨w, hw⟩ : ∃ w : M₀.E, w = T f - f := ⟨_, rfl⟩
  have hTf : T f = f + w := by
    rw [hw]
    abel
  have hbTf : M₀.B b (T f) = M₀.B b f := by
    have h1 := Tim79.QuadModel.B_iso hT b f
    rwa [hTb] at h1
  have hbw : M₀.B b w = 0 := by
    rw [hw, map_sub, hbTf, sub_self]
  have hwb : M₀.B w b = 0 := by
    rw [Tim79.QuadModel.B_comm, hbw, neg_zero]
  have hbf : M₀.B b f = -1 := by
    rw [Tim79.QuadModel.B_comm, hfb]
  have hQw : M₀.Qf w + M₀.B f w = 0 := by
    have h1 := M₀.Qf_add f w
    rw [← hTf, hT f] at h1
    linear_combination (-1 : K) * h1
  have hstep : ∀ y, M₀.B y b = 0 → T y = y + M₀.B y w • b := by
    intro y hy
    obtain ⟨c, hc⟩ := hr y hy
    have h1 : M₀.B (T y) (T f) = M₀.B y f := Tim79.QuadModel.B_iso hT y f
    rw [hc] at h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have h4 : M₀.B y w = M₀.B y (T f) - M₀.B y f := by
      rw [hw, map_sub]
    have hcw : c = M₀.B y w := by
      linear_combination (-1 : K) * h1 + c * hbTf + c * hbf - h4
    rw [hc, hcw]
  refine ⟨w, hwb, fun y => ?_⟩
  have hz : M₀.B (y - M₀.B y b • f) b = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hfb,
      mul_one, sub_self]
  have hsplit : T y = T (y - M₀.B y b • f) + M₀.B y b • T f := by
    rw [← map_smul, ← map_add, sub_add_cancel]
  have hsc : M₀.B (y - M₀.B y b • f) w = M₀.B y w + M₀.Qf w * M₀.B y b := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination (-M₀.B y b) * hQw
  rw [hsplit, hstep _ hz, hTf, hsc]
  module

end Eichler

section LBFlag

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.eichler_of_Spure (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hb0 : b ≠ 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {t : G} (ht : t ∈ hc.Spure) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) :
    ∃ v : M₀.E, M₀.B v b = 0 ∧
      ∀ y, T y = y + M₀.B y b • v + M₀.B y v • b + (M₀.Qf v * M₀.B y b) • b := by
  have htM : t ∈ M := hc.LB_le_M ht.1
  obtain ⟨T', hT'π, hT'Q, -⟩ := h.linear_of_centralizes htM (hc.LB_centralizes_Z ht.1)
  have hTT' : ∀ e, T e = T' e := fun e => by
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hT x hxQ, hT'π x hxQ]
  have hiso : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => by
    rw [hTT', hT'Q]
  obtain ⟨hTb, hr⟩ := hc.Spure_act h hB hcent ht (T := (T : M₀.E → M₀.E)) hT
  exact eichler_of_isometry M₀ hiso hb0 hTb hr

theorem Ctx.img_inf_QB_lagrangian [CharP K 2] (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀) :
    ∃ W : Submodule K M₀.E, (∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W) ∧
      ∀ v : M₀.E, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W := by
  have hK2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1n : 1 ≤ n := by omega
  have hDQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hVD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD := (hc.card_of_3_3 hw h1n hno (stroth_3_3 hc hw h1n)).2
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (n + 1) := by
    rw [hD, h.card]
  have hE : Module.finrank K M₀.E = 2 * n :=
    Stroth57D.finrank_of_card (n := n) M₀ h.reg h.card hw
  obtain ⟨W, hmem, -, hWo⟩ :=
    Stroth57D.lagrangian_img M₀ h.reg hK2 h.card hE hDQ hVD hDc hDcard
  refine ⟨W, hmem, fun v hv => ?_⟩
  have hvO : v ∈ M₀.B.orthogonal W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [Tim79.QuadModel.B_comm, hv u hu, neg_zero]
  rwa [hWo] at hvO

theorem Ctx.LB_act_flag (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) [CharP K 2] (h : GlobalModelData M Q Z γ M₀) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) {r : G} (hr : r ∈ LB M Q B)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x)) :
    (∀ y : M₀.E, M₀.B (T y - y) b = 0) ∧
      (∀ e ∈ M₀.img (Q ⊓ QB B), ∃ c : K, T e - e = c • b) ∧
      ∀ y : M₀.E, M₀.B y b = 0 → T y - y ∈ M₀.img (Q ⊓ QB B) := by
  have hrM : r ∈ M := hc.LB_le_M hr
  obtain ⟨T', hT'π, hT'Q, -⟩ := h.linear_of_centralizes hrM (hc.LB_centralizes_Z hr)
  have hTT' : ∀ e, T e = T' e := fun e => by
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hT x hxQ, hT'π x hxQ]
  have hiso : ∀ e, M₀.Qf (T e) = M₀.Qf e := fun e => by
    rw [hTT', hT'Q]
  have hTb : T b = b := by
    obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
    rw [← hu, ← hT u huQ]
    exact (M₀.comm_mem_iff huQ ((hc.conj_mem_Q_of_mem_M hrM).1 u huQ)).mp
      (hc.comm_B_mem_Z hr huB)
  have hBZ : ∀ x ∈ (B ⊔ Z : Subgroup G), x ∈ Q ∧ M₀.π x ∈ M₀.img B := by
    intro x hx
    have hle : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := by
      refine sup_le (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩) (fun z hz => ?_)
      refine ⟨h.reg.V_le hz, ?_⟩
      rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
      exact AddSubgroup.zero_mem _
    exact ⟨(hle hx).1, (hle hx).2⟩
  have hcomm_BZ : ∀ d ∈ Q ⊓ QB B, ⁅r, d⁆ ∈ (B ⊔ Z : Subgroup G) := by
    intro d hd
    obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hr
    have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
    have hyd : ⁅y, d⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy (Subgroup.mem_inf.mp hd).1
    have e : ⁅s * y, d⁆ = (s * ⁅y, d⁆ * s⁻¹) * ⁅s, d⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (B ⊔ Z : Subgroup G).mul_mem (Subgroup.mem_sup_right (hsZ _ hyd))
      (Subgroup.mem_sup_left (hc.comm_QB_le_B hs.1 (Subgroup.mem_inf.mp hd).2))
  obtain ⟨W, hWmem, hWperp⟩ := hc.img_inf_QB_lagrangian hw hn hno h
  have hi : ∀ y : M₀.E, M₀.B (T y - y) b = 0 := by
    intro y
    have h1 := Tim79.QuadModel.B_iso hiso y b
    rw [hTb] at h1
    rw [map_sub, LinearMap.sub_apply, h1, sub_self]
  have hii : ∀ e ∈ M₀.img (Q ⊓ QB B), ∃ c : K, T e - e = c • b := by
    rintro _ ⟨d, hd, hdQ, rfl⟩
    obtain ⟨c, hcs⟩ := (hB _).mp (hBZ _ (hcomm_BZ d hd)).2
    refine ⟨c, ?_⟩
    have hkQ : ⁅r, d⁆ ∈ Q := (hBZ _ (hcomm_BZ d hd)).1
    have hkd : ⁅r, d⁆ * d = r * d * r⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [← hT d hdQ, ← hkd, M₀.π_mul _ hkQ _ hdQ, add_sub_cancel_right, hcs]
  have hiii : ∀ y : M₀.E, M₀.B y b = 0 → T y - y ∈ M₀.img (Q ⊓ QB B) := by
    intro y hy
    apply (hWmem _).mpr
    apply hWperp
    intro w hw'
    obtain ⟨d, hd, hdQ, rfl⟩ := (hWmem w).mpr hw'
    obtain ⟨c, hcs⟩ := hii (M₀.π d) (M₀.pi_mem_img hd hdQ)
    have hTe : T (M₀.π d) = M₀.π d + c • b :=
      (sub_eq_iff_eq_add.mp hcs).trans (add_comm _ _)
    have hBTy : M₀.B (T y) b = 0 := by
      have h1 := Tim79.QuadModel.B_iso hiso y b
      rw [hTb, hy] at h1
      exact h1
    have h2 := Tim79.QuadModel.B_iso hiso y (M₀.π d)
    rw [hTe, map_add, map_smul, hBTy, smul_zero, add_zero] at h2
    rw [map_sub, LinearMap.sub_apply, h2, sub_self]
  exact ⟨hi, hii, hiii⟩

end LBFlag

end CFSG.RankThree.GF2n.Stroth80
