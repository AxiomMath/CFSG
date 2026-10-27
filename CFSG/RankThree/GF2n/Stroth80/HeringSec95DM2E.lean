module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM2D
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM2P

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups Pointwise

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_mul_XB (hc : Ctx M Q Z B) {t : G} {z : G}
    (hz : z ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) :
    ∃ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ∃ v ∈ Vt M (LB M Q B) B Z t, z = a * v := by
  have hnorm : Vt M (LB M Q B) B Z t ≤
      Subgroup.normalizer ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv x hx
    have e : v * x * v⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp hx.2.2 v hv]
      group
    rw [e]
    exact hx
  have hz' : z ∈ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) : Subgroup G) : Set G) *
      (Vt M (LB M Q B) B Z t : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hz
  obtain ⟨a, ha, v, hv, rfl⟩ := hz'
  exact ⟨a, ha, v, hv, rfl⟩

section Setup

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}

theorem qf_phi_inv (hc : Ctx M Q Z B) (M₀ : Tim79.QuadModel Q Z K γ)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (m : ↥(H0 M Z)) (e : M₀.E) : M₀.Qf (φ m e) = M₀.Qf e := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  have hmM : (m : G) ∈ M := m.2.1
  have hyQ : (m : G) * x * (m : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hmM) x).mp hxQ
  rw [← hφπ m x hxQ, ← M₀.sq_eq _ hyQ, ← M₀.sq_eq x hxQ, conj_pow]
  have hx2 : x ^ 2 ∈ Z := M₀.sq_mem x hxQ
  have hcomm : x ^ 2 * (m : G) = (m : G) * x ^ 2 :=
    Subgroup.mem_centralizer_iff.mp m.2.2 (x ^ 2) hx2
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  exact hcomm.symm

namespace SetupW

variable (S : SetupW hc t M₀ φ)

@[expose] noncomputable def thetaN (n : ↥(hc.CN t)) : S.Wq →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  S.VW.liftQ (S.vd.cV ∘ₗ (((actM φ (n : G) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) -
      LinearMap.id) ∘ₗ S.Wsub.subtype)
    (fun w hw => LinearMap.mem_ker.mpr (by
      have h : actM φ (n : G) (w : M₀.E) = w := S.actM_fix_V n.2 hw
      simp [h]))

theorem thetaN_mk (n : ↥(hc.CN t)) (w : S.Wsub) :
    S.thetaN n (S.mkW w) = S.vd.cV (actM φ (n : G) (w : M₀.E) - w) := rfl

theorem thetaN_comm [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    (nn : ↥(hc.CN t)) (hnL : (nn : G) ∈ LB M Q B) (a a' : K) (x : S.Wq) :
    S.thetaN nn (S.Act (M1.uSL a, M1.uSL a') x) =
      M1.uMat a * S.thetaN nn x * (M1.uMat a')ᵀ := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  obtain ⟨l, hl, h1, h2⟩ := S.rhoV_LB_surj h34 hs a a'
  have hρ : rhoV S.vd l = (M1.uSL a, M1.uSL a') := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hlR := le_Rt (M := M) (LB M Q B) S.ht hl
  have hlH : l ∈ H0 M Z := hc.Rt_le_H0 t hlR
  have hnH : (nn : G) ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t nn.2)
  rw [← hρ, S.Act_rhoV hlR]
  have hcomm : ⁅l, (nn : G)⁆ ∈ Q :=
    hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hl hnL)
  have e : l * (nn : G) * l⁻¹ = ⁅l, (nn : G)⁆ * nn := by
    simp only [commutatorElement_def]
    group
  have h1' : actM φ (l * (nn : G) * l⁻¹) = actM φ (nn : G) := by
    rw [e, actM_mul (hc.Q_le_H0 hcomm) hnH, S.actM_eq_one_of_mem_Q hcomm, one_mul]
  have hswap : actM φ (nn : G) (actM φ l (w : M₀.E)) = actM φ l (actM φ (nn : G) (w : M₀.E)) := by
    have h := actM_conj_apply (φ := φ) hlH hnH (w : M₀.E)
    rwa [h1'] at h
  have hu : actM φ (nn : G) (w : M₀.E) - w ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    S.actM_sub_mem_V nn.2 w.2
  have hcv := S.vd.cV_act ⟨l, hlR⟩ _ hu
  have hρ1 : ((S.vd.ρ ⟨l, hlR⟩).1 : Matrix (Fin 2) (Fin 2) K) = M1.uMat a := by
    rw [← rhoV_of_mem S.vd hlR]
    exact h1
  have hρ2 : ((S.vd.ρ ⟨l, hlR⟩).2 : Matrix (Fin 2) (Fin 2) K) = M1.uMat a' := by
    rw [← rhoV_of_mem S.vd hlR]
    exact h2
  rw [hρ1, hρ2] at hcv
  show S.vd.cV (actM φ (nn : G) (actM φ l (w : M₀.E)) - actM φ l (w : M₀.E)) = _
  rw [hswap, ← map_sub]
  have hact : actM φ l (actM φ (nn : G) (w : M₀.E) - w) =
      φ ⟨l, hlH⟩ (actM φ (nn : G) (w : M₀.E) - w) := by
    rw [actM_of_mem hlH]
  rw [hact, hcv]
  rfl

@[expose] noncomputable def Theta : AddSubgroup (S.Wq →ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
  AddSubgroup.closure {θ | ∃ n : ↥(hc.CN t), (n : G) ∈ LB M Q B ∧ θ = S.thetaN n}

theorem Theta_equivariant [CharP K 2] (h34 : Stroth34Statement) {n : ℕ} (hs : Sec9Hyp hc n t)
    {θ : S.Wq →ₗ[K] Matrix (Fin 2) (Fin 2) K} (hθ : θ ∈ S.Theta) (a a' : K) (x : S.Wq) :
    θ (S.Act (M1.uSL a, M1.uSL a') x) = M1.uMat a * θ x * (M1.uMat a')ᵀ := by
  refine AddSubgroup.closure_induction (p := fun θ _ =>
    θ (S.Act (M1.uSL a, M1.uSL a') x) = M1.uMat a * θ x * (M1.uMat a')ᵀ) ?_ ?_ ?_ ?_ hθ
  · rintro θ ⟨nn, hnL, rfl⟩
    exact S.thetaN_comm h34 hs nn hnL a a' x
  · simp
  · intro θ₁ θ₂ _ _ h₁ h₂
    rw [LinearMap.add_apply, LinearMap.add_apply, h₁, h₂, Matrix.mul_add, Matrix.add_mul]
  · intro θ₁ _ h₁
    rw [LinearMap.neg_apply, LinearMap.neg_apply, h₁, Matrix.mul_neg, Matrix.neg_mul]

theorem eq_zero_of_Theta_eq_zero [CharP K 2] (h34 : Stroth34Statement) {n : ℕ}
    (hs : Sec9Hyp hc n t)
    (hwlb : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      (∀ g ∈ LB M Q B, ⁅g, w⁆ ∈ Vt M (LB M Q B) B Z t) →
        w ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
    {x : S.Wq} (hx : x ∈ S.Xfix) (hθ : ∀ θ ∈ S.Theta, θ x = 0) : x = 0 := by
  obtain ⟨w, rfl⟩ := S.mkW_surjective x
  obtain ⟨z, hzX, hzQ, hzw⟩ := (S.mkW_mem_Xfix_iff h34 hs hwlb w).mp hx
  obtain ⟨a, haX, v, hv, rfl⟩ := exists_mul_XB hc hzX
  have haQ : a ∈ Q := haX.2.1
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hcomm : ∀ y ∈ LB M Q B ⊓ hc.CN t, ⁅y, a⁆ ∈ Z := by
    intro y hy
    have hyH : y ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hy.2)
    have h0 := hθ (S.thetaN ⟨y, hy.2⟩) (AddSubgroup.subset_closure ⟨⟨y, hy.2⟩, hy.1, rfl⟩)
    rw [thetaN_mk] at h0
    have hVmem : actM φ y (w : M₀.E) - w ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      S.actM_sub_mem_V hy.2 w.2
    have hfix : actM φ y (w : M₀.E) - w = 0 := S.vd.cV_inj _ hVmem (by simpa using h0)
    have hQav : a * v ∈ Q := Q.mul_mem haQ hvQ
    have h1 : M₀.π ⁅y, a * v⁆ = 0 := by
      rw [S.pi_comm hyH hQav]
      rw [← hzw] at hfix
      exact hfix
    have h2 : ⁅y, a * v⁆ ∈ Z := (M₀.π_ker _ (S.comm_mem_Q hyH.1 hQav)).mp h1
    have h3 : ⁅y, v⁆ ∈ Z := (Ctx.mem_CN.mp hy.2).2 v hv
    have hZn : ∀ g ∈ M, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg) z).mp hz
    have e : ⁅y, a⁆ = ⁅y, a * v⁆ * (a * ⁅y, v⁆ * a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z.mul_mem h2 (Z.inv_mem (hZn a (hc.hyp.Q_normal.1 haQ) _ h3))
  have haV : a ∈ Vt M (LB M Q B) B Z t := p1_95 h34 hs ⟨haQ, haX.1⟩ hcomm
  refine S.mkW_eq_zero_iff.mpr ?_
  show (w : M₀.E) ∈ S.Vsub
  rw [← hzw]
  exact M₀.pi_mem_img ((Vt M (LB M Q B) B Z t).mul_mem haV hv) (Q.mul_mem haQ hvQ)

end SetupW

end Setup

end HS9

end CFSG.RankThree.GF2n.Stroth80
