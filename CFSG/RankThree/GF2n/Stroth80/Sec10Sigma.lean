module

public import CFSG.LinearAlgebra.SLTwoCommutatorForms
public import CFSG.RankThree.GF2n.Stroth80.Sec10Five
public import CFSG.RankThree.GF2n.Stroth80.Sec10SLBasis
public import CFSG.RankThree.GF2n.Stroth80.Sec8CentreModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good103.sub_mem_Vsp_of_orthogonal (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    (τ : M₀.E ≃ₗ[K] M₀.E)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x)) :
    ∀ e, (∀ v ∈ imgSub M₀ (Vt M (LB M Q B) B Z t)
        (fun c _ he => hc.smul_mem_img_Vt hM t c he), M₀.B e v = 0) →
      τ e - e ∈ imgSub M₀ (Vt M (LB M Q B) B Z t)
        (fun c _ he => hc.smul_mem_img_Vt hM t c he) := by
  intro e he
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hV
  have hVQ : V ≤ Q := by rw [hV]; exact hc.Vt_le_Q t
  have horth : ∀ v ∈ M₀.img V, M₀.B e v = 0 := fun v hv => he v hv
  obtain ⟨w, hwW, hwQ, hwe⟩ := M₀.mem_img.mp ((mem_img_Wt_iff M₀ hM.reg hVQ).mpr horth)
  have hcQ : ⁅w, t⁆⁻¹ ∈ Q :=
    Q.inv_mem (hc.comm_mem_Q (hc.LB_le_M ht.1.mem_LB) hwQ)
  have e1 : t * w * t⁻¹ = ⁅w, t⁆⁻¹ * w := by
    rw [commutatorElement_inv w t]
    simp only [commutatorElement_def]
    group
  have himg : τ e - e = M₀.π ⁅w, t⁆⁻¹ := by
    rw [← hwe, ← hTπ w hwQ, e1, M₀.π_mul _ hcQ _ hwQ]
    abel
  have hcm : ⁅w, t⁆⁻¹ ∈ ⁅Wt Q V, Subgroup.zpowers t⁆ :=
    ((⁅Wt Q V, Subgroup.zpowers t⁆ : Subgroup G).inv_mem
      (Subgroup.commutator_mem_commutator (H₁ := Wt Q V)
        (H₂ := Subgroup.zpowers t) hwW (Subgroup.mem_zpowers t)))
  have hmemTt : ⁅w, t⁆⁻¹ ∈ Tt Q Z V t := Subgroup.mem_sup_left hcm
  have hmemV : ⁅w, t⁆⁻¹ ∈ V := by
    rw [hV]
    exact (Sec10Hyp.Tt_le_Vt h34 h311a hspread H ht) (by rwa [hV] at hmemTt)
  rw [himg]
  exact mem_imgSub.mpr (M₀.pi_mem_img hmemV (hVQ hmemV))

private theorem D_le_H0 {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {D : Subgroup G}
    (hD : D ≤ QB Y ⊓ M) : D ≤ H0 M Z :=
  hD.trans (Lx_le_H0 hs (smith_1_12 hs))

private theorem action_fix_of_centralizes {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {d : G} (hd : d ∈ H0 M Z) {S : Subgroup G} (hSQ : S ≤ Q)
    (hfix : ∀ x ∈ S, d * x * d⁻¹ = x) (v : M₀.E) (hv : v ∈ M₀.img S) :
    φ ⟨d, hd⟩ v = v := by
  obtain ⟨x, hxS, hxQ, rfl⟩ := M₀.mem_img.mp hv
  rw [← hφπ ⟨d, hd⟩ x (hSQ hxS), hfix x hxS]

private theorem D_fixes_Vt (hc : Ctx M Q Z B) {Y : Subgroup G} {t : G}
    (ht : Good103 M Q Z B t) (hs : Sit M Q Z Y t) {D : Subgroup G} (hDH0 : D ≤ H0 M Z)
    (hD : D ≤ QB Y ⊓ M) {d : G} (hd : d ∈ D) (x : G)
    (hx : x ∈ Vt M (LB M Q B) B Z t) : d * x * d⁻¹ = x := by
  have hdLx : d ∈ Lx M Y := hD hd
  have hdA : ∀ a ∈ Q ⊓ QB Y, d * a * d⁻¹ = a := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp ((smith_1_13 hs).2.2.1 hdLx) a ha).symm ▸ by group
  have hdZ : ∀ z ∈ Z, d * z * d⁻¹ = z := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hDH0 hd).2 z hz).symm ▸ by group
  rw [Good103.Vt_eq ht hs] at hx
  have hnorm : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun a ha => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (Subgroup.mem_inf.mp ha).1)
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hx
  calc d * (a * z) * d⁻¹ = (d * a * d⁻¹) * (d * z * d⁻¹) := by group
    _ = a * z := by rw [hdA a ha, hdZ z hz]

theorem Good103.actionHom_fixes_img_Vt (hc : Ctx M Q Z B) {Y : Subgroup G} {t : G}
    (ht : Good103 M Q Z B t) (hs : Sit M Q Z Y t) {D : Subgroup G} (hDH0 : D ≤ H0 M Z)
    (hD : D ≤ QB Y ⊓ M) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {d : G} (hd : d ∈ D) {v : M₀.E} (hv : v ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    φ ⟨d, hDH0 hd⟩ v = v :=
  action_fix_of_centralizes hφπ (hDH0 hd) (hc.Vt_le_Q t)
    (fun x hx => D_fixes_Vt hc ht hs hDH0 hD hd x hx) v hv

private theorem D_comm_tau (hc : Ctx M Q Z B) {Y : Subgroup G} {t : G}
    (ht : Good103 M Q Z B t) (hs : Sit M Q Z Y t) {D : Subgroup G} (hDH0 : D ≤ H0 M Z)
    (hD : D ≤ QB Y ⊓ M) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {d : ↥(H0 M Z)} (hd : d ∈ D.subgroupOf (H0 M Z)) (e : M₀.E) :
    φ d (φ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ e) =
      φ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ (φ d e) := by
  have hdD : (d : G) ∈ D := hd
  have hcomm : (d : G) * t = t * (d : G) :=
    (Sit.QB_comm_X hs hs.mem (hD hdD).1).symm
  exact StrothHyp.comm_action hc.hyp (hD hdD).2 (hc.LB_le_M ht.1.mem_LB)
    (by rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]; exact Q.one_mem)
    (fun x hx => hφπ d x hx)
    (fun x hx => hφπ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ x hx) e

private theorem Rt_comm_tau (hc : Ctx M Q Z B) {t : G}
    {r : ↥(H0 M Z)} (hr : (r : G) ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G))
    {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ht : Good103 M Q Z B t) (e : M₀.E) :
    φ r (φ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ e) =
      φ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ (φ r e) :=
  StrothHyp.comm_action hc.hyp (hc.Rt_le_M t hr.1) (hc.LB_le_M ht.1.mem_LB)
    (hc.Rt_comm_mem_Q hr.1)
    (fun x hx => hφπ r x hx)
    (fun x hx => hφπ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ x hx) e

private theorem pi_injOn_A {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {a b : G} (ha : a ∈ Q ⊓ QB Y) (hb : b ∈ Q ⊓ QB Y) (h : M₀.π a = M₀.π b) : a = b := by
  have haQ : a ∈ Q := (Subgroup.mem_inf.mp ha).1
  have hbQ : b ∈ Q := (Subgroup.mem_inf.mp hb).1
  have hmemA : a * b⁻¹ ∈ Q ⊓ QB Y :=
    (Q ⊓ QB Y).mul_mem ha ((Q ⊓ QB Y).inv_mem hb)
  have hpi : M₀.π (a * b⁻¹) = 0 := by
    rw [M₀.π_mul _ haQ _ (Q.inv_mem hbQ), h, M₀.pi_inv hbQ, add_neg_cancel]
  have hmemZ : a * b⁻¹ ∈ Z ⊓ QB Y := ⟨(M₀.π_ker _ hmemA.1).mp hpi, hmemA.2⟩
  rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hmemZ
  exact mul_inv_eq_one.mp hmemZ

private theorem pi_comm_action (hc : Ctx M Q Z B) {K : Type} [Field K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {d x : G} (hd : d ∈ H0 M Z) (hx : x ∈ Q) :
    M₀.π ⁅x, d⁆ = (φ ⟨d, hd⟩ : M₀.E →ₗ[K] M₀.E) (M₀.π x) - M₀.π x := by
  have hdM : d ∈ M := hd.1
  have hxd : d * x * d⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hdM) x).mp hx
  have hx'd : d * x⁻¹ * d⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hdM) x⁻¹).mp (Q.inv_mem hx)
  have hneg : ∀ e : M₀.E, -e = e := fun e => by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h : e + e = 0 := by rw [← two_smul K e, h2, zero_smul]
    exact neg_eq_of_add_eq_zero_right h
  have e : ⁅x, d⁆ = x * (d * x⁻¹ * d⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, M₀.π_mul _ hx _ hx'd, hφπ ⟨d, hd⟩ _ (Q.inv_mem hx), M₀.pi_inv hx, map_neg, hneg,
    sub_eq_add_neg, hneg, LinearEquiv.coe_coe, add_comm]

private theorem pi_Ut_mem_range (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (τ : M₀.E ≃ₗ[K] M₀.E)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    {x : G} (hx : x ∈ Ut Q Z t) : M₀.π x ∈ LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
  have htQ := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1.mem_LB)).1
  have htQ' := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1.mem_LB)).2
  exact (mem_img_comm_zpowers_sup_iff M₀ hM.reg τ htQ htQ' hTπ _).mp
    (M₀.pi_mem_img hx (hc.Ut_le_Q (hc.LB_le_M ht.1.mem_LB) hx))

private noncomputable def psiForm {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {V : Submodule K E}
    (B : LinearMap.BilinForm K E) (b : Module.Basis (Fin 2) K V) (e : E) : E :=
  B e (b 1) • (b 0 : E) + B e (b 0) • (b 1 : E)

private theorem comm_Ut_D_le_A (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {D : Subgroup G} (hD : D ≤ QB Y ⊓ M)
    {x d : G} (hx : x ∈ Ut Q Z t) (hd : d ∈ D) : ⁅x, d⁆ ∈ Q ⊓ QB Y := by
  have ht2 : t * t = 1 := hs.x_sq
  have hxK : x ∈ Kx Q Y := by
    rw [Kx_eq hs (smith_1_12 hs)]
    exact ⟨hc.Ut_le_Q (hc.LB_le_M ht.1.mem_LB) hx,
      Ctx.Ut_le_centralizer h34 hc (H.toSec5 ht.1.mem_LB ht.1.2.2.1)
        (SLMNat.toSLNat hm (by norm_num)) (by rw [sq]; exact ht2) hx⟩
  exact Subgroup.commutator_le.mp (smith_1_13 hs).1 x hxK d (hD hd)

private theorem comm_Ut_of_mu_zero (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {D : Subgroup G} (hD : D ≤ QB Y ⊓ M)
    (hDH0 : D ≤ H0 M Z) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Submodule K M₀.E} (b : Module.Basis (Fin 2) K V)
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    (μ : H0 M Z → K)
    (hμ : ∀ d ∈ D.subgroupOf (H0 M Z), ∀ e,
      φ d (τ e - e) - (τ e - e) = μ d • psiForm M₀.B b e)
    {d : G} (hd : d ∈ D) (hmu : μ ⟨d, hDH0 hd⟩ = 0) :
    ∀ x ∈ Ut Q Z t, x * d = d * x := by
  intro x hx
  obtain ⟨e, he⟩ := LinearMap.mem_range.mp (pi_Ut_mem_range hc ht hM τ hτπ hx)
  have hpi : M₀.π ⁅x, d⁆ = 0 := by
    rw [pi_comm_action hc hφπ (hDH0 hd) (hc.Ut_le_Q (hc.LB_le_M ht.1.mem_LB) hx), ← he]
    have h := hμ ⟨d, hDH0 hd⟩ hd e
    rw [hmu, zero_smul] at h
    simpa [LinearMap.sub_apply] using h
  have hmem : ⁅x, d⁆ ∈ Z ⊓ QB Y :=
    ⟨(M₀.π_ker _ (comm_Ut_D_le_A h34 H ht hm hs hD hx hd).1).mp hpi,
      (comm_Ut_D_le_A h34 H ht hm hs hD hx hd).2⟩
  rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

private theorem commutators_surj_of_mu_ne_zero (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    (hm : SLMNat hc t 2) {Y : Subgroup G} (hs : Sit M Q Z Y t) {D : Subgroup G}
    (hD : D ≤ QB Y ⊓ M) (hDH0 : D ≤ H0 M Z) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Submodule K M₀.E} (b : Module.Basis (Fin 2) K V)
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    (hVA : ∀ a ∈ Q ⊓ QB Y, M₀.π a ∈ V)
    (μ : H0 M Z → K)
    (hμ : ∀ d ∈ D.subgroupOf (H0 M Z), ∀ e,
      φ d (τ e - e) - (τ e - e) = μ d • psiForm M₀.B b e)
    {d : G} (hd : d ∈ D) (hmu : μ ⟨d, hDH0 hd⟩ ≠ 0) :
    ∀ a ∈ Q ⊓ QB Y, ∃ x ∈ Ut Q Z t, ⁅x, d⁆ = a := by
  intro a ha
  let v : V := ⟨M₀.π a, hVA a ha⟩
  let ξ : Fin 2 → K := fun i => (μ ⟨d, hDH0 hd⟩)⁻¹ * b.repr v (if i = 0 then 1 else 0)
  obtain ⟨e, he⟩ := CFSG.LinearAlgebra.exists_apply_basis_eq M₀.B M₀.nondeg V b ξ
  have he0 : M₀.B e (b 0) = ξ 0 := he 0
  have he1 : M₀.B e (b 1) = ξ 1 := he 1
  have hψ : μ ⟨d, hDH0 hd⟩ • psiForm M₀.B b e = M₀.π a := by
    change μ ⟨d, hDH0 hd⟩ • psiForm M₀.B b e = (v : M₀.E)
    have hξ0 : ξ 0 = (μ ⟨d, hDH0 hd⟩)⁻¹ * b.repr v 1 := rfl
    have hξ1 : ξ 1 = (μ ⟨d, hDH0 hd⟩)⁻¹ * b.repr v 0 := rfl
    have hv : (v : M₀.E) = ∑ i, b.repr v i • (b i : M₀.E) := by
      have h : ((∑ i, b.repr v i • b i : V) : M₀.E) =
          ∑ i, b.repr v i • (b i : M₀.E) := by
        rw [Submodule.coe_sum]
        simp
      exact h ▸ congrArg (fun w : V => (w : M₀.E)) (b.sum_repr v).symm
    have hc0 : μ ⟨d, hDH0 hd⟩ * ((μ ⟨d, hDH0 hd⟩)⁻¹ * b.repr v 0) =
        b.repr v 0 := by
      rw [← mul_assoc, mul_inv_cancel₀ hmu, one_mul]
    have hc1 : μ ⟨d, hDH0 hd⟩ * ((μ ⟨d, hDH0 hd⟩)⁻¹ * b.repr v 1) =
        b.repr v 1 := by
      rw [← mul_assoc, mul_inv_cancel₀ hmu, one_mul]
    rw [hv, Fin.sum_univ_two, psiForm, he1, he0, hξ1, hξ0, smul_add, smul_smul, smul_smul,
      hc0, hc1]
  have hrange : τ e - e ∈ M₀.img (Ut Q Z t) := by
    have htQ := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1.mem_LB)).1
    have htQ' := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1.mem_LB)).2
    exact (mem_img_comm_zpowers_sup_iff M₀ hM.reg τ htQ htQ' hτπ _).mpr
      (LinearMap.mem_range.mpr ⟨e, rfl⟩)
  obtain ⟨x, hxU, -, hxπ⟩ := M₀.mem_img.mp hrange
  have hxA : ⁅x, d⁆ ∈ Q ⊓ QB Y := comm_Ut_D_le_A h34 H ht hm hs hD hxU hd
  refine ⟨x, hxU, pi_injOn_A (M₀ := M₀) (γ := γ) hs hxA ha ?_⟩
  rw [pi_comm_action hc hφπ (hDH0 hd) (hc.Ut_le_Q (hc.LB_le_M ht.1.mem_LB) hxU), hxπ]
  have h := hμ ⟨d, hDH0 hd⟩ hd e
  rw [hψ] at h
  simpa [LinearMap.sub_apply] using h

private theorem comm_Ut_or_of_mu (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {D : Subgroup G} (hD : D ≤ QB Y ⊓ M)
    (hDH0 : D ≤ H0 M Z) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Submodule K M₀.E} (b : Module.Basis (Fin 2) K V)
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    (hVA : ∀ a ∈ Q ⊓ QB Y, M₀.π a ∈ V)
    (μ : H0 M Z → K)
    (hμ : ∀ d ∈ D.subgroupOf (H0 M Z), ∀ e,
      φ d (τ e - e) - (τ e - e) = μ d • psiForm M₀.B b e)
    {d : G} (hd : d ∈ D) :
    (∀ x ∈ Ut Q Z t, x * d = d * x) ∨
      ∀ a ∈ Q ⊓ QB Y, ∃ x ∈ Ut Q Z t, ⁅x, d⁆ = a := by
  by_cases hmu : μ ⟨d, hDH0 hd⟩ = 0
  · exact Or.inl (comm_Ut_of_mu_zero h34 H ht hm hs hD hDH0 hM hφπ b τ hτπ μ hμ hd hmu)
  · exact Or.inr (commutators_surj_of_mu_ne_zero h34 H ht hm hs hD hDH0 hM hφπ b τ hτπ
      hVA μ hμ hd hmu)

private theorem card_commutators_le (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {D : Subgroup G} (hD : D ≤ QB Y ⊓ M)
    (hDH0 : D ≤ H0 M Z) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Submodule K M₀.E} (b : Module.Basis (Fin 2) K V)
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    (μ : H0 M Z → K)
    (hμ : ∀ d ∈ D.subgroupOf (H0 M Z), ∀ e,
      φ d (τ e - e) - (τ e - e) = μ d • psiForm M₀.B b e)
    {u : G} (hu : u ∈ Ut Q Z t) :
    Nat.card {c : G // ∃ d ∈ D, ⁅u, d⁆ = c} ≤ Nat.card Z := by
  obtain ⟨e, he⟩ := LinearMap.mem_range.mp (pi_Ut_mem_range hc ht hM τ hτπ hu)
  let F : {c : G // ∃ d ∈ D, ⁅u, d⁆ = c} → K := fun c =>
    μ ⟨Classical.choose c.2, hDH0 (Classical.choose_spec c.2).1⟩
  have hF : Function.Injective F := by
    intro c1 c2 h
    let d1 := Classical.choose c1.2
    let d2 := Classical.choose c2.2
    have h1 := Classical.choose_spec c1.2
    have h2 := Classical.choose_spec c2.2
    have hμeq : μ ⟨d1, hDH0 h1.1⟩ = μ ⟨d2, hDH0 h2.1⟩ := h
    have hA1 : (c1 : G) ∈ Q ⊓ QB Y := by
      rw [← h1.2]
      exact comm_Ut_D_le_A h34 H ht hm hs hD hu h1.1
    have hA2 : (c2 : G) ∈ Q ⊓ QB Y := by
      rw [← h2.2]
      exact comm_Ut_D_le_A h34 H ht hm hs hD hu h2.1
    have hpi1 : M₀.π (c1 : G) = μ ⟨d1, hDH0 h1.1⟩ • psiForm M₀.B b e :=
      calc M₀.π (c1 : G) = M₀.π ⁅u, d1⁆ := by rw [h1.2.symm]
        _ = μ ⟨d1, hDH0 h1.1⟩ • psiForm M₀.B b e := by
            rw [pi_comm_action hc hφπ (hDH0 h1.1)
              (hc.Ut_le_Q (hc.LB_le_M ht.1.mem_LB) hu), ← he]
            simpa [LinearMap.sub_apply] using hμ ⟨d1, hDH0 h1.1⟩ h1.1 e
    have hpi2 : M₀.π (c2 : G) = μ ⟨d2, hDH0 h2.1⟩ • psiForm M₀.B b e :=
      calc M₀.π (c2 : G) = M₀.π ⁅u, d2⁆ := by rw [h2.2.symm]
        _ = μ ⟨d2, hDH0 h2.1⟩ • psiForm M₀.B b e := by
            rw [pi_comm_action hc hφπ (hDH0 h2.1)
              (hc.Ut_le_Q (hc.LB_le_M ht.1.mem_LB) hu), ← he]
            simpa [LinearMap.sub_apply] using hμ ⟨d2, hDH0 h2.1⟩ h2.1 e
    have hp : M₀.π (c1 : G) = M₀.π (c2 : G) := by
      rw [hpi1, hpi2, hμeq]
    exact Subtype.ext (pi_injOn_A (M₀ := M₀) (γ := γ) hs hA1 hA2 hp)
  have hle := Nat.card_le_card_of_injective F hF
  rwa [hM.card] at hle

private theorem D₀_fixes_tau_sub (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t)
    {D₀ : Subgroup G} (hD₀U : ∀ d ∈ D₀, ∀ x ∈ Ut Q Z t, x * d = d * x)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    {d : ↥(H0 M Z)} (hd : d ∈ D₀.subgroupOf (H0 M Z)) (e : M₀.E) :
    φ d (τ e - e) = τ e - e := by
  have hdD : (d : G) ∈ D₀ := hd
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  have htxQ : ⁅t, x⁆ ∈ Q := by
    rw [show ⁅t, x⁆ = ⁅x, t⁆⁻¹ by rw [← commutatorElement_inv x t]]
    exact Q.inv_mem (hc.comm_mem_Q (hc.LB_le_M ht.1.mem_LB) hxQ)
  have e1 : t * x * t⁻¹ = ⁅t, x⁆ * x := by simp only [commutatorElement_def]; group
  have hτsub : τ (M₀.π x) - M₀.π x = M₀.π ⁅t, x⁆ := by
    rw [← hτπ x hxQ, e1, M₀.π_mul _ htxQ _ hxQ]
    abel
  have hmemUt : ⁅t, x⁆ ∈ Ut Q Z t := by
    rw [show ⁅t, x⁆ = ⁅x, t⁆⁻¹ by rw [← commutatorElement_inv x t]]
    exact (Ut Q Z t).inv_mem (comm_mem_Ut hxQ)
  have hcomm : ⁅t, x⁆ * (d : G) = (d : G) * ⁅t, x⁆ := hD₀U (d : G) hdD ⁅t, x⁆ hmemUt
  have hfix : (d : G) * ⁅t, x⁆ * (d : G)⁻¹ = ⁅t, x⁆ := by
    rw [← hcomm]
    group
  rw [hτsub, ← hφπ d ⁅t, x⁆ htxQ, hfix]

private theorem comm_Ut_or_of_model (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {D D₀ : Subgroup G} (hD : D ≤ QB Y ⊓ M)
    (hD₀ : D₀ ≤ D) (hDnorm : ∀ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ d ∈ D, r * d * r⁻¹ ∈ D)
    (hD₀U : ∀ d ∈ D₀, ∀ x ∈ Ut Q Z t, x * d = d * x)
    (hcard : Nat.card D < Nat.card Z ^ 3 * Nat.card D₀)
    (hDH0 : D ≤ H0 M Z) (hD₀H0 : D₀ ≤ H0 M Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Submodule K M₀.E} (b : Module.Basis (Fin 2) K V)
    (hb : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      ∃ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G), ∃ hr : r ∈ H0 M Z,
        ∀ j, φ ⟨r, hr⟩ (b j) = ∑ i, (A : Matrix (Fin 2) (Fin 2) K) i j • (b i : M₀.E))
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτeq : τ = φ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩)
    (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    (hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f) (hτ2 : ∀ e, τ (τ e) = e)
    (hNV : ∀ e, (∀ v ∈ V, M₀.B e v = 0) → τ e - e ∈ V)
    (hVA : ∀ a ∈ Q ⊓ QB Y, M₀.π a ∈ V)
    (hVmem : ∀ v, v ∈ V ↔ v ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hρB : ∀ h e f, M₀.B (φ h e) (φ h f) = M₀.B e f)
    (hK : 2 < Nat.card K) :
    (∀ d ∈ D, (∀ x ∈ Ut Q Z t, x * d = d * x) ∨ ∀ a ∈ Q ⊓ QB Y, ∃ x ∈ Ut Q Z t, ⁅x, d⁆ = a) ∧
    ∀ u ∈ Ut Q Z t, Nat.card {c : G // ∃ d ∈ D, ⁅u, d⁆ = c} ≤ Nat.card Z := by
  let D' : Subgroup ↥(H0 M Z) := D.subgroupOf (H0 M Z)
  let D₀' : Subgroup ↥(H0 M Z) := D₀.subgroupOf (H0 M Z)
  have hD₀D : D₀' ≤ D' := Subgroup.subgroupOf_mono _ hD₀
  have hDτ : ∀ d ∈ D', ∀ e, φ d (τ e) = τ (φ d e) := by
    intro d hd e
    rw [hτeq]
    exact D_comm_tau hc ht hs hDH0 hD hφπ hd e
  have hDV : ∀ d ∈ D', ∀ v ∈ V, φ d v = v := by
    intro d hd v hv
    simpa using
      Good103.actionHom_fixes_img_Vt hc ht hs hDH0 hD hφπ (d := (d : G)) hd ((hVmem v).mp hv)
  have hD₀U' : ∀ d ∈ D₀', ∀ e, φ d (τ e - e) = τ e - e :=
    fun d hd e => D₀_fixes_tau_sub hc ht hD₀U hφπ τ hτπ hd e
  have hcard' : Nat.card D' < Nat.card K ^ 3 * Nat.card D₀' := by
    have hDcard : Nat.card D' = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH0).toEquiv
    have hD₀card : Nat.card D₀' = Nat.card D₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀H0).toEquiv
    rw [hDcard, hD₀card, hM.card]
    exact hcard
  let Γ : Set ↥(H0 M Z) :=
    {h | (h : G) ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G)}
  have hΓτ : ∀ r ∈ Γ, ∀ e, φ r (τ e) = τ (φ r e) := by
    intro r hr e
    rw [hτeq]
    exact Rt_comm_tau hc hr hφπ ht e
  have hΓD : ∀ r ∈ Γ, ∀ d ∈ D', r * d * r⁻¹ ∈ D' := by
    intro r hr d hd
    exact Subgroup.mem_subgroupOf.mpr (hDnorm (r : G) hr (d : G) hd)
  have hΓ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      ∃ r ∈ Γ, ∀ j, φ r (b j) = ∑ i, (A : Matrix (Fin 2) (Fin 2) K) i j • (b i : M₀.E) := by
    intro A
    obtain ⟨r, hrR, hrH0, hsum⟩ := hb A
    exact ⟨⟨r, hrH0⟩, hrR, hsum⟩
  obtain ⟨μ, hμ⟩ := CFSG.LinearAlgebra.exists_sub_one_mul_sub_one_eq_smul
    (K := K) (E := M₀.E) (H := ↥(H0 M Z)) hK M₀.B M₀.alt M₀.nondeg
    φ hρB τ hτB hτ2 V b hNV D' D₀' hD₀D hDτ hDV hD₀U' hcard' Γ hΓτ hΓD hΓ
  refine ⟨fun d hd => comm_Ut_or_of_mu h34 H ht hm hs hD hDH0 hM hφπ (V := V) b τ hτπ
    hVA μ hμ hd, fun u hu => card_commutators_le h34 H ht hm hs hD hDH0 hM hφπ (V := V) b τ
    hτπ μ hμ hu⟩

theorem Good103.comm_Ut_or_of_SL2 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {D D₀ : Subgroup G} (hD : D ≤ QB Y ⊓ M) (hD₀ : D₀ ≤ D)
    (hDnorm : ∀ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G), ∀ d ∈ D,
      r * d * r⁻¹ ∈ D)
    (hD₀U : ∀ d ∈ D₀, ∀ x ∈ Ut Q Z t, x * d = d * x)
    (hcard : Nat.card D < Nat.card Z ^ 3 * Nat.card D₀) :
    (∀ d ∈ D, (∀ x ∈ Ut Q Z t, x * d = d * x) ∨ ∀ a ∈ Q ⊓ QB Y, ∃ x ∈ Ut Q Z t, ⁅x, d⁆ = a) ∧
    ∀ u ∈ Ut Q Z t, Nat.card {c : G // ∃ d ∈ D, ⁅u, d⁆ = c} ≤ Nat.card Z := by
  classical
  have hDH0 : D ≤ H0 M Z := D_le_H0 hs hD
  have hD₀H0 : D₀ ≤ H0 M Z := hD₀.trans hDH0
  obtain ⟨n', γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφQf⟩ := exists_actionHom_H0 hc.hyp hM
  have hK : 2 < Nat.card (GaloisField 2 n') := by
    rw [hM.card]
    have hq4 := hc.hyp.q4
    omega
  let V : Submodule (GaloisField 2 n') M₀.E :=
    imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he)
  obtain ⟨b, hb⟩ := SLMNat.exists_basis_statedSL (m := 2) h34 hspread H ht.1 hm
    (by norm_num) hM φ hφπ
  let tH : ↥(H0 M Z) := ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩
  let τ : M₀.E ≃ₗ[GaloisField 2 n'] M₀.E := φ tH
  have hτeq : τ = φ ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩ := rfl
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ tH x hx
  have hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f := fun e f =>
    quadModel_B_iso M₀ τ (hφQf tH) e f
  have hτ2 : ∀ e, τ (τ e) = e := by
    have h := hc.actionHom_sq_eq_one φ hφQ ht.1.mem_LB
    intro e
    have := congrArg (fun f : M₀.E ≃ₗ[GaloisField 2 n'] M₀.E => f e) h
    simpa [τ, tH, pow_two] using this
  have hNV : ∀ e, (∀ v ∈ V, M₀.B e v = 0) → τ e - e ∈ V :=
    Good103.sub_mem_Vsp_of_orthogonal h34 h311a hspread H ht hM τ hτπ
  have hVA : ∀ a ∈ Q ⊓ QB Y, M₀.π a ∈ V := by
    intro a ha
    have haV : a ∈ Vt M (LB M Q B) B Z t := by
      rw [Good103.Vt_eq ht hs]
      exact Subgroup.mem_sup_left ha
    exact mem_imgSub.mpr (M₀.pi_mem_img haV (hc.Vt_le_Q t haV))
  have hVmem : ∀ v, v ∈ V ↔ v ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun v => Iff.rfl
  have hρB : ∀ h e f, M₀.B (φ h e) (φ h f) = M₀.B e f :=
    fun h e f => quadModel_B_iso M₀ (φ h) (hφQf h) e f
  exact comm_Ut_or_of_model h34 H ht hm hs hD hD₀ hDnorm hD₀U hcard hDH0 hD₀H0
    hM hφπ (V := V) b hb τ hτeq hτπ hτB hτ2 hNV hVA hVmem hρB hK
end CFSG.RankThree.GF2n.Stroth80
