module

public import CFSG.RankThree.GF2n.Smith81.Orth28EpsFour
public import CFSG.RankThree.GF2n.Smith81.Orth28DT
public import CFSG.RankThree.GF2n.Smith81.Orth28Dim

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

@[expose, reducible] def OrthCtx.change (C : OrthCtx M Q Z B) (h : GL (Fin 2) C.K)
    (hdet : (h : Matrix (Fin 2) (Fin 2) C.K).det = 1) : OrthCtx M Q Z B :=
  { C with φ := C.φ.trans (orthTensorEquiv h), hF := C.hF.change hdet, hA := C.hA.change hdet }

namespace OrthCaseI

section Matrix2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_unipotent {g : Matrix (Fin 2) (Fin 2) K} (hgg : g * g = 1) (hg : g ≠ 1) :
    ∃ h : GL (Fin 2) K, (h : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      (h : Matrix (Fin 2) (Fin 2) K) * g * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        !![1, 1; 0, 1] := by
  obtain ⟨v, hv⟩ : ∃ e : Fin 2 → K, g *ᵥ e ≠ e := by
    by_contra h
    push Not at h
    apply hg
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
        Pi.single_apply] using this
  set w : Fin 2 → K := g *ᵥ v - v with hw
  have hw0 : w ≠ 0 := fun h => hv (sub_eq_zero.mp h)
  have hgv : g *ᵥ v = v + w := by rw [hw]; abel
  have hgw : g *ᵥ w = w := by
    have h1 : g *ᵥ (g *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
    have h2 : g *ᵥ w = g *ᵥ (g *ᵥ v) - g *ᵥ v := by rw [hw, Matrix.mulVec_sub]
    rw [h2, h1, hgv, show v - (v + w) = -w by abel]
    funext i
    simp [CharTwo.neg_eq]
  set P : Matrix (Fin 2) (Fin 2) K := Matrix.of ![![w 0, v 0], ![w 1, v 1]] with hP
  have hPz : ∀ z : Fin 2 → K, P *ᵥ z = z 0 • w + z 1 • v := by
    intro z
    funext i
    fin_cases i <;> simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPz] at hz
    have h1 : g *ᵥ (z 0 • w + z 1 • v) - (z 0 • w + z 1 • v) = z 1 • w := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hgw, hgv]
      module
    rw [hz, Matrix.mulVec_zero, zero_sub] at h1
    have h2 : z 1 • w = 0 := by
      rw [← h1]
      simp
    have h3 : z 1 = 0 := (smul_eq_zero.mp h2).resolve_right hw0
    rw [h3, zero_smul, add_zero] at hz
    have h4 : z 0 = 0 := (smul_eq_zero.mp hz).resolve_right hw0
    apply hz0
    funext i
    fin_cases i
    · exact h4
    · exact h3
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) P.det⁻¹
  set P' : Matrix (Fin 2) (Fin 2) K := μ • P with hP'
  have hdet' : P'.det = 1 := by
    rw [hP', Matrix.det_smul, Fintype.card_fin, pow_two, ← hμ, inv_mul_cancel₀ hdet]
  have hgP : g * P = P * !![1, 1; 0, 1] := by
    have e0 : g 0 0 * w 0 + g 0 1 * w 1 = w 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hgw 0
    have e1 : g 1 0 * w 0 + g 1 1 * w 1 = w 1 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hgw 1
    have f0 : g 0 0 * v 0 + g 0 1 * v 1 = v 0 + w 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hgv 0
    have f1 : g 1 0 * v 0 + g 1 1 * v 1 = v 1 + w 1 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hgv 1
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination e0
    · simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination f0
    · simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination e1
    · simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination f1
  have hgP' : g * P' = P' * !![1, 1; 0, 1] := by
    rw [hP', Matrix.mul_smul, Matrix.smul_mul, hgP]
  let Pgl : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero P' (by rw [hdet']; exact one_ne_zero)
  have hPgl : (Pgl : Matrix (Fin 2) (Fin 2) K) = P' := rfl
  have hdetPgl : (Pgl : Matrix (Fin 2) (Fin 2) K).det = 1 := by rw [hPgl]; exact hdet'
  refine ⟨Pgl⁻¹, det_units_inv_eq_one Pgl hdetPgl, ?_⟩
  rw [inv_inv, hPgl]
  calc ((Pgl⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * g * P'
      = ((Pgl⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (g * P') := by rw [mul_assoc]
    _ = ((Pgl⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (P' * !![1, 1; 0, 1]) := by
        rw [hgP']
    _ = (((Pgl⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (Pgl : Matrix (Fin 2) (Fin 2) K)) *
          !![1, 1; 0, 1] := by rw [hPgl, mul_assoc]
    _ = !![1, 1; 0, 1] := by rw [Units.inv_mul, one_mul]

end Matrix2

structure InvAct (C : OrthCtx M Q Z B) (x : G) (g : Matrix (Fin 2) (Fin 2) C.K)
    (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) : Prop where
  act : ActsAsTensor Q Z C.M₀ C.φ x g o
  oo : ∀ v, o (o v) = v
  iso : ∀ v, C.qU (o v) = C.qU v
  even : Even (Module.finrank C.K (OrthogonalInvolutions.commSpace o))

section Normal

variable [Finite G]

theorem normal_form (hc : SmithOrthCfg M Q Z B) (hno : NoA2 Q Z (LB M Q B))
    (C : OrthCtx M Q Z B) {x : G} (hxL : x ∈ Lgen M (LB M Q B)) (hx2 : x * x = 1) :
    ∃ o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K), InvAct C x 1 o ∨
      ∃ (h : GL (Fin 2) C.K) (hdet : (h : Matrix (Fin 2) (Fin 2) C.K).det = 1),
        InvAct (C.change h hdet) x !![1, 1; 0, 1] o := by
  obtain ⟨g, o, hact, hgg, hoo, hiso, heven⟩ := lgen_involution_normalized hc hno C hxL hx2
  by_cases hg1 : g = 1
  · subst hg1
    exact ⟨o, Or.inl ⟨hact, hoo, hiso, heven⟩⟩
  · obtain ⟨h, hdet, hh⟩ := exists_conj_unipotent hgg hg1
    refine ⟨o, Or.inr ⟨h, hdet, ?_, hoo, hiso, heven⟩⟩
    have := hact.change h (fun a b => map_add o a b) (fun c a => map_smul o c a)
    rw [hh] at this
    exact this

end Normal

section Group

variable [Finite G] {X : Subgroup G} {x : G}

theorem comm_mem_Z_iff (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {y : G} (hy : y ∈ Q) :
    ⁅y, x⁆ ∈ Z ↔ orthTensor g o (C.φ (C.M₀.π y)) = C.φ (C.M₀.π y) := by
  have H := hc.ctx.hyp
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  have hcQ : ⁅y, x⁆ ∈ Q := comm_mem_Q H hs.memM hy
  rw [← C.M₀.π_ker _ hcQ, ← C.φ.map_eq_zero_iff, OrthEps.phi_pi_commutator C hxQ hy hact,
    sub_eq_zero]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem exists_comm_ne (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) : ∃ q₀ ∈ Q, C.M₀.π ⁅q₀, x⁆ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hs.notQ
  refine mem_Q_of_pi_conj_eq (M₀ := C.M₀) hc.ctx.hyp hs.memM fun y hy => ?_
  have hZ : ⁅y, x⁆ ∈ Z := (C.M₀.π_ker _ (comm_mem_Q hc.ctx.hyp hs.memM hy)).mp (hcon y hy)
  have hfix := (comm_mem_Z_iff hc C hs hact hy).mp hZ
  apply C.φ.injective
  rw [hact y hy, hfix]

theorem exists_comm_rep (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {y : G} (hy : y ∈ Q)
    {p' : (C.ι → C.K) × (C.ι → C.K)} (h : C.φ (C.M₀.π y) = p' - orthTensor g o p') :
    ∃ q₀ ∈ Q, ⁅q₀, x⁆⁻¹ * y ∈ Z ∧ C.φ (C.M₀.π ⁅q₀, x⁆) = C.φ (C.M₀.π y) := by
  have H := hc.ctx.hyp
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  obtain ⟨q₀, hq₀Q, hq₀⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p'
  have hcQ : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hs.memM hq₀Q
  have hφc : C.φ (C.M₀.π ⁅q₀, x⁆) = C.φ (C.M₀.π y) := by
    rw [OrthEps.phi_pi_commutator C hxQ hq₀Q hact, hq₀, h]
  exact ⟨q₀, hq₀Q, (Tim79.QuadModel.pi_eq_iff C.M₀ hcQ hy).mp (C.φ.injective hφc), hφc⟩

theorem theta_of_range (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {y : G} (hy : y ∈ Q)
    {p' : (C.ι → C.K) × (C.ι → C.K)} (h : C.φ (C.M₀.π y) = p' - orthTensor g o p') :
    ⁅x, y⁆ ∈ Z ∧ C.γ ⁅x, y⁆ =
      polar C.qU (C.φ (C.M₀.π y)).1 (C.φ (C.M₀.π y)).2 := by
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  obtain ⟨q₀, hq₀Q, hq₀⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p'
  set c : G := ⁅q₀, x⁆ with hcdef
  have hcQ : c ∈ Q := comm_mem_Q H hs.memM hq₀Q
  have hφc : C.φ (C.M₀.π c) = C.φ (C.M₀.π y) := by
    rw [hcdef, OrthEps.phi_pi_commutator C hxQ hq₀Q hact, hq₀, h]
  have hπ : C.M₀.π c = C.M₀.π y := C.φ.injective hφc
  have hcy : c⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff C.M₀ hcQ hy).mp hπ
  obtain ⟨z₀, hz₀, hyz⟩ : ∃ z₀ ∈ Z, y = c * z₀ := ⟨c⁻¹ * y, hcy, by group⟩
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    have h1 : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
    calc x * c * x⁻¹ = x * q₀ * x * q₀⁻¹ * (x⁻¹ * x⁻¹) := by
          simp only [hcdef, commutatorElement_def]; group
      _ = x * q₀ * x * q₀⁻¹ := by rw [h1, mul_one]
      _ = x * q₀ * x⁻¹ * q₀⁻¹ := by rw [hxinv]
      _ = c⁻¹ := by simp only [hcdef, commutatorElement_def]; group
  have hxy : ⁅x, y⁆ = (c ^ 2)⁻¹ := by
    have hz₀x : x * z₀ * x⁻¹ = z₀ := hxZ z₀ hz₀
    calc ⁅x, y⁆ = x * (c * z₀) * x⁻¹ * (c * z₀)⁻¹ := by
          rw [hyz]; simp only [commutatorElement_def]
      _ = (x * c * x⁻¹) * (x * z₀ * x⁻¹) * z₀⁻¹ * c⁻¹ := by group
      _ = c⁻¹ * z₀ * z₀⁻¹ * c⁻¹ := by rw [hxc, hz₀x]
      _ = (c ^ 2)⁻¹ := by group
  have hc2 : c ^ 2 ∈ Z := C.M₀.sq_mem c hcQ
  refine ⟨by rw [hxy]; exact Z.inv_mem hc2, ?_⟩
  rw [hxy, GM.γ_inv C.hD hc2, CharTwo.neg_eq, C.M₀.sq_eq c hcQ, C.hF.qf, hφc]

theorem mem_comm_of_range (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {y : G} (hy : y ∈ Q)
    {p' : (C.ι → C.K) × (C.ι → C.K)} (h : C.φ (C.M₀.π y) = p' - orthTensor g o p') :
    y ∈ ⁅Q, Subgroup.zpowers x⁆ := by
  have H := hc.ctx.hyp
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  obtain ⟨q₁, hq₁Q, hne⟩ := exists_comm_ne hc C hs hact
  have hZ := OrthEps.Z_le_commutator hc C hq₁Q hne hs.memM
  obtain ⟨q₀, hq₀Q, hq₀⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p'
  have hcQ : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hs.memM hq₀Q
  have hφc : C.φ (C.M₀.π ⁅q₀, x⁆) = C.φ (C.M₀.π y) := by
    rw [OrthEps.phi_pi_commutator C hxQ hq₀Q hact, hq₀, h]
  have hcy : ⁅q₀, x⁆⁻¹ * y ∈ Z :=
    (Tim79.QuadModel.pi_eq_iff C.M₀ hcQ hy).mp (C.φ.injective hφc)
  have : y = ⁅q₀, x⁆ * (⁅q₀, x⁆⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hq₀Q (Subgroup.mem_zpowers x))
    (hZ hcy)

theorem exists_comm_of_hI (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z)
    (hI : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z') : ∀ w ∈ Z, ∃ y ∈ Q, ⁅x, y⁆ = w := by
  intro w hw
  obtain ⟨q, hq, hqx⟩ := hI w⁻¹ (Z.inv_mem hw)
  refine ⟨q⁻¹, Q.inv_mem hq, ?_⟩
  have h1 : q⁻¹ * x⁻¹ * q = w * x⁻¹ := by
    calc q⁻¹ * x⁻¹ * q = (q⁻¹ * x * q)⁻¹ := by group
      _ = (x * w⁻¹)⁻¹ := by rw [hqx]
      _ = w * x⁻¹ := by group
  calc ⁅x, q⁻¹⁆ = x * (q⁻¹ * x⁻¹ * q) := by simp only [commutatorElement_def]; group
    _ = x * (w * x⁻¹) := by rw [h1]
    _ = w := by rw [← mul_assoc]; exact hxZ w hw

end Group

section Range

variable [Finite G] {X : Subgroup G} {x : G}

@[expose] noncomputable def Rsp (C : OrthCtx M Q Z B) (g : Matrix (Fin 2) (Fin 2) C.K)
    (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) :
    Submodule C.K ((C.ι → C.K) × (C.ι → C.K)) :=
  LinearMap.range (orthTensorLin g (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) - 1)

theorem mem_Rsp_iff (C : OrthCtx M Q Z B) (g : Matrix (Fin 2) (Fin 2) C.K)
    (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) {r : (C.ι → C.K) × (C.ι → C.K)} :
    r ∈ Rsp C g o ↔ ∃ p', r = p' - orthTensor g o p' := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨-p, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    have : orthTensor g (⇑o) (-p) = -(orthTensorLin g (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) p) :=
      map_neg (orthTensorLin g (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))) p
    rw [this]
    abel
  · rintro ⟨p', rfl⟩
    refine ⟨-p', ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    have : orthTensor g (⇑o) p' =
        orthTensorLin g (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) p' := rfl
    rw [map_neg, ← this]
    abel

theorem card_preimSub (C : OrthCtx M Q Z B) (hc : SmithOrthCfg M Q Z B)
    (R : Submodule C.K ((C.ι → C.K) × (C.ι → C.K))) :
    Nat.card ↥(OrthDT.preimSub C.M₀ C.φ R) = Nat.card ↥Z * Nat.card ↥R := by
  set S := OrthDT.preimSub C.M₀ C.φ R with hS
  have hZQ : Z ≤ Q := hc.ctx.hyp.Z_normal.1
  have hSQ : S ≤ Q := fun y hy => hy.1
  have hZS : Z ≤ S := fun z hz => by
    refine ⟨hZQ hz, ?_⟩
    rw [(C.M₀.π_ker z (hZQ hz)).mpr hz, map_zero]
    exact R.zero_mem
  have h1 := C.M₀.card_eq hSQ hZS
  have hmem : ∀ r : ↥R, C.φ.symm (r : (C.ι → C.K) × (C.ι → C.K)) ∈ C.M₀.img S := by
    intro r
    obtain ⟨y, hyQ, hy⟩ := C.M₀.π_surj (C.φ.symm (r : (C.ι → C.K) × (C.ι → C.K)))
    refine ⟨y, ⟨hyQ, ?_⟩, hyQ, hy⟩
    rw [hy, LinearEquiv.apply_symm_apply]
    exact r.2
  have himg : Nat.card ↥(C.M₀.img S) = Nat.card ↥R := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun r : ↥R => (⟨C.φ.symm r, hmem r⟩ : ↥(C.M₀.img S)))
      ⟨?_, ?_⟩)
    · intro r r' h
      exact Subtype.ext (C.φ.symm.injective (congrArg Subtype.val h))
    · rintro ⟨e, y, hyS, hyQ, rfl⟩
      refine ⟨⟨C.φ (C.M₀.π y), hyS.2⟩, Subtype.ext ?_⟩
      exact LinearEquiv.symm_apply_apply _ _
  rw [h1, himg]

theorem comm_sup_eq_preimSub (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) {g : Matrix (Fin 2) (Fin 2) C.K}
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) :
    ⁅Q, Subgroup.zpowers x⁆ ⊔ Z = OrthDT.preimSub C.M₀ C.φ (Rsp C g o) := by
  have H := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  apply le_antisymm
  · refine sup_le (Subgroup.commutator_le.mpr fun q hq t ht => ?_) fun z hz => ?_
    · rcases mem_zpowers_of_mul_self_eq_one hs.x_sq ht with rfl | rfl
      · rw [commutatorElement_one_right]
        exact (OrthDT.preimSub C.M₀ C.φ (Rsp C g o)).one_mem
      · refine ⟨comm_mem_Q H hs.memM hq, (mem_Rsp_iff C g o).mpr ⟨C.φ (C.M₀.π q), ?_⟩⟩
        rw [OrthEps.phi_pi_commutator C hxQ hq hact]
    · refine ⟨hZQ hz, ?_⟩
      rw [(C.M₀.π_ker z (hZQ hz)).mpr hz, map_zero]
      exact (Rsp C g o).zero_mem
  · rintro y ⟨hyQ, hy⟩
    obtain ⟨p', hp'⟩ := (mem_Rsp_iff C g o).mp hy
    obtain ⟨q₀, hq₀, hz, -⟩ := exists_comm_rep hc C hs hact hyQ hp'
    have : y = ⁅q₀, x⁆ * (⁅q₀, x⁆⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup
      (Subgroup.commutator_mem_commutator hq₀ (Subgroup.mem_zpowers x)) hz

end Range

section Shapes

variable [Finite G] {X : Subgroup G} {x : G}
  {C : OrthCtx M Q Z B} {g : Matrix (Fin 2) (Fin 2) C.K}
  {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}

theorem InvAct.mem_orth (h : InvAct C x g o) : o ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr h.iso

theorem InvAct.mul_self (h : InvAct C x g o) : o * o = 1 := LinearEquiv.ext fun v => h.oo v

theorem InvAct.fix_of_mem_commSpace (h : InvAct C x g o) {v : C.ι → C.K}
    (hv : v ∈ OrthogonalInvolutions.commSpace o) : o v = v :=
  OrthogonalInvolutions.mem_fixSpace.mp
    (OrthogonalInvolutions.commSpace_le_fixSpace h.mul_self hv)

theorem Rsp_one (C : OrthCtx M Q Z B) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) :
    Rsp C 1 o = (OrthogonalInvolutions.commSpace o).prod (OrthogonalInvolutions.commSpace o) := by
  unfold Rsp
  rw [orthTensorLin_one_sub, LinearMap.range_prodMap]

theorem fixed_mem_Rsp_t (C : OrthCtx M Q Z B) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K))
    (hoo : ∀ v, o (o v) = v) {p : (C.ι → C.K) × (C.ι → C.K)}
    (hp : orthTensor !![1, 1; 0, 1] (⇑o) p = p) : p ∈ Rsp C !![1, 1; 0, 1] o := by
  have hlin : (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) ∘ₗ (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) =
      1 := LinearMap.ext fun v => by simpa using hoo v
  have h := (range_eq_ker_transv (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) hlin
    (s := (1 : C.K)) one_ne_zero).1
  unfold Rsp
  rw [← h, LinearMap.mem_ker]
  show orthTensor !![1, 1; 0, 1] (⇑o) p - p = 0
  rw [hp, sub_self]

theorem orthTensor_one_apply {K ι : Type} [Field K] (o : (ι → K) → (ι → K))
    (p : (ι → K) × (ι → K)) : orthTensor (1 : Matrix (Fin 2) (Fin 2) K) o p = (o p.1, o p.2) := by
  simp [orthTensor, Matrix.one_apply]

theorem orthTensor_t_apply {K ι : Type} [Field K] (o : (ι → K) → (ι → K))
    (p : (ι → K) × (ι → K)) :
    orthTensor (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) o p = (o p.1 + o p.2, o p.2) := by
  simp [orthTensor]

theorem fixed_of_commute (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {d : G} (hd : d ∈ Q) (hdx : d * x = x * d) :
    orthTensor g o (C.φ (C.M₀.π d)) = C.φ (C.M₀.π d) := by
  refine (comm_mem_Z_iff hc C hs hact hd).mp ?_
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hdx]
  exact Z.one_mem

theorem comm_one_of_mem_P (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x 1 o) {y : G}
    (hy : y ∈ Q) (h1 : (C.φ (C.M₀.π y)).1 ∈ OrthogonalInvolutions.commSpace o)
    (h2 : (C.φ (C.M₀.π y)).2 ∈ OrthogonalInvolutions.commSpace o) : ⁅x, y⁆ = 1 := by
  have hR : C.φ (C.M₀.π y) ∈ Rsp C 1 o := by
    rw [Rsp_one]
    exact ⟨h1, h2⟩
  obtain ⟨p', hp'⟩ := (mem_Rsp_iff C 1 o).mp hR
  obtain ⟨hZ, hγ⟩ := theta_of_range hc C hs hI.act hy hp'
  rw [OrthogonalInvolutions.polar_commSpace_eq_zero hI.mem_orth hI.mul_self h1 h2] at hγ
  exact C.hD.reg.inj _ hZ hγ

theorem theta_fixed_t (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o) {y : G}
    (hy : y ∈ Q) (hfix : orthTensor !![1, 1; 0, 1] (⇑o) (C.φ (C.M₀.π y)) = C.φ (C.M₀.π y)) :
    ⁅x, y⁆ ∈ Z ∧ C.γ ⁅x, y⁆ = C.qU (o (C.φ (C.M₀.π y)).1 - (C.φ (C.M₀.π y)).1) := by
  have hR := fixed_mem_Rsp_t C o hI.oo hfix
  obtain ⟨p', hp'⟩ := (mem_Rsp_iff C _ o).mp hR
  obtain ⟨hZ, hγ⟩ := theta_of_range hc C hs hI.act hy hp'
  refine ⟨hZ, hγ.trans ?_⟩
  set a := (C.φ (C.M₀.π y)).1 with ha
  set b := (C.φ (C.M₀.π y)).2 with hb
  have hfix' : (o a + o b, o b) = (a, b) := by
    rw [← orthTensor_t_apply (⇑o) (C.φ (C.M₀.π y))]
    exact hfix
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp hfix'
  simp only at e1 e2
  rw [e2] at e1
  have hb' : b = a - o a := by
    calc b = (o a + b) - o a := by abel
      _ = a - o a := by rw [e1]
  rw [hb', QuadraticMap.polar_sub_right, QuadraticMap.polar_self, two_nsmul,
    ← two_mul, CharTwo.two_eq_zero, zero_mul, zero_sub, CharTwo.neg_eq,
    OrthogonalInvolutions.map_sub_eq_polar hI.mem_orth a, QuadraticMap.polar_comm]

end Shapes

section Coordinates

variable [Finite G] {X : Subgroup G} {x : G}

theorem B_phi (C : OrthCtx M Q Z B) (e e' : C.M₀.E) :
    C.M₀.B e e' = polar C.qU (C.φ e).1 (C.φ e').2 + polar C.qU (C.φ e').1 (C.φ e).2 := by
  have h := C.M₀.Qf_add e e'
  rw [C.hF.qf, C.hF.qf, C.hF.qf, map_add] at h
  simp only [Prod.fst_add, Prod.snd_add, polar_add_left, polar_add_right] at h
  linear_combination (-1 : C.K) * h

theorem comm_x_mem_Z_iff (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) → (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x g o) {y : G} (hy : y ∈ Q) :
    ⁅x, y⁆ ∈ Z ↔ orthTensor g o (C.φ (C.M₀.π y)) = C.φ (C.M₀.π y) := by
  rw [← comm_mem_Z_iff hc C hs hact hy, ← commutatorElement_inv, Z.inv_mem_iff]

theorem mem_commSpace_of_polar_fix {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]
    {qU : QuadraticForm K (ι → K)} (hnd : qU.polarBilin.Nondegenerate)
    {o : (ι → K) ≃ₗ[K] (ι → K)} (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup qU)
    (hoo : o * o = 1) {a : ι → K} (h : ∀ w, o w = w → polar qU a w = 0) :
    a ∈ OrthogonalInvolutions.commSpace o := by
  have hfix := OrthogonalInvolutions.fixSpace_eq_orthogonal_commSpace hnd hO hoo
  have hperp : LinearMap.BilinForm.orthogonal qU.polarBilin (OrthogonalInvolutions.fixSpace o) =
      OrthogonalInvolutions.commSpace o := by
    rw [hfix]
    exact LinearMap.BilinForm.orthogonal_orthogonal hnd
      (QuadraticMap.isSymm_polarBilin qU).isRefl _
  rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rw [OrthogonalInvolutions.mem_fixSpace] at hw
  have := h w hw
  rw [QuadraticMap.polar_comm] at this
  simpa [QuadraticMap.polarBilin_apply_apply] using this

theorem polar_commSpace_fix {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]
    {qU : QuadraticForm K (ι → K)} (hnd : qU.polarBilin.Nondegenerate)
    {o : (ι → K) ≃ₗ[K] (ι → K)} (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup qU)
    (hoo : o * o = 1) {p w : ι → K} (hp : p ∈ OrthogonalInvolutions.commSpace o)
    (hw : o w = w) : polar qU p w = 0 := by
  have hfix := OrthogonalInvolutions.fixSpace_eq_orthogonal_commSpace hnd hO hoo
  have hw' : w ∈ LinearMap.BilinForm.orthogonal qU.polarBilin
      (OrthogonalInvolutions.commSpace o) := by
    rw [← hfix]
    exact OrthogonalInvolutions.mem_fixSpace.mpr hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw'
  simpa [QuadraticMap.polarBilin_apply_apply] using hw' p hp

end Coordinates

end OrthCaseI

end CFSG.RankThree.GF2n.Smith81
