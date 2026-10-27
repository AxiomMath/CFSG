module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
import CFSG.RankThree.GF2n.Smith81.OrthE1Small
import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClOrth

public section

open scoped commutatorElement Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80

section Abstract

variable {G T : Type} [Group G] [Group T]

theorem ct_index_abstract {C R X N Q : Subgroup G} {O Ω : Subgroup T} [Finite T]
    (Θ : ↥C →* T) (hRC : R ≤ C) (hXR : X ≤ R) (hNR : N ≤ R) (hQN : Q ≤ N)
    (hXC : X ≤ C) (hQC : Q ≤ C)
    (hRNX : ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ X, r = n * x)
    (hX : X = ⁅R, R⁆ ⊔ Q)
    (hΩO : Ω ≤ O) (hΩ : Ω = ⁅O, O⁆) (hcard : Nat.card O = 2 * Nat.card Ω)
    (hΘO : ∀ c : ↥C, Θ c ∈ O)
    (hΘX : ∀ (x : G) (hx : x ∈ X), Θ ⟨x, hXC hx⟩ ∈ Ω)
    (hΘX' : ∀ ω ∈ Ω, ∃ x : G, ∃ hx : x ∈ X, Θ ⟨x, hXC hx⟩ = ω)
    (hN1 : ∀ (n : G) (hn : n ∈ N), Θ ⟨n, hRC (hNR hn)⟩ = 1)
    (hker : ∀ (c : G) (hc : c ∈ C), Θ ⟨c, hc⟩ = 1 → c ∈ R) :
    R.relIndex C ≤ 2 ∧ ∀ P : Subgroup G, Q ≤ P → P ≤ C → ⁅P, P⁆ ⊔ Q = P → P ≤ X := by
  have hR : ∀ (c : G) (hc : c ∈ C), c ∈ R ↔ Θ ⟨c, hc⟩ ∈ Ω := by
    intro c hc
    constructor
    · intro hcR
      obtain ⟨n, hn, x, hx, rfl⟩ := hRNX c hcR
      have hnC : n ∈ C := hRC (hNR hn)
      have hxC : x ∈ C := hXC hx
      have h1 : Θ ⟨n * x, hc⟩ = Θ ⟨n, hnC⟩ * Θ ⟨x, hxC⟩ := by
        rw [← map_mul]; rfl
      rw [h1, hN1 n hn, one_mul]
      exact hΘX x hx
    · intro hΘc
      obtain ⟨x, hx, hxΘ⟩ := hΘX' _ hΘc
      have hxC : x ∈ C := hXC hx
      have hk : x⁻¹ * c ∈ R := by
        apply hker (x⁻¹ * c) (C.mul_mem (C.inv_mem hxC) hc)
        have h2 : Θ ⟨x⁻¹ * c, C.mul_mem (C.inv_mem hxC) hc⟩ =
            (Θ ⟨x, hxC⟩)⁻¹ * Θ ⟨c, hc⟩ := by
          rw [← map_inv, ← map_mul]; rfl
        rw [h2, hxΘ, inv_mul_cancel]
      have := R.mul_mem (hXR hx) hk
      simpa using this
  refine ⟨?_, ?_⟩
  ·
    have hsub : R.subgroupOf C = Ω.comap Θ := by
      ext c
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact hR c.1 c.2
    have hrange : Θ.range ≤ O := by
      rintro _ ⟨c, rfl⟩
      exact hΘO c
    have hOΩ : Ω.relIndex O = 2 := by
      have h := Subgroup.relIndex_mul_card (H := Ω) (K := O)
      rw [inf_of_le_left hΩO, hcard] at h
      have hpos : 0 < Nat.card Ω := Nat.card_pos
      have h' : Ω.relIndex O * Nat.card Ω = 2 * Nat.card Ω := by rw [h, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hpos h'
    have hne : Ω.relIndex O ≠ 0 := by rw [hOΩ]; norm_num
    calc R.relIndex C = (Ω.comap Θ).index := by
          rw [← hsub]; rfl
      _ = Ω.relIndex Θ.range := Subgroup.index_comap Ω Θ
      _ ≤ Ω.relIndex O := Subgroup.relIndex_le_of_le_right hrange hne
      _ = 2 := hOΩ
  · intro P hQP hPC hperf
    have hcommR : ⁅P, P⁆ ≤ R := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haC : a ∈ C := hPC ha
      have hbC : b ∈ C := hPC hb
      have hcC : ⁅a, b⁆ ∈ C := by
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem haC hbC) (C.inv_mem haC)) (C.inv_mem hbC)
      refine (hR _ hcC).mpr ?_
      have h1 : Θ ⟨⁅a, b⁆, hcC⟩ = ⁅Θ ⟨a, haC⟩, Θ ⟨b, hbC⟩⁆ := by
        rw [← map_commutatorElement]; rfl
      rw [h1, hΩ]
      exact Subgroup.commutator_mem_commutator (hΘO _) (hΘO _)
    have hQR : Q ≤ R := hQN.trans hNR
    have hPR : P ≤ R := by
      rw [← hperf]
      exact sup_le hcommR hQR
    rw [← hperf, hX]
    exact sup_le_sup (Subgroup.commutator_mono hPR hPR) le_rfl

end Abstract

section Lin

variable {K : Type} [Field K] (S : QSpace K)

theorem ctS_beta_range_eq (h8 : Module.finrank K S.E = 8) {V : Submodule K S.E}
    (h4 : Module.finrank K V = 4) {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) :
    LinearMap.range β = V := by
  have hle : LinearMap.range β ≤ V := by
    rintro _ ⟨e, rfl⟩
    exact hβ.range e
  have hker : LinearMap.ker β = V := by
    ext e
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hβ.ker e h, fun h => hβ.kills e h⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker β
  rw [hker, h4, h8] at hrk
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

theorem beta_section (h8 : Module.finrank K S.E = 8) {V : Submodule K S.E}
    (h4 : Module.finrank K V = 4) {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) :
    ∃ σ : V →ₗ[K] S.E, ∀ v : V, β (σ v) = v := by
  have hr := ctS_beta_range_eq S h8 h4 hβ
  let β' : S.E →ₗ[K] V := LinearMap.codRestrict V β (fun e => hβ.range e)
  have hsurj : LinearMap.range β' = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    have : (v : S.E) ∈ LinearMap.range β := by rw [hr]; exact v.2
    obtain ⟨e, he⟩ := this
    exact ⟨e, Subtype.ext he⟩
  obtain ⟨σ, hσ⟩ := β'.exists_rightInverse_of_surjective hsurj
  refine ⟨σ, fun v => ?_⟩
  have := congrArg (fun f => (f v : S.E)) hσ
  simpa [β'] using this

theorem beta_eq_zero_iff {V : Submodule K S.E} {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β)
    (e : S.E) : β e = 0 ↔ e ∈ V :=
  ⟨fun h => hβ.ker e h, fun h => hβ.kills e h⟩

theorem form_invariant {V : Submodule K S.E} (hTS : S.IsTS V) {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) {σ : V →ₗ[K] S.E} (hσ : ∀ v : V, β (σ v) = v)
    {g : S.E ≃ₗ[K] S.E} (hg : g ∈ S.O) (hgV : ∀ v ∈ V, g v ∈ V)
    (hgβ : ∀ e, g (β e) = β (g e)) (v w : V) :
    S.B (σ ⟨g v, hgV v v.2⟩) (g w) = S.B (σ v) w := by
  set k : S.E := σ ⟨g v, hgV v v.2⟩ - g (σ v) with hk
  have hβk : β k = 0 := by
    rw [hk, map_sub, hσ, ← hgβ, hσ]
    simp
  have hkV : k ∈ V := (beta_eq_zero_iff S hβ k).mp hβk
  have hsplit : σ ⟨g v, hgV v v.2⟩ = g (σ v) + k := by rw [hk]; abel
  have hgw : g (w : S.E) ∈ V := hgV _ w.2
  rw [hsplit, map_add, LinearMap.add_apply, KFLin.B_isometry S hg,
    KFLin.B_zero_of_isTS S hTS hkV hgw, add_zero]

end Lin

section Scalar

variable {K : Type} [Field K]

theorem eq_one_of_sq_eq_one [CharP K 2] {s : K} (h : s * s = 1) : s = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (s - 1) ^ 2 = 0 := by linear_combination h + (1 - s) * h2
  have : s - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  exact sub_eq_zero.mp this

theorem scalar_one_of {ι : Type} [Fintype ι] [DecidableEq ι] [CharP K 2]
    (Q : QuadraticForm K (ι → K)) (G A : Matrix ι ι K) (c0 : K)
    (hG : G = c0 • polarGram ⇑Q) (hG0 : G ≠ 0) (hA : Aᵀ * G * A = G)
    (s : K) (hQs : ∀ v, Q (s • (A *ᵥ v)) = Q v) :
    s = 1 ∧ ∀ v, Q (A *ᵥ v) = Q v := by
  set P := polarGram ⇑Q with hP
  have hc0 : c0 ≠ 0 := by
    rintro rfl
    apply hG0
    rw [hG, zero_smul]
  have hP0 : P ≠ 0 := by
    intro h0
    apply hG0
    rw [hG, h0, smul_zero]
  have hAP : Aᵀ * P * A = P := by
    have h1 : c0 • (Aᵀ * P * A) = c0 • P := by
      have : Aᵀ * G * A = c0 • (Aᵀ * P * A) := by
        rw [hG, Matrix.mul_smul, Matrix.smul_mul]
      rw [← this, hA, hG]
    exact smul_right_injective _ hc0 h1
  have hg : ∀ v, Q ((s • A) *ᵥ v) = Q v := fun v => by
    rw [Matrix.smul_mulVec]
    exact hQs v
  have hT : (s • A)ᵀ * P * (s • A) = P := KFLin.gram_invariant (Q := Q) hg
  have hss : (s * s) • P = P := by
    have h1 : (s • A)ᵀ * P * (s • A) = (s * s) • (Aᵀ * P * A) := by
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    calc (s * s) • P = (s * s) • (Aᵀ * P * A) := by rw [hAP]
      _ = (s • A)ᵀ * P * (s • A) := h1.symm
      _ = P := hT
  have hsq : s * s = 1 := by
    obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hP0 (Matrix.ext fun i j => h i j)
    have h2 := congrArg (fun M : Matrix ι ι K => M i j) hss
    simp only [Matrix.smul_apply, smul_eq_mul] at h2
    have h3 : (s * s - 1) * P i j = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linear_combination h4
    · exact absurd h4 hij
  have hs1 : s = 1 := eq_one_of_sq_eq_one hsq
  refine ⟨hs1, fun v => ?_⟩
  have := hQs v
  rw [hs1, one_smul] at this
  exact this

end Scalar

section Coord

variable {K : Type} [Field K] (S : QSpace K) {ι : Type} [Fintype ι] [DecidableEq ι]

def formBil {V : Submodule K S.E} (σ : V →ₗ[K] S.E) : V →ₗ[K] V →ₗ[K] K :=
  S.B.compl₁₂ σ V.subtype

def coordForm {V : Submodule K S.E} (σ : V →ₗ[K] S.E) (cV : V ≃ₗ[K] (ι → K)) :
    (ι → K) →ₗ[K] (ι → K) →ₗ[K] K :=
  (formBil S σ).compl₁₂ cV.symm.toLinearMap cV.symm.toLinearMap

theorem coordForm_dot (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K) (a a' : ι → K) :
    B a a' = a ⬝ᵥ (LinearMap.toMatrix₂' K B *ᵥ a') := by
  have h := congrArg (fun F : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K => F a a')
    (Matrix.toLinearMap₂'_toMatrix' (R := K) B)
  rw [← h, Matrix.toLinearMap₂'_apply']

theorem gram_conj (B : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K) (T : (ι → K) → (ι → K))
    (A : Matrix ι ι K) (hA : ∀ w, A *ᵥ w = T w) (hinv : ∀ a a', B (T a) (T a') = B a a') :
    Aᵀ * LinearMap.toMatrix₂' K B * A = LinearMap.toMatrix₂' K B := by
  apply KFLin.matrix_eq_of_dotProduct
  intro v w
  rw [← KFLin.dotProduct_conj, hA, hA, ← coordForm_dot B (T v) (T w),
    ← coordForm_dot B v w]
  exact hinv v w

end Coord

section Rep

variable {K : Type} [Field K] (S : QSpace K) {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def glEquiv : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

theorem glEquiv_mulVec (A : GL ι K) (w : ι → K) :
    glEquiv A w = (A : Matrix ι ι K) *ᵥ w := by
  unfold glEquiv
  rw [MulEquiv.trans_apply]
  simp [LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply]

@[expose] noncomputable def restrV {G : Type} [Group G] {V : Submodule K S.E}
    (ψ : G → (S.E ≃ₗ[K] S.E)) (c : G) (hc : V.map (ψ c : S.E →ₗ[K] S.E) = V) : V ≃ₗ[K] V :=
  LinearEquiv.ofSubmodules (ψ c) V V hc

@[expose] noncomputable def repV {V : Submodule K S.E} (cV : V ≃ₗ[K] (ι → K))
    (e : V ≃ₗ[K] V) : (ι → K) ≃ₗ[K] (ι → K) :=
  cV.symm.trans (e.trans cV)

theorem repV_apply {V : Submodule K S.E} (cV : V ≃ₗ[K] (ι → K)) (e : V ≃ₗ[K] V)
    (x : ι → K) : repV S cV e x = cV (e (cV.symm x)) := rfl

theorem repV_mul {V : Submodule K S.E} (cV : V ≃ₗ[K] (ι → K)) (e f : V ≃ₗ[K] V) :
    repV S cV (e * f) = repV S cV e * repV S cV f := by
  ext x
  rw [repV_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, repV_apply, repV_apply]
  simp

theorem ctS_rep_exists {G : Type} [Group G] {V : Submodule K S.E} (ψ : G → (S.E ≃ₗ[K] S.E))
    (C : Subgroup G) (hψ1 : ψ 1 = 1) (hmul : ∀ c ∈ C, ∀ d ∈ C, ψ (c * d) = ψ c * ψ d)
    (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V) (cV : V ≃ₗ[K] (ι → K)) :
    ∃ Θ : ↥C →* GL ι K, ∀ (c : ↥C) (v : V),
      cV ⟨ψ c v, hV c c.2 v v.2⟩ = (Θ c : Matrix ι ι K) *ᵥ cV v := by
  have hmap : ∀ c ∈ C, V.map (ψ c : S.E →ₗ[K] S.E) = V := by
    intro c hc
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hV c hc v hv
    · intro v hv
      refine ⟨ψ c⁻¹ v, hV c⁻¹ (C.inv_mem hc) v hv, ?_⟩
      have h1 : ψ c (ψ c⁻¹ v) = v := by
        have := hmul c hc c⁻¹ (C.inv_mem hc)
        rw [mul_inv_cancel, hψ1] at this
        have h2 := congrArg (fun f : S.E ≃ₗ[K] S.E => f v) this
        simpa using h2.symm
      exact h1
  let ρ : ↥C →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    MonoidHom.mk' (fun c => repV S cV (restrV S ψ c.1 (hmap c.1 c.2))) (fun c d => by
      rw [← repV_mul S]
      congr 1
      ext v
      simp only [LinearEquiv.mul_apply, restrV, LinearEquiv.ofSubmodules_apply, Subgroup.coe_mul]
      rw [hmul c.1 c.2 d.1 d.2]
      rfl)
  refine ⟨glEquiv.symm.toMonoidHom.comp ρ, fun c v => ?_⟩
  have key : ∀ w : ι → K, (((glEquiv.symm.toMonoidHom.comp ρ) c : GL ι K) : Matrix ι ι K) *ᵥ w =
      repV S cV (restrV S ψ c.1 (hmap c.1 c.2)) w := by
    intro w
    show ((glEquiv.symm (ρ c) : GL ι K) : Matrix ι ι K) *ᵥ w = _
    rw [← glEquiv_mulVec, MulEquiv.apply_symm_apply]
    rfl
  rw [key, repV_apply, LinearEquiv.symm_apply_apply]
  rfl

end Rep

section Isom

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_isometry_of [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hKF2 : NatIrredFor K ⇑Q) (hKF5 : NormalizerOmegaFor K ⇑Q)
    (Gm : Matrix ι ι K) (hGm0 : Gm ≠ 0)
    (hGm : ∀ g ∈ StatedOmega ⇑Q, (g : Matrix ι ι K)ᵀ * Gm * (g : Matrix ι ι K) = Gm)
    (g0 : GL ι K) (hg0 : (g0 : Matrix ι ι K)ᵀ * Gm * (g0 : Matrix ι ι K) = Gm)
    (hnorm : ∀ g ∈ StatedOmega ⇑Q, g0 * g * g0⁻¹ ∈ StatedOmega ⇑Q) :
    g0 ∈ CFSG.MatrixModel.isometryCore ⇑Q := by
  obtain ⟨c0, hc0⟩ := hKF2.2 Gm hGm
  obtain ⟨s, hs0, hs⟩ := hKF5 g0 hnorm
  obtain ⟨-, hiso⟩ := scalar_one_of Q Gm (g0 : Matrix ι ι K) c0 hc0 hGm0 hg0 s hs
  apply Subgroup.subset_closure
  exact hiso

end Isom

section Perfect

theorem kill_of_perfect {G : Type} [Group G] {X Q : Subgroup G} {A : Type} [AddCommGroup A]
    (hperf : ⁅X, X⁆ ⊔ Q = X) (f : G → A) (hmul : ∀ x ∈ X, ∀ y ∈ X, f (x * y) = f x + f y)
    (hQ : ∀ q ∈ Q, f q = 0) : ∀ x ∈ X, f x = 0 := by
  have hf1 : f 1 = 0 := by
    have := hmul 1 X.one_mem 1 X.one_mem
    rw [one_mul] at this
    exact (left_eq_add).mp this
  have hinv : ∀ x ∈ X, f x⁻¹ = - f x := by
    intro x hx
    have := hmul x hx x⁻¹ (X.inv_mem hx)
    rw [mul_inv_cancel, hf1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  let Y : Subgroup G :=
    { carrier := {x | x ∈ X ∧ f x = 0}
      one_mem' := ⟨X.one_mem, hf1⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨X.mul_mem ha.1 hb.1, by rw [hmul a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by rw [hinv a ha.1, ha.2, neg_zero]⟩ }
  have hcomm : ⁅X, X⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ X := by
      rw [commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
    refine ⟨hab, ?_⟩
    have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by rw [commutatorElement_def]
    rw [e, hmul _ (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) b⁻¹ (X.inv_mem hb),
      hmul _ (X.mul_mem ha hb) a⁻¹ (X.inv_mem ha), hmul a ha b hb, hinv a ha, hinv b hb]
    abel
  have hQY : Q ≤ Y := by
    intro q hq
    have hqX : q ∈ X := by
      rw [← hperf]
      exact (le_sup_right : Q ≤ ⁅X, X⁆ ⊔ Q) hq
    exact ⟨hqX, hQ q hq⟩
  have hXY : X ≤ Y := by
    rw [← hperf]
    exact sup_le hcomm hQY
  intro x hx
  exact (hXY hx).2

end Perfect

section Gram

variable {K : Type} [Field K] (S : QSpace K) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gram_inv_of {G : Type} [Group G] {V : Submodule K S.E} (hTS : S.IsTS V)
    {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) {σ : V →ₗ[K] S.E}
    (hσ : ∀ v : V, β (σ v) = v) (cV : V ≃ₗ[K] (ι → K)) (ψ : G → (S.E ≃ₗ[K] S.E))
    (C : Subgroup G) (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V) (hO : ∀ c ∈ C, ψ c ∈ S.O)
    (hβc : ∀ c ∈ C, ∀ e, ψ c (β e) = β (ψ c e))
    (Θ : ↥C →* GL ι K)
    (hΘ : ∀ (c : ↥C) (v : V), cV ⟨ψ c v, hV c c.2 v v.2⟩ = (Θ c : Matrix ι ι K) *ᵥ cV v)
    (c : G) (hc : c ∈ C) :
    (Θ ⟨c, hc⟩ : Matrix ι ι K)ᵀ * LinearMap.toMatrix₂' K (coordForm S σ cV) *
        (Θ ⟨c, hc⟩ : Matrix ι ι K) = LinearMap.toMatrix₂' K (coordForm S σ cV) := by
  apply gram_conj (coordForm S σ cV) (fun a => (Θ ⟨c, hc⟩ : Matrix ι ι K) *ᵥ a)
  · intro w
    rfl
  · intro a a'
    have ha := hΘ ⟨c, hc⟩ (cV.symm a)
    have ha' := hΘ ⟨c, hc⟩ (cV.symm a')
    rw [LinearEquiv.apply_symm_apply] at ha ha'
    unfold coordForm formBil
    simp only [LinearMap.compl₁₂_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    rw [← ha, ← ha', LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact form_invariant S hTS hβ hσ (hO c hc) (hV c hc) (hβc c hc) (cV.symm a)
      (cV.symm a')

theorem gram_ne_zero_of {V : Submodule K S.E} (hperp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V)
    {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) {σ : V →ₗ[K] S.E}
    (hσ : ∀ v : V, β (σ v) = v) (cV : V ≃ₗ[K] (ι → K)) (hV0 : V ≠ ⊥) :
    LinearMap.toMatrix₂' K (coordForm S σ cV) ≠ 0 := by
  intro h
  obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  have hzero : ∀ a a', coordForm S σ cV a a' = 0 := by
    intro a a'
    rw [coordForm_dot, h, Matrix.zero_mulVec, dotProduct_zero]
  have hperp' : σ ⟨v, hvV⟩ ∈ V := by
    apply hperp
    intro w hw
    have := hzero (cV ⟨v, hvV⟩) (cV ⟨w, hw⟩)
    unfold coordForm formBil at this
    simpa [LinearEquiv.symm_apply_apply] using this
  have hβ0 : β (σ ⟨v, hvV⟩) = 0 := (beta_eq_zero_iff S hβ _).mpr hperp'
  rw [hσ] at hβ0
  exact hv0 hβ0

end Gram

section Unip

variable {K : Type} [Field K]

theorem comm_fixes {G : Type} [Group G] {S : QSpace K} {V : Submodule K S.E}
    (ψ : G → (S.E ≃ₗ[K] S.E)) (C R X : Subgroup G) (hψ1 : ψ 1 = 1)
    (hmul : ∀ c ∈ C, ∀ d ∈ C, ψ (c * d) = ψ c * ψ d)
    (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V) (hXC : X ≤ C) (x c : G) (hx : x ∈ C) (hc : c ∈ C)
    (hcfix : ∀ v ∈ V, ψ c v = v) (v : S.E) (hv : v ∈ V) :
    ψ ⁅x, c⁆ v = v := by
  have hinv : ∀ w ∈ V, ψ c⁻¹ w = w := by
    intro w hw
    have h1 : ψ c (ψ c⁻¹ w) = w := by
      have := hmul c hc c⁻¹ (C.inv_mem hc)
      rw [mul_inv_cancel, hψ1] at this
      have h2 := congrArg (fun f : S.E ≃ₗ[K] S.E => f w) this
      simpa using h2.symm
    have hu : ψ c⁻¹ w ∈ V := hV c⁻¹ (C.inv_mem hc) w hw
    rw [← hcfix _ hu, h1]
  have hxinv : ψ x⁻¹ v ∈ V := hV x⁻¹ (C.inv_mem hx) v hv
  have hx1 : ψ x (ψ x⁻¹ v) = v := by
    have := hmul x hx x⁻¹ (C.inv_mem hx)
    rw [mul_inv_cancel, hψ1] at this
    have h2 := congrArg (fun f : S.E ≃ₗ[K] S.E => f v) this
    simpa using h2.symm
  have e : ⁅x, c⁆ = x * (c * (x⁻¹ * (c⁻¹))) := by
    rw [commutatorElement_def]; group
  rw [e, hmul x hx _ (C.mul_mem hc (C.mul_mem (C.inv_mem hx) (C.inv_mem hc))),
    hmul c hc _ (C.mul_mem (C.inv_mem hx) (C.inv_mem hc)),
    hmul x⁻¹ (C.inv_mem hx) _ (C.inv_mem hc)]
  simp only [LinearEquiv.mul_apply]
  rw [hinv v hv, hcfix _ hxinv, hx1]

theorem psi_inv_cancel {G : Type} [Group G] {S : QSpace K} (ψ : G → (S.E ≃ₗ[K] S.E))
    (C : Subgroup G) (hψ1 : ψ 1 = 1) (hmul : ∀ c ∈ C, ∀ d ∈ C, ψ (c * d) = ψ c * ψ d)
    {g : G} (hg : g ∈ C) (u : S.E) :
    ψ g (ψ g⁻¹ u) = u ∧ ψ g⁻¹ (ψ g u) = u := by
  have h1 := hmul g hg g⁻¹ (C.inv_mem hg)
  have h2 := hmul g⁻¹ (C.inv_mem hg) g hg
  rw [mul_inv_cancel, hψ1] at h1
  rw [inv_mul_cancel, hψ1] at h2
  have e1 := congrArg (fun f : S.E ≃ₗ[K] S.E => f u) h1
  have e2 := congrArg (fun f : S.E ≃ₗ[K] S.E => f u) h2
  simp only [LinearEquiv.mul_apply] at e1 e2
  exact ⟨by simpa using e1.symm, by simpa using e2.symm⟩

theorem commute_of_unipotent {G : Type} [Group G] {S : QSpace K} {V : Submodule K S.E}
    {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) (hβne : ∃ e, β e ≠ 0)
    (ψ : G → (S.E ≃ₗ[K] S.E)) (C R X N Q : Subgroup G) (hψ1 : ψ 1 = 1)
    (hmul : ∀ c ∈ C, ∀ d ∈ C, ψ (c * d) = ψ c * ψ d)
    (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V)
    (hXC : X ≤ C) (hXR : X ≤ R) (hRC : R ≤ C) (hQX : Q ≤ X)
    (hperf : ⁅X, X⁆ ⊔ Q = X)
    (hcx : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hQnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hQψ : ∀ q ∈ Q, ψ q = 1)
    (hβR : ∀ r ∈ R, ∀ e, ψ r (β e) = β (ψ r e))
    (hline : ∀ n ∈ N, ∃ l : K, ∀ e, ψ n e = e + l • β e)
    (hkerR : ∀ r ∈ R, (∀ v ∈ V, ψ r v = v) → r ∈ N)
    (c : G) (hc : c ∈ C) (hcfix : ∀ v ∈ V, ψ c v = v) :
    ∀ x ∈ X, ∀ e, ψ x (ψ c e) = ψ c (ψ x e) := by
  obtain ⟨e0, he0⟩ := hβne
  classical
  have hscal : ∀ a : K, (∀ e, a • β e = 0) → a = 0 := fun a ha => by
    rcases smul_eq_zero.mp (ha e0) with h | h
    · exact h
    · exact absurd h he0
  have hββ : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  have hRx : ∀ x ∈ X, ⁅x, c⁆ ∈ R := by
    intro x hx
    rw [commutatorElement_def]
    have e : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [e]
    exact R.mul_mem (hXR hx) (hXR (hcx c hc x⁻¹ (X.inv_mem hx)))
  have hNx : ∀ x ∈ X, ⁅x, c⁆ ∈ N := fun x hx =>
    hkerR _ (hRx x hx) (fun v hv => comm_fixes ψ C R X hψ1 hmul hV hXC x c (hXC hx) hc hcfix v hv)
  have hex : ∀ x ∈ X, ∃ l : K, ∀ e, ψ ⁅x, c⁆ e = e + l • β e := fun x hx =>
    hline _ (hNx x hx)
  let lam : G → K := fun x => if h : x ∈ X then Classical.choose (hex x h) else 0
  have hlam : ∀ x (hx : x ∈ X) e, ψ ⁅x, c⁆ e = e + lam x • β e := by
    intro x hx e
    simp only [lam, dif_pos hx]
    exact Classical.choose_spec (hex x hx) e
  have hmulL : ∀ x ∈ X, ∀ y ∈ X, lam (x * y) = lam x + lam y := by
    intro x hx y hy
    have hxC := hXC hx
    have hdC : ⁅y, c⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem (hXC hy) hc) (C.inv_mem (hXC hy))) (C.inv_mem hc)
    have hdx : ⁅x, c⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hxC hc) (C.inv_mem hxC)) (C.inv_mem hc)
    have hAC : x * (⁅y, c⁆ * x⁻¹) ∈ C := C.mul_mem hxC (C.mul_mem hdC (C.inv_mem hxC))
    have key : ∀ u, ψ (x * (⁅y, c⁆ * x⁻¹)) u = u + lam y • β u := by
      intro u
      have hxR : x ∈ R := hXR hx
      rw [hmul x hxC _ (C.mul_mem hdC (C.inv_mem hxC)), hmul _ hdC x⁻¹ (C.inv_mem hxC)]
      simp only [LinearEquiv.mul_apply]
      rw [hlam y hy (ψ x⁻¹ u), map_add, map_smul, hβR x hxR,
        (psi_inv_cancel ψ C hψ1 hmul hxC u).1]
    have hcomm_split : ⁅x * y, c⁆ = (x * (⁅y, c⁆ * x⁻¹)) * ⁅x, c⁆ := by
      simp only [commutatorElement_def]
      group
    have hpt : ∀ e, ψ ⁅x * y, c⁆ e = e + (lam x + lam y) • β e := by
      intro e
      rw [hcomm_split, hmul _ hAC _ hdx, LinearEquiv.mul_apply, hlam x hx e, key,
        map_add, map_smul, hββ, smul_zero, add_zero, add_smul]
      abel
    have hs : ∀ e, (lam (x * y) - (lam x + lam y)) • β e = 0 := by
      intro e
      have h1 := hlam (x * y) (X.mul_mem hx hy) e
      have h3 : lam (x * y) • β e = (lam x + lam y) • β e :=
        add_left_cancel (h1.symm.trans (hpt e))
      rw [sub_smul, h3, sub_self]
    exact sub_eq_zero.mp (hscal _ hs)
  have hlamQ : ∀ q ∈ Q, lam q = 0 := by
    intro q hq
    have hqX := hQX hq
    have hqc : ⁅q, c⁆ ∈ Q := by
      rw [commutatorElement_def]
      have e : q * c * q⁻¹ * c⁻¹ = q * (c * q⁻¹ * c⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq (hQnorm c hc q⁻¹ (Q.inv_mem hq))
    apply hscal
    intro e
    have h1 := hlam q hqX e
    rw [hQψ _ hqc] at h1
    have h2 : (1 : S.E ≃ₗ[K] S.E) e = e := rfl
    have h3 : e + lam q • β e = e := by rw [← h1, h2]
    calc lam q • β e = (e + lam q • β e) - e := by abel
      _ = e - e := by rw [h3]
      _ = 0 := sub_self e
  have hzero := kill_of_perfect hperf lam hmulL hlamQ
  intro x hx e
  have hxC := hXC hx
  have hexp : ∀ u, ψ ⁅x, c⁆ u = ψ x (ψ c (ψ x⁻¹ (ψ c⁻¹ u))) := by
    intro u
    rw [commutatorElement_def, hmul _ (C.mul_mem (C.mul_mem hxC hc) (C.inv_mem hxC)) c⁻¹
      (C.inv_mem hc), hmul _ (C.mul_mem hxC hc) x⁻¹ (C.inv_mem hxC), hmul x hxC c hc]
    simp only [LinearEquiv.mul_apply]
  have hfix : ψ ⁅x, c⁆ (ψ c (ψ x e)) = ψ c (ψ x e) := by
    rw [hlam x hx, hzero x hx, zero_smul, add_zero]
  rw [hexp, (psi_inv_cancel ψ C hψ1 hmul hc (ψ x e)).2,
    (psi_inv_cancel ψ C hψ1 hmul hxC e).2] at hfix
  exact hfix

end Unip

section UnipLine

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem unip_line {G : Type} [Group G] {S : QSpace K} {V : Submodule K S.E}
    {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) {σ : V →ₗ[K] S.E}
    (hσ : ∀ v : V, β (σ v) = v) (hTS : S.IsTS V)
    (hpar : ∀ g : S.E ≃ₗ[K] S.E, g ∈ S.U V ↔ ∃ β' : S.E →ₗ[K] S.E,
      (∀ e, β' e ∈ V) ∧ (∀ v ∈ V, β' v = 0) ∧ (∀ e, S.B e (β' e) = 0) ∧ ∀ e, g e = e + β' e)
    (ψ : G → (S.E ≃ₗ[K] S.E)) (C X : Subgroup G) (hO : ∀ c ∈ C, ψ c ∈ S.O)
    (hβc : ∀ c ∈ C, ∀ e, ψ c (β e) = β (ψ c e)) (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V)
    (hXC : X ≤ C) (cV : V ≃ₗ[K] (ι → K))
    (Θ : ↥C →* GL ι K)
    (hΘ : ∀ (c : ↥C) (v : V), cV ⟨ψ c v, hV c c.2 v v.2⟩ = (Θ c : Matrix ι ι K) *ᵥ cV v)
    (Q' : QuadraticForm K (ι → K)) (hKF2 : NatIrredFor K ⇑Q')
    (hΘX' : ∀ ω ∈ StatedOmega ⇑Q', ∃ x : G, ∃ hx : x ∈ X, Θ ⟨x, hXC hx⟩ = ω)
    (c : G) (hc : c ∈ C) (hcfix : ∀ v ∈ V, ψ c v = v)
    (hcomm : ∀ x ∈ X, ∀ e, ψ x (ψ c e) = ψ c (ψ x e)) :
    ∃ l : K, ∀ e, ψ c e = e + l • β e := by
  have hUmem : ψ c ∈ S.U V := ⟨hO c hc, fun v hv => hcfix v hv⟩
  obtain ⟨α, hαE, hαV, hαB, hαeq⟩ := (hpar (ψ c)).mp hUmem
  have hαcomm : ∀ x ∈ X, ∀ e, ψ x (α e) = α (ψ x e) := by
    intro x hx e
    have h1 := hcomm x hx e
    rw [hαeq e, hαeq (ψ x e), map_add] at h1
    exact add_left_cancel h1
  have hαS : ∀ x (hx : x ∈ X) (v' : V),
      α (σ ⟨ψ x v', hV x (hXC hx) v' v'.2⟩) = ψ x (α (σ v')) := by
    intro x hx v'
    have hxC := hXC hx
    have hk : σ ⟨ψ x v', hV x hxC v' v'.2⟩ - ψ x (σ v') ∈ V := by
      apply (beta_eq_zero_iff S hβ _).mp
      rw [map_sub, hσ, ← hβc x hxC, hσ]
      simp
    have h1 := hαV _ hk
    have h2 : α (σ ⟨ψ x v', hV x hxC v' v'.2⟩) =
        α (ψ x (σ v')) + α (σ ⟨ψ x v', hV x hxC v' v'.2⟩ - ψ x (σ v')) := by
      rw [← map_add, add_sub_cancel]
    rw [h2, h1, add_zero, hαcomm x hx]
  let αV : V →ₗ[K] V := LinearMap.codRestrict V (α.comp σ) (fun v => hαE (σ v))
  let Mℓ : (ι → K) →ₗ[K] (ι → K) := cV.toLinearMap.comp (αV.comp cV.symm.toLinearMap)
  let M : Matrix ι ι K := LinearMap.toMatrix' Mℓ
  have hMv : ∀ a, M *ᵥ a = Mℓ a := fun a => by
    simp only [M]
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hMl : ∀ a, Mℓ a = cV (αV (cV.symm a)) := fun a => rfl
  have hMcomm : ∀ g ∈ StatedOmega ⇑Q', M * (g : Matrix ι ι K) = (g : Matrix ι ι K) * M := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hΘX' g hg
    have hxC := hXC hx
    have hA : ∀ a, (Θ ⟨x, hxC⟩ : Matrix ι ι K) *ᵥ a =
        cV ⟨ψ x (cV.symm a), hV x hxC _ (cV.symm a).2⟩ := by
      intro a
      have h := hΘ ⟨x, hxC⟩ (cV.symm a)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    have key : ∀ a, (M * (Θ ⟨x, hxC⟩ : Matrix ι ι K)) *ᵥ a =
        ((Θ ⟨x, hxC⟩ : Matrix ι ι K) * M) *ᵥ a := by
      intro a
      have e1 : M *ᵥ ((Θ ⟨x, hxC⟩ : Matrix ι ι K) *ᵥ a) =
          cV ⟨α (σ ⟨ψ x (cV.symm a), hV x hxC _ (cV.symm a).2⟩),
            hαE _⟩ := by
        rw [hA a, hMv, hMl, LinearEquiv.symm_apply_apply]
        rfl
      have e2 : (Θ ⟨x, hxC⟩ : Matrix ι ι K) *ᵥ (M *ᵥ a) =
          cV ⟨ψ x (α (σ (cV.symm a))), hV x hxC _ (hαE _)⟩ := by
        rw [hMv, hMl, hA, LinearEquiv.symm_apply_apply]
        rfl
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2]
      congr 1
      exact Subtype.ext (hαS x hx (cV.symm a))
    ext i j
    simpa [Matrix.mulVec_single_one] using congrFun (key (Pi.single j 1)) i
  obtain ⟨l, hl⟩ := hKF2.1 M hMcomm
  have hαl : ∀ v : V, α (σ v) = l • (v : S.E) := by
    intro v
    have h1 : cV (αV v) = l • cV v := by
      have h2 : M *ᵥ (cV v) = Mℓ (cV v) := hMv _
      have h3 : Mℓ (cV v) = cV (αV v) := by
        rw [hMl, LinearEquiv.symm_apply_apply]
      rw [← h3, ← h2, hl, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h4 : αV v = l • v := by
      apply cV.injective
      rw [h1, map_smul]
    exact congrArg Subtype.val h4
  refine ⟨l, fun e => ?_⟩
  have hk : e - σ ⟨β e, hβ.range e⟩ ∈ V := by
    apply (beta_eq_zero_iff S hβ _).mp
    rw [map_sub, hσ]
    simp
  have h6 : α e = α (σ ⟨β e, hβ.range e⟩) := by
    have h7 := hαV _ hk
    rw [map_sub] at h7
    exact sub_eq_zero.mp h7
  rw [hαeq e, h6, hαl]

end UnipLine


section Final

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mat_eq_of_mulVec {A B : Matrix ι ι K} (h : ∀ w, A *ᵥ w = B *ᵥ w) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem theta_isom_of {G : Type} [Group G] [CharP K 2] {S : QSpace K} {V : Submodule K S.E}
    (hTS : S.IsTS V) {β : S.E →ₗ[K] S.E} (hβ : BetaProps S V β) {σ : V →ₗ[K] S.E}
    (hσ : ∀ v : V, β (σ v) = v) (hperp : ∀ e, (∀ v ∈ V, S.B e v = 0) → e ∈ V)
    (hV0 : V ≠ ⊥) (cV : V ≃ₗ[K] (ι → K)) (ψ : G → (S.E ≃ₗ[K] S.E)) (C X : Subgroup G)
    (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V) (hO : ∀ c ∈ C, ψ c ∈ S.O)
    (hβc : ∀ c ∈ C, ∀ e, ψ c (β e) = β (ψ c e)) (hXC : X ≤ C)
    (hcx : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (Θ : ↥C →* GL ι K)
    (hΘ : ∀ (c : ↥C) (v : V), cV ⟨ψ c v, hV c c.2 v v.2⟩ = (Θ c : Matrix ι ι K) *ᵥ cV v)
    (Q' : QuadraticForm K (ι → K)) (hKF2 : NatIrredFor K ⇑Q') (hKF5 : NormalizerOmegaFor K ⇑Q')
    (hΘX : ∀ (x : G) (hx : x ∈ X), Θ ⟨x, hXC hx⟩ ∈ StatedOmega ⇑Q')
    (hΘX' : ∀ ω ∈ StatedOmega ⇑Q', ∃ x : G, ∃ hx : x ∈ X, Θ ⟨x, hXC hx⟩ = ω) :
    ∀ (c : G) (hc : c ∈ C), Θ ⟨c, hc⟩ ∈ CFSG.MatrixModel.isometryCore ⇑Q' := by
  intro c hc
  apply mem_isometry_of Q' hKF2 hKF5 (LinearMap.toMatrix₂' K (coordForm S σ cV))
    (gram_ne_zero_of S hperp hβ hσ cV hV0)
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := hΘX' g hg
    exact gram_inv_of S hTS hβ hσ cV ψ C hV hO hβc Θ hΘ x (hXC hx)
  · exact gram_inv_of S hTS hβ hσ cV ψ C hV hO hβc Θ hΘ c hc
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := hΘX' g hg
    have h1 : Θ ⟨c, hc⟩ * Θ ⟨x, hXC hx⟩ * (Θ ⟨c, hc⟩)⁻¹ =
        Θ ⟨c * x * c⁻¹, hXC (hcx c hc x hx)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    exact hΘX _ (hcx c hc x hx)

theorem theta_one_of {G : Type} [Group G] {S : QSpace K} {V : Submodule K S.E}
    (cV : V ≃ₗ[K] (ι → K)) (ψ : G → (S.E ≃ₗ[K] S.E)) (C : Subgroup G)
    (hV : ∀ c ∈ C, ∀ v ∈ V, ψ c v ∈ V) (Θ : ↥C →* GL ι K)
    (hΘ : ∀ (c : ↥C) (v : V), cV ⟨ψ c v, hV c c.2 v v.2⟩ = (Θ c : Matrix ι ι K) *ᵥ cV v)
    (n : G) (hn : n ∈ C) (hfix : ∀ v ∈ V, ψ n v = v) : Θ ⟨n, hn⟩ = 1 := by
  apply Units.ext
  rw [Units.val_one]
  apply mat_eq_of_mulVec
  intro w
  have h := hΘ ⟨n, hn⟩ (cV.symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [Matrix.one_mulVec, ← h]
  have hfx : (⟨ψ n (cV.symm w), hV n hn _ (cV.symm w).2⟩ : V) = cV.symm w :=
    Subtype.ext (hfix _ (cV.symm w).2)
  rw [hfx, LinearEquiv.apply_symm_apply]

theorem mem_sup_normalizes {G : Type} [Group G] {R N X : Subgroup G} (hNR : N ≤ R)
    (hnorm : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X) (r : G) (hr : r ∈ N ⊔ X) :
    ∃ n ∈ N, ∃ x ∈ X, r = n * x := by
  let P : Subgroup G :=
    { carrier := {g | ∃ n ∈ N, ∃ x ∈ X, g = n * x}
      one_mem' := ⟨1, N.one_mem, 1, X.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, x, hx, rfl⟩ ⟨n', hn', x', hx', rfl⟩
        refine ⟨n * n', N.mul_mem hn hn', n'⁻¹ * x * n' * x', ?_, ?_⟩
        · have h1 := hnorm n'⁻¹ (R.inv_mem (hNR hn')) x hx
          have e : n'⁻¹ * x * n'⁻¹⁻¹ = n'⁻¹ * x * n' := by group
          rw [e] at h1
          exact X.mul_mem h1 hx'
        · group
      inv_mem' := by
        rintro _ ⟨n, hn, x, hx, rfl⟩
        exact ⟨n⁻¹, N.inv_mem hn, n * x⁻¹ * n⁻¹, hnorm n (hNR hn) x⁻¹ (X.inv_mem hx), by group⟩ }
  have hNP : N ≤ P := fun n hn => ⟨n, hn, 1, X.one_mem, by simp⟩
  have hXP : X ≤ P := fun x hx => ⟨1, N.one_mem, x, hx, by simp⟩
  obtain ⟨n, hn, x, hx, rfl⟩ : ∃ n ∈ N, ∃ x ∈ X, r = n * x := sup_le hNP hXP hr
  exact ⟨n, hn, x, hx, rfl⟩

end Final


@[expose] noncomputable def phiG {G : Type} [Group G] {M Q Z : Subgroup G}
    (AM : ActionModel M Q Z) (g : G) : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E := by
  classical
  exact if h : g ∈ H0 M Z then AM.φ ⟨g, h⟩ else 1

theorem phiG_mem {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z) {g : G}
    (h : g ∈ H0 M Z) : phiG AM g = AM.φ ⟨g, h⟩ := by
  unfold phiG
  rw [dif_pos h]

theorem phiG_one {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z) :
    phiG AM 1 = 1 := by
  rw [phiG_mem AM (H0 M Z).one_mem]
  exact map_one AM.φ

theorem phiG_mul {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z) {c d : G}
    (hc : c ∈ H0 M Z) (hd : d ∈ H0 M Z) : phiG AM (c * d) = phiG AM c * phiG AM d := by
  rw [phiG_mem AM (mul_mem hc hd), phiG_mem AM hc, phiG_mem AM hd, ← map_mul]
  rfl

theorem phiG_ker {G : Type} [Group G] {M Q Z : Subgroup G} (AM : ActionModel M Q Z) {g : G}
    (h : g ∈ H0 M Z) (h1 : phiG AM g = 1) : g ∈ Q := by
  rw [phiG_mem AM h] at h1
  exact (AM.φ_ker ⟨g, h⟩).mp h1




section Main


theorem ctStructure_of (hNK : E1NaturalKStatement) (hSplit : RtSplitStatement)
    (hCN : CtNormalizesStatement) (hLine : NtLineStatement) (_hLC : LemmaCStatement)
    (hKF5 : NormalizerOmegaStatement) : CtStructureStatement := by
  intro G _ _ M Q Z B t hH
  classical
  have hc : Ctx M Q Z B := hH.ctx
  obtain ⟨AM⟩ := ActionModel.nonempty hc.hyp
  obtain ⟨β, hβ, hβRx, hβNx, hβNex⟩ := hLine G M Q Z B t hH AM
  obtain ⟨-, -, hNXsup, hXnorm, hXperf, -, -, -, -⟩ := hSplit G M Q Z B t hH
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have htQ : t ∉ Q := hH.notQ
  have hK4 : 4 ≤ Nat.card AM.K := by
    rw [AM.glob.card]
    exact hc.hyp.q4
  have hfin8 : Module.finrank AM.K AM.M₀.E = 8 := by
    have h := AM.glob.finrank_E hH.sec.width (by omega : 1 < Nat.card AM.K)
    omega
  have hhyp : AM.S.IsHyp := AM.glob.hyperbolic
  have hQH0 : Q ≤ H0 M Z := hc.Q_le_H0
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hNH0 : Nt M (LB M Q B) t ≤ H0 M Z := hNR.trans hRH0
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
  set R := Rt M (LB M Q B) t with hRdef
  set N := Nt M (LB M Q B) t with hNdef
  set X := E1Xpre M Q B t with hXdef
  set C := E1Ct hc t with hCdef
  set V := AM.Vsp hc t with hVdef
  have hRC : R ≤ C := fun r hr => Subgroup.mem_inf.mpr ⟨(hc.Rt_le_CommQ t) hr, hRH0 hr⟩
  have hcomR : ⁅R, R⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  have hXR : X ≤ R := sup_le hcomR (hQN.trans hNR)
  have hXC : X ≤ C := hXR.trans hRC
  have hNC : N ≤ C := hNR.trans hRC
  have hQC : Q ≤ C := hQN.trans hNC
  have hCH0 : C ≤ H0 M Z := fun c hc' => (Subgroup.mem_inf.mp hc').2
  have hCM : ∀ c ∈ C, c ∈ M := fun c hc' => (Subgroup.mem_inf.mp (hCH0 hc')).1
  have hCcomm : ∀ c ∈ C, ⁅c, t⁆ ∈ Q := fun c hc' =>
    (mem_CommQ.mp (Subgroup.mem_inf.mp hc').1).2
  have hXH0 : X ≤ H0 M Z := hXR.trans hRH0
  have hRNX : ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ X, r = n * x := fun r hr =>
    mem_sup_normalizes hNR hXnorm r (by rw [hNXsup]; exact hr)
  have hcxX : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro c hc' x hx
    have h := (hCN G M Q Z B t hH c⁻¹ (hCM _ (C.inv_mem hc')) (hCcomm _ (C.inv_mem hc'))).2.2
    have hx' : x ∈ conjSubgroup c⁻¹ X := by
      rw [h]
      exact hx
    have := mem_conjSubgroup.mp hx'
    simpa using this
  have hQnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc' q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hCM c hc')) q).mp hq
  have hψ1 : phiG AM 1 = 1 := phiG_one AM
  have hψmul : ∀ c ∈ C, ∀ d ∈ C, phiG AM (c * d) = phiG AM c * phiG AM d :=
    fun c hc' d hd => phiG_mul AM (hCH0 hc') (hCH0 hd)
  have hψO : ∀ c ∈ C, phiG AM c ∈ AM.S.O := fun c hc' => by
    rw [phiG_mem AM (hCH0 hc')]
    exact fun e => AM.φ_Qf _ e
  have hψQ : ∀ q ∈ Q, phiG AM q = 1 := fun q hq => by
    rw [phiG_mem AM (hQH0 hq)]
    exact (AM.φ_ker _).mpr hq
  have hψN : ∀ n ∈ N, ∃ l : AM.K, ∀ e, phiG AM n e = e + l • β e := fun n hn => by
    obtain ⟨l, hl⟩ := hβNx ⟨n, hNH0 hn⟩ hn
    exact ⟨l, fun e => by rw [phiG_mem AM (hNH0 hn)]; exact hl e⟩
  have hψNex : ∀ l : AM.K, ∃ n ∈ N, ∀ e, phiG AM n e = e + l • β e := fun l => by
    obtain ⟨x, hxN, hxl⟩ := hβNex l
    exact ⟨x.1, hxN, fun e => by rw [phiG_mem AM x.2]; exact hxl e⟩
  have hψR : ∀ r ∈ R, ∀ e, phiG AM r (β e) = β (phiG AM r e) := fun r hr e => by
    rw [phiG_mem AM (hRH0 hr)]
    exact hβRx ⟨r, hRH0 hr⟩ hr e
  obtain ⟨c₀, hc₀, hc0⟩ : ∃ c₀ : AM.K, c₀ ≠ 0 ∧ ∀ e, phiG AM t e = e + c₀ • β e := by
    obtain ⟨c₀, hc₀⟩ := hψN t htN
    refine ⟨c₀, fun h0 => htQ ?_, hc₀⟩
    apply phiG_ker AM (hNH0 htN)
    ext e
    rw [hc₀ e, h0, zero_smul, add_zero]
    rfl
  have hβc : ∀ c ∈ C, ∀ e, phiG AM c (β e) = β (phiG AM c e) := by
    intro c hc' e
    have htC : t ∈ C := hNC htN
    have hcomC : ⁅c, t⁆ ∈ C := hQC (hCcomm c hc')
    have htCc : t * c ∈ C := C.mul_mem htC hc'
    have hct : phiG AM ⁅c, t⁆ = 1 := hψQ _ (hCcomm c hc')
    have e1 : c * t = ⁅c, t⁆ * (t * c) := by
      simp only [commutatorElement_def]
      group
    have hA : phiG AM (c * t) = phiG AM c * phiG AM t := hψmul c hc' t htC
    have hB : phiG AM (c * t) = phiG AM t * phiG AM c := by
      rw [e1, hψmul _ hcomC _ htCc, hct, one_mul, hψmul t htC c hc']
    have hcomm' : phiG AM c * phiG AM t = phiG AM t * phiG AM c := by
      rw [← hA]
      exact hB
    have hpt : phiG AM c (phiG AM t e) = phiG AM t (phiG AM c e) := by
      have := congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f e) hcomm'
      simpa [LinearEquiv.mul_apply] using this
    rw [hc0 e, map_add, map_smul, hc0 (phiG AM c e)] at hpt
    exact smul_right_injective _ hc₀ (add_left_cancel hpt)
  have hV : ∀ c ∈ C, ∀ v ∈ V, phiG AM c v ∈ V := fun c hc' v hv =>
    (beta_eq_zero_iff AM.S hβ _).mp (by
      rw [← hβc c hc' v, (beta_eq_zero_iff AM.S hβ v).mpr hv, map_zero])
  have hfixN : ∀ n ∈ N, ∀ v ∈ V, phiG AM n v = v := fun n hn v hv => by
    obtain ⟨l, hl⟩ := hψN n hn
    rw [hl v, (beta_eq_zero_iff AM.S hβ v).mpr hv, smul_zero, add_zero]
  have hmemX : ∀ x ∈ X, phiG AM x ∈ AM.actImage X := fun x hx => by
    rw [phiG_mem AM (hXH0 hx)]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have key : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Qf : QuadraticForm AM.K (ι → AM.K))
      (cV : V ≃ₗ[AM.K] (ι → AM.K)), Fintype.card ι = 4 →
      ActsAsNatural AM.S V (AM.actImage X) cV ⇑Qf →
      NatIrredFor AM.K ⇑Qf → NormalizerOmegaFor AM.K ⇑Qf →
      Nat.card (CFSG.MatrixModel.isometryCore ⇑Qf) = 2 * Nat.card (StatedOmega ⇑Qf) →
      R.relIndex C ≤ 2 ∧ ∀ P : Subgroup G, Q ≤ P → P ≤ C → ⁅P, P⁆ ⊔ Q = P → P ≤ X := by
    intro ι _ _ Qf cV hι hAN hK2 hK5 hcard
    obtain ⟨hXV, hcl1, hcl2, hcl3⟩ := hAN
    have hV4 : Module.finrank AM.K V = 4 := by
      rw [LinearEquiv.finrank_eq cV, Module.finrank_fintype_fun_eq_card, hι]
    have hV0 : V ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hV4
      norm_num at hV4
    have hrange : LinearMap.range β = V := ctS_beta_range_eq AM.S hfin8 hV4 hβ
    have hTS : AM.S.IsTS V := by
      intro v hv
      rw [← hrange] at hv
      obtain ⟨e, rfl⟩ := hv
      have hiso : AM.M₀.Qf (AM.φ ⟨t, hNH0 htN⟩ e) = AM.M₀.Qf e := AM.φ_Qf _ e
      have hφt : AM.φ ⟨t, hNH0 htN⟩ e = e + c₀ • β e := by
        rw [← phiG_mem AM (hNH0 htN)]
        exact hc0 e
      rw [hφt] at hiso
      have h1 := AM.M₀.Qf_add e (c₀ • β e)
      have h2 := AM.M₀.Qf_smul c₀ (β e)
      have h3 := hβ.alt e
      rw [h1, h2, LinearMap.map_smul, h3, smul_zero, add_zero] at hiso
      have h4 : c₀ ^ 2 * AM.M₀.Qf (β e) = 0 := by linear_combination hiso
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h5) hc₀
      · exact h5
    have hperp := (parabolic_holds AM.K hK4 AM.S hfin8 hhyp V hTS hV4).1
    have hpar := (parabolic_holds AM.K hK4 AM.S hfin8 hhyp V hTS hV4).2.2.1
    obtain ⟨σ, hσ⟩ := beta_section AM.S hfin8 hV4 hβ
    have hβne : ∃ e, β e ≠ 0 := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
      refine ⟨σ ⟨v, hv⟩, ?_⟩
      rw [hσ ⟨v, hv⟩]
      exact hv0
    have hkerR : ∀ r ∈ R, (∀ v ∈ V, phiG AM r v = v) → r ∈ N := by
      intro r hr hfix
      obtain ⟨n, hn, y, hy, rfl⟩ := hRNX r hr
      have hyfix : ∀ v ∈ V, phiG AM y v = v := by
        intro v hv
        have h1 : phiG AM (n * y) v = phiG AM n (phiG AM y v) := by
          rw [hψmul n (hNC hn) y (hXC hy), LinearEquiv.mul_apply]
        have h2 := hfixN n hn _ (hV y (hXC hy) v hv)
        exact h2.symm.trans (h1.symm.trans (hfix v hv))
      have hyQ : y ∈ Q := phiG_ker AM (hXH0 hy) (hcl3 (phiG AM y) (hmemX y hy) hyfix)
      exact N.mul_mem hn (hQN hyQ)
    obtain ⟨Θ, hΘ⟩ := ctS_rep_exists AM.S (phiG AM) C hψ1 hψmul hV cV
    have hΘeq : ∀ (x : G) (hx : x ∈ X) (A : GL ι AM.K),
        (∀ (v : AM.M₀.E) (hv : v ∈ V),
          cV ⟨phiG AM x v, hV x (hXC hx) v hv⟩ = (A : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩) →
        Θ ⟨x, hXC hx⟩ = A := by
      intro x hx A hA
      apply Units.ext
      apply mat_eq_of_mulVec
      intro w
      have h1 := hΘ ⟨x, hXC hx⟩ (cV.symm w)
      have h2 := hA (cV.symm w).1 (cV.symm w).2
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [Subtype.coe_eta, LinearEquiv.apply_symm_apply] at h2
      exact h1.symm.trans h2
    have hΘX : ∀ (x : G) (hx : x ∈ X), Θ ⟨x, hXC hx⟩ ∈ StatedOmega ⇑Qf := by
      intro x hx
      obtain ⟨A, hA, hAv⟩ := hcl1 (phiG AM x) (hmemX x hx)
      rw [hΘeq x hx A hAv]
      exact hA
    have hΘX' : ∀ ω ∈ StatedOmega ⇑Qf, ∃ x : G, ∃ hx : x ∈ X, Θ ⟨x, hXC hx⟩ = ω := by
      intro ω hω
      obtain ⟨g, hg, hgv⟩ := hcl2 ω hω
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
      refine ⟨y, hyX, hΘeq y hyX ω (fun v hv => ?_)⟩
      have hφ : phiG AM (y : G) v = g v := by
        rw [phiG_mem AM y.2, ← hyg]
      exact (congrArg cV (Subtype.ext hφ)).trans (hgv v hv)
    have hN1 : ∀ (n : G) (hn : n ∈ N), Θ ⟨n, hNC hn⟩ = 1 := fun n hn =>
      theta_one_of (S := AM.S) cV (phiG AM) C hV Θ hΘ n (hNC hn) (hfixN n hn)
    have hΘO : ∀ c : ↥C, Θ c ∈ CFSG.MatrixModel.isometryCore ⇑Qf := fun c =>
      theta_isom_of hTS hβ hσ hperp hV0 cV (phiG AM) C X hV hψO hβc hXC hcxX Θ hΘ Qf hK2 hK5
        hΘX hΘX' c.1 c.2
    have hker : ∀ (c : G) (hc' : c ∈ C), Θ ⟨c, hc'⟩ = 1 → c ∈ R := by
      intro c hc' h1
      have hcfix : ∀ v ∈ V, phiG AM c v = v := by
        intro v hv
        have h2 := hΘ ⟨c, hc'⟩ ⟨v, hv⟩
        rw [h1, Units.val_one, Matrix.one_mulVec] at h2
        exact congrArg Subtype.val (cV.injective h2)
      have hcomm := commute_of_unipotent hβ hβne (phiG AM) C R X N Q hψ1 hψmul hV hXC hXR hRC
        (le_sup_right : Q ≤ ⁅R, R⁆ ⊔ Q) hXperf hcxX hQnorm hψQ hψR hψN hkerR c hc' hcfix
      obtain ⟨l, hl⟩ := unip_line hβ hσ hTS hpar (phiG AM) C X hψO hβc hV hXC cV Θ hΘ Qf hK2
        hΘX' c hc' hcfix hcomm
      obtain ⟨n, hn, hnl⟩ := hψNex l
      have hnC : n ∈ C := hNC hn
      have hcn : phiG AM c = phiG AM n := by
        ext e
        rw [hl e, hnl e]
      have hpt : phiG AM (n⁻¹ * c) = 1 := by
        rw [hψmul n⁻¹ (C.inv_mem hnC) c hc', hcn, ← hψmul n⁻¹ (C.inv_mem hnC) n hnC,
          inv_mul_cancel, hψ1]
      have hq : n⁻¹ * c ∈ Q := phiG_ker AM (hCH0 (C.mul_mem (C.inv_mem hnC) hc')) hpt
      have hcN : c ∈ N := by
        have e : c = n * (n⁻¹ * c) := by group
        rw [e]
        exact N.mul_mem hn (hQN hq)
      exact hNR hcN
    have hΩ : StatedOmega ⇑Qf = ⁅CFSG.MatrixModel.isometryCore ⇑Qf,
        CFSG.MatrixModel.isometryCore ⇑Qf⁆ := rfl
    have hΩO : StatedOmega ⇑Qf ≤ CFSG.MatrixModel.isometryCore ⇑Qf := by
      rw [hΩ, Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
        ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem
          ((CFSG.MatrixModel.isometryCore ⇑Qf).mul_mem ha hb)
          ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem ha))
        ((CFSG.MatrixModel.isometryCore ⇑Qf).inv_mem hb)
    exact ct_index_abstract Θ hRC hXR hNR hQN hXC hQC hRNX rfl hΩO hΩ hcard hΘO hΘX hΘX' hN1 hker
  obtain ⟨hQc, hNc, hsign⟩ := hH.case
  rcases hsign with hPlus | hMinus
  · obtain ⟨cV, hAN⟩ := (hNK G M Q Z B t hH AM).1 ⟨hQc, hNc, hPlus⟩
    have hK2Q : NatIrredFor AM.K ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 AM.K) := by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact (natIrred_holds AM.K hK4).1
    have hK5Q : NormalizerOmegaFor AM.K ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 AM.K) := by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact (hKF5 AM.K hK4).1
    have hcard : Nat.card
        (CFSG.MatrixModel.isometryCore ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 AM.K)) =
        2 * Nat.card (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 AM.K)) := by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      have h1 : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 AM.K)) =
          2 * Nat.card AM.K ^ 2 * (Nat.card AM.K ^ 2 - 1) * (Nat.card AM.K ^ 2 - 1) := by
        have := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoPlus (K := AM.K) 1
        norm_num [Finset.Icc_self] at this
        exact this
      have h2 : Nat.card (StatedOmega (StatedQuadPlus 2 AM.K)) =
          Nat.card AM.K ^ 2 * (Nat.card AM.K ^ 2 - 1) ^ 2 := by
        have h2z := orthE2_card_omega_plus_two hK4
        have hq1 : 1 ≤ Nat.card AM.K ^ 2 := Nat.one_le_pow _ _ (by omega)
        apply Nat.cast_injective (R := ℤ)
        rw [h2z]
        push_cast [Nat.cast_sub hq1]
        ring
      rw [h1, h2]
      ring
    obtain ⟨hI, hP⟩ := key (Fin 2 ⊕ Fin 2) (CFSG.LieType.Universal.Spin.quadPlus 2 AM.K) cV
      (by simp)
      (by rw [CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hAN) hK2Q hK5Q hcard
    exact ⟨hRC, hI, hP⟩
  · obtain ⟨b, c', hirr, cV, hAN⟩ := (hNK G M Q Z B t hH AM).2 ⟨hQc, hNc, hMinus⟩
    have hK2Q : NatIrredFor AM.K ⇑(CFSG.LieType.Universal.Spin.quadMinus 2 AM.K b c') := by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact (natIrred_holds AM.K hK4).2 b c' hirr
    have hK5Q : NormalizerOmegaFor AM.K ⇑(CFSG.LieType.Universal.Spin.quadMinus 2 AM.K b c') := by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact (hKF5 AM.K hK4).2 b c' hirr
    have hcard : Nat.card
        (CFSG.MatrixModel.isometryCore ⇑(CFSG.LieType.Universal.Spin.quadMinus 2 AM.K b c')) =
        2 * Nat.card (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus 2 AM.K b c')) := by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) AM.K b c')) : ℤ) =
          2 * (Nat.card AM.K : ℤ) ^ (1 * (1 + 1)) * ((Nat.card AM.K : ℤ) ^ (1 + 1) + 1) *
            ∏ i ∈ Finset.Icc 1 1, ((Nat.card AM.K : ℤ) ^ (2 * i) - 1) := by
        have := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 1
        simp only [← pow_mul] at this
        exact this
      have h1 : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 AM.K b c')) =
          2 * Nat.card AM.K ^ 2 * (Nat.card AM.K ^ 2 + 1) * (Nat.card AM.K ^ 2 - 1) := by
        have := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoMinus (m := 1) hO
        norm_num [Finset.Icc_self] at this
        exact this
      have h2 : Nat.card (StatedOmega (StatedQuadMinus 2 AM.K b c')) =
          Nat.card AM.K ^ 2 * ((Nat.card AM.K ^ 2 + 1) * (Nat.card AM.K ^ 2 - 1)) := by
        have h2z := orthE2_card_omega_minus_two hirr
        have hq1 : 1 ≤ Nat.card AM.K ^ 2 := Nat.one_le_pow _ _ (by omega)
        apply Nat.cast_injective (R := ℤ)
        rw [h2z]
        push_cast [Nat.cast_sub hq1]
        ring
      rw [h1, h2]
      ring
    have hι : Fintype.card (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) = 4 := by simp
    obtain ⟨hI, hP⟩ := key (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
      (CFSG.LieType.Universal.Spin.quadMinus 2 AM.K b c') cV hι
      (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hAN) hK2Q hK5Q hcard
    exact ⟨hRC, hI, hP⟩

end Main


end CFSG.RankThree.GF2n.Smith81.Smith23E1
