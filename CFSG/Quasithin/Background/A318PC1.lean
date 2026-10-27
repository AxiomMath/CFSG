module

public import CFSG.Quasithin.Background.A318PHat
public import CFSG.RankThree.PartTwo.Sec4.LThreePiField
public import CFSG.RankThree.Asc83Table.Reduction

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.Asc83Table (E9Basis)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix

theorem false_of_centralized_pair {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {x : X} (hx : orderOf x = 3) (hxS : x ∉ S)
    {a b : X} (haS : a ∈ S) (hbS : b ∈ S) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2)
    (hxa : x * a = a * x) (hxb : x * b = b * x) : False := by
  have hcomm : Commute a b := hab
  let E : E9Basis X := E9Basis.ofNe ha hb hcomm ha1 hb1 hba hba2
  have hES : E.sub ≤ S := by
    refine (Subgroup.closure_le S).2 ?_
    rintro _ (rfl | rfl)
    exacts [haS, hbS]
  have hEel : CFSG.Open.IsElemAbelian 3 E.sub :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 E.isElementaryAbelian
  have hEcard : Nat.card E.sub = 3 ^ 2 := by
    rw [E.card]
    norm_num
  have hle : E.sub ≤ Subgroup.centralizer {x} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxa.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxb.symm
  have h3 := three_le_pRank_of_centralizes (hp := ⟨Nat.prime_three⟩) hx hxS hES hEel hEcard
    (fun e he => (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm)
  omega


section SlPi

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_scalar_three (s : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) s) = s ^ 3 :=
  Units.ext (by rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])

theorem diagTau_ne_scalar {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (s : Kˣ) :
    diagTau hτ ≠ GeneralLinearGroup.scalar (Fin 3) s := by
  intro h
  have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) h
  simp [coe_diagTau, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h22
  exact hτ1 (h00.trans h22.symm)

theorem eq_scalar_of_conj_eq_scalar {g D : GL (Fin 3) K} {s : Kˣ}
    (h : g * D * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) s) :
    D = GeneralLinearGroup.scalar (Fin 3) s := by
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s g).eq
  calc D = g⁻¹ * (g * D * g⁻¹) * g := by group
    _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) s * g := by rw [h]
    _ = GeneralLinearGroup.scalar (Fin 3) s := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_E9_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) :
    ∃ (u : Kˣ) (a b : slPi π 3 (p ^ f) K), (u : K) = τ ∧
      (a : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) u ∧
      (b : GL (Fin 3) K) = g * diagTau hτ * g⁻¹ ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ a ^ 2 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set u : Kˣ := Units.mk0 τ hτ0 with hu
  have huτ : (u : K) = τ := rfl
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, huτ]; exact hτ)
  have huT : u ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    cube_root_mem_qSubPi hq ((mem_rootsOfUnity _ _).2 hu3)
  have hsH : GeneralLinearGroup.scalar (Fin 3) u ∈ glPi π 3 (p ^ f) K :=
    (scalar_mem_glPi_iff hK u).2 huT
  have hsdet : ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg Units.val (det_scalar_three u)
    rw [GeneralLinearGroup.val_det_apply] at this
    rw [this, Units.val_pow_eq_pow_val, huτ, hτ]
  have hsL : GeneralLinearGroup.scalar (Fin 3) u ∈ slPi π 3 (p ^ f) K :=
    (mem_slPi_iff hπ).2 ⟨hsH, hsdet⟩
  have hbL : g * diagTau hτ * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ)
  refine ⟨u, ⟨_, hsL⟩, ⟨_, hbL⟩, huτ, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, hu3, map_one]
    rfl
  · apply Subtype.ext
    rw [Subgroup.coe_pow, conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel]
    rfl
  · apply Subtype.ext
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u (g * diagTau hτ * g⁻¹)).eq.symm
  · intro h
    have h1 := congrArg Subtype.val h
    change GeneralLinearGroup.scalar (Fin 3) u = 1 at h1
    rw [← map_one (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K)] at h1
    exact hτ1 (by rw [← huτ, scalar_injective_three h1, Units.val_one])
  · intro h
    have h1 := congrArg Subtype.val h
    change g * diagTau hτ * g⁻¹ = 1 at h1
    have h2 : diagTau hτ = 1 := by
      calc diagTau hτ = g⁻¹ * (g * diagTau hτ * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact diagTau_ne_scalar hτ hτ1 1 (by rw [map_one]; exact h2)
  · intro h
    have h1 := congrArg Subtype.val h
    change g * diagTau hτ * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) u at h1
    exact diagTau_ne_scalar hτ hτ1 u (eq_scalar_of_conj_eq_scalar h1)
  · intro h
    have h1 := congrArg Subtype.val h
    change g * diagTau hτ * g⁻¹ = (GeneralLinearGroup.scalar (Fin 3) u) ^ 2 at h1
    rw [← map_pow] at h1
    exact diagTau_ne_scalar hτ hτ1 (u ^ 2) (eq_scalar_of_conj_eq_scalar h1)

end SlPi

section Action

variable {X : Type} [Group X] {S : Subgroup X} [hSn : S.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem conj_eq_of_slAct_eq {S' : Type*} [Group S'] (e : ↥S ≃* S') (x : X) (s : S')
    (h : slAct e ⟨x, mem_normalizer_of_normal x⟩ s = s) :
    x * ((e.symm s : ↥S) : X) * x⁻¹ = ((e.symm s : ↥S) : X) := by
  have h1 : (S.normalizerMonoidHom ⟨x, mem_normalizer_of_normal x⟩ (e.symm s) : ↥S) = e.symm s := by
    have := congrArg e.symm h
    rwa [slAct_apply, MulEquiv.symm_apply_apply] at this
  exact congrArg (fun l : ↥S => (l : X)) h1

variable [Finite X]

theorem false_of_slPi_pair (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {x : X}
    (hx : orderOf x = 3) (hxS : x ∉ S) (e : ↥S ≃* slPi π 3 (p ^ f) K)
    {a b : slPi π 3 (p ^ f) K} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2)
    (hxa : slAct e ⟨x, mem_normalizer_of_normal x⟩ a = a)
    (hxb : slAct e ⟨x, mem_normalizer_of_normal x⟩ b = b) : False := by
  have hca := conj_eq_of_slAct_eq e x a hxa
  have hcb := conj_eq_of_slAct_eq e x b hxb
  have inj : ∀ {u v : ↥S}, (u : X) = v → u = v := fun h => Subtype.ext h
  refine false_of_centralized_pair hX hx hxS (a := ((e.symm a : ↥S) : X))
    (b := ((e.symm b : ↥S) : X)) (e.symm a).2 (e.symm b).2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have : (e.symm a) ^ 3 = 1 := by rw [← map_pow, ha, map_one]
    exact congrArg Subtype.val this
  · have : (e.symm b) ^ 3 = 1 := by rw [← map_pow, hb, map_one]
    exact congrArg Subtype.val this
  · have : e.symm a * e.symm b = e.symm b * e.symm a := by rw [← map_mul, ← map_mul, hab]
    exact congrArg Subtype.val this
  · intro h
    exact ha1 (e.symm.injective (by rw [map_one]; exact inj h))
  · intro h
    exact hb1 (e.symm.injective (by rw [map_one]; exact inj h))
  · intro h
    exact hba (e.symm.injective (inj h))
  · intro h
    have : e.symm b = e.symm (a ^ 2) := by rw [map_pow]; exact inj h
    exact hba2 (e.symm.injective this)
  · calc x * ((e.symm a : ↥S) : X) = x * ((e.symm a : ↥S) : X) * x⁻¹ * x := by group
      _ = ((e.symm a : ↥S) : X) * x := by rw [hca]
  · calc x * ((e.symm b : ↥S) : X) = x * ((e.symm b : ↥S) : X) * x⁻¹ * x := by group
      _ = ((e.symm b : ↥S) : X) * x := by rw [hcb]

end Action

section Field

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem piCard_mod_three {f₀ : ℕ} (hq : ModThree π (p ^ (3 * f₀))) :
    piCard π (p ^ f₀) % 3 = 1 := by
  have h1 : p ^ (3 * f₀) = (p ^ f₀) ^ 3 := by rw [pow_mul']
  rw [h1] at hq
  have h2 := pow_three_mod_three (p ^ f₀)
  cases π
  · change (p ^ f₀) ^ 3 % 3 = 2 at hq
    change (p ^ f₀) ^ 2 % 3 = 1
    have h3 : p ^ f₀ % 3 = 2 := by omega
    rw [Nat.pow_mod, h3]
  · change (p ^ f₀) ^ 3 % 3 = 1 at hq
    change p ^ f₀ % 3 = 1
    omega

theorem pow_eq_self_of_pow_three {c : K} (hc : c ^ 3 = 1) {r : ℕ} (hr : r % 3 = 1) : c ^ r = c := by
  rw [pow_eq_pow_mod r hc, hr, pow_one]

theorem eq_or_eq_sq_of_pow' {r : ℕ} {φ ψ : K ≃+* K} (hφ : ∀ c, φ c = c ^ r)
    (hψ : (∀ c, ψ c = c ^ r) ∨ ∀ c, ψ c = c ^ (r ^ 2)) : ψ = φ ∨ ψ = φ ^ 2 := by
  rcases hψ with h | h
  · exact Or.inl (RingEquiv.ext fun c => by rw [h, hφ])
  · refine Or.inr (RingEquiv.ext fun c => ?_)
    rw [h, ringAut_sq_apply, hφ, hφ, ← pow_mul, pow_two]

theorem frobGL_scalar {ψ : K ≃+* K} {u : Kˣ} (hu : ψ (u : K) = u) :
    frobGL ψ (GeneralLinearGroup.scalar (Fin 3) u) = GeneralLinearGroup.scalar (Fin 3) u := by
  apply Units.ext
  rw [coe_frobGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hu]

theorem frobGL_diagTau {ψ : K ≃+* K} {τ : K} (hτ : τ ^ 3 = 1) (hψτ : ψ τ = τ) :
    frobGL ψ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_frobGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagTau, hψτ]

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal]

theorem false_of_field (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {x : X} (hx : orderOf x = 3)
    (hxS : x ∉ S) (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : ↥S ≃* slPi π 3 (p ^ f) K) {ψ : K ≃+* K} (hψc : ∀ c : K, c ^ 3 = 1 → ψ c = c)
    (hxψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨x, mem_normalizer_of_normal x⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s) : False := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨u, a, b, huτ, ha, hb, ha3, hb3, hab, ha1, hb1, hba, hba2⟩ :=
    exists_E9_slPi hK hq hτ hτ1 (g := 1) (one_mem _)
  have hψτ : ψ τ = τ := hψc τ hτ
  have hψu : ψ (u : K) = u := by rw [huτ]; exact hψτ
  refine false_of_slPi_pair hX hx hxS e ha3 hb3 hab ha1 hb1 hba hba2 ?_ ?_
  · apply Subtype.ext
    rw [hxψ, ha]
    exact frobGL_scalar hψu
  · apply Subtype.ext
    rw [hxψ, hb, one_mul, inv_one, mul_one]
    exact frobGL_diagTau hτ hψτ

end Field

section Lifts

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool} {e : L ≃* slPi π 3 (p ^ f) K}

theorem isPGLAt_pow {g : G} {y : GL (Fin 3) K} (hy : IsPGLAt e g y) (n : ℕ) :
    IsPGLAt e (g ^ n) (y ^ n) := by
  induction n with
  | zero =>
    simpa using isPGLAt_of_mem_centralizer e
      (Subgroup.one_mem _ : (1 : G) ∈ Subgroup.centralizer (L : Set G))
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact isPGLAt_mul e ih hy

theorem isPGLAt_mul_scalar {g : G} {y z : GL (Fin 3) K} (hy : IsPGLAt e g y)
    (hzs : z ∈ StatedScalars (Fin 3) K) (hzH : z ∈ glPi π 3 (p ^ f) K) :
    IsPGLAt e g (y * z) := by
  refine ⟨mul_mem hy.1 hzH, fun s => ?_⟩
  rw [hy.2 s]
  have hc := commute_of_mem_statedScalars hzs (s : GL (Fin 3) K)
  calc y * (s : GL (Fin 3) K) * y⁻¹ = y * ((s : GL (Fin 3) K) * z) * z⁻¹ * y⁻¹ := by group
    _ = y * (z * (s : GL (Fin 3) K)) * z⁻¹ * y⁻¹ := by rw [hc]
    _ = (y * z) * (s : GL (Fin 3) K) * (y * z)⁻¹ := by group

end Lifts

section Diagonal

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem commute_of_coe_diagonal {M N : GL (Fin 3) K} {d₁ d₂ : Fin 3 → K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = diagonal d₁)
    (hN : (N : Matrix (Fin 3) (Fin 3) K) = diagonal d₂) : M * N = N * M := by
  apply Units.ext
  simp only [Units.val_mul, hM, hN, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem coe_diagonal_mul_scalar {D : GL (Fin 3) K} {d : Fin 3 → K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d) (s : Kˣ) :
    ((D * GeneralLinearGroup.scalar (Fin 3) s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => d i * s) := by
  rw [Units.val_mul, hD, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_mul_diagonal]

theorem not_irreducible_of_conj_diagonal {y g D : GL (Fin 3) K} {d : Fin 3 → K}
    (hgD : g⁻¹ * y * g = D) (hD : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  set e₀ : Fin 3 → K := Pi.single 0 1 with he₀
  set w : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e₀ with hw
  have hyg : (y : Matrix (Fin 3) (Fin 3) K) * g = g * (D : Matrix (Fin 3) (Fin 3) K) := by
    have : y * g = g * D := by rw [← hgD]; group
    exact congrArg (fun m : GL (Fin 3) K => (m : Matrix (Fin 3) (Fin 3) K)) this
  have hDe : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ e₀ = d 0 • e₀ := by
    rw [hD]
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal, he₀]
  have hyw : (y : Matrix (Fin 3) (Fin 3) K) *ᵥ w = d 0 • w := by
    rw [hw, Matrix.mulVec_mulVec, hyg, ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_smul]
  have hw0 : w ≠ 0 := by
    intro h
    have h2 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = e₀ := by
      rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at h2
    have := congrFun h2 0
    simp [he₀] at this
  rcases hirr (K ∙ w) (fun v hv => by
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [Matrix.mulVec_smul, hyw]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)))
    with h | h
  · exact hw0 ((Submodule.span_singleton_eq_bot).1 h)
  · have := finrank_span_singleton (K := K) hw0
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega

section DiagonalFalse

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal]

theorem false_of_diagonal (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {x : X}
    (hx : orderOf x = 3) (hxS : x ∉ S) (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : ↥S ≃* slPi π 3 (p ^ f) K) {y : GL (Fin 3) K} (hy : IsPGLAt e x y)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) {D : GL (Fin 3) K} {d : Fin 3 → K}
    (hgD : g⁻¹ * y * g = D) (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d) : False := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨u, a, b, huτ, ha, hb, ha3, hb3, hab, ha1, hb1, hba, hba2⟩ :=
    exists_E9_slPi hK hq hτ hτ1 hg
  have hyD : y = g * D * g⁻¹ := eq_conj_of_inv_conj hgD
  have hDT : D * diagTau hτ = diagTau hτ * D :=
    commute_of_coe_diagonal hD (coe_diagTau_eq_diagonal hτ)
  refine false_of_slPi_pair hX hx hxS e ha3 hb3 hab ha1 hb1 hba hba2 ?_ ?_
  · apply Subtype.ext
    rw [hy.2 a, ha, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u y).eq,
      mul_inv_cancel_right]
  · apply Subtype.ext
    rw [hy.2 b, hb, hyD]
    calc g * D * g⁻¹ * (g * diagTau hτ * g⁻¹) * (g * D * g⁻¹)⁻¹ =
        g * (D * diagTau hτ * D⁻¹) * g⁻¹ := by group
      _ = g * diagTau hτ * g⁻¹ := by rw [hDT]; group

end DiagonalFalse

section TypeIII

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal]

theorem not_irreducible_of_mul_scalar_diagonal {y g D : GL (Fin 3) K} {d : Fin 3 → K} {s : Kˣ}
    (hgD : g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) s) * g = D)
    (hD : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s g).eq
  have h1 : g⁻¹ * y * g = D * GeneralLinearGroup.scalar (Fin 3) s⁻¹ := by
    rw [map_inv, eq_mul_inv_iff_mul_eq, ← hgD]
    calc g⁻¹ * y * g * GeneralLinearGroup.scalar (Fin 3) s =
        g⁻¹ * y * (g * GeneralLinearGroup.scalar (Fin 3) s) := by rw [mul_assoc]
      _ = g⁻¹ * y * (GeneralLinearGroup.scalar (Fin 3) s * g) := by rw [hc]
      _ = g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) s) * g := by group
  exact not_irreducible_of_conj_diagonal h1 (coe_diagonal_mul_scalar hD s⁻¹) hirr

theorem central_type_iii
    (hQ : CFSG.IsQuasisimple ↥S) (hS2 : 2 ≤ CFSG.Open.pRank 3 S)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (e : ↥S ≃* slPi π 3 (p ^ f) K) {x : X}
    (hx : orderOf x = 3) (hxS : x ∉ S) :
    ∃ y : GL (Fin 3) K, IsPGLAt e x y ∧ y ^ 3 ∈ zPi π 3 (p ^ f) K ∧
      (∀ W : Submodule K (Fin 3 → K),
        (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      (¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∃ z ∈ zPi π 3 (p ^ f) K, y = l * z) ∧
      IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ∧
      Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) =
        qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have : Group.IsPerfect ↥S := hQ.1
  have hθ := aschbacherSolvableCore_eq_bot_of_slPi hK hq hQ e
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hσ3 : (⟨x, mem_normalizer_of_normal x⟩ : Subgroup.normalizer (S : Set X)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hx3)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  rcases slAct_pgl_or_field hK hq2 hθ e _ hσ3 with ⟨y₀, hy₀, hy₀s⟩ |
    ⟨-, f₀, hf, ψ, hψpow, g, hg, hσg⟩
  swap
  ·
    exfalso
    obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
    have hψ := eq_or_eq_sq_of_pow' hφ hψpow
    obtain ⟨e', he'⟩ := exists_normalized_field hK hq hf hφ hφ3 hψ e hx3 hg hσg
    have hr : piCard π (p ^ f₀) % 3 = 1 := piCard_mod_three (hf ▸ hq)
    have hψc : ∀ c : K, c ^ 3 = 1 → ψ c = c := by
      intro c hc
      rcases hψ with rfl | rfl
      · rw [hφ, pow_eq_self_of_pow_three hc hr]
      · rw [ringAut_sq_apply, hφ, hφ, ← pow_mul, pow_eq_self_of_pow_three hc]
        rw [Nat.mul_mod, hr]
    exact false_of_field hX hx hxS hK hq e' hψc he'
  have hxy : IsPGLAt e x y₀ := ⟨hy₀, hy₀s⟩
  have hy₀Z : y₀ ∉ zPi π 3 (p ^ f) K := by
    intro hz
    have hscal : y₀ ∈ StatedScalars (Fin 3) K :=
      (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
    have hc := mem_centralizer_of_isPGLAt_scalar hxy hscal
    exact hxS (mem_of_centralizes_of_orderOf_three hS2 hX hx
      (fun s hs => ((Subgroup.mem_centralizer_iff.1 hc s hs).symm)))
  have hy₀3 : y₀ ^ 3 ∈ zPi π 3 (p ^ f) K := by
    have h1 := isPGLAt_pow hxy 3
    rw [hx3] at h1
    have h2 := (isPGLAt_one_iff e h1.1).1 h1
    have hscal : y₀ ^ 3 ∈ StatedScalars (Fin 3) K := by
      refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
      have := h2 ⟨m, hm⟩
      change y₀ ^ 3 * m * (y₀ ^ 3)⁻¹ = m at this
      calc y₀ ^ 3 * m = y₀ ^ 3 * m * (y₀ ^ 3)⁻¹ * y₀ ^ 3 := by group
        _ = m * y₀ ^ 3 := by rw [this]
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.2 ⟨pow_mem hy₀ 3, hscal⟩
  obtain ⟨y, ⟨z, hz, hyz⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hy₀ hy₀Z hy₀3
  have hzs : z ∈ StatedScalars (Fin 3) K := (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
  have hzH : z ∈ glPi π 3 (p ^ f) K := (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).1
  have hxy' : IsPGLAt e x y := by rw [hyz]; exact isPGLAt_mul_scalar hxy hzs hzH
  have hyH : y ∈ glPi π 3 (p ^ f) K := hxy'.1
  have hyZ : y ∉ zPi π 3 (p ^ f) K := by
    intro h
    apply hy₀Z
    have : y₀ = y * z⁻¹ := by rw [hyz]; group
    rw [this]
    exact mul_mem h (inv_mem hz)
  have hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [hyz, (show Commute y₀ z from commute_of_mem_statedScalars hzs y₀).mul_pow]
    exact mul_mem hy₀3 (pow_mem hz 3)
  rcases hcases with ⟨⟨g, hg, hgD⟩, -, -⟩ | ⟨⟨⟨g, hg, e', he', hgD⟩, -, -⟩ | ⟨-, -, hirry, hcyc, hcard, -⟩⟩
  · exact (false_of_diagonal hX hx hxS hK hq e hxy' hg hgD
      (coe_diagTau_eq_diagonal hτ)).elim
  · exact (false_of_diagonal hX hx hxS hK hq e hxy' hg hgD (coe_diagE e')).elim
  · refine ⟨y, hxy', hy3, hirry, ?_, hcyc, hcard⟩
    rintro ⟨l, hl, z₁, hz₁, hyl⟩
    have hz₁s : z₁ ∈ StatedScalars (Fin 3) K :=
      (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz₁)).2
    have hinner : ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K,
        y * m * y⁻¹ = l * m * l⁻¹ := by
      refine ⟨l, hl, fun m _ => ?_⟩
      rw [hyl]
      have hc := commute_of_mem_statedScalars hz₁s m
      calc l * z₁ * m * (l * z₁)⁻¹ = l * (z₁ * m) * z₁⁻¹ * l⁻¹ := by group
        _ = l * (m * z₁) * z₁⁻¹ * l⁻¹ := by rw [hc]
        _ = l * m * l⁻¹ := by group
    rcases (rank3II_4_10_two hK hq hτ hτ1 hyH hyZ hy3).1 hinner with
      ⟨y'', ⟨z', hz', hy''⟩, g, hg, hgD⟩ | ⟨⟨y'', ⟨z', hz', hy''⟩, g, hg, e', he', hgD⟩, -⟩
    · obtain ⟨ξ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz'
      rw [hy''] at hgD
      exact not_irreducible_of_mul_scalar_diagonal hgD (coe_diagTau_eq_diagonal hτ) hirry
    · obtain ⟨ξ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz'
      rw [hy''] at hgD
      exact not_irreducible_of_mul_scalar_diagonal hgD (coe_diagE e') hirry

end TypeIII

end Diagonal

end A318P

end CFSG.Quasithin
