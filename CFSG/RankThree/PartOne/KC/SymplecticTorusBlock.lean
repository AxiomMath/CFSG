module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusCover

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Module CFSG.RankThree.CentralCover CFSG.Assembly CFSG.Assembly.RankThreeEven

section Maps

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {m : ℕ} (b : Basis (Fin m) E W)

@[expose] noncomputable def diagEquiv (c : Fin m → Eˣ) : W ≃ₗ[E] W :=
  b.equiv (b.unitsSMul c) (Equiv.refl _)

theorem diagEquiv_apply_basis (c : Fin m → Eˣ) (j : Fin m) :
    diagEquiv b c (b j) = (c j : E) • b j := by
  simp [diagEquiv, Basis.equiv_apply, Basis.unitsSMul_apply, Units.smul_def]

@[expose] noncomputable def permEquiv (τ : Equiv.Perm (Fin m)) : W ≃ₗ[E] W :=
  b.equiv b τ

theorem permEquiv_apply_basis (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    permEquiv b τ (b j) = b (τ j) := by
  simp [permEquiv, Basis.equiv_apply]

theorem diagEquiv_mul (c c' : Fin m → Eˣ) :
    diagEquiv b (c * c') = diagEquiv b c * diagEquiv b c' := by
  refine LinearEquiv.toLinearMap_injective (b.ext fun j => ?_)
  change diagEquiv b (c * c') (b j) = diagEquiv b c (diagEquiv b c' (b j))
  rw [diagEquiv_apply_basis, diagEquiv_apply_basis, map_smul, diagEquiv_apply_basis,
    Pi.mul_apply, smul_smul, Units.val_mul, mul_comm]

theorem diagEquiv_one : diagEquiv b (1 : Fin m → Eˣ) = 1 := by
  refine LinearEquiv.toLinearMap_injective (b.ext fun j => ?_)
  change diagEquiv b 1 (b j) = b j
  rw [diagEquiv_apply_basis]
  simp

theorem permEquiv_mul_diagEquiv (τ : Equiv.Perm (Fin m)) (c : Fin m → Eˣ) :
    permEquiv b τ * diagEquiv b c = diagEquiv b (fun j => c (τ⁻¹ j)) * permEquiv b τ := by
  refine LinearEquiv.toLinearMap_injective (b.ext fun j => ?_)
  change permEquiv b τ (diagEquiv b c (b j)) = diagEquiv b _ (permEquiv b τ (b j))
  rw [diagEquiv_apply_basis, map_smul, permEquiv_apply_basis, diagEquiv_apply_basis]
  simp

theorem diagEquiv_injective : Function.Injective (diagEquiv b : (Fin m → Eˣ) → W ≃ₗ[E] W) := by
  intro c c' h
  funext j
  have := congrArg (fun f : W ≃ₗ[E] W => f (b j)) h
  simp only [diagEquiv_apply_basis] at this
  exact Units.ext (smul_left_injective E (b.ne_zero j) this)

@[expose] noncomputable def diagHom : (Fin m → Eˣ) →* (W ≃ₗ[E] W) where
  toFun := diagEquiv b
  map_one' := diagEquiv_one b
  map_mul' := diagEquiv_mul b

@[expose] noncomputable def signEquiv (i : Fin m) : W ≃ₗ[E] W :=
  diagEquiv b (Function.update 1 i (-1))

theorem signEquiv_apply_basis (i j : Fin m) :
    signEquiv b i (b j) = if j = i then -b j else b j := by
  rw [signEquiv, diagEquiv_apply_basis]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem signEquiv_mul_self (i : Fin m) : signEquiv b i * signEquiv b i = 1 := by
  rw [signEquiv, ← diagEquiv_mul, ← diagEquiv_one b]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem signEquiv_mul_comm (i : Fin m) (c : Fin m → Eˣ) :
    signEquiv b i * diagEquiv b c = diagEquiv b c * signEquiv b i := by
  rw [signEquiv, ← diagEquiv_mul, ← diagEquiv_mul, mul_comm]

theorem sign_not_scalar (h2 : (2 : E) ≠ 0) {i₀ i₁ : Fin m} (hi : i₀ ≠ i₁) (c : E)
    (hc : ∀ w : W, signEquiv b i₀ w = c • w) : False := by
  have e0 : -b i₀ = c • b i₀ := by simpa [signEquiv_apply_basis] using hc (b i₀)
  have e1 : b i₁ = c • b i₁ := by simpa [signEquiv_apply_basis, Ne.symm hi] using hc (b i₁)
  have hc1 : c = 1 := by
    have : (1 - c) • b i₁ = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right (b.ne_zero i₁))).symm
  have hc2 : c = -1 := by
    have : (1 + c) • b i₀ = 0 := by rw [add_smul, one_smul, ← e0, add_neg_cancel]
    exact eq_neg_of_add_eq_zero_right ((smul_eq_zero.mp this).resolve_right (b.ne_zero i₀))
  rw [hc1] at hc2
  exact h2 (by linear_combination hc2)

end Maps

section Hermitian

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
  {m : ℕ} (b : Basis (Fin m) E W) (H : W →ₛₗ[σ] W →ₗ[E] E)

theorem herm_expand (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (u v : W) :
    H u v = ∑ i, σ (b.repr u i) * b.repr v i := by
  have h1 : ∀ i, H (b i) v = b.repr v i := by
    intro i
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum, Finset.sum_eq_single i]
    · simp [hb]
    · intro j _ hj
      simp [hb, Ne.symm hj]
    · simp
  conv_lhs => rw [← b.sum_repr u]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, h1, smul_eq_mul]

theorem repr_diagEquiv (c : Fin m → Eˣ) (u : W) (i : Fin m) :
    b.repr (diagEquiv b c u) i = c i * b.repr u i := by
  have : diagEquiv b c u = ∑ j, ((c j : E) * b.repr u j) • b j := by
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, diagEquiv_apply_basis, smul_smul, mul_comm]
  rw [this, b.repr_sum_self]

theorem repr_permEquiv (τ : Equiv.Perm (Fin m)) (u : W) (i : Fin m) :
    b.repr (permEquiv b τ u) (τ i) = b.repr u i := by
  have : permEquiv b τ u = ∑ j, (b.repr u j) • b (τ j) := by
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, permEquiv_apply_basis]
  rw [this, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [τ.injective.eq_iff, Ne.symm hj]
  · simp

theorem herm_diag (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (c : Fin m → Eˣ)
    (hc : ∀ i, σ (c i) * c i = 1) (u v : W) :
    H (diagEquiv b c u) (diagEquiv b c v) = H u v := by
  rw [herm_expand b H hb, herm_expand b H hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_diagEquiv, repr_diagEquiv, map_mul]
  calc σ (c i) * σ (b.repr u i) * (c i * b.repr v i)
      = (σ (c i) * c i) * (σ (b.repr u i) * b.repr v i) := by ring
    _ = σ (b.repr u i) * b.repr v i := by rw [hc i, one_mul]

theorem herm_perm (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (τ : Equiv.Perm (Fin m))
    (u v : W) : H (permEquiv b τ u) (permEquiv b τ v) = H u v := by
  rw [herm_expand b H hb, herm_expand b H hb, ← Equiv.sum_comp τ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_permEquiv, repr_permEquiv]

end Hermitian

section Torus

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {m : ℕ}
variable {p : ℕ} [NeZero p] (lam : Eˣ) (hlam : lam ^ p = 1)

@[expose] noncomputable def torusExps : Multiplicative (Fin m → ZMod p) →* (Fin m → Eˣ) :=
  MonoidHom.pi fun i => (zmodPowHom lam hlam).comp
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod p) i))

theorem torusExps_apply (a : Multiplicative (Fin m → ZMod p)) (j : Fin m) :
    torusExps (m := m) lam hlam a j = lam ^ (Multiplicative.toAdd a j).val := rfl

theorem torusExps_injective (hlamo : orderOf lam = p) :
    Function.Injective (torusExps (m := m) lam hlam) := by
  intro a a' h
  apply Multiplicative.toAdd.injective
  funext j
  exact Multiplicative.toAdd.injective (zmodPowHom_injective hlamo hlam (congrFun h j))

theorem torusExps_mem_zpowers (a : Multiplicative (Fin m → ZMod p)) (j : Fin m) :
    torusExps (m := m) lam hlam a j ∈ Subgroup.zpowers lam := by
  rw [torusExps_apply]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers lam) _

end Torus

theorem single_perm_inv_apply {N : Type*} [Zero N] {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m)
    (x : N) : (fun t => (Pi.single i x : Fin m → N) (σ⁻¹ t)) = Pi.single (σ i) x := by
  funext t
  simp only [Pi.single_apply]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

section Glue

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {m : ℕ} (b : Basis (Fin m) E W)
variable {p : ℕ} [NeZero p] (lam : Eˣ) (hlam : lam ^ p = 1)
variable {S : Type*} [Group S] {F : Subgroup S} (ψ : F →* (W ≃ₗ[E] W))
  (hψ : Function.Injective ψ)
  (hdiag : ∀ c : Fin m → Eˣ, (∀ j, c j ∈ Subgroup.zpowers lam) → diagEquiv b c ∈ ψ.range)

@[expose] noncomputable def torusF : Multiplicative (Fin m → ZMod p) →* F :=
  ((MonoidHom.ofInjective hψ).symm : ψ.range ≃* F).toMonoidHom.comp
    (((diagHom b).comp (torusExps lam hlam)).codRestrict ψ.range fun a =>
      hdiag _ (torusExps_mem_zpowers lam hlam a))

theorem psi_torusF (a : Multiplicative (Fin m → ZMod p)) :
    ψ (torusF b lam hlam ψ hψ hdiag a) = diagEquiv b (torusExps lam hlam a) := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hψ)
    (⟨diagEquiv b (torusExps lam hlam a), hdiag _ (torusExps_mem_zpowers lam hlam a)⟩ :
      ψ.range)
  exact congrArg Subtype.val h

@[expose] noncomputable def torusS : Multiplicative (Fin m → ZMod p) →* S :=
  F.subtype.comp (torusF b lam hlam ψ hψ hdiag)

theorem torusF_injective (hlamo : orderOf lam = p) :
    Function.Injective (torusF b lam hlam ψ hψ hdiag) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : ψ (torusF b lam hlam ψ hψ hdiag a) = ψ 1 := by rw [ha]
  rw [psi_torusF, map_one] at h1
  have h5 : torusExps lam hlam a = torusExps lam hlam 1 := by
    rw [map_one]
    exact diagEquiv_injective b (h1.trans (diagEquiv_one b).symm)
  exact torusExps_injective lam hlam hlamo h5

theorem torusS_injective (hlamo : orderOf lam = p) :
    Function.Injective (torusS b lam hlam ψ hψ hdiag) :=
  Subtype.val_injective.comp (torusF_injective b lam hlam ψ hψ hdiag hlamo)

theorem torusS_mem (a : Multiplicative (Fin m → ZMod p)) :
    torusS b lam hlam ψ hψ hdiag a ∈ F := (torusF b lam hlam ψ hψ hdiag a).2

theorem torusS_pow (a : Multiplicative (Fin m → ZMod p)) :
    torusS b lam hlam ψ hψ hdiag a ^ p = 1 := by
  rw [torusS, MonoidHom.comp_apply, ← map_pow, ← map_pow, pow_eq_one_of_zmod, map_one, map_one]

@[expose] noncomputable def permF (τ : Equiv.Perm (Fin m)) (hτ : permEquiv b τ ∈ ψ.range) : F :=
  (MonoidHom.ofInjective hψ).symm ⟨permEquiv b τ, hτ⟩

theorem psi_permF (τ : Equiv.Perm (Fin m)) (hτ : permEquiv b τ ∈ ψ.range) :
    ψ (permF b ψ hψ τ hτ) = permEquiv b τ := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hψ) (⟨permEquiv b τ, hτ⟩ : ψ.range)
  exact congrArg Subtype.val h

theorem permF_conj (τ : Equiv.Perm (Fin m)) (hτ : permEquiv b τ ∈ ψ.range)
    (a : Multiplicative (Fin m → ZMod p)) :
    permF b ψ hψ τ hτ * torusF b lam hlam ψ hψ hdiag a * (permF b ψ hψ τ hτ)⁻¹ =
      torusF b lam hlam ψ hψ hdiag
        (Multiplicative.ofAdd fun t => Multiplicative.toAdd a (τ⁻¹ t)) := by
  apply hψ
  rw [map_mul, map_mul, map_inv, psi_permF, psi_torusF, psi_torusF, mul_inv_eq_iff_eq_mul]
  exact permEquiv_mul_diagEquiv b τ _

theorem torusS_swap (hperm : ∀ τ : Equiv.Perm (Fin m), permEquiv b τ ∈ ψ.range) (i j : Fin m) :
    ∃ g : S, g * torusS b lam hlam ψ hψ hdiag (Multiplicative.ofAdd (Pi.single i 1)) * g⁻¹ =
        torusS b lam hlam ψ hψ hdiag (Multiplicative.ofAdd (Pi.single j 1)) ∧
      g * torusS b lam hlam ψ hψ hdiag (Multiplicative.ofAdd (Pi.single j 1)) * g⁻¹ =
        torusS b lam hlam ψ hψ hdiag (Multiplicative.ofAdd (Pi.single i 1)) := by
  set τ : Equiv.Perm (Fin m) := Equiv.swap i j
  refine ⟨(permF b ψ hψ τ (hperm τ) : S), ?_, ?_⟩
  · have h := permF_conj b lam hlam ψ hψ hdiag τ (hperm τ) (Multiplicative.ofAdd (Pi.single i 1))
    have e : (fun t => Multiplicative.toAdd
        (Multiplicative.ofAdd (Pi.single i (1 : ZMod p) : Fin m → ZMod p)) (τ⁻¹ t)) =
          Pi.single j 1 := by
      rw [toAdd_ofAdd, single_perm_inv_apply]
      simp [τ]
    rw [e] at h
    have := congrArg (fun y : F => (y : S)) h
    simpa [torusS] using this
  · have h := permF_conj b lam hlam ψ hψ hdiag τ (hperm τ) (Multiplicative.ofAdd (Pi.single j 1))
    have e : (fun t => Multiplicative.toAdd
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod p) : Fin m → ZMod p)) (τ⁻¹ t)) =
          Pi.single i 1 := by
      rw [toAdd_ofAdd, single_perm_inv_apply]
      simp [τ]
    rw [e] at h
    have := congrArg (fun y : F => (y : S)) h
    simpa [torusS] using this

theorem exists_sign_lift (i₀ : Fin m) (hsign : signEquiv b i₀ ∈ ψ.range) :
    ∃ g : F, ψ g = signEquiv b i₀ ∧ (g : S) ^ 2 = 1 ∧
      ∀ a, Commute (g : S) (torusS b lam hlam ψ hψ hdiag a) := by
  set g : F := (MonoidHom.ofInjective hψ).symm ⟨signEquiv b i₀, hsign⟩ with hg
  have hψg : ψ g = signEquiv b i₀ := by
    have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hψ)
      (⟨signEquiv b i₀, hsign⟩ : ψ.range)
    exact congrArg Subtype.val h
  refine ⟨g, hψg, ?_, fun a => ?_⟩
  · have : g ^ 2 = 1 := by
      apply hψ
      rw [map_pow, map_one, hψg, pow_two]
      exact signEquiv_mul_self b i₀
    rw [← Subgroup.coe_pow, this]
    rfl
  · have : g * torusF b lam hlam ψ hψ hdiag a = torusF b lam hlam ψ hψ hdiag a * g := by
      apply hψ
      rw [map_mul, map_mul, hψg, psi_torusF]
      exact signEquiv_mul_comm b i₀ _
    exact congrArg (fun y : F => (y : S)) this

end Glue

section Witness

variable {G : Type*} [Group G] [Finite G] {S T : Type*} [Group S] [Group T]
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {m : ℕ} (b : Basis (Fin m) E W)

theorem block_torus_central_cover_witness (Y : Subgroup G) (ρ : S →* T) (φ : Y →* T)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) {lam : Eˣ} (hlamp : lam ^ p = 1) (hlam : orderOf lam = p)
    {F : Subgroup S} (ψ : F →* (W ≃ₗ[E] W)) (hψ : Function.Injective ψ)
    (hdiag : ∀ c : Fin m → Eˣ, (∀ j, c j ∈ Subgroup.zpowers lam) → diagEquiv b c ∈ ψ.range)
    (hperm : ∀ τ : Equiv.Perm (Fin m), permEquiv b τ ∈ ψ.range)
    (hinj : ∀ g ∈ F, ρ g = 1 → g ^ p = 1 → g = 1)
    (E' : Subgroup (Multiplicative (Fin m → ZMod p))) {k : ℕ} (hE : p ^ k ≤ Nat.card E')
    {z : S} (hz2 : z ^ 2 = 1) (hz1 : ρ z ≠ 1)
    (hzc : ∀ a ∈ E', Commute z (torusS b lam hlamp ψ hψ hdiag a)) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ k ∧ k ≤ localRank p G := by
  classical
  set θ : Multiplicative (Fin m → ZMod p) →* T := ρ.comp (torusS b lam hlamp ψ hψ hdiag) with hθ
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : torusS b lam hlamp ψ hψ hdiag a = 1 :=
      hinj _ (torusS_mem b lam hlamp ψ hψ hdiag a) ha (torusS_pow b lam hlamp ψ hψ hdiag a)
    exact torusS_injective b lam hlamp ψ hψ hdiag hlam (h1.trans (map_one _).symm)
  have hswap : ∀ i j : Fin m, i ≠ j → ∃ g : T,
      g * θ (Multiplicative.ofAdd (Pi.single i 1)) * g⁻¹ =
          θ (Multiplicative.ofAdd (Pi.single j 1)) ∧
        g * θ (Multiplicative.ofAdd (Pi.single j 1)) * g⁻¹ =
          θ (Multiplicative.ofAdd (Pi.single i 1)) := by
    intro i j _
    obtain ⟨g, hg1, hg2⟩ := torusS_swap b lam hlamp ψ hψ hdiag hperm i j
    refine ⟨ρ g, ?_, ?_⟩
    · simp only [hθ, MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul, hg1]
    · simp only [hθ, MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul, hg2]
  have hzo : orderOf (ρ z) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hz2, map_one]) hz1
  exact torus_central_cover_witness Y φ hφ hker hp hp2 θ hθinj hswap E' hE hzo
    (fun a ha => (hzc a ha).map ρ)

end Witness

end CFSG.RankThree.PartOne.KCSymplectic
