module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

abbrev normD (K : Type) [Field K] : Subgroup (MulAut (W6 K)) :=
  Subgroup.normalizer (diagSL K : Set (MulAut (W6 K)))

theorem exists_conj_of_mem {x : MulAut (W6 K)} (hx : x ∈ normD K) {g : GL (Fin 3) K}
    (hg : g ∈ StatedSL 3 K) :
    ∃ g' ∈ StatedSL 3 K, x * matAut (dgHom g) * x⁻¹ = matAut (dgHom g') := by
  have h := (Subgroup.mem_normalizer_iff.mp hx (matAut (dgHom g))).mp
    (matAut_dgHom_mem_diagSL hg)
  obtain ⟨g', hg', e⟩ := h
  exact ⟨g', hg', e.symm⟩

theorem isInvD_map {x : MulAut (W6 K)} (hx : x ∈ normD K) {M : Subgroup (W6 K)}
    (hM : IsInvD M) : IsInvD (M.map x.toMonoidHom) := by
  rintro g hg _ ⟨y, hy, rfl⟩
  obtain ⟨g', hg', e⟩ := exists_conj_of_mem (Subgroup.inv_mem _ hx) hg
  have e' : matAut (dgHom g) (x y) = x (matAut (dgHom g') y) := by
    have := congrArg (fun z : MulAut (W6 K) => (x * z) y) e
    simp only [MulAut.mul_apply, inv_inv] at this
    rw [← this]
    simp
  exact ⟨matAut (dgHom g') y, hM g' hg' y hy, e'.symm⟩

theorem card_map_aut (x : MulAut (W6 K)) (M : Subgroup (W6 K)) :
    Nat.card ↥(M.map x.toMonoidHom) = Nat.card ↥M :=
  Subgroup.card_map_of_injective x.injective

theorem exists_aut_of_map {x : MulAut (W6 K)} {a b a' b' : K}
    (hab : a ≠ 0 ∨ b ≠ 0) (hab' : a' ≠ 0 ∨ b' ≠ 0)
    (hmap : (natSub a b).map x.toMonoidHom = natSub a' b') :
    ∃ φ : MulAut (StdMod (Fin 3) K), (∀ u, x (natEmb a b u) = natEmb a' b' (φ u)) ∧
      ∀ g g' : GL (Fin 3) K, x * matAut (dgHom g) * x⁻¹ = matAut (dgHom g') →
        φ * matAut g * φ⁻¹ = matAut g' := by
  let e₁ : StdMod (Fin 3) K ≃* ↥(natSub a b) := MonoidHom.ofInjective (natEmb_injective hab)
  let e₂ : StdMod (Fin 3) K ≃* ↥(natSub a' b') := MonoidHom.ofInjective (natEmb_injective hab')
  let xs : ↥(natSub a b) ≃* ↥(natSub a' b') :=
    (x.subgroupMap (natSub a b)).trans (MulEquiv.subgroupCongr hmap)
  let φ : MulAut (StdMod (Fin 3) K) := e₁.trans (xs.trans e₂.symm)
  have hφ : ∀ u, x (natEmb a b u) = natEmb a' b' (φ u) := by
    intro u
    have h1 : (e₂ (φ u) : W6 K) = natEmb a' b' (φ u) := rfl
    have h2 : e₂ (φ u) = xs (e₁ u) := MulEquiv.apply_symm_apply e₂ _
    rw [← h1, h2]
    rfl
  refine ⟨φ, hφ, fun g g' hgg' => ?_⟩
  have hconj : ∀ y, x (matAut (dgHom g) y) = matAut (dgHom g') (x y) := by
    intro y
    rw [← hgg']
    simp [MulAut.mul_apply]
  have key : ∀ u, φ (matAut g u) = matAut g' (φ u) := by
    intro u
    apply natEmb_injective hab'
    calc natEmb a' b' (φ (matAut g u)) = x (natEmb a b (matAut g u)) := (hφ _).symm
      _ = x (matAut (dgHom g) (natEmb a b u)) := by rw [matAut_dgHom_natEmb]
      _ = matAut (dgHom g') (x (natEmb a b u)) := hconj _
      _ = matAut (dgHom g') (natEmb a' b' (φ u)) := by rw [hφ]
      _ = natEmb a' b' (matAut g' (φ u)) := matAut_dgHom_natEmb _ _ _ _
  refine MulEquiv.ext fun u => ?_
  simp only [MulAut.mul_apply]
  rw [key, MulAut.apply_inv_self]

theorem exists_semilinear_tens [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K) :
    ∃ (σ : K ≃+* K) (Φ : MulAut (StdMod (Fin 3) K)) (M : Matrix (Fin 2) (Fin 2) K),
      IsSemilinear Φ σ ∧ ∀ v : I6 → K, toAddMap x v =
        Sum.elim (toAddMap Φ (M 0 0 • (v ∘ Sum.inl) + M 0 1 • (v ∘ Sum.inr)))
          (toAddMap Φ (M 1 0 • (v ∘ Sum.inl) + M 1 1 • (v ∘ Sum.inr))) := by
  have hcl : ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → ∃ a' b' : K, (a' ≠ 0 ∨ b' ≠ 0) ∧
      (natSub a b).map x.toMonoidHom = natSub a' b' := by
    intro a b hab
    rcases eq_natSub_of_card (isInvD_map hx (natSub_isInv a b))
      (by rw [card_map_aut, card_natSub hab]) with h | ⟨c, h⟩
    · exact ⟨0, 1, Or.inr one_ne_zero, h⟩
    · exact ⟨1, c, Or.inl one_ne_zero, h⟩
  obtain ⟨a, b, hab, h1⟩ := hcl 1 0 (Or.inl one_ne_zero)
  obtain ⟨a', b', hab', h2⟩ := hcl 0 1 (Or.inr one_ne_zero)
  obtain ⟨φ₁, hφ₁, hc₁⟩ := exists_aut_of_map (Or.inl one_ne_zero) hab h1
  obtain ⟨φ₂, hφ₂, hc₂⟩ := exists_aut_of_map (Or.inr one_ne_zero) hab' h2
  have hN : ∀ φ : MulAut (StdMod (Fin 3) K), (∀ g g' : GL (Fin 3) K,
      x * matAut (dgHom g) * x⁻¹ = matAut (dgHom g') → φ * matAut g * φ⁻¹ = matAut g') →
      φ ∈ natNorm (StatedSL 3 K) := by
    intro φ hφ
    refine SL3Pair.mem_natNorm_of (fun γ hγ => ?_) (fun γ hγ => ?_)
    · obtain ⟨δ, hδ, e⟩ := exists_conj_of_mem hx hγ
      exact ⟨δ, hδ, hφ γ δ e⟩
    · obtain ⟨δ, hδ, e⟩ := exists_conj_of_mem (Subgroup.inv_mem _ hx) hγ
      refine ⟨δ, hδ, ?_⟩
      have e' : x * matAut (dgHom δ) * x⁻¹ = matAut (dgHom γ) := by
        rw [← e]
        group
      have h3 := hφ δ γ e'
      rw [← h3]
      group
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  obtain ⟨σ, hσ⟩ := exists_semilinear hΓ (hN φ₂ hc₂)
  have hcomm : ∀ γ ∈ StatedSL 3 K, ∀ v, toAddMap (φ₂⁻¹ * φ₁)
      ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ toAddMap (φ₂⁻¹ * φ₁) v := by
    intro γ hγ v
    obtain ⟨δ, -, e⟩ := exists_conj_of_mem hx hγ
    have e1 := hc₁ γ δ e
    have e2 := hc₂ γ δ e
    have h3 : φ₁ * matAut γ = matAut δ * φ₁ := by
      rw [← e1]
      group
    have h4 : φ₂⁻¹ * matAut δ = matAut γ * φ₂⁻¹ := by
      have h5 : φ₂ * matAut γ = matAut δ * φ₂ := by
        rw [← e2]
        group
      calc φ₂⁻¹ * matAut δ = φ₂⁻¹ * (matAut δ * φ₂) * φ₂⁻¹ := by group
        _ = φ₂⁻¹ * (φ₂ * matAut γ) * φ₂⁻¹ := by rw [h5]
        _ = matAut γ * φ₂⁻¹ := by group
    have h6 : (φ₂⁻¹ * φ₁) * matAut γ = matAut γ * (φ₂⁻¹ * φ₁) := by
      calc (φ₂⁻¹ * φ₁) * matAut γ = φ₂⁻¹ * (φ₁ * matAut γ) := by group
        _ = φ₂⁻¹ * (matAut δ * φ₁) := by rw [h3]
        _ = (φ₂⁻¹ * matAut δ) * φ₁ := by group
        _ = (matAut γ * φ₂⁻¹) * φ₁ := by rw [h4]
        _ = matAut γ * (φ₂⁻¹ * φ₁) := by group
    have h7 := congrArg (fun z => toAddMap z v) h6
    simpa only [toAddMap_mul, toAddMap_matAut] using h7
  let f : (Fin 3 → K) →+ (Fin 3 → K) :=
    AddMonoidHom.mk' (toAddMap (φ₂⁻¹ * φ₁)) (toAddMap_add _)
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hφ₁μ : ∀ v, toAddMap φ₁ v = toAddMap φ₂ (μ • v) := by
    intro v
    have h3 := hμ v
    change toAddMap (φ₂⁻¹ * φ₁) v = μ • v at h3
    rw [toAddMap_mul] at h3
    rw [← h3, toAddMap_inv_apply]
  have hs : ∀ (c : K) (y : Fin 3 → K), toAddMap φ₂ (σ.symm c • y) = c • toAddMap φ₂ y :=
    fun c y => by rw [hσ, RingEquiv.apply_symm_apply]
  refine ⟨σ, φ₂, !![σ.symm a * μ, σ.symm a'; σ.symm b * μ, σ.symm b'], hσ, fun v => ?_⟩
  have hv : Multiplicative.ofAdd v = natEmb 1 0 (Multiplicative.ofAdd (v ∘ Sum.inl)) *
      natEmb 0 1 (Multiplicative.ofAdd (v ∘ Sum.inr)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_natEmb, toAdd_natEmb]
    funext i
    rcases i with i | i <;> simp [natVec]
  have e1 : toAddMap φ₂ ((σ.symm a * μ) • (v ∘ Sum.inl) + σ.symm a' • (v ∘ Sum.inr)) =
      a • toAddMap φ₁ (v ∘ Sum.inl) + a' • toAddMap φ₂ (v ∘ Sum.inr) := by
    rw [toAddMap_add, mul_smul, hs, hs, ← hφ₁μ]
  have e2 : toAddMap φ₂ ((σ.symm b * μ) • (v ∘ Sum.inl) + σ.symm b' • (v ∘ Sum.inr)) =
      b • toAddMap φ₁ (v ∘ Sum.inl) + b' • toAddMap φ₂ (v ∘ Sum.inr) := by
    rw [toAddMap_add, mul_smul, hs, hs, ← hφ₁μ]
  change Multiplicative.toAdd (x (Multiplicative.ofAdd v)) = _
  rw [hv, map_mul, hφ₁, hφ₂, toAdd_mul, toAdd_natEmb, toAdd_natEmb]
  funext i
  rcases i with i | i
  · have h3 := congrFun e1 i
    simp only [Pi.add_apply, Pi.smul_apply] at h3
    simp only [natVec, Pi.add_apply, Sum.elim_inl, Pi.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h3]
  · have h3 := congrFun e2 i
    simp only [Pi.add_apply, Pi.smul_apply] at h3
    simp only [natVec, Pi.add_apply, Sum.elim_inr, Pi.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h3]

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
