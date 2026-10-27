module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

theorem eq_sign_or_eq_twist_of_isRefl (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r)
    (hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, r (b i) = c i • b (σ i)) :
    (∃ i, r = diagMap p b (fun j => if j = i then -1 else 1)) ∨
      ∃ i j, i ≠ j ∧ ∃ c : (ZMod p)ˣ,
        r = diagMap p b (pairUnit p i j c) * permMap p b (Equiv.swap i j) := by
  obtain ⟨σ, c, hc, hrb⟩ := hmon
  rcases CFSG.StandardType.ggRC_monomial_refl_shape hp b r hr σ c hc hrb with
      ⟨i, hσ1, hci, hcj⟩ | ⟨i, j, hij, hσswap, hcprod, hck⟩
  · refine Or.inl ⟨i, ?_⟩
    refine b.ext' fun k => ?_
    rw [diagMap_apply_basis, hrb k, hσ1]
    by_cases hk : k = i
    · subst hk; simp [hci]
    · simp [hcj k hk, hk]
  · refine Or.inr ⟨i, j, hij, Units.mk0 (c j) (hc j), ?_⟩
    refine b.ext' fun k => ?_
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis, hrb k, hσswap]
    by_cases hki : k = i
    · rw [hki]
      have hp : pairUnit p i j (Units.mk0 (c j) (hc j)) j = (Units.mk0 (c j) (hc j))⁻¹ := by
        simp [pairUnit, Ne.symm hij]
      rw [Equiv.swap_apply_left, hp]
      have hs : c i = ((Units.mk0 (c j) (hc j))⁻¹ : ZMod p) := by
        rw [Units.val_mk0]
        exact eq_inv_of_mul_eq_one_left hcprod
      rw [hs, Units.val_inv_eq_inv_val]
    · by_cases hkj : k = j
      · rw [hkj]
        have hp : pairUnit p i j (Units.mk0 (c j) (hc j)) i = Units.mk0 (c j) (hc j) := by
          simp [pairUnit]
        rw [Equiv.swap_apply_right, hp, Units.val_mk0]
      · have hswap : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
        rw [hswap]
        have hp : pairUnit p i j (Units.mk0 (c j) (hc j)) k = 1 := by
          simp [pairUnit, hki, hkj]
        rw [hp, hck k hki hkj]
        simp

private theorem zsExistsPermPair {i₀ i₁ i j : Fin n} (hi : i₀ ≠ i₁) (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin n), τ i₀ = i ∧ τ i₁ = j := by
  refine ⟨Equiv.swap (Equiv.swap i₀ i i₁) j * Equiv.swap i₀ i, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hij
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact (hi h1.symm).elim
    · exact fun h => h1 (h2.trans h)
    · exact fun h => h2 h.symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem zsPermMapConjPairUnit (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ i j : Fin n} (τ : Equiv.Perm (Fin n)) (hτ₀ : τ i₀ = i) (hτ₁ : τ i₁ = j)
    (c : (ZMod p)ˣ) :
    permMap p b τ * diagMap p b (pairUnit p i₀ i₁ c) * (permMap p b τ)⁻¹ =
      diagMap p b (pairUnit p i j c) := by
  rw [permMap_mul_diagMap_mul_inv]
  congr 1
  funext k
  simp only [Function.comp_apply, pairUnit, Equiv.symm_apply_eq, hτ₀, hτ₁]

private theorem zs_gmmn_le_of_diag (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A) {i₀ i₁ : Fin n}
    {ζ : (ZMod p)ˣ} (hζ : diagMap p b (pairUnit p i₀ i₁ ζ) ∈ A) :
    gmmn p b i₀ i₁ ζ ≤ A := by
  rw [gmmn, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨σ, rfl⟩ := hx; exact hperm σ
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hζ

private theorem zsTwistDiag_mem_gmmn (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (M : Subgroup (ZMod p)ˣ)
    (hMζ : M = Subgroup.zpowers ζ)
    (hMmem : ∀ c : (ZMod p)ˣ, c ∈ M ↔ diagMap p b (pairUnit p i₀ i₁ c) ∈ A)
    {i j : Fin n} (hij : i ≠ j) {u : (ZMod p)ˣ}
    (hdiag_A : diagMap p b (pairUnit p i j u) ∈ A) :
    diagMap p b (pairUnit p i j u) ∈ gmmn p b i₀ i₁ ζ := by
  let φ : (ZMod p)ˣ →* (U ≃ₗ[ZMod p] U) :=
    { toFun := fun c => diagMap p b (pairUnit p i₀ i₁ c)
      map_one' := by rw [pairUnit_one, diagMap_one]
      map_mul' := fun c c' => by rw [pairUnit_mul, ← diagMap_mul] }
  obtain ⟨τ, hτ₀, hτ₁⟩ := zsExistsPermPair hi hij
  have hconj := zsPermMapConjPairUnit b τ hτ₀ hτ₁ u
  have hAu : diagMap p b (pairUnit p i₀ i₁ u) ∈ A := by
    have h1 : permMap p b τ * diagMap p b (pairUnit p i₀ i₁ u) *
          (permMap p b τ)⁻¹ ∈ A := by
      rw [hconj]; exact hdiag_A
    have h2 : diagMap p b (pairUnit p i₀ i₁ u) =
        (permMap p b τ)⁻¹ * (permMap p b τ * diagMap p b (pairUnit p i₀ i₁ u) *
          (permMap p b τ)⁻¹) * permMap p b τ := by group
    rw [h2]
    exact A.mul_mem (A.mul_mem (A.inv_mem (hperm τ)) h1) (hperm τ)
  have hMu : u ∈ M := (hMmem u).mpr hAu
  have hugmmn : φ u ∈ gmmn p b i₀ i₁ ζ := by
    obtain ⟨m, hm⟩ := (Subgroup.mem_zpowers_iff).mp (hMζ ▸ hMu)
    rw [show φ u = φ (ζ ^ m) from by rw [hm], map_zpow]
    exact (gmmn p b i₀ i₁ ζ).zpow_mem (Subgroup.subset_closure (Or.inr rfl)) m
  have hτ_gmmn : permMap p b τ ∈ gmmn p b i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self τ))
  rw [← hconj]
  exact (gmmn p b i₀ i₁ ζ).mul_mem ((gmmn p b i₀ i₁ ζ).mul_mem hτ_gmmn hugmmn)
    ((gmmn p b i₀ i₁ ζ).inv_mem hτ_gmmn)


theorem eq_gmmn_of_permMap_mem (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (b i) = c i • b (σ i))
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsign : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∉ A) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) : ∃ ζ : (ZMod p)ˣ, A = gmmn p b i₀ i₁ ζ := by
  classical
  let φ : (ZMod p)ˣ →* (U ≃ₗ[ZMod p] U) :=
    { toFun := fun c => diagMap p b (pairUnit p i₀ i₁ c)
      map_one' := by rw [pairUnit_one, diagMap_one]
      map_mul' := fun c c' => by rw [pairUnit_mul, ← diagMap_mul] }
  let M : Subgroup (ZMod p)ˣ := A.comap φ
  have hMmem : ∀ c : (ZMod p)ˣ, c ∈ M ↔ diagMap p b (pairUnit p i₀ i₁ c) ∈ A := by
    intro c
    exact Subgroup.mem_comap
  obtain ⟨ζ, hζ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top M).mp (Subgroup.isCyclic M)
  have hMζ : M = Subgroup.zpowers ζ := hζ.symm
  have hgmmn_le : gmmn p b i₀ i₁ ζ ≤ A := by
    refine zs_gmmn_le_of_diag b hperm ?_
    have : ζ ∈ M := by rw [hMζ]; exact Subgroup.mem_zpowers ζ
    exact (hMmem ζ).mp this
  refine ⟨ζ, le_antisymm ?_ hgmmn_le⟩
  rw [hgen, Subgroup.closure_le]
  intro t ht
  rcases ht with ⟨htA, htRefl⟩
  obtain ⟨σ, c, hc, hrb⟩ := hmon t htA
  rcases eq_sign_or_eq_twist_of_isRefl hp b htRefl ⟨σ, c, hc, hrb⟩ with
      ⟨k, hk⟩ | ⟨i, j, hij, u, hu⟩
  · exact (hsign k (hk ▸ htA)).elim
  · rw [hu]
    have hdiag_A : diagMap p b (pairUnit p i j u) ∈ A := by
      have h1 : diagMap p b (pairUnit p i j u) * permMap p b (Equiv.swap i j) ∈ A := by
        rw [← hu]; exact htA
      have h2 : diagMap p b (pairUnit p i j u) =
          (diagMap p b (pairUnit p i j u) * permMap p b (Equiv.swap i j)) *
            (permMap p b (Equiv.swap i j))⁻¹ := by group
      rw [h2]
      exact A.mul_mem h1 (A.inv_mem (hperm (Equiv.swap i j)))
    exact (gmmn p b i₀ i₁ ζ).mul_mem
      (zsTwistDiag_mem_gmmn b hperm hi M hMζ hMmem hij hdiag_A)
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap i j))))

private theorem zsPermMapConjSign (b : Module.Basis (Fin n) (ZMod p) U)
    {i k : Fin n} (τ : Equiv.Perm (Fin n)) (hτ : τ i = k) :
    permMap p b τ * diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) *
      (permMap p b τ)⁻¹ =
      diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
  rw [permMap_mul_diagMap_mul_inv]
  congr 1
  funext j
  simp only [Function.comp_apply, Equiv.symm_apply_eq, hτ]

private theorem zsSign_mul (b : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) :
    diagMap p b (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) *
      diagMap p b (fun j => if j = i₁ then (-1 : (ZMod p)ˣ) else 1) =
      diagMap p b (pairUnit p i₀ i₁ (-1)) := by
  rw [diagMap_mul]
  congr 1
  funext j
  rw [Pi.mul_apply, pairUnit]
  by_cases h0 : j = i₀
  · rw [h0]; simp [hi]
  · by_cases h1 : j = i₁
    · rw [h1]; simp [Ne.symm hi]
    · simp [h0, h1]

private theorem zsSignMemOfExists (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsign : ∃ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A) :
    ∀ k, diagMap p b (fun j => if j = k then -1 else 1) ∈ A := by
  obtain ⟨i, hi_mem⟩ := hsign
  intro k
  by_cases hk : k = i
  · rw [hk]; exact hi_mem
  · have hτ : Equiv.swap i k i = k := Equiv.swap_apply_left i k
    have hconj := zsPermMapConjSign (p := p) b (Equiv.swap i k) hτ
    rw [← hconj]
    exact A.mul_mem (A.mul_mem (hperm (Equiv.swap i k)) hi_mem)
      (A.inv_mem (hperm (Equiv.swap i k)))

private theorem zsSignMemG2mmn (b : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (ζ : (ZMod p)ˣ) :
    ∀ k, diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈ g2mmn p b i₀ i₁ ζ := by
  intro k
  have hτ : Equiv.swap i₀ k i₀ = k := Equiv.swap_apply_left i₀ k
  have hconj := zsPermMapConjSign (p := p) b (Equiv.swap i₀ k) hτ
  have hpermτ : permMap p b (Equiv.swap i₀ k) ∈ g2mmn p b i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap i₀ k)))
  have hsi₀ : diagMap p b (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈
      g2mmn p b i₀ i₁ ζ := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  rw [← hconj]
  exact (g2mmn p b i₀ i₁ ζ).mul_mem ((g2mmn p b i₀ i₁ ζ).mul_mem hpermτ hsi₀)
    ((g2mmn p b i₀ i₁ ζ).inv_mem hpermτ)

private theorem zsEvenOrderOfNeg (hp : p ≠ 2) {ζ₀ : (ZMod p)ˣ} (hodd : Odd (orderOf ζ₀)) :
    Even (orderOf (-ζ₀)) := by
  have hord_neg_one : orderOf (-1 : (ZMod p)ˣ) = 2 := by
    rw [← orderOf_units (y := (-1 : (ZMod p)ˣ))]
    exact (CharP.orderOf_eq_two_iff p hp).mpr rfl
  have hcop : Nat.Coprime (orderOf (-1 : (ZMod p)ˣ)) (orderOf ζ₀) := by
    rw [hord_neg_one]; exact Nat.coprime_two_left.mpr hodd
  have hcomm : Commute (-1 : (ZMod p)ˣ) ζ₀ := Commute.all _ _
  have hneg : (-ζ₀ : (ZMod p)ˣ) = (-1) * ζ₀ := by ext; simp
  rw [hneg, Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcop, hord_neg_one]
  exact even_two_mul _

private theorem zs_g2mmn_le_of (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A) {i₀ i₁ : Fin n}
    {ζ : (ZMod p)ˣ} (hs : ∀ k, diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈ A)
    (hζ : diagMap p b (pairUnit p i₀ i₁ ζ) ∈ A) :
    g2mmn p b i₀ i₁ ζ ≤ A := by
  rw [g2mmn, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨σ, rfl⟩ := hx; exact hperm σ
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hs i₀
    · exact hζ

private theorem zsDiagNeg_mem (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ₀ : (ZMod p)ˣ}
    (hs : ∀ k, diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈ A)
    (hζ₀ : diagMap p b (pairUnit p i₀ i₁ ζ₀) ∈ A) :
    diagMap p b (pairUnit p i₀ i₁ (-ζ₀)) ∈ A := by
  have hpair : pairUnit p i₀ i₁ (-ζ₀) =
      pairUnit p i₀ i₁ (-1) * pairUnit p i₀ i₁ ζ₀ := by
    conv_lhs => rw [show (-ζ₀ : (ZMod p)ˣ) = (-1) * ζ₀ from by ext; simp]
    rw [pairUnit_mul]
  rw [hpair, ← diagMap_mul]
  refine A.mul_mem ?_ hζ₀
  rw [← zsSign_mul b hi]
  exact A.mul_mem (hs i₀) (hs i₁)

private theorem zsDiagNeg_g2mmn (b : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hs : ∀ k, diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈
      g2mmn p b i₀ i₁ ζ)
    (hζ : diagMap p b (pairUnit p i₀ i₁ ζ) ∈ g2mmn p b i₀ i₁ ζ) :
    diagMap p b (pairUnit p i₀ i₁ (-ζ)) ∈ g2mmn p b i₀ i₁ ζ := by
  have hpair : pairUnit p i₀ i₁ (-ζ) =
      pairUnit p i₀ i₁ (-1) * pairUnit p i₀ i₁ ζ := by
    conv_lhs => rw [show (-ζ : (ZMod p)ˣ) = (-1) * ζ from by ext; simp]
    rw [pairUnit_mul]
  rw [hpair, ← diagMap_mul]
  refine (g2mmn p b i₀ i₁ ζ).mul_mem ?_ hζ
  rw [← zsSign_mul b hi]
  exact (g2mmn p b i₀ i₁ ζ).mul_mem (hs i₀) (hs i₁)

private theorem zsTwistDiag_mem_g2mmn (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ ζ₀ : (ZMod p)ˣ} (M : Subgroup (ZMod p)ˣ)
    (hMζ : M = Subgroup.zpowers ζ₀)
    (hMmem : ∀ c : (ZMod p)ˣ, c ∈ M ↔ diagMap p b (pairUnit p i₀ i₁ c) ∈ A)
    (hζ₀ : diagMap p b (pairUnit p i₀ i₁ ζ₀) ∈ g2mmn p b i₀ i₁ ζ)
    {i j : Fin n} (hij : i ≠ j) {u : (ZMod p)ˣ}
    (hdiag_A : diagMap p b (pairUnit p i j u) ∈ A) :
    diagMap p b (pairUnit p i j u) ∈ g2mmn p b i₀ i₁ ζ := by
  let φ : (ZMod p)ˣ →* (U ≃ₗ[ZMod p] U) :=
    { toFun := fun c => diagMap p b (pairUnit p i₀ i₁ c)
      map_one' := by rw [pairUnit_one, diagMap_one]
      map_mul' := fun c c' => by rw [pairUnit_mul, ← diagMap_mul] }
  obtain ⟨τ, hτ₀, hτ₁⟩ := zsExistsPermPair hi hij
  have hconj := zsPermMapConjPairUnit b τ hτ₀ hτ₁ u
  have hAu : diagMap p b (pairUnit p i₀ i₁ u) ∈ A := by
    have h1 : permMap p b τ * diagMap p b (pairUnit p i₀ i₁ u) *
          (permMap p b τ)⁻¹ ∈ A := by
      rw [hconj]; exact hdiag_A
    have h2 : diagMap p b (pairUnit p i₀ i₁ u) =
        (permMap p b τ)⁻¹ * (permMap p b τ * diagMap p b (pairUnit p i₀ i₁ u) *
          (permMap p b τ)⁻¹) * permMap p b τ := by group
    rw [h2]
    exact A.mul_mem (A.mul_mem (A.inv_mem (hperm τ)) h1) (hperm τ)
  have hMu : u ∈ M := (hMmem u).mpr hAu
  have hugmmn : φ u ∈ g2mmn p b i₀ i₁ ζ := by
    obtain ⟨m, hm⟩ := (Subgroup.mem_zpowers_iff).mp (hMζ ▸ hMu)
    rw [show φ u = φ (ζ₀ ^ m) from by rw [hm], map_zpow]
    exact (g2mmn p b i₀ i₁ ζ).zpow_mem hζ₀ m
  have hτ_g : permMap p b τ ∈ g2mmn p b i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self τ))
  rw [← hconj]
  exact (g2mmn p b i₀ i₁ ζ).mul_mem ((g2mmn p b i₀ i₁ ζ).mul_mem hτ_g hugmmn)
    ((g2mmn p b i₀ i₁ ζ).inv_mem hτ_g)


private theorem zsDiagOfTwist_mem (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ A) {i j : Fin n} {u : (ZMod p)ˣ}
    (hu : t = diagMap p b (pairUnit p i j u) * permMap p b (Equiv.swap i j)) :
    diagMap p b (pairUnit p i j u) ∈ A := by
  have h1 : diagMap p b (pairUnit p i j u) * permMap p b (Equiv.swap i j) ∈ A := by
    rw [← hu]; exact ht
  have h2 : diagMap p b (pairUnit p i j u) =
      (diagMap p b (pairUnit p i j u) * permMap p b (Equiv.swap i j)) *
        (permMap p b (Equiv.swap i j))⁻¹ := by group
  rw [h2]
  exact A.mul_mem h1 (A.inv_mem (hperm (Equiv.swap i j)))


theorem eq_g2mmn_of_permMap_mem (hp : p ≠ 2) (b : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (b i) = c i • b (σ i))
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsign : ∃ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) : ∃ ζ : (ZMod p)ˣ, Even (orderOf ζ) ∧ A = g2mmn p b i₀ i₁ ζ := by
  classical
  let φ : (ZMod p)ˣ →* (U ≃ₗ[ZMod p] U) :=
    { toFun := fun c => diagMap p b (pairUnit p i₀ i₁ c)
      map_one' := by rw [pairUnit_one, diagMap_one]
      map_mul' := fun c c' => by rw [pairUnit_mul, ← diagMap_mul] }
  let M : Subgroup (ZMod p)ˣ := A.comap φ
  have hMmem : ∀ c : (ZMod p)ˣ, c ∈ M ↔ diagMap p b (pairUnit p i₀ i₁ c) ∈ A :=
    fun c => Subgroup.mem_comap
  obtain ⟨ζ₀, hζ₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top M).mp (Subgroup.isCyclic M)
  have hMζ : M = Subgroup.zpowers ζ₀ := hζ₀.symm
  have hφζ₀_A : φ ζ₀ ∈ A := (hMmem ζ₀).mp (by rw [hMζ]; exact Subgroup.mem_zpowers ζ₀)
  have hs := zsSignMemOfExists b hperm hsign
  set ζ : (ZMod p)ˣ := if Even (orderOf ζ₀) then ζ₀ else -ζ₀ with hζdef
  have hζ_cases : ζ = ζ₀ ∨ ζ = -ζ₀ := by rw [hζdef]; split_ifs <;> tauto
  have hζeven : Even (orderOf ζ) := by
    rw [hζdef]; split_ifs with hE
    exacts [hE, zsEvenOrderOfNeg hp (Nat.not_even_iff_odd.mp hE)]
  have hφζ_g : φ ζ ∈ g2mmn p b i₀ i₁ ζ := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hφζ_A : φ ζ ∈ A := by
    rcases hζ_cases with h | h
    · simpa [h] using hφζ₀_A
    · rw [h]; exact zsDiagNeg_mem b hi hs hφζ₀_A
  have hφζ₀_g : φ ζ₀ ∈ g2mmn p b i₀ i₁ ζ := by
    rcases hζ_cases with h | h
    · simpa [h] using hφζ_g
    · rw [show ζ₀ = -ζ from by rw [h, neg_neg]]
      exact zsDiagNeg_g2mmn b hi (zsSignMemG2mmn (i₀ := i₀) (i₁ := i₁) b ζ) hφζ_g
  have hg2mmn_le : g2mmn p b i₀ i₁ ζ ≤ A := zs_g2mmn_le_of b hperm hs hφζ_A
  refine ⟨ζ, hζeven, le_antisymm ?_ hg2mmn_le⟩
  rw [hgen, Subgroup.closure_le]
  intro t ht
  rcases ht with ⟨htA, htRefl⟩
  obtain ⟨σ, c, hc, hrb⟩ := hmon t htA
  rcases eq_sign_or_eq_twist_of_isRefl hp b htRefl ⟨σ, c, hc, hrb⟩ with
      ⟨k, hk⟩ | ⟨i, j, hij, u, hu⟩
  · rw [hk]; exact zsSignMemG2mmn (i₀ := i₀) (i₁ := i₁) b ζ k
  · rw [hu]
    exact (g2mmn p b i₀ i₁ ζ).mul_mem
      (zsTwistDiag_mem_g2mmn b hperm hi M hMζ hMmem hφζ₀_g hij
        (zsDiagOfTwist_mem b hperm htA hu))
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self (Equiv.swap i j))))

private theorem zsGmmnOne_fix_sum (b : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) :
    ∀ a ∈ gmmn p b i₀ i₁ 1, a (∑ i : Fin n, b i) = ∑ i : Fin n, b i := by
  have hperm_fix : ∀ σ : Equiv.Perm (Fin n),
      permMap p b σ (∑ i : Fin n, b i) = ∑ i : Fin n, b i := by
    intro σ
    rw [map_sum]
    simp only [permMap_apply_basis]
    rw [Equiv.sum_comp]
  intro a ha
  have ha' : a ∈ Subgroup.closure
      (Set.range (permMap p b) ∪ {diagMap p b (pairUnit p i₀ i₁ 1)}) := ha
  exact Subgroup.closure_induction (p := fun a _ => a (∑ i : Fin n, b i) = ∑ i : Fin n, b i)
    (fun x hx => by
      rcases hx with hx | hx
      · obtain ⟨σ, rfl⟩ := hx
        exact hperm_fix σ
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, pairUnit_one, diagMap_one]
        simp)
    (by simp)
    (fun x y _ _ hx hy => by rw [LinearEquiv.mul_apply, hy, hx])
    (fun x _ hx => by
      calc x⁻¹ (∑ i : Fin n, b i) = x⁻¹ (x (∑ i : Fin n, b i)) := by rw [hx]
        _ = (x⁻¹ * x) (∑ i : Fin n, b i) := by rw [LinearEquiv.mul_apply]
        _ = ∑ i : Fin n, b i := by simp)
    ha'


theorem not_absIrred_gmmn_one (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) :
    ¬ AbsIrred p (gmmn p b i₀ i₁ 1) := by
  intro hA
  set w : U := ∑ i : Fin n, b i with hw
  have hfix : ∀ a ∈ gmmn p b i₀ i₁ 1, a w = w := by
    intro a ha
    rw [hw]
    exact zsGmmnOne_fix_sum b i₀ i₁ a ha
  have hw_repr : ∀ k : Fin n, b.repr w k = 1 := by
    intro k
    rw [hw, map_sum]
    simp [Module.Basis.repr_self, Finsupp.single_apply]
  set W : Submodule (ZMod p) U := Submodule.span (ZMod p) {w} with hW
  have hwW : w ∈ W := by rw [hW]; exact Submodule.subset_span (Set.mem_singleton w)
  have hinv : ∀ a ∈ gmmn p b i₀ i₁ 1, ∀ x ∈ W, a x ∈ W := by
    intro a ha x hx
    rw [hW, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_smul, hfix a ha, hW]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
  rcases hA.1 W hinv with hbot | htop
  · have hw_ne : w ≠ 0 := by
      intro h0
      have h1 := hw_repr ⟨0, by omega⟩
      rw [h0] at h1
      simp at h1
    exact hw_ne (by simpa [hbot] using hwW)
  · have hk0 : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
      intro h
      exact Nat.zero_ne_one (by simpa using congrArg Fin.val h)
    have hbk0 : b (⟨0, by omega⟩ : Fin n) ∈ W := by rw [htop]; trivial
    rw [hW, Submodule.mem_span_singleton] at hbk0
    obtain ⟨c, hc⟩ := hbk0
    have hc0 : c = 1 := by
      have h := congrArg (fun x => b.repr x (⟨0, by omega⟩ : Fin n)) hc
      simpa [map_smul, hw_repr, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
        Finsupp.smul_apply] using h
    have hc1 : c = 0 := by
      have h := congrArg (fun x => b.repr x (⟨1, by omega⟩ : Fin n)) hc
      simpa [map_smul, hw_repr, Module.Basis.repr_self, Finsupp.single_eq_of_ne', hk0,
        smul_eq_mul, Finsupp.smul_apply] using h
    exact one_ne_zero (hc0.symm.trans hc1)

end CFSG.StandardType.ZS
