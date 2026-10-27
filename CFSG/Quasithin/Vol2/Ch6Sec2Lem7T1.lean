module

public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.Quasithin.H13

open CFSG.LieType.BorelTits

variable {W : Type} [CommGroup W]

@[expose] noncomputable def linMulAut627 [Module (ZMod 2) (Additive W)] :
    MulAut W →* Module.End (ZMod 2) (Additive W) where
  toFun φ := (MonoidHom.toAdditive φ.toMonoidHom).toZModLinearMap 2
  map_one' := by
    ext v
    rfl
  map_mul' φ ψ := by
    ext v
    rfl

theorem linMulAut627_apply [Module (ZMod 2) (Additive W)] (φ : MulAut W) (v : Additive W) :
    linMulAut627 φ v = Additive.ofMul (φ (Additive.toMul v)) := rfl

theorem linMulAut627_injective [Module (ZMod 2) (Additive W)] :
    Function.Injective (linMulAut627 (W := W)) := by
  intro φ ψ h
  ext w
  have := LinearMap.congr_fun h (Additive.ofMul w)
  simpa [linMulAut627_apply] using this

@[expose] def mulAutOfInvol627 (τ : Additive W →+ Additive W) (hτ : ∀ v, τ (τ v) = v) :
    MulAut W where
  toFun w := Additive.toMul (τ (Additive.ofMul w))
  invFun w := Additive.toMul (τ (Additive.ofMul w))
  left_inv w := by simp [hτ]
  right_inv w := by simp [hτ]
  map_mul' a b := by
    show Additive.toMul (τ (Additive.ofMul a + Additive.ofMul b)) = _
    rw [map_add]
    rfl

theorem containsTransvections_linMulAut627 [Module (ZMod 2) (Additive W)] :
    ContainsTransvections (linMulAut627 (W := W)) := by
  intro x f hfx
  set τ : Additive W →+ Additive W :=
    { toFun := fun v => v + f v • x
      map_zero' := by simp
      map_add' := fun a b => by
        rw [map_add, add_smul]
        abel } with hτ
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  have hinv : ∀ v, τ (τ v) = v := by
    intro v
    show (v + f v • x) + f (v + f v • x) • x = v
    rw [map_add, map_smul, hfx, smul_zero, add_zero, add_assoc, ← add_smul, h2, zero_smul,
      add_zero]
  refine ⟨mulAutOfInvol627 τ hinv, fun v => ?_⟩
  rfl

theorem mem_flagKernel_of_mem_flagStab_two {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Type} [Group H] {ρ : H →* Module.End (ZMod 2) V} {C : ℕ → Submodule (ZMod 2) V}
    (hC : IsCompleteFlag C) {g : H} (hg : g ∈ flagStab ρ C) : g ∈ flagKernel ρ C := by
  refine ⟨hg, fun k v hv => ?_⟩
  obtain ⟨u, hu⟩ := hC.succ k
  have hcases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have huC : u ∈ C (k + 1) := by
    rw [hu]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
  have hgu : ρ g u ∈ C (k + 1) := flagStab_apply_mem ρ hg huC
  rw [hu, Submodule.mem_sup] at hgu
  obtain ⟨c', hc', w, hw, hgu'⟩ := hgu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [hu, Submodule.mem_sup] at hv
  obtain ⟨c, hc, w', hw', rfl⟩ := hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw'
  have hgc : ρ g c ∈ C k := flagStab_apply_mem ρ hg hc
  rcases hcases b with rfl | rfl
  ·
    rw [zero_smul, add_zero] at hgu'
    have hu' : u ∈ C k := by
      have h1 : ρ g⁻¹ (ρ g u) ∈ C k := (hg k _ (hgu' ▸ hc')).2
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] at h1
    rw [map_add, map_smul]
    have h1 : ρ g u ∈ C k := hgu' ▸ hc'
    exact sub_mem (add_mem hgc (Submodule.smul_mem _ _ h1))
      (add_mem hc (Submodule.smul_mem _ _ hu'))
  · rw [one_smul] at hgu'
    have e : ρ g (c + a • u) - (c + a • u) = (ρ g c - c) + a • c' := by
      rw [map_add, map_smul, ← hgu', smul_add]
      abel
    rw [e]
    exact add_mem (sub_mem hgc hc) (Submodule.smul_mem _ _ hc')

theorem eq_one_of_mem_normalizer_sylow_ch627 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) {δ : MulAut W}
    (hδ : δ ∈ Subgroup.normalizer (P : Set (MulAut W))) (hodd : Odd (orderOf δ)) : δ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : ∀ x : Additive W, 2 • x = 0 := fun x => by
    show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
    rw [hW]
    rfl
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW'
  have : Finite (Additive W) := inferInstanceAs (Finite W)
  have : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  set ρ := linMulAut627 (W := W) with hρdef
  have hρinj : Function.Injective ρ := linMulAut627_injective
  have hρ : ContainsTransvections ρ := containsTransvections_linMulAut627
  obtain ⟨C, hC, -⟩ := exists_isCompleteFlag_forall_exists_eq
    (F := fun k : ℕ => if k = 0 then (⊥ : Submodule (ZMod 2) (Additive W)) else ⊤)
    (monotone_nat_of_le_succ fun k => by
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk]) ⟨1, by simp⟩
  have huni : ∀ X : Submodule (ZMod 2) (Additive W),
      (∀ h ∈ flagKernel ρ C, ∀ v ∈ X, ρ h v ∈ X) → ∃ i, X = C i :=
    fun X hX => hρ.exists_eq_of_flagKernel_invariant hC hX
  obtain ⟨S, hS⟩ := hC.exists_sylow_normalizer_le_flagStab ρ 2 hρinj huni
  obtain ⟨M, hM⟩ := hC.exists_eq_top
  have hK2 : IsPGroup 2 (flagKernel ρ C) := isPGroup_flagKernel ρ 2 hρinj hC.zero hM
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut W) S (hP2.toSylow hPi)
  have hPg : ∀ x : MulAut W, x ∈ P ↔ g⁻¹ * x * g ∈ (S : Subgroup (MulAut W)) := by
    intro x
    have h1 : (x ∈ (hP2.toSylow hPi : Subgroup (MulAut W))) ↔ x ∈ P := by
      rw [IsPGroup.toSylow_coe]
    rw [← h1, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  set δ' := g⁻¹ * δ * g with hδ'
  have hδ'N : δ' ∈ Subgroup.normalizer ((S : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 : y ∈ (S : Subgroup (MulAut W)) ↔ g * y * g⁻¹ ∈ P := by
      rw [hPg]
      simp [mul_assoc]
    have e2 : δ' * y * δ'⁻¹ ∈ (S : Subgroup (MulAut W)) ↔
        δ * (g * y * g⁻¹) * δ⁻¹ ∈ P := by
      rw [hPg]
      simp [hδ', mul_assoc]
    rw [e1, e2]
    exact Subgroup.mem_normalizer_iff.mp hδ _
  have hδ'K : δ' ∈ flagKernel ρ C := mem_flagKernel_of_mem_flagStab_two hC (hS hδ'N)
  obtain ⟨n, hn⟩ := hK2 ⟨δ', hδ'K⟩
  have hδ'n : δ' ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hord : orderOf δ' = orderOf δ := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective δ
    simpa [MulAut.conj_apply, hδ'] using this
  have h1 : orderOf δ' ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hδ'n
  rw [hord] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

end CFSG.Quasithin.H13
