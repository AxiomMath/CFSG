module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.ClassicalGroups.Unitary.Transitivity
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K]

theorem s16k_herm_self_eq_zero_or_one {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hfix : ∀ x : K, σ x = x → x = 0 ∨ x = 1) {n : ℕ} (v : Fin n → K) :
    herm σ v v = 0 ∨ herm σ v v = 1 :=
  hfix (herm σ v v) (herm_self_fixed σ hσ.invol v)

private def s16k_fixSpace {K : Type*} [Field K] {n : ℕ}
    (B : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ b ∈ B, (b : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' := by
    intro v w hv hw b hb
    rw [Matrix.mulVec_add, hv b hb, hw b hb]
  zero_mem' := by intro b hb; simp
  smul_mem' := by
    intro c v hv b hb
    rw [Matrix.mulVec_smul, hv b hb]

theorem s16k_finrank_two_of_nofix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {n : ℕ} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ^ p = 1)
    (U : Submodule K (Fin n → K)) (hU : U ≠ ⊥)
    (hUg : ∀ u ∈ U, (g : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ U)
    (hnofix : ∀ u ∈ U, (g : Matrix (Fin n) (Fin n) K) *ᵥ u = u → u = 0) :
    2 ≤ Module.finrank K U := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let f : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have hf_apply : ∀ v : Fin n → K, f v = (g : Matrix (Fin n) (Fin n) K) *ᵥ v := by
    intro v
    change ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv) v =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ v
    rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
      Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  have hfpow : f ^ p = 1 := by
    change ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))
        (Matrix.GeneralLinearGroup.toLin g)) ^ p = 1
    rw [← map_pow, ← map_pow, hg, map_one, map_one]
  have hfU : ∀ u ∈ U, f u ∈ U := fun u hu => by rw [hf_apply]; exact hUg u hu
  have hmapU : U.map (f : (Fin n → K) →ₗ[K] (Fin n → K)) ≤ U :=
    Submodule.map_le_iff_le_comap.mpr hfU
  have hmapU_eq : U.map (f : (Fin n → K) →ₗ[K] (Fin n → K)) = U :=
    Submodule.eq_of_le_of_finrank_le hmapU (by rw [LinearEquiv.finrank_map_eq])
  have hf_inv_U : ∀ u ∈ U, f.symm u ∈ U := by
    intro u hu
    have hcomap : U ≤ U.comap (f.symm : (Fin n → K) →ₗ[K] (Fin n → K)) := by
      rw [← Submodule.map_equiv_eq_comap_symm f U]
      exact hmapU_eq.ge
    exact hcomap hu
  let gU : U ≃ₗ[K] U :=
    { toFun := fun u => ⟨f u, hfU u u.2⟩
      invFun := fun u => ⟨f.symm u, hf_inv_U u u.2⟩
      left_inv := fun u => Subtype.ext (f.symm_apply_apply u)
      right_inv := fun u => Subtype.ext (f.apply_symm_apply u)
      map_add' := fun u v => Subtype.ext (by
        change f ((u : Fin n → K) + (v : Fin n → K)) =
          f (u : Fin n → K) + f (v : Fin n → K)
        exact map_add f _ _)
      map_smul' := fun r u => Subtype.ext (by
        change f (r • (u : Fin n → K)) = r • f (u : Fin n → K)
        exact map_smul f _ _) }
  have hgU_pow : gU ^ p = 1 := by
    ext u
    have hiter : ∀ m : ℕ, ((gU ^ m) u : Fin n → K) = (f ^ m) u := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ', LinearEquiv.mul_apply]
          change (f ((gU ^ m) u) : Fin n → K) = (f ^ (m + 1)) u
          rw [ih, pow_succ']
          rfl
    rw [hiter p, hfpow]
    rfl
  have hgU_ne : gU ≠ 1 := by
    intro h
    obtain ⟨u₀, hu₀U, hu₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have h1 : f u₀ = u₀ := by
      have h2 := congrArg (fun e : U ≃ₗ[K] U => (e ⟨u₀, hu₀U⟩ : Fin n → K)) h
      simpa [gU] using h2
    have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ u₀ = u₀ := by rwa [hf_apply] at h1
    exact hu₀ (hnofix u₀ hu₀U h3)
  have horder : orderOf gU = p := orderOf_eq_prime hgU_pow hgU_ne
  haveI : Module.Finite K U := Module.Finite.of_injective U.subtype Subtype.coe_injective
  have hcardz : Nat.card ↥(Subgroup.zpowers gU) = p := by
    rw [Nat.card_zpowers, horder]
  haveI hGp : IsPGroup p ↥(Subgroup.zpowers gU) :=
    IsPGroup.of_card (n := 1) (by rw [hcardz, pow_one])
  letI : MulAction ↥(Subgroup.zpowers gU) U :=
    MulAction.compHom U (Subgroup.subtype (Subgroup.zpowers gU))
  have hfixset : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers gU) U) = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨(0 : U), ?_⟩⟩⟩
    · have ha : (a : U) = 0 := by
        have h'mem := a.2 (⟨gU, Subgroup.mem_zpowers gU⟩ : ↥(Subgroup.zpowers gU))
        rw [MulAction.compHom_smul_def] at h'mem
        have h2 : gU (a : U) = (a : U) := by simpa using h'mem
        have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) = (a : Fin n → K) := by
          have h4 := congrArg (fun x : U => (x : Fin n → K)) h2
          simpa [gU, hf_apply] using h4
        exact Subtype.ext (hnofix (a : Fin n → K) (a : U).2 h3)
      have hb : (b : U) = 0 := by
        have h'mem := b.2 (⟨gU, Subgroup.mem_zpowers gU⟩ : ↥(Subgroup.zpowers gU))
        rw [MulAction.compHom_smul_def] at h'mem
        have h2 : gU (b : U) = (b : U) := by simpa using h'mem
        have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ (b : Fin n → K) = (b : Fin n → K) := by
          have h4 := congrArg (fun x : U => (x : Fin n → K)) h2
          simpa [gU, hf_apply] using h4
        exact Subtype.ext (hnofix (b : Fin n → K) (b : U).2 h3)
      rw [ha, hb]
    · intro m
      exact smul_zero m
  have hmod := hGp.card_modEq_card_fixedPoints U
  rw [hfixset] at hmod
  have hdvd : p ∣ Nat.card U - 1 := (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm
  have hcardU : Nat.card U = Nat.card K ^ Module.finrank K U := Module.natCard_eq_pow_finrank
  rw [hcardU, hK] at hdvd
  have hge1 : 1 ≤ Module.finrank K U := by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨u, huU⟩, fun h => hu0 (Subtype.ext_iff.mp h)⟩
  have hne1 : Module.finrank K U ≠ 1 := by
    intro h1
    have h3 : p ∣ 3 := by
      rw [h1] at hdvd
      simpa using hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 3) h3
    omega
  omega

theorem s16k_exists_herm_eq_zero_of_two_le_finrank {K : Type*} [Field K]
    {n : ℕ} {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hnorm : ∀ v : Fin n → K, herm σ v v = 0 ∨ herm σ v v = 1)
    (U : Submodule K (Fin n → K)) (hU : 2 ≤ Module.finrank K U) :
    ∃ u ∈ U, u ≠ 0 ∧ herm σ u u = 0 := by
  classical
  haveI : Module.Finite K U := Module.Finite.of_injective U.subtype Subtype.coe_injective
  haveI : Module.Free K U := Module.Free.of_divisionRing K U
  obtain ⟨c, hcU, hc0⟩ : ∃ c ∈ U, c ≠ 0 := by
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank K U)
    exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩
  rcases hnorm c with hc | hc
  · exact ⟨c, hcU, hc0, hc⟩
  have hnotle : ¬ Module.finrank K U ≤ 1 := by omega
  have hnot : ∀ v : U, ∃ w : U, ∀ a : K, a • v ≠ w := by
    intro v
    by_contra h
    apply hnotle
    rw [finrank_le_one_iff]
    refine ⟨v, fun w => ?_⟩
    by_contra h2
    exact h ⟨w, fun a ha => h2 ⟨a, ha⟩⟩
  obtain ⟨w, hw⟩ := hnot ⟨c, hcU⟩
  let y : Fin n → K := w.1
  have hyU : y ∈ U := w.2
  have hynot : ∀ a : K, a • c ≠ y := by
    intro a ha
    exact hw a (Subtype.ext ha)
  let x : Fin n → K := y - herm σ c y • c
  have hxU : x ∈ U := U.sub_mem hyU (U.smul_mem _ hcU)
  have hxc : herm σ c x = 0 := by
    rw [show x = y - herm σ c y • c from rfl, herm_sub_right, herm_smul_right, hc, mul_one,
      sub_self]
  have hx0 : x ≠ 0 := by
    intro hx
    have hy : herm σ c y • c = y := by
      have h := sub_eq_zero.mp (show y - herm σ c y • c = 0 from hx)
      exact h.symm
    exact hynot (herm σ c y) hy
  rcases hnorm x with hx | hx
  · exact ⟨x, hxU, hx0, hx⟩
  obtain ⟨l, hl⟩ := hσ.exists_norm (d := -1) (by rw [map_neg, map_one])
  have hxc' : herm σ x c = 0 := by rw [herm_conj σ hσ.invol, hxc, map_zero]
  refine ⟨c + l • x, U.add_mem hcU (U.smul_mem _ hxU), ?_, ?_⟩
  · intro hzero
    have h1 : herm σ c (c + l • x) = 1 := by
      rw [herm_add_right, herm_smul_right, hc, hxc, mul_zero, add_zero]
    rw [hzero, herm_zero_right] at h1
    exact zero_ne_one h1
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hc, hx, hxc,
      hxc']
    linear_combination hl

theorem s16k_exists_herm_ne_zero_of_fixed {K : Type*} [Field K] [Finite K]
    {n : ℕ} {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (B : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hBiso : ∀ b ∈ B, b ∈ SUid σ n)
    (hBinv : (Nat.card ↥B : K) ≠ 0)
    (U : Submodule K (Fin n → K)) (hUne : U ≠ ⊥)
    (hUfix : ∀ b ∈ B, ∀ u ∈ U, (b : Matrix (Fin n) (Fin n) K) *ᵥ u = u) :
    ∃ w : Fin n → K, herm σ w w ≠ 0 ∧
      ∀ b ∈ B, (b : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
  classical
  haveI : Fintype ↥B := Fintype.ofFinite ↥B
  let M : ↥B → (Fin n → K) →ₗ[K] (Fin n → K) := fun b =>
    Matrix.mulVecLin ((b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hM_apply : ∀ (b : ↥B) (v : Fin n → K),
      M b v = ((b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v :=
    fun b v => by
    simp only [M, Matrix.mulVecLin_apply]
  have hUle : U ≤ s16k_fixSpace B := fun u hu b hb => hUfix b hb u hu
  have hPfix : ∀ (v : Fin n → K) (b₀ : ↥B),
      M b₀ ((Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b v)
        = (Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b v := by
    intro v b₀
    rw [LinearMap.map_smul, map_sum]
    congr 1
    refine Fintype.sum_bijective (fun b : ↥B => b₀ * b) (Group.mulLeft_bijective b₀)
      (fun b => M b₀ (M b v)) (fun b => M b v) (fun b => ?_)
    simp only [M, Matrix.mulVecLin_mul, LinearMap.comp_apply, Subgroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_mul]
  have hPmem : ∀ v : Fin n → K,
      (Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b v ∈ s16k_fixSpace B := by
    intro v b₀ hb₀
    simpa only [hM_apply] using hPfix v ⟨b₀, hb₀⟩
  have hPherm : ∀ w : Fin n → K, w ∈ s16k_fixSpace B → ∀ v : Fin n → K,
      herm σ w ((Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b v) = herm σ w v := by
    intro w hw v
    rw [herm_smul_right, ← hermL_apply, map_sum]
    simp only [hermL_apply]
    have hsum : (∑ b : ↥B, herm σ w (M b v)) = ∑ _b : ↥B, herm σ w v := by
      refine Finset.sum_congr rfl fun b _ => ?_
      have hfixw : ((b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w
          = w := hw b b.2
      have hbiso : herm σ (((b : Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ w)
          (((b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
            = herm σ w v := by
        simpa only [smul_def] using
          herm_smul_smul σ (⟨(b : Matrix.GeneralLinearGroup (Fin n) K), hBiso b b.2⟩ :
            SUid σ n) w v
      calc herm σ w (M b v)
          = herm σ w (((b : Matrix.GeneralLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hM_apply]
        _ = herm σ (((b : Matrix.GeneralLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K) *ᵥ w)
              (((b : Matrix.GeneralLinearGroup (Fin n) K) :
                Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [hfixw]
        _ = herm σ w v := hbiso
    rw [hsum, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul K, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hBinv, one_mul]
  have hex : ∃ w ∈ s16k_fixSpace B, herm σ w w ≠ 0 := by
    by_contra hcon
    have hzero' : ∀ w : Fin n → K, w ∈ s16k_fixSpace B → herm σ w w = 0 := by
      intro w hw
      by_contra hne
      exact hcon ⟨w, hw, hne⟩
    have hvan : ∀ x ∈ s16k_fixSpace B, ∀ y ∈ s16k_fixSpace B, herm σ x y = 0 :=
      fun x hx y hy => herm_eq_zero_of_forall_isotropic hσ (fun s hs => hzero' s hs) hx hy
    have hzero : ∀ w ∈ s16k_fixSpace B, w = 0 := by
      intro w hw
      apply eq_zero_of_herm σ
      intro v
      rw [← hPherm w hw v]
      exact hvan w hw ((Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b v) (hPmem v)
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    exact hu0 (hzero u (hUle huU))
  obtain ⟨w, hwC, hww⟩ := hex
  exact ⟨w, hww, fun b hb => hwC b hb⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
