module

public import CFSG.ClassicalInvolution.AschTight.S19KUniIn
public import CFSG.ClassicalInvolution.AschTight.S19KOutU2

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups Matrix

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem false_of_twistU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f) {E : Type}
    [Group E] (θ : Phan.Su K p f 3 →* E) (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3))
    {v : MulAut E} {α : Phan.Su K p f 3 →* Phan.Su K p f 3} {G : GL (Fin 3) K}
    (hα : ∀ x, θ (α x) = v (θ x))
    (hform : ∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) * (unitaryInvolution K p f).mapMatrix
        (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hiso : ((G : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K p f)).transpose *
      (G : Matrix (Fin 3) (Fin 3) K) = 1)
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) K)) (hv2 : v * v = 1)
    (hfix : ∀ A : Phan.Su K p f 2, v (θ (Phan.blockEmb K p f 3 2 0 (by norm_num) A)) =
      θ (Phan.blockEmb K p f 3 2 0 (by norm_num) A)) : False := by
  set σ := unitaryInvolution K p f with hσdef
  have hσσc : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hσσM : ∀ M : Matrix (Fin 3) (Fin 3) K, σ.mapMatrix (σ.mapMatrix M) = M := fun M => by
    ext i j
    simp [RingEquiv.mapMatrix_apply, hσσc]
  have : Group.IsPerfect (Phan.Su K p f 3) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) le_rfl
      fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK
        (Models.prime_pow_ne_two_of_ne_two hp f)
  have hvv : ∀ x, v (v x) = x := fun x => by rw [← MulAut.mul_apply, hv2, MulAut.one_apply]
  have hαα := ModelFacts.UnitaryAut.lift_comp_self_eq_id hker hvv hα
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  set Gm := (G : Matrix (Fin 3) (Fin 3) K) with hGm
  set Gi := ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hGidef
  have hGi : Gi * Gm = 1 := Units.inv_mul G
  have hGi' : Gm * Gi = 1 := Units.mul_inv G
  have hdet0 : Gm.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hGi'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hσG : σ.mapMatrix Gm = Giᵀ := by
    have h1 : (Gm.map σ)ᵀ = Gi := by
      calc (Gm.map σ)ᵀ = (Gm.map σ)ᵀ * Gm * Gi := by rw [Matrix.mul_assoc, hGi', Matrix.mul_one]
        _ = Gi := by rw [hiso, Matrix.one_mul]
    rw [RingEquiv.mapMatrix_apply, ← h1, Matrix.transpose_transpose]
  have hσGi : σ.mapMatrix Gi = Gmᵀ := by
    have h1 : σ.mapMatrix Gi * σ.mapMatrix Gm = 1 := by rw [← map_mul, hGi, map_one]
    rw [hσG] at h1
    calc σ.mapMatrix Gi = σ.mapMatrix Gi * (Giᵀ * Gmᵀ) := by
          rw [← Matrix.transpose_mul, hGi', Matrix.transpose_one, Matrix.mul_one]
      _ = Gmᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcomm : ∀ x : Phan.Su K p f 3,
      (Gm * Giᵀ) * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (Gm * Giᵀ) := by
    intro x
    have h1 := congrArg (fun y : Phan.Su K p f 3 =>
      (((y : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (DFunLike.congr_fun hαα x)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h1
    rw [hform, hform, map_mul, map_mul, hσσM, hσG, hσGi] at h1
    have hP : Gmᵀ * Gi * (Gm * Giᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Gi Gm, hGi, Matrix.one_mul,
        ← Matrix.transpose_mul, hGi, Matrix.transpose_one]
    calc Gm * Giᵀ * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Gm * Giᵀ * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (Gmᵀ * Gi * (Gm * Giᵀ)) := by rw [hP, Matrix.mul_one]
      _ = (Gm * (Giᵀ * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Gmᵀ) * Gi) * (Gm * Giᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  obtain ⟨s, hs⟩ := ModelFacts.UnitaryAut.eq_smul_one_of_commute hU hp (le_refl 3) (Gm * Giᵀ)
    fun y hy => by
      have hy' : y ∈ SUid σ 3 := by rw [SUid_eq_statedSU hK]; exact hy
      exact hcomm ⟨y, hy'⟩
  have hGs : Gm = s • Gmᵀ := by
    have h1 : Gm * Giᵀ * Gmᵀ = Gm := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hGi', Matrix.transpose_one, Matrix.mul_one]
    rw [hs, Matrix.smul_mul, Matrix.one_mul] at h1
    exact h1.symm
  obtain ⟨hG02, hG12, hG20, hG21⟩ := hG
  have hdetB : Gm.det = (Gm 0 0 * Gm 1 1 - Gm 0 1 * Gm 1 0) * Gm 2 2 := by
    rw [Matrix.det_fin_three, hG02, hG12, hG20, hG21]
    ring
  have hG22 : Gm 2 2 ≠ 0 := fun h => hdet0 (by rw [hdetB, h, mul_zero])
  have hs1 : s = 1 := by
    have h1 := congrFun (congrFun hGs 2) 2
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h1
    have h3 : 1 * Gm 2 2 = s * Gm 2 2 := by rw [one_mul]; exact h1
    exact (mul_right_cancel₀ hG22 h3).symm
  have hsymm : Gm 0 1 = Gm 1 0 := by
    have h1 := congrFun (congrFun hGs 0) 1
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hs1, one_mul] at h1
    exact h1
  have heq : ∀ A : Phan.Su K p f 2, ∃ r : K,
      Gm * σ.mapMatrix (((Phan.blockEmb K p f 3 2 0 (by norm_num) A : Phan.Su K p f 3) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        r • (((Phan.blockEmb K p f 3 2 0 (by norm_num) A : Phan.Su K p f 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * Gm := by
    intro A
    set x := Phan.blockEmb K p f 3 2 0 (by norm_num) A with hx
    have h1 : α x * x⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hfix A, mul_inv_cancel]
    obtain ⟨r, hr⟩ := ModelFacts.UnitaryAut.eq_smul_one_of_commute hU hp (le_refl 3)
      ((((α x * x⁻¹ : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      fun y hy => by
        have hy' : y ∈ SUid σ 3 := by rw [SUid_eq_statedSU hK]; exact hy
        have h3 := Subgroup.mem_center_iff.mp (hker h1) ⟨y, hy'⟩
        have h4 := congrArg (fun z : Phan.Su K p f 3 =>
          ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h3
        simp only [Subgroup.coe_mul, Units.val_mul] at h4
        exact h4.symm
    refine ⟨r, ?_⟩
    have h3 : (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        r • (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have h4 : α x = (α x * x⁻¹) * x := by group
      rw [h4, Subgroup.coe_mul, Units.val_mul, hr, Matrix.smul_mul, Matrix.one_mul]
    rw [hform] at h3
    calc Gm * σ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Gm * σ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Gi * Gm := by rw [Matrix.mul_assoc _ Gi Gm, hGi, Matrix.mul_one]
      _ = _ := by rw [h3]
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := normOne σ)
  rw [Phan.card_normOne hK] at hu
  have hu0 : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hσu : σ ((u : Kˣ) : K) = ((u : Kˣ) : K)⁻¹ :=
    eq_inv_of_mul_eq_one_left ((mem_normOne σ).mp u.2)
  have hu2 : ((u : Kˣ) : K) ≠ ((u : Kˣ) : K)⁻¹ := by
    intro h
    have hsq : ((u : Kˣ) : K) * ((u : Kˣ) : K) = 1 := by
      calc ((u : Kˣ) : K) * ((u : Kˣ) : K) = ((u : Kˣ) : K) * ((u : Kˣ) : K)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hu0
    have h1 : u ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_one, Units.val_one, pow_two]
      exact hsq
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at h3
    have h4 := Nat.le_of_dvd (by norm_num) h3
    have h5 : 3 ≤ p ^ f := by
      have h6 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have h7 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    omega
  obtain ⟨r₁, h₁⟩ := heq (torusTwo σ u)
  obtain ⟨r₂, h₂⟩ := heq (Phan.weylElt K p f)
  rw [coe_blockEmb3] at h₁ h₂
  have e122 := congrFun (congrFun h₁ 2) 2
  have e100 := congrFun (congrFun h₁ 0) 0
  have e111 := congrFun (congrFun h₁ 1) 1
  have e200 := congrFun (congrFun h₂ 0) 0
  have e222 := congrFun (congrFun h₂ 2) 2
  simp [coe_torusTwo, Phan.weylElt, RingEquiv.mapMatrix_apply, Matrix.mul_apply,
    Fin.sum_univ_three, hG02, hG12, hG20, hG21, hσu] at e122 e100 e111 e200 e222
  have hr₁ : r₁ = 1 := (mul_right_cancel₀ hG22 (by rw [one_mul]; exact e122)).symm
  have hr₂ : r₂ = 1 := (mul_right_cancel₀ hG22 (by rw [one_mul]; exact e222)).symm
  subst hr₁ hr₂
  simp only [one_mul] at e100 e111 e200
  have ha : Gm 0 0 = 0 := by
    have h3 : Gm 0 0 * (((u : Kˣ) : K)⁻¹ - ((u : Kˣ) : K)) = 0 := by linear_combination e100
    exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr (Ne.symm hu2))
  have hd : Gm 1 1 = 0 := by
    have h3 : Gm 1 1 * (((u : Kˣ) : K) - ((u : Kˣ) : K)⁻¹) = 0 := by linear_combination e111
    exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hu2)
  have hb : Gm 0 1 = 0 := by
    have h3 : (2 : K) * Gm 0 1 = 0 := by linear_combination hsymm - e200
    exact (mul_eq_zero.mp h3).resolve_left h2
  apply hdet0
  rw [hdetB, ha, hd, hb]
  ring

theorem inner_of_fix_rootU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {E : Type} [Group E] (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) {v : MulAut E} (hv2 : v * v = 1)
    (hfix : ∀ A : Phan.Su K p f 2, v (θ (Phan.blockEmb K p f 3 2 0 (by norm_num) A)) =
      θ (Phan.blockEmb K p f 3 2 0 (by norm_num) A)) : ∃ y : E, v = MulAut.conj y := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hh : v ∈ fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E) := by
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    exact hfix A
  obtain ⟨α, G, τ, hα, hform, hiso, hG, hτ⟩ := uni_lift_data hK hp hq (card_fixedSubfield hK)
    θ hθ hker v (hyp_of_mem_fixingSubgroupU hK hp hf θ hker hh)
  rcases hτ with rfl | rfl
  · refine uni_inner hK hp hf θ hθ hker hα (fun x => ?_) hiso hv2
    rw [hform, RingEquiv.mapMatrix_refl]
    rfl
  · exact (false_of_twistU hK hp hf θ hker hα hform hiso hG hv2 hfix).elim

end CFSG.Quasithin.Ch3E213M.OLA
