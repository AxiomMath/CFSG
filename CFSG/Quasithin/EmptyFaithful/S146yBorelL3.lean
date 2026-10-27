module

public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.LieType.Simplicity.Classical

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace CFSG.Quasithin

section Three

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem core_projectiveSL_three (hK : 4 ≤ Nat.card K) :
    ∀ x : projectiveSL 3 K, x * x = 1 → (∀ b ∈ projUpperTriangular 3 K, x * b = b * x) → x = 1 := by
  intro x hx hc
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hUle : projUnitriangular 3 K ≤ projUpperTriangular 3 K :=
    Subgroup.map_mono (unitriangular_le_upperTriangular 3 K)
  have hxS : x ∈ projUnitriangular 3 K := by
    rw [← hS]
    refine mem_sylow_of_involution_commute S hx (fun s hs => hc s ?_)
    rw [hS] at hs
    exact hUle hs
  obtain ⟨u, hu, rfl⟩ := hxS
  have hcu : ∀ v ∈ unitriangular 3 K, u * v = v * u := by
    intro v hv
    have h1 := hc (proj 3 K v) (Subgroup.mem_map_of_mem _ (unitriangular_le_upperTriangular 3 K hv))
    rw [← map_mul, ← map_mul] at h1
    exact proj_injOn_unitriangular 3 ((unitriangular 3 K).mul_mem hu hv)
      ((unitriangular 3 K).mul_mem hv hu) h1
  obtain ⟨b, hb⟩ := K1.exists_eq_one_add_single_of_commute (n := 3) (by norm_num) hu hcu
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, t ≠ 1 := by
    have h4 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h4
    exact exists_ne 1
  have hdet : (diagonal ![(1 : K), (t : K), ((t⁻¹ : Kˣ) : K)]).det = 1 := by
    simp [det_diagonal, Fin.prod_univ_three]
  let h : SpecialLinearGroup (Fin 3) K := ⟨diagonal ![(1 : K), (t : K), ((t⁻¹ : Kˣ) : K)], hdet⟩
  have hhup : h ∈ upperTriangular 3 K := by
    intro i j hij
    exact diagonal_apply_ne _ (ne_of_gt hij)
  have hcomm := hc (proj 3 K h) (Subgroup.mem_map_of_mem _ hhup)
  have h2 : proj 3 K (h * u * h⁻¹) = proj 3 K u := by
    rw [map_mul, map_mul, map_inv, ← hcomm]
    group
  have h3 : h * u * h⁻¹ = u :=
    proj_injOn_unitriangular 3 (conj_mem_unitriangular hhup hu) hu h2
  have h4 : h * u = u * h := by
    calc h * u = h * u * h⁻¹ * h := by group
      _ = u * h := by rw [h3]
  have h5 : ((h : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K)) 0 2 =
      ((u : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K)) 0 2 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h4
    simpa [SpecialLinearGroup.coe_mul] using this
  have hhmat : (h : Matrix (Fin 3) (Fin 3) K) = diagonal ![(1 : K), (t : K), ((t⁻¹ : Kˣ) : K)] := rfl
  rw [hhmat, hb] at h5
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply] at h5
  have htK : (t : K) ≠ 1 := fun h' => ht (Units.ext h')
  have hb0 : b = 0 := by
    have h6 : b * (t : K) = b := by
      calc b * (t : K) = b * (t : K)⁻¹ * (t : K) := by rw [← h5]
        _ = b := inv_mul_cancel_right₀ t.ne_zero b
    have h7 : b * ((t : K) - 1) = 0 := by rw [mul_sub, h6, mul_one, sub_self]
    rcases mul_eq_zero.mp h7 with h8 | h8
    · exact h8
    · exact absurd (sub_eq_zero.mp h8) htK
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [hb, hb0]
    simp
  rw [hu1, map_one]

omit [Finite K] [CharP K 2] in
theorem projectiveSL_three_not_comm : ∃ a b : projectiveSL 3 K, a * b ≠ b * a := by
  have h01 : (⟨0, by norm_num⟩ : Fin 3) < ⟨1, by norm_num⟩ := by decide
  have h12 : (⟨1, by norm_num⟩ : Fin 3) < ⟨2, by norm_num⟩ := by decide
  have hu₁ := K1.transvection_mem_unitriangular (K := K) h01 1
  have hu₂ := K1.transvection_mem_unitriangular (K := K) h12 1
  refine ⟨proj 3 K (SpecialLinearGroup.transvection h01.ne (1 : K)),
    proj 3 K (SpecialLinearGroup.transvection h12.ne (1 : K)), fun h => ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact K1.transvection_mul_ne_of_ne_zero (K := K) (n := 3) le_rfl one_ne_zero
    (proj_injOn_unitriangular 3 ((unitriangular 3 K).mul_mem hu₁ hu₂)
      ((unitriangular 3 K).mul_mem hu₂ hu₁) h)

theorem borelRigid_projectiveSL_three (hK : 4 ≤ Nat.card K) (hsimple : IsSimpleGroup (projectiveSL 3 K)) :
    BorelRigid (projectiveSL 3 K) := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have h0 : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
    rw [← hS]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL 3 K)) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := projectiveSL_three_not_comm (K := K)
      apply hab
      have : a ∈ Subgroup.center (projectiveSL 3 K) := by rw [ht]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  refine borelRigid_of_inner (K1.sylowCentralizingAutInner_projectiveSL (by norm_num)) hZ h0 ?_
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2]
  exact core_projectiveSL_three hK

end Three

theorem borelRigid_psl3 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 3 2 f X) :
    BorelRigid X := by
  have hsimpleX : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 f h).2
  obtain ⟨-, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : IsSimpleGroup (projectiveSL 3 K) := e'.symm.isSimpleGroup
  exact BorelRigid.of_mulEquiv e' (borelRigid_projectiveSL_three hK4 this)

end CFSG.Quasithin
