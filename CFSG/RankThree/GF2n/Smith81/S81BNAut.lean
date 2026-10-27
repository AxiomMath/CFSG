module

public import CFSG.RankThree.GF2n.Smith81.S81A5Normalizer
public import CFSG.RankThree.GF2n.Smith81.S81BA5Frame

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

private def schur6_I0 : Set.powersetCard (Fin 6) 3 :=
  tripleSet 0 1 2 (by decide) (by decide) (by decide)

private theorem schur6_gap_decide : ∀ x y z : Fin 6, x ≠ y → x ≠ z → y ≠ z →
    ({x, y, z} : Finset (Fin 6)) ≠ {0, 1, 2} →
    ∃ a b : Fin 6, a.val + 1 = b.val ∧ b ∈ ({x, y, z} : Finset (Fin 6)) ∧
      a ∉ ({x, y, z} : Finset (Fin 6)) := by
  decide

private theorem schur6_no_straddle : ∀ a b : Fin 6, a.val + 1 = b.val →
    ¬ (b ∈ ({0, 1, 2} : Finset (Fin 6)) ∧ a ∉ ({0, 1, 2} : Finset (Fin 6))) := by
  decide

private theorem schur6_gap (I : Set.powersetCard (Fin 6) 3) (hI : I ≠ schur6_I0) :
    ∃ a b : Fin 6, a.val + 1 = b.val ∧ b ∈ I.val ∧ a ∉ I.val := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hIxyz⟩ := Finset.card_eq_three.mp I.prop
  have hne : ({x, y, z} : Finset (Fin 6)) ≠ {0, 1, 2} := fun h =>
    hI (Subtype.ext ((hIxyz.trans h).trans rfl))
  rw [hIxyz]
  exact schur6_gap_decide x y z hxy hxz hyz hne

private theorem schur6_eq_smul (ξ : Cube K) (I : Set.powersetCard (Fin 6) 3)
    (h : ∀ J : Set.powersetCard (Fin 6) 3, J ≠ I → coord K ξ J = 0) :
    ξ = coord K ξ I • cubeBasis K I := by
  apply (cubeBasis K).repr.injective
  refine Finsupp.ext fun J => ?_
  show coord K ξ J = coord K (coord K ξ I • cubeBasis K I) J
  rw [coord_smul, coord_cubeBasis]
  by_cases hJ : I = J
  · subst hJ
    simp
  · rw [if_neg hJ, mul_zero]
    exact h J (fun h' => hJ h'.symm)

private theorem schur6_step (T : Cube K →ₗ[K] Cube K) (c : K)
    (hT' : ∀ {a b : Fin 6} (hne : a ≠ b) (ξ : Cube K),
      T (rho K (transvGL K a b hne 1) ξ) = rho K (transvGL K a b hne 1) (T ξ))
    {a b : Fin 6} (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hne : a ≠ b)
    (I : Set.powersetCard (Fin 6) 3) (hb : b ∈ I.val) (ha : a ∉ I.val)
    (hI : T (cubeBasis K I) = c • cubeBasis K I) :
    T (cubeBasis K (replSet I a b hb ha)) = c • cubeBasis K (replSet I a b hb ha) := by
  have hrho : rho K (transvGL K a b hne 1) (cubeBasis K I) =
      cubeBasis K I + cubeBasis K (replSet I a b hb ha) := by
    rw [rho_transvGL_cubeBasis (K := K) hab hne 1 I, dif_pos (And.intro hb ha), one_smul]
  have h1 := hT' hne (cubeBasis K I)
  rw [hrho, map_add, hI, map_smul, hrho, smul_add] at h1
  exact add_left_cancel h1

theorem commutes_scalar (T : Cube K →ₗ[K] Cube K)
    (hT : ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ∀ ξ, T (rho K g ξ) = rho K g (T ξ)) :
    ∃ c : K, ∀ ξ, T ξ = c • ξ := by
  have hT' : ∀ {a b : Fin 6} (hne : a ≠ b) (ξ : Cube K),
      T (rho K (transvGL K a b hne 1) ξ) = rho K (transvGL K a b hne 1) (T ξ) := by
    intro a b hne ξ
    refine hT _ ?_ ξ
    rw [transvGL_val]
    exact Matrix.det_transvection_of_ne a b hne 1
  have hzero : ∀ J : Set.powersetCard (Fin 6) 3, J ≠ schur6_I0 →
      coord K (T (cubeBasis K schur6_I0)) J = 0 := by
    intro J hJ
    obtain ⟨a, b, hab, hbJ, haJ⟩ := schur6_gap J hJ
    have hne : a ≠ b := fun h => by subst h; omega
    have hno : ¬ (b ∈ schur6_I0.val ∧ a ∉ schur6_I0.val) := schur6_no_straddle a b hab
    have hfix : rho K (transvGL K a b hne 1) (cubeBasis K schur6_I0) =
        cubeBasis K schur6_I0 := by
      rw [rho_transvGL_cubeBasis (K := K) (Or.inl hab) hne 1 schur6_I0, dif_neg hno]
    have hTfix : rho K (transvGL K a b hne 1) (T (cubeBasis K schur6_I0)) =
        T (cubeBasis K schur6_I0) := by
      rw [← hT' hne, hfix]
    exact coord_eq_zero_of_fixed (K := K) (Or.inl hab) hne hTfix hbJ haJ
  obtain ⟨c, hc⟩ : ∃ c : K, T (cubeBasis K schur6_I0) = c • cubeBasis K schur6_I0 :=
    ⟨_, schur6_eq_smul _ schur6_I0 hzero⟩
  have main : ∀ n : ℕ, ∀ I : Set.powersetCard (Fin 6) 3, (∑ i ∈ I.val, (i : ℕ)) = n →
      T (cubeBasis K I) = c • cubeBasis K I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro I hI
      by_cases hI0 : I = schur6_I0
      · subst hI0
        exact hc
      · obtain ⟨a, b, hab, hbI, haI⟩ := schur6_gap I hI0
        have hne : a ≠ b := fun h => by subst h; omega
        have hna : a ∉ I.val.erase b := fun h => haI (Finset.mem_of_mem_erase h)
        have hsum : ∑ i ∈ (replSet I a b hbI haI).val, (i : ℕ) + 1 = n := by
          rw [← hI]
          show ∑ i ∈ insert a (I.val.erase b), (i : ℕ) + 1 = ∑ i ∈ I.val, (i : ℕ)
          rw [Finset.sum_insert hna, ← Finset.add_sum_erase I.val _ hbI]
          omega
        have hPI := ih _ (by omega) (replSet I a b hbI haI) rfl
        have hb' : a ∈ (replSet I a b hbI haI).val := Finset.mem_insert_self a _
        have ha' : b ∉ (replSet I a b hbI haI).val := by
          intro h
          have h' : b ∈ insert a (I.val.erase b) := h
          rcases Finset.mem_insert.mp h' with h1 | h1
          · exact hne h1.symm
          · exact Finset.notMem_erase b I.val h1
        have hstep := schur6_step (a := b) (b := a) T c hT' (Or.inr hab) hne.symm
          (replSet I a b hbI haI) hb' ha' hPI
        have hback : replSet (replSet I a b hbI haI) b a hb' ha' = I :=
          (replSet_eq_iff hb' ha' hbI haI).mpr rfl
        rw [hback] at hstep
        exact hstep
  have hlin : T = c • LinearMap.id := by
    apply (cubeBasis K).ext
    intro I
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact main _ I rfl
  exact ⟨c, fun ξ => by simpa using LinearMap.congr_fun hlin ξ⟩

theorem invTransp_mul (g h : GL (Fin 6) K) : invTransp (g * h) = invTransp g * invTransp h := by
  refine Units.ext ?_
  show (((g * h)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ =
    ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ *
      ((h⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem invTransp_invTransp (g : GL (Fin 6) K) : invTransp (invTransp g) = g := by
  refine Units.ext ?_
  show ((g : Matrix (Fin 6) (Fin 6) K)ᵀ)ᵀ = (g : Matrix (Fin 6) (Fin 6) K)
  exact Matrix.transpose_transpose _

theorem invTransp_inv (g : GL (Fin 6) K) : invTransp g⁻¹ = (invTransp g)⁻¹ := by
  refine Units.ext ?_
  rfl

theorem det_invTransp (g : GL (Fin 6) K) :
    ((invTransp g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det =
      ((g : Matrix (Fin 6) (Fin 6) K).det)⁻¹ := by
  have h1 : (g : Matrix (Fin 6) (Fin 6) K).det *
      ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  show (((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ).det = _
  rw [Matrix.det_transpose]
  exact eq_inv_of_mul_eq_one_right h1

@[expose] def InnerType (T : Cube K ≃ₗ[K] Cube K) : Prop :=
  ∃ P : GL (Fin 6) K, ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
    ∀ ξ, T (rho K g ξ) = rho K (P * g * P⁻¹) (T ξ)

@[expose] def GraphType (T : Cube K ≃ₗ[K] Cube K) : Prop :=
  ∃ P : GL (Fin 6) K, ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
    ∀ ξ, T (rho K g ξ) = rho K (P * invTransp g * P⁻¹) (T ξ)

theorem normalizer_dichotomy [Finite K] [CharP K 2] {T : Cube K ≃ₗ[K] Cube K}
    (hT : NormalizesSL T) : InnerType T ∨ GraphType T := by
  obtain ⟨P, hP | hP⟩ := a5NormalizerModelStatement_holds K T hT
  · exact Or.inl ⟨P, hP⟩
  · exact Or.inr ⟨P, hP⟩

theorem innerType_mul_of_graphType {T₁ T₂ : Cube K ≃ₗ[K] Cube K} (h₁ : GraphType T₁)
    (h₂ : GraphType T₂) : InnerType (T₁ * T₂) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨P₁ * invTransp P₂, fun g hg ξ => ?_⟩
  have hdet : ((P₂ * invTransp g * P₂⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, det_invTransp, hg, inv_one]
  have hconj : P₁ * invTransp (P₂ * invTransp g * P₂⁻¹) * P₁⁻¹ =
      P₁ * invTransp P₂ * g * (P₁ * invTransp P₂)⁻¹ := by
    rw [invTransp_mul, invTransp_mul, invTransp_invTransp, invTransp_inv]
    simp only [_root_.mul_inv_rev, _root_.mul_assoc]
  show T₁ (T₂ (rho K g ξ)) = rho K (P₁ * invTransp P₂ * g * (P₁ * invTransp P₂)⁻¹) (T₁ (T₂ ξ))
  rw [hP₂ g hg ξ, hP₁ (P₂ * invTransp g * P₂⁻¹) hdet (T₂ ξ), hconj]

private theorem qn_rho_mul (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho_mul, Module.End.mul_apply]

private theorem qn_rho_one : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem qn_rho_inv_apply (P : GL (Fin 6) K) (x : Cube K) :
    rho K P (rho K P⁻¹ x) = x := by
  rw [← qn_rho_mul, mul_inv_cancel, qn_rho_one, Module.End.one_apply]

private theorem qn_scalar (P : GL (Fin 6) K) (T : Cube K ≃ₗ[K] Cube K)
    (hT : ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ∀ ξ, T (rho K g ξ) = rho K (P * g * P⁻¹) (T ξ)) :
    ∃ c : K, c ≠ 0 ∧ ∀ ξ, T ξ = c • rho K P ξ := by
  obtain ⟨c, hc⟩ := commutes_scalar (rho K P⁻¹ ∘ₗ T.toLinearMap) (by
    intro g hg ξ
    have hPg : P⁻¹ * (P * g * P⁻¹) = g * P⁻¹ := by group
    show rho K P⁻¹ (T (rho K g ξ)) = rho K g (rho K P⁻¹ (T ξ))
    rw [hT g hg ξ, ← qn_rho_mul, ← qn_rho_mul, hPg])
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : rho K P⁻¹ (T (p0 K)) = 0 := by
      have h2 : rho K P⁻¹ (T (p0 K)) = c • p0 K := hc (p0 K)
      rw [h0, zero_smul] at h2
      exact h2
    have h3 : T (p0 K) = 0 := by
      refine (rhoEquiv K P⁻¹).injective ?_
      simp only [rhoEquiv_apply, h1, map_zero]
    exact p0_ne_zero (K := K) (T.injective (h3.trans (map_zero T).symm))
  refine ⟨c, hc0, fun ξ => ?_⟩
  have h1 : rho K P⁻¹ (T ξ) = c • ξ := hc ξ
  calc T ξ = rho K P (rho K P⁻¹ (T ξ)) := (qn_rho_inv_apply P (T ξ)).symm
    _ = rho K P (c • ξ) := by rw [h1]
    _ = c • rho K P ξ := map_smul _ _ _

private theorem qn_pow_apply (P : GL (Fin 6) K) (T : Cube K ≃ₗ[K] Cube K) (c : K)
    (hTc : ∀ ξ, T ξ = c • rho K P ξ) (j : ℕ) (ξ : Cube K) :
    (T ^ j) ξ = (c ^ j) • rho K (P ^ j) ξ := by
  induction j generalizing ξ with
  | zero => simp [qn_rho_one]
  | succ j ih =>
    rw [pow_succ' T j, pow_succ' c j, pow_succ' P j, LinearEquiv.mul_apply, ih, map_smul, hTc,
      ← qn_rho_mul, smul_smul, mul_comm (c ^ j) c]

theorem mem_Gam_of_innerType_pow [Finite K] [CharP K 2] {T : Cube K ≃ₗ[K] Cube K}
    (hT : InnerType T) {k : ℕ} (hk : T ^ (2 ^ k) = 1) : T ∈ Gam K := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨P, hP⟩ := hT
  obtain ⟨c, hc0, hTc⟩ := qn_scalar P T hP
  have hcard : 2 ∣ Fintype.card K := by
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    rw [hm]
    exact dvd_pow_self 2 (PNat.pos m).ne'
  have hodd : ¬ 2 ∣ Fintype.card K - 1 := by
    have hpos : 0 < Fintype.card K := Fintype.card_pos
    omega
  obtain ⟨r, hr_odd, hr_pow⟩ : ∃ r : ℕ, ¬ 2 ∣ r ∧ ∀ x : K, x ≠ 0 → x ^ r = 1 :=
    ⟨Fintype.card K - 1, hodd, fun x hx => FiniteField.pow_card_sub_one_eq_one x hx⟩
  have hTr : T ^ r = rhoEquiv K (P ^ r) := by
    refine LinearEquiv.ext (fun ξ => ?_)
    rw [qn_pow_apply P T c hTc r ξ, hr_pow c hc0, one_smul, rhoEquiv_apply]
  have hdetP : (P : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
  have hdetr : ((P ^ r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow]
    exact hr_pow _ hdetP
  have hTrGam : T ^ r ∈ Gam K := by
    rw [hTr, Gam, Subgroup.mem_map]
    exact ⟨P ^ r, CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdetr, rfl⟩
  have hcop2 : Nat.Coprime (2 ^ k) r :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr_odd)
  have hdvd : orderOf T ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime r (orderOf T) := (Nat.Coprime.coprime_dvd_left hdvd hcop2).symm
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact Subgroup.pow_mem _ hTrGam j

end CFSG.RankThree.GF2n.Smith81.A5Cube
