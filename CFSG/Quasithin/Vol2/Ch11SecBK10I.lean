module

public import CFSG.Quasithin.Vol2.Ch11SecBK10H
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L2

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem map_diagHom {σ : K ≃+* K} {u : Kˣ} (h : σ u = u) :
    SpecialLinearGroup.map σ.toRingHom (diagHom u) = diagHom u := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    diagHom_apply]
  fin_cases i <;> fin_cases j <;> simp [h]

theorem map_unip_one (σ : K ≃+* K) :
    SpecialLinearGroup.map σ.toRingHom (sl2UpperUnipotent 1) = sl2UpperUnipotent 1 := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent]

theorem ringAut_mul_apply (σ τ : K ≃+* K) (x : K) : (σ * τ) x = σ (τ x) := rfl

theorem pow_apply_eq {σ : K ≃+* K} {x : K} (h : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ringAut_mul_apply, h, ih]

variable [Finite K] [CharP K 2]

theorem two_dvd_card : 2 ∣ Nat.card K := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.ne_zero

theorem torusRigidAt_psl2 : TorusRigidAt (PSL2 K) (psl2UpperUnipotentSubgroup K) := by
  classical
  intro Sh hSh2 hSP hSs
  set Γ₀ := Sh.map (galPart (K := K)) with hΓ₀
  have hΓ₀2 : IsPGroup 2 Γ₀ := hSh2.map _
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := (FixedPoints.subfield Γ₀ K)ˣ)
  set u : Kˣ := Units.map (FixedPoints.subfield Γ₀ K).subtype.toMonoidHom u₀ with hu
  have hucoe : (u : K) = ((u₀ : FixedPoints.subfield Γ₀ K) : K) := rfl
  have hufix : ∀ σ ∈ Γ₀, σ (u : K) = u := fun σ hσ => by
    rw [hucoe]
    exact (u₀ : FixedPoints.subfield Γ₀ K).2 ⟨σ, hσ⟩
  set Y := diagHom u with hY
  have hY10 : (Y : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp [hY, diagHom_apply]
  have hY00 : (Y : Matrix (Fin 2) (Fin 2) K) 0 0 = u := by simp [hY, diagHom_apply]
  have hY11 : (Y : Matrix (Fin 2) (Fin 2) K) 1 1 = ((u⁻¹ : Kˣ) : K) := by
    rw [hY, diagHom_apply]
    simp
  refine ⟨psl2QuotientMap K Y, fun s hs => ?_, ?_, fun y' hy' _ β hβ hβy' => ?_⟩
  ·
    obtain ⟨G, hG⟩ := exists_rep s
    have hσ : galPart s ∈ Γ₀ := ⟨s, hs, rfl⟩
    have hGU : (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      apply lower_eq_zero_of_conj_mem
      have h1 := (hSs s hs (psl2QuotientMap K (sl2UpperUnipotent 1))).mp
        ((mem_unip_iff _).mpr (by simp [sl2UpperUnipotent]))
      rw [hG, MulAut.mul_apply, psl2FieldAut_mk, map_unip_one] at h1
      exact h1
    have hsY : s (psl2QuotientMap K Y) = psl2QuotientMap K (conjSL G Y) := by
      rw [hG, MulAut.mul_apply, psl2FieldAut_mk, map_diagHom (hufix _ hσ), pglAction_mk]
    rw [hsY, ← map_inv, ← map_mul, mem_unip_iff]
    obtain ⟨h00, h10, h11⟩ := conjSL_diagHom G hGU u
    exact unitriangular_mul_inv Y (conjSL G Y) hY10 h10 (by rw [h00, hY00]) (by rw [h11, hY11])
  ·
    have h1 : orderOf (psl2QuotientMap K Y) ∣ orderOf u :=
      (orderOf_map_dvd _ _).trans (orderOf_map_dvd _ _)
    have h2 : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
    have h3 : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units]
      have h4 := two_dvd_card (K := K)
      have h5 : 1 ≤ Nat.card K := Nat.card_pos
      exact Nat.Even.sub_odd h5 (even_iff_two_dvd.mpr h4) odd_one
    exact Odd.of_dvd_nat h3 (h1.trans h2)
  obtain ⟨Y', rfl⟩ := psl2QuotientMap_surjective y'
  have htr : (Y' : Matrix (Fin 2) (Fin 2) K) 0 0 + (Y' : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (u : K) + ((u⁻¹ : Kˣ) : K) := by
    rw [← map_inv, ← map_mul, mem_unip_iff] at hy'
    obtain ⟨n00, n10, n11⟩ := hy'
    have e : (Y' : Matrix (Fin 2) (Fin 2) K) =
        ((Y' * Y⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (Y : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [e]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, n00, n10, n11, hY10, hY00, hY11]
    have hY01 : (Y : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp [hY, diagHom_apply]
    rw [hY01]
    ring
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  obtain ⟨H, hH⟩ := exists_rep β
  set τ := galPart β with hτ
  have hfix : conjSL H (SpecialLinearGroup.map τ.toRingHom Y') = Y' := by
    apply psl2QuotientMap_injective
    rw [← pglAction_mk, ← psl2FieldAut_mk, ← MulAut.mul_apply, ← hH]
    exact hβy'
  have htau : τ ((u : K) + ((u⁻¹ : Kˣ) : K)) = (u : K) + ((u⁻¹ : Kˣ) : K) := by
    have h1 := congrArg (fun A : SL(2, K) => Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) hfix
    simp only [coe_conjSL] at h1
    rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.trace_fin_two, Matrix.trace_fin_two,
      SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.map_apply] at h1
    rw [← htr, map_add]
    exact h1
  have hτu : τ (u : K) = u ∨ τ (u : K) = ((u⁻¹ : Kˣ) : K) := by
    have hne : τ (u : K) ≠ 0 := (map_ne_zero τ).mpr u.ne_zero
    have h1 := eq_or_eq_inv_of_add_inv hne u.ne_zero (by
      rw [← map_inv₀, ← map_add, ← Units.val_inv_eq_inv_val, htau, Units.val_inv_eq_inv_val])
    rwa [← Units.val_inv_eq_inv_val] at h1
  have hτ2 : (τ ^ 2) (u : K) = u := by
    rw [sq, ringAut_mul_apply]
    rcases hτu with h | h
    · rw [h, h]
    · rw [h, Units.val_inv_eq_inv_val, map_inv₀, h, Units.val_inv_eq_inv_val, inv_inv]
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hrX
    have h1 := Subgroup.card_subgroup_dvd_card (psl2UpperUnipotentSubgroup K)
    rw [psl2UpperUnipotentSubgroup_card] at h1
    exact two_dvd_card.trans h1
  have hτr : τ ^ r = 1 := by rw [hτ, ← map_pow, hβr, map_one]
  have hτfix : τ (u : K) = u := by
    obtain ⟨m, hm⟩ := hr.odd_of_ne_two hr2
    have h1 : τ = (τ ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = r + 1 by omega, pow_succ, hτr, one_mul]
    rw [h1]
    exact pow_apply_eq hτ2 _
  have hτK₀ : ∀ z ∈ FixedPoints.subfield Γ₀ K, τ z = z := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, map_zero]
    · have hz0' : (⟨z, hz⟩ : FixedPoints.subfield Γ₀ K) ≠ 0 := fun h =>
        hz0 (congrArg Subtype.val h)
      obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hu₀ (Units.mk0 _ hz0')))
      have h1 : z = (u : K) ^ k := by
        have h2 := congrArg (fun v : (FixedPoints.subfield Γ₀ K)ˣ =>
          ((v : FixedPoints.subfield Γ₀ K) : K)) hk
        simp only [Units.val_mk0] at h2
        rw [← h2, hucoe, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
      rw [h1, map_pow, hτfix]
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  have hτΓ : τ ∈ Γ₀ := by
    have : FaithfulSMul Γ₀ K := ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩
    let φ : K →ₐ[FixedPoints.subfield Γ₀ K] K :=
      { τ.toRingHom with commutes' := fun z => hτK₀ z z.2 }
    obtain ⟨γ, hγ⟩ := (FixedPoints.toAlgHom_bijective Γ₀ K).2 φ
    have h1 : (γ : K ≃+* K) = τ := RingEquiv.ext fun x => by
      have h2 := congrArg (fun f : K →ₐ[FixedPoints.subfield Γ₀ K] K => f x) hγ
      exact h2
    rw [← h1]
    exact γ.2
  have hτ1 : τ = 1 := by
    obtain ⟨k, hk⟩ := hΓ₀2 ⟨τ, hτΓ⟩
    have h1 : orderOf τ ∣ 2 ^ k := by
      have h2 := orderOf_dvd_of_pow_eq_one hk
      rwa [Subgroup.orderOf_mk] at h2
    have h3 : orderOf τ ∣ r := orderOf_dvd_of_pow_eq_one hτr
    rcases (Nat.dvd_prime hr).mp h3 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at h1
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
  have hβin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) := by
    rw [hH, hτ1, map_one, mul_one]
    exact pglAction_mem_inner _
  exact eq_one_of_mem_inner ⟨r, hr, hβr, hβ1, hrX⟩ hβin

theorem torusRigid_psl2 : TorusRigid (PSL2 K) :=
  TorusRigid.of_at isSylowTwoOf_unip torusRigidAt_psl2

end BK10.L2

end CFSG.Quasithin.Vol2.Ch11.SecD
