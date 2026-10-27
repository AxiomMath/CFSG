module

public import CFSG.Quasithin.Vol2.Ch11SecBK10R
public import CFSG.Quasithin.Vol2.Ch11SecBK10I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def barAut (h : UnitaryFieldData 2 f K) : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem isPGroup_zpowers_bar (h : UnitaryFieldData 2 f K) :
    IsPGroup 2 (Subgroup.zpowers (barAut h)) ∧ (Subgroup.zpowers (barAut h)).Normal := by
  have hbb : barAut h ^ 2 = 1 := RingEquiv.ext fun c => by
    rw [pow_two]
    change h.bar (h.bar c) = c
    exact h.bar_bar c
  refine ⟨?_, ⟨fun n hn g => ?_⟩⟩
  · rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (barAut h ^ k) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hbb,
      _root_.one_zpow]
  · have hc : Commute g (barAut h) := RingEquiv.ext fun c => (map_bar_comm h g c)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact hn

theorem torusRigidAt_hyp (h : UnitaryFieldData 2 f K) (hf : Even f) :
    TorusRigidAt (hypPSU h 1 1) (hypProjUnitriangular h 1 1) := by
  classical
  have : Finite K := h.finite
  have h3 := not_three_dvd_of_even hf
  have hq := hq_of_even h hf
  have hΦ := semilinearAutHom_surjective_of_admissible h (le_refl 1) (le_refl 1) (by norm_num) hq
  intro Sh hSh2 hSP hSs
  obtain ⟨hb2, hbN⟩ := isPGroup_zpowers_bar h
  set Γ₀ := Sh.map (galPart h hq) ⊔ Subgroup.zpowers (barAut h) with hΓ₀
  have hΓ₀2 : IsPGroup 2 Γ₀ := IsPGroup.to_sup_of_normal_right (hSh2.map _) hb2
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := (FixedPoints.subfield Γ₀ K)ˣ)
  set u : Kˣ := Units.map (FixedPoints.subfield Γ₀ K).subtype.toMonoidHom u₀ with hu
  have hucoe : (u : K) = ((u₀ : FixedPoints.subfield Γ₀ K) : K) := rfl
  have hufix : ∀ σ ∈ Γ₀, σ (u : K) = u := fun σ hσ => by
    rw [hucoe]
    exact (u₀ : FixedPoints.subfield Γ₀ K).2 ⟨σ, hσ⟩
  have hubar : h.bar (u : K) = u :=
    hufix (barAut h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨t, ht⟩ := exists_torus h hubar
  have htT : ((t : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
    rw [ht]
    exact blockTriangular_diagonal _
  refine ⟨hypProj h 1 1 t, fun s hs => ?_, ?_, fun y' hy' _ β hβ hβy' => ?_⟩
  ·
    obtain ⟨x, rfl⟩ := hΦ s
    set σ := (x : SemiGL (HypIndex 1 1) K).right with hσ
    have hσΓ : σ ∈ Γ₀ := Subgroup.mem_sup_left ⟨_, hs, galPart_apply h hq x⟩
    obtain ⟨z, hz⟩ := semilinearAutHom_mem_inner h h3 (x := ⟨_, inl_mem h x.2⟩)
      (SemidirectProduct.right_inl _)
    have hdec := semilinearAutHom_eq_mul h x
    rw [← hz] at hdec
    have hzN : z ∈ Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have hF : fieldAutHom h σ (fieldAutHom h σ⁻¹ w) = w := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      have e : semilinearAutHom h (le_refl 1) (le_refl 1) x (fieldAutHom h σ⁻¹ w) =
          z * w * z⁻¹ := by
        rw [hdec, MulAut.mul_apply, hF, MulAut.conj_apply]
      rw [← e, ← hSs _ hs]
      refine ⟨fieldAutHom_mem h σ⁻¹, fun hw => ?_⟩
      have := fieldAutHom_mem h σ hw
      rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
    rw [normalizer_hypProjUnitriangular h (le_refl 1) (le_refl 1)] at hzN
    obtain ⟨c, hc, rfl⟩ := hzN
    have hcT := blockTriangular_of_mem_hypBorel h (le_refl 1) hc
    have hst : semilinearAutHom h (le_refl 1) (le_refl 1) x (hypProj h 1 1 t) =
        hypProj h 1 1 (c * t * c⁻¹) := by
      rw [hdec, MulAut.mul_apply, fieldAutHom_torus ht (hufix σ hσΓ), MulAut.conj_apply,
        ← map_inv, ← map_mul, ← map_mul]
    rw [hst, ← map_inv, ← map_mul]
    refine ⟨t * c * t⁻¹ * c⁻¹, ?_, by congr 1; group⟩
    exact Subgroup.mem_subgroupOf.mpr (commutator_mem_fullUnitriangular htT hcT)
  ·
    have h1 : orderOf (hypProj h 1 1 t) ∣ orderOf u := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, torus_pow_orderOf hubar ht, map_one])
    have h2 : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
    have h4 : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units, h.card]
      have h5 : Even (2 ^ (2 * f)) :=
        (Nat.even_pow' (by have := h.one_le; omega)).mpr even_two
      exact Nat.Even.sub_odd Nat.one_le_two_pow h5 odd_one
    exact Odd.of_dvd_nat h4 (h1.trans h2)
  obtain ⟨g', hg'U, hg'⟩ := hy'
  have hy'eq : y' = hypProj h 1 1 (g' * t) := by rw [map_mul, hg', inv_mul_cancel_right]
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  obtain ⟨x, rfl⟩ := hΦ β
  set τ := (x : SemiGL (HypIndex 1 1) K).right with hτ
  have hfix : (x : SemiGL (HypIndex 1 1) K).left * glAut τ ((g' * t : hypSU h 1 1) :
      GL (HypIndex 1 1) K) * (x : SemiGL (HypIndex 1 1) K).left⁻¹ =
      ((g' * t : hypSU h 1 1) : GL (HypIndex 1 1) K) := by
    rw [hy'eq, semilinearAutHom_apply] at hβy'
    exact congrArg Subtype.val (hypProj_injective h h3 hβy')
  have htr := trace_mul_torus ht hg'U
  rw [hubar] at htr
  have htau : τ ((u : K) + 1 + (u : K)⁻¹) = (u : K) + 1 + (u : K)⁻¹ := by
    have h1 := congrArg (fun A : GL (HypIndex 1 1) K =>
      Matrix.trace (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hfix
    simp only [Units.val_mul] at h1
    rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      coe_glAut, trace_map_ringEquiv] at h1
    rw [← htr]
    exact h1
  have hτu : τ (u : K) = u ∨ τ (u : K) = (u : K)⁻¹ := by
    refine L2.eq_or_eq_inv_of_add_inv ((map_ne_zero τ).mpr u.ne_zero) u.ne_zero ?_
    rw [map_add, map_add, map_one, map_inv₀] at htau
    linear_combination htau
  have hτ2 : (τ ^ 2) (u : K) = u := by
    rw [sq, L2.ringAut_mul_apply]
    rcases hτu with e | e
    · rw [e, e]
    · rw [e, map_inv₀, e, inv_inv]
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hrX
    obtain ⟨hU, -, -, ⟨e, -⟩, -⟩ :=
      unitary_order_and_Sylow h (r := 1) (ε := 1) (le_refl 1) (le_refl 1)
    have h1 := Subgroup.card_subgroup_dvd_card (hypProjUnitriangular h 1 1)
    rw [← Nat.card_congr e.toEquiv, hU] at h1
    refine dvd_trans ?_ h1
    have := h.one_le
    exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have hτr : τ ^ r = 1 := by rw [hτ, ← galPart_apply h hq, ← map_pow, hβr, map_one]
  have hτfix : τ (u : K) = u := by
    obtain ⟨m, hm⟩ := hr.odd_of_ne_two hr2
    have h1 : τ = (τ ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = r + 1 by omega, pow_succ, hτr, one_mul]
    rw [h1]
    exact L2.pow_apply_eq hτ2 _
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
    rcases (Nat.dvd_prime hr).mp h3 with e | e
    · exact orderOf_eq_one_iff.mp e
    · exfalso
      rw [e] at h1
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
  exact eq_one_of_mem_inner ⟨r, hr, hβr, hβ1, hrX⟩ (semilinearAutHom_mem_inner h h3 hτ1)

theorem torusRigid_even (h : UnitaryFieldData 2 f K) (hf : Even f) :
    TorusRigid (unitaryPSU h 3) := by
  have : Finite K := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  exact (TorusRigid.of_at (isSylowTwoOf_hyp h) (torusRigidAt_hyp h hf)).of_mulEquiv
    (hypProjTransport h hR)

end BK10.U3

end CFSG.Quasithin.Vol2.Ch11.SecD
