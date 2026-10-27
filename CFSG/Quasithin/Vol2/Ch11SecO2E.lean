module

public import CFSG.Quasithin.Vol2.Ch11SecO2D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spMat spMat_leviSp_one spLevi_mem_perfectCore
  blkN blkN_coe blkIdx sigma2 spMat_inr_inl_of_mem_Q2_one)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {K : Type} [Field K]

noncomputable def swap2 [CharP K 2] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of, mul_zero, one_mul, zero_sub, CharTwo.neg_eq]⟩

theorem mulVec_spLevi_swap2 [CharP K 2] (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (spLevi 1 swap2) *ᵥ v = vec4 (v (.inl 1)) (v (.inl 0)) (v (.inr 1)) (v (.inr 0)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [show mat 2 K (spLevi 1 swap2) = spMat (spLevi 1 swap2) from rfl, spMat_leviSp_one,
    Matrix.SpecialLinearGroup.coe_inv]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [swap2, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.adjugate_fin_two, vec4, CharTwo.neg_eq]

theorem mulVec_of_conj_swap [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    {N N' : StatedSp 2 K} (hN : N ∈ pCoreOf 2 (perfectCore (Q2 K 0)))
    (hN' : N' ∈ pCoreOf 2 (perfectCore (Q2 K 0)))
    (h : N' = (spLevi 1 swap2)⁻¹ * N * spLevi 1 swap2) :
    ∃ s : K, ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K N *ᵥ v =
      vec4 (v (.inl 0) + s * v (.inr 1)) (v (.inl 1) + s * v (.inr 0)) (v (.inr 0))
        (v (.inr 1)) := by
  obtain ⟨a, b, c, hNv⟩ := mulVec_of_mem_pCoreOf hK4 hN
  obtain ⟨a', b', c', hN'v⟩ := mulVec_of_mem_pCoreOf hK4 hN'
  have hE2 : (spLevi 1 swap2 : StatedSp 2 K)⁻¹ = spLevi 1 swap2 := by
    rw [inv_eq_iff_mul_eq_one]
    apply mat_injective
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, map_mul, map_one, ← Matrix.mulVec_mulVec,
      mulVec_spLevi_swap2, mulVec_spLevi_swap2, Matrix.one_mulVec]
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]
  rw [hE2] at h
  have key : ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K N' *ᵥ v =
      mat 2 K (spLevi 1 swap2) *ᵥ (mat 2 K N *ᵥ (mat 2 K (spLevi 1 swap2) *ᵥ v)) := by
    intro v
    rw [h, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e := fun v => (key v).symm.trans (hN'v v)
  have e1 := congrFun (e (vec4 0 0 0 1)) (.inl 1)
  have e4 := congrFun (e (vec4 0 0 0 1)) (.inr 0)
  simp only [mulVec_spLevi_swap2, hNv, vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one] at e1 e4
  have hb : b = 0 := by linear_combination e1
  have ha : a = 0 := by linear_combination e4
  refine ⟨c, fun v => ?_⟩
  rw [hNv, ha, hb]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

theorem commute_of_mem_Q1 [Finite K] [CharP K 2] {M : StatedSp 2 K}
    (hM : M ∈ perfectCore (Q2 K 1)) {N : StatedSp 2 K} {s : K}
    (hN : ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K N *ᵥ v =
      vec4 (v (.inl 0) + s * v (.inr 1)) (v (.inl 1) + s * v (.inr 0)) (v (.inr 0))
        (v (.inr 1))) :
    M * N = N * M := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hMQ : M ∈ Q2 K 1 := perfectCore_le _ hM
  have hdet : (blkIdx (sigma2 1) (spMat M)).det = 1 := by
    rw [← blkN_coe 1 ⟨M, hM⟩]
    exact Matrix.SpecialLinearGroup.det_coe _
  rw [Matrix.det_fin_two] at hdet
  simp only [blkIdx, sigma2, Matrix.submatrix_apply, one_ne_zero, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have z00 := spMat_inr_inl_of_mem_Q2_one hMQ 0 0
  have z01 := spMat_inr_inl_of_mem_Q2_one hMQ 0 1
  have z10 := spMat_inr_inl_of_mem_Q2_one hMQ 1 0
  have z11 := spMat_inr_inl_of_mem_Q2_one hMQ 1 1
  have hB : ∀ x y : Fin 2 ⊕ Fin 2 → K, Matrix.toBilin' (spJ K) (mat 2 K M *ᵥ x)
      (mat 2 K M *ᵥ y) = Matrix.toBilin' (spJ K) x y := spB_mat M
  have hcol : ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K M *ᵥ v =
      vec4 (spMat M (.inl 0) (.inl 0) * v (.inl 0) + spMat M (.inl 0) (.inl 1) * v (.inl 1) +
          spMat M (.inl 0) (.inr 0) * v (.inr 0) + spMat M (.inl 0) (.inr 1) * v (.inr 1))
        (spMat M (.inl 1) (.inl 0) * v (.inl 0) + spMat M (.inl 1) (.inl 1) * v (.inl 1) +
          spMat M (.inl 1) (.inr 0) * v (.inr 0) + spMat M (.inl 1) (.inr 1) * v (.inr 1))
        (spMat M (.inr 0) (.inr 0) * v (.inr 0) + spMat M (.inr 0) (.inr 1) * v (.inr 1))
        (spMat M (.inr 1) (.inr 0) * v (.inr 0) + spMat M (.inr 1) (.inr 1) * v (.inr 1)) := by
    intro v
    refine vec4_eq ?_ ?_ ?_ ?_ <;>
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, vec4,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        show mat 2 K M = spMat M from rfl, z00, z01, z10, z11] <;> ring
  have k1 := hB (vec4 1 0 0 0) (vec4 0 0 1 0)
  have k2 := hB (vec4 1 0 0 0) (vec4 0 0 0 1)
  have k3 := hB (vec4 0 1 0 0) (vec4 0 0 1 0)
  have k4 := hB (vec4 0 1 0 0) (vec4 0 0 0 1)
  rw [hcol, hcol, toBilin'_spJ_apply, toBilin'_spJ_apply] at k1 k2 k3 k4
  simp only [Fin.sum_univ_two, vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one] at k1 k2 k3 k4
  set a00 := spMat M (.inl 0) (.inl 0)
  set a01 := spMat M (.inl 0) (.inl 1)
  set a10 := spMat M (.inl 1) (.inl 0)
  set a11 := spMat M (.inl 1) (.inl 1)
  set d00 := spMat M (.inr 0) (.inr 0)
  set d01 := spMat M (.inr 0) (.inr 1)
  set d10 := spMat M (.inr 1) (.inr 0)
  set d11 := spMat M (.inr 1) (.inr 1)
  have hd00 : d00 = a11 := by linear_combination a11 * k1 - a10 * k3 - d00 * hdet
  have hd10 : d10 = a01 := by linear_combination a00 * k3 - a01 * k1 - d10 * hdet - a01 * h2
  have hd01 : d01 = a10 := by linear_combination a11 * k2 - a10 * k4 - d01 * hdet - a10 * h2
  have hd11 : d11 = a00 := by linear_combination a00 * k4 - a01 * k2 - d11 * hdet
  apply mat_injective
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hN, hN, hcol, hcol]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      hd00, hd01, hd10, hd11] <;> ring

end O2

open O2 in
theorem factSp4L2Rad_holds : FactSp4L2Rad := by
  intro G _ _ T L I n V₁ V₂ hS hk hV₁ hV₂ P hP hPN hPP
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, hV₂g, -⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hψ := psiSp_injective hf g
  have hL₂V : LOf L V₂ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hS.le_normalizer)
  have hA₂ : autOn (LOf L V₂) (fsuV T I) = (perfectCore (Q2 K 1)).map (psiSp π g) := by
    rw [SecA.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₂), hV₂g V₂ hV₂, KA.gamma2_eq hf g]
  have hmem : psiSp π g (spLevi 1 swap2) ∈ autOn (LOf L V₂) (fsuV T I) := by
    rw [hA₂]
    exact ⟨_, spLevi_mem_perfectCore hK4 1 swap2, rfl⟩
  obtain ⟨l₀, hl₀, hl₀V, hl₀eq⟩ := SecA.mem_autOn_iff.mp hmem
  have hq : ∀ p (hp : p ∈ P), ∃ (N : StatedSp 2 K) (s : K), SecA.conjV (fsuV T I) p
      (r1_le hS hV₁ (hP hp)).1.1.1 = psiSp π g N ∧ ∀ v : Fin 2 ⊕ Fin 2 → K,
        mat 2 K N *ᵥ v = vec4 (v (.inl 0) + s * v (.inr 1)) (v (.inl 1) + s * v (.inr 0))
          (v (.inr 0)) (v (.inr 1)) := by
    intro p hp
    obtain ⟨N, hN, hpN⟩ := exists_core_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hP hp)
    have hp' : l₀⁻¹ * p * l₀⁻¹⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPN ((LOf L V₂).inv_mem hl₀)) p).mp hp
    rw [inv_inv] at hp'
    obtain ⟨N', hN', hpN'⟩ := exists_core_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hP hp')
    have hconj : psiSp π g N' = psiSp π g ((spLevi 1 swap2)⁻¹ * N * spLevi 1 swap2) := by
      rw [map_mul, map_mul, map_inv, ← hpN, hl₀eq, ← hpN', ← SecA.conjV_inv,
        ← SecA.conjV_mul, ← SecA.conjV_mul]
    obtain ⟨s, hs⟩ := mulVec_of_conj_swap hK4 hN hN' (hψ hconj)
    exact ⟨N, s, hpN, hs⟩
  have hcent : ⁅P, LOf L V₂⁆ ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [Subgroup.commutator_le]
    intro p hp l hl
    obtain ⟨N, s, hpN, hNv⟩ := hq p hp
    have hlV := hL₂V hl
    have hlmem : SecA.conjV (fsuV T I) l hlV ∈ autOn (LOf L V₂) (fsuV T I) :=
      SecA.conjV_mem_autOn hl hlV
    rw [hA₂] at hlmem
    obtain ⟨M, hM, hMl⟩ := hlmem
    have hcomm := commute_of_mem_Q1 hM hNv
    have hpV := (r1_le hS hV₁ (hP hp)).1.1.1
    have hab : SecA.conjV (fsuV T I) p hpV * SecA.conjV (fsuV T I) l hlV =
        SecA.conjV (fsuV T I) l hlV * SecA.conjV (fsuV T I) p hpV := by
      rw [hpN, ← hMl, ← map_mul, ← map_mul, hcomm]
    have hpl : ∀ w : ↥(fsuV T I),
        p * (l * (w : G) * l⁻¹) * p⁻¹ = l * (p * (w : G) * p⁻¹) * l⁻¹ := by
      intro w
      have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ w : ↥(fsuV T I)) : G)) hab
      simpa only [MulAut.mul_apply, SecA.conjV_apply_coe] using h1
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : l⁻¹ * v * l⁻¹⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) v).mp hv
    have h2 : p⁻¹ * (l⁻¹ * v * l⁻¹⁻¹) * p⁻¹⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpV) _).mp h1
    have hw : p⁻¹ * l⁻¹ * v * l * p ∈ fsuV T I := by simpa only [inv_inv, mul_assoc] using h2
    have h3 := hpl ⟨_, hw⟩
    have h4 : l * (p * (p⁻¹ * l⁻¹ * v * l * p) * p⁻¹) * l⁻¹ = v := by group
    rw [h4] at h3
    calc v * (p * l * p⁻¹ * l⁻¹)
        = p * (l * (p⁻¹ * l⁻¹ * v * l * p) * l⁻¹) * p⁻¹ * (p * l * p⁻¹ * l⁻¹) := by rw [h3]
      _ = p * l * p⁻¹ * l⁻¹ * v := by group
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv p hp
  have hpc : p ∈ Subgroup.centralizer (fsuV T I : Set G) := hcent (by rw [hPP]; exact hp)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_centralizer_iff.mp hpc v hv

end CFSG.Quasithin.Vol2.Ch11.SecF
