module

public import CFSG.Quasithin.Vol2.Ch11SecO2C
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGI

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spMat spMat_lam spLevi_mem_perfectCore blkQ
  blkQ_apply blkIdx sigma2 spMat_inl_zero_eq_one_of_perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (mem_pCoreOf_N_iff gammaW_pre_eq)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {K : Type} [Field K]

theorem mulVec_of_mem_pCoreOf [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    {N : StatedSp 2 K} (hN : N ∈ pCoreOf 2 (perfectCore (Q2 K 0))) :
    ∃ a b c : K, ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K N *ᵥ v =
      vec4 (v (.inl 0) + a * v (.inl 1) + b * v (.inr 0) + c * v (.inr 1))
        (v (.inl 1) + c * v (.inr 0)) (v (.inr 0)) (v (.inr 1) + a * v (.inr 0)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hNc : N ∈ perfectCore (Q2 K 0) := Subgroup.map_subtype_le _ hN
  have hNQ : N ∈ Q2 K 0 := perfectCore_le _ hNc
  have hblk : blkIdx (sigma2 0) (spMat N) = 1 := by
    rw [← blkQ_apply 0 ⟨N, hNQ⟩]
    exact (mem_pCoreOf_N_iff hK4 0 hNc).mp hN
  have e00 : mat 2 K N (.inl 0) (.inl 0) = 1 := spMat_inl_zero_eq_one_of_perfectCore hNc
  obtain ⟨c1, c2, r1, r2, c3⟩ := SecA.C11P9B.shape_of_mem_Q0 hNQ
  have hb : ∀ i j : Fin 2,
      mat 2 K N (sigma2 0 i) (sigma2 0 j) = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => congrFun (congrFun hblk i) j
  have b11 : mat 2 K N (.inl 1) (.inl 1) = 1 := by simpa [sigma2] using hb 0 0
  have b12 : mat 2 K N (.inl 1) (.inr 1) = 0 := by simpa [sigma2] using hb 0 1
  have b21 : mat 2 K N (.inr 1) (.inl 1) = 0 := by simpa [sigma2] using hb 1 0
  have b22 : mat 2 K N (.inr 1) (.inr 1) = 1 := by simpa [sigma2] using hb 1 1
  set a := mat 2 K N (.inl 0) (.inl 1) with ha
  set b := mat 2 K N (.inl 0) (.inr 0) with hb
  set c := mat 2 K N (.inl 0) (.inr 1) with hc
  set d := mat 2 K N (.inl 1) (.inr 0) with hd
  set e := mat 2 K N (.inr 0) (.inr 0) with he
  set h := mat 2 K N (.inr 1) (.inr 0) with hh
  have hmv : ∀ v : Fin 2 ⊕ Fin 2 → K, mat 2 K N *ᵥ v =
      vec4 (v (.inl 0) + a * v (.inl 1) + b * v (.inr 0) + c * v (.inr 1))
        (v (.inl 1) + d * v (.inr 0)) (e * v (.inr 0)) (v (.inr 1) + h * v (.inr 0)) := by
    intro v
    refine vec4_eq ?_ ?_ ?_ ?_ <;>
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, vec4,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        e00, c1, c2, c3, r1, r2, b11, b12, b21, b22] <;> ring
  have hB : ∀ x y : Fin 2 ⊕ Fin 2 → K, Matrix.toBilin' (spJ K) (mat 2 K N *ᵥ x)
      (mat 2 K N *ᵥ y) = Matrix.toBilin' (spJ K) x y := spB_mat N
  have k1 := hB (vec4 1 0 0 0) (vec4 0 0 1 0)
  have k2 := hB (vec4 0 1 0 0) (vec4 0 0 1 0)
  have k3 := hB (vec4 0 0 0 1) (vec4 0 0 1 0)
  rw [hmv, hmv, toBilin'_spJ_apply, toBilin'_spJ_apply] at k1 k2 k3
  simp only [Fin.sum_univ_two, vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one] at k1 k2 k3
  have he1 : e = 1 := by linear_combination k1
  have hh1 : h = a := by linear_combination k2 - a * he1 - a * h2
  have hd1 : d = c := by linear_combination -k3 + c * he1
  refine ⟨a, b, c, fun v => ?_⟩
  rw [hmv, he1, hh1, hd1, one_mul]

theorem exists_sl2_row [CharP K 2] {a c : K} (h : a ≠ 0 ∨ c ≠ 0) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) K,
      (B : Matrix (Fin 2) (Fin 2) K) 1 0 = a ∧ (B : Matrix (Fin 2) (Fin 2) K) 1 1 = c := by
  by_cases hc : c = 0
  · have ha : a ≠ 0 := h.resolve_right (not_not.mpr hc)
    refine ⟨⟨!![0, a⁻¹; a, 0], ?_⟩, rfl, by simp [hc]⟩
    rw [Matrix.det_fin_two_of, zero_mul, zero_sub, inv_mul_cancel₀ ha, CharTwo.neg_eq]
  · exact ⟨⟨!![c⁻¹, 0; a, c], by rw [Matrix.det_fin_two_of, zero_mul, sub_zero,
      inv_mul_cancel₀ hc]⟩, rfl, rfl⟩

end O2

open O2 in
theorem factSp4RadLine_holds : FactSp4RadLine := by
  intro G _ _ T L I n V₁ V₂ V₃ hS hk hV₁ hV₂ hV₃ P hP hcomm hne
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, hV₂g, hV₃g⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hinj := SecO1.IsCoord.injective_of_bot hf
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨p, hp, u, hu, hpu⟩ : ∃ p ∈ P, ∃ u ∈ V₃, p * u ≠ u * p := by
    by_contra hall
    push Not at hall
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu p hp
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hall p hp u hu).symm
  have hpV := (r1_le hS hV₁ (hP hp)).1.1.1
  obtain ⟨N, hN, hpN⟩ := exists_core_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hP hp)
  obtain ⟨a, b, c, hNv⟩ := mulVec_of_mem_pCoreOf hK4 hN
  have hact : ∀ w : ↥(fsuV T I), mat 2 K g⁻¹ *ᵥ f (SecA.conjV (fsuV T I) p hpV w) =
      mat 2 K N *ᵥ (mat 2 K g⁻¹ *ᵥ f w) := fun w => by
    rw [hpN, psiSp_apply, hf.act4, conj_mulVec_sp]
  have huV : u ∈ fsuV T I := SecA.IsVi.le_fsuV hV₃ hu
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h0
    push Not at h0
    apply hpu
    have hu2 : (mat 2 K g⁻¹ *ᵥ f ⟨u, huV⟩) (.inr 0) = 0 :=
      (mem_iff_of_eq (hV₃g V₃ hV₃) ⟨u, huV⟩).mp hu
    have hfix : SecA.conjV (fsuV T I) p hpV ⟨u, huV⟩ = ⟨u, huV⟩ := by
      apply hinj
      have h1 := hact ⟨u, huV⟩
      rw [hNv, h0.1, h0.2, hu2] at h1
      have h3 : mat 2 K g⁻¹ *ᵥ f (SecA.conjV (fsuV T I) p hpV ⟨u, huV⟩) =
          mat 2 K g⁻¹ *ᵥ f ⟨u, huV⟩ := by
        rw [h1]
        refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4, hu2]
      have h4 := congrArg (fun x => mat 2 K g *ᵥ x) h3
      simpa only [mat_mulVec_inv] using h4
    have h5 := congrArg Subtype.val hfix
    rw [SecA.conjV_apply_coe] at h5
    calc p * u = p * u * p⁻¹ * p := by group
      _ = u * p := by rw [h5]
  set W₀ : (Fin 2 ⊕ Fin 2 → K) → Prop := fun x =>
    x (.inr 0) = 0 ∧ a * x (.inl 1) + c * x (.inr 1) = 0 with hW₀
  have hK1 : ∀ w : ↥(fsuV T I), SecA.conjV (fsuV T I) p hpV w = w →
      W₀ (mat 2 K g⁻¹ *ᵥ f w) := by
    intro w hw
    have h1 := hact w
    rw [hw, hNv] at h1
    have e0 := congrFun h1 (.inl 0)
    have e1 := congrFun h1 (.inl 1)
    have e3 := congrFun h1 (.inr 1)
    simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one] at e0 e1 e3
    have hx2 : (mat 2 K g⁻¹ *ᵥ f w) (.inr 0) = 0 := by
      rcases hac with ha | hc
      · exact (mul_eq_zero.mp (by linear_combination -e3 : a * _ = 0)).resolve_left ha
      · exact (mul_eq_zero.mp (by linear_combination -e1 : c * _ = 0)).resolve_left hc
    refine ⟨hx2, ?_⟩
    rw [hx2] at e0
    linear_combination -e0
  have hK2 : ∀ w : ↥(fsuV T I), W₀ (mat 2 K g⁻¹ *ᵥ f w) →
      ∃ v : ↥(fsuV T I), SecA.conjV (fsuV T I) p hpV v * v⁻¹ = w := by
    intro w ⟨hy2, hy⟩
    set y := mat 2 K g⁻¹ *ᵥ f w with hydef
    obtain ⟨x, hx⟩ : ∃ x : Fin 2 ⊕ Fin 2 → K, mat 2 K N *ᵥ x - x = y := by
      rcases eq_or_ne a 0 with ha | ha
      · have hc : c ≠ 0 := hac.resolve_left (not_not.mpr ha)
        have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
        have hy3 : y (.inr 1) = 0 := by
          rw [ha, zero_mul, zero_add] at hy
          exact (mul_eq_zero.mp hy).resolve_left hc
        refine ⟨vec4 0 0 (y (.inl 1) * c⁻¹) ((y (.inl 0) - b * (y (.inl 1) * c⁻¹)) * c⁻¹), ?_⟩
        rw [hNv]
        refine vec4_eq ?_ ?_ ?_ ?_ <;>
          simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
            Matrix.cons_val_one, Pi.sub_apply]
        · linear_combination (y (.inl 0) - b * (y (.inl 1) * c⁻¹)) * hci
        · linear_combination y (.inl 1) * hci
        · linear_combination -hy2
        · linear_combination (y (.inl 1) * c⁻¹) * ha - hy3
      · have hai : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
        refine ⟨vec4 0 ((y (.inl 0) - b * (y (.inr 1) * a⁻¹)) * a⁻¹) (y (.inr 1) * a⁻¹) 0, ?_⟩
        rw [hNv]
        refine vec4_eq ?_ ?_ ?_ ?_ <;>
          simp only [vec4, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
            Matrix.cons_val_one, Pi.sub_apply]
        · linear_combination (y (.inl 0) - b * (y (.inr 1) * a⁻¹)) * hai
        · linear_combination a⁻¹ * hy - y (.inl 1) * hai - y (.inl 1) * h2
        · linear_combination -hy2
        · linear_combination y (.inr 1) * hai
    obtain ⟨v, hv⟩ := hf.surj (mat 2 K g *ᵥ x)
    refine ⟨v, hinj ?_⟩
    rw [hf.map_mul_inv]
    have h1 := hact v
    rw [hv, mat_inv_mulVec] at h1
    have h3 : f (SecA.conjV (fsuV T I) p hpV v) = mat 2 K g *ᵥ (mat 2 K N *ᵥ x) := by
      rw [← h1, mat_mulVec_inv]
    rw [h3, hv, ← Matrix.mulVec_sub, hx, hydef, mat_mulVec_inv]
  obtain ⟨B₀, hB₀1, hB₀2⟩ := exists_sl2_row hac
  have hmemL : psiSp π g (spLevi 0 B₀) ∈ autOn (LOf L V₁) (fsuV T I) := by
    rw [SecA.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁), hV₁g V₁ hV₁]
    change _ ∈ SecS.gammaW _ _
    rw [gammaW_pre_eq hf g 0 _ flag_one_eq]
    exact ⟨_, spLevi_mem_perfectCore hK4 0 B₀, rfl⟩
  obtain ⟨l, hl, hlV, hleq⟩ := SecA.mem_autOn_iff.mp hmemL
  have hS₀ : ∀ v : ↥(fsuV T I), (v : G) ∈ conjSubgroup V₂ l ↔ W₀ (mat 2 K g⁻¹ *ᵥ f v) := by
    intro v
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have e1 : l * (v : G) * l⁻¹ = ((SecA.conjV (fsuV T I) l hlV v : ↥(fsuV T I)) : G) := by
      rw [SecA.conjV_apply_coe]
    rw [e1, mem_iff_of_eq (hV₂g V₂ hV₂), ← hleq, psiSp_apply, hf.act4, conj_mulVec_sp,
      show mat 2 K (spLevi 0 B₀) = spMat (spLevi 0 B₀) from rfl, spMat_lam, mem_spPlane]
    have r0 : (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
        (B₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ (mat 2 K g⁻¹ *ᵥ f v)) (.inr 0) =
        (mat 2 K g⁻¹ *ᵥ f v) (.inr 0) := by
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pairMat,
        Matrix.one_apply]
    have r1 : (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
        (B₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ (mat 2 K g⁻¹ *ᵥ f v)) (.inr 1) =
        a * (mat 2 K g⁻¹ *ᵥ f v) (.inl 1) + c * (mat 2 K g⁻¹ *ᵥ f v) (.inr 1) := by
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pairMat,
        hB₀1, hB₀2]
    rw [r0, r1]
  have hSV : conjSubgroup V₂ l ≤ fsuV T I := by
    intro x hx
    have h1 := (CFSG.Quasithin.mem_conjSubgroup_iff.mp hx)
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) _).mp
      (SecA.IsVi.le_fsuV hV₂ h1)
    simpa [mul_assoc] using h3
  have hA : conjSubgroup V₂ l ≤ ⁅fsuV T I, P⁆ := by
    intro w hw
    obtain ⟨v, hv⟩ := hK2 ⟨w, hSV hw⟩ ((hS₀ ⟨w, hSV hw⟩).mp hw)
    have h1 := SecB.K7.conjV_comm_mem hp hpV v
    rw [hv] at h1
    exact h1
  have hB : ⁅fsuV T I, P⁆ ≤ fsuV T I ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf (commutator_le_of_le_normalizer fun x hx => (r1_le hS hV₁ (hP hx)).1.1.1) hcomm
  have hC : fsuV T I ⊓ Subgroup.centralizer (P : Set G) ≤ conjSubgroup V₂ l := by
    rintro v ⟨hvV, hvP⟩
    refine (hS₀ ⟨v, hvV⟩).mpr (hK1 ⟨v, hvV⟩ (Subtype.ext ?_))
    rw [SecA.conjV_apply_coe, Subgroup.mem_centralizer_iff.mp hvP p hp, mul_inv_cancel_right]
  exact ⟨l, hl, le_antisymm hC (hA.trans hB), le_antisymm (hB.trans hC) hA⟩

end CFSG.Quasithin.Vol2.Ch11.SecF
