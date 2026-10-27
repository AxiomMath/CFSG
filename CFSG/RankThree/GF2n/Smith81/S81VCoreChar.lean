module

public import CFSG.RankThree.GF2n.Smith81.S81VCoreFix
public import CFSG.RankThree.GF2n.Smith81.S81VPlucker
public import CFSG.RankThree.GF2n.Smith81.S81VModelChar
public import CFSG.RankThree.GF2n.Smith81.S81VAmbPts

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.RankThree.GF2n.Smith81.A5Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {b : Fin 3 → Fin 6 → F}
  {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

private theorem conj_mem_PtStab_co3 {g u : SUid σ 6} (hg : g ∈ Pstab σ (W₀ F))
    (hu : u ∈ PtStab σ (W₀ F)) : g⁻¹ * u * g ∈ PtStab σ (W₀ F) := by
  have hg' : (W₀ F).map (gLin g) = W₀ F := hg
  rw [mem_ptStab]
  intro w hw
  have hgw : g • w ∈ W₀ F := by
    have h1 : gLin g w ∈ (W₀ F).map (gLin g) := Submodule.mem_map_of_mem hw
    rw [hg'] at h1
    exact h1
  rw [mul_smul, mul_smul, hu (g • w) hgw, inv_smul_smul]

private theorem fixU_map_le_co3 {A : SUid σ 6 →* (V ≃ₗ[K] V)} {g : SUid σ 6} (hg : g ∈ Pstab σ (W₀ F)) :
    (fixU σ A).map (A g : V →ₗ[K] V) ≤ fixU σ A := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_fixU]
  intro u hu
  have hc : g⁻¹ * u * g ∈ PtStab σ (W₀ F) := conj_mem_PtStab_co3 hg hu
  have hfix : A (g⁻¹ * u * g) v = v := mem_fixU.1 hv _ hc
  have key : A u * A g = A g * A (g⁻¹ * u * g) := by
    rw [← map_mul, ← map_mul]
    exact congrArg A (by group)
  have h2 : A u (A g v) = A g (A (g⁻¹ * u * g) v) := by
    rw [← LinearEquiv.mul_apply (A u) (A g), ← LinearEquiv.mul_apply (A g) (A (g⁻¹ * u * g)), key]
  show A u (A g v) = A g v
  rw [h2, hfix]

theorem exists_chiV (A : SUid σ 6 →* (V ≃ₗ[K] V)) (hline : finrank K (fixU σ A) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ fixU σ A) (hne : v₀ ≠ 0) :
    ∃ χ : ↥(Pstab σ (W₀ F)) →* Kˣ, ∀ g : ↥(Pstab σ (W₀ F)), A (g : SUid σ 6) v₀ = ((χ g : Kˣ) : K) • v₀ := by
  have hmul : ∀ x ∈ fixU σ A, ∃ c : K, c • v₀ = x := by
    intro x hx
    have hnz : (⟨v₀, hv₀⟩ : ↥(fixU σ A)) ≠ 0 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hnz ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hmem : ∀ g : ↥(Pstab σ (W₀ F)), ∃ c : K, c • v₀ = A (g : SUid σ 6) v₀ :=
    fun g => hmul _ (fixU_map_le_co3 (A := A) g.2 (Submodule.mem_map_of_mem hv₀))
  choose c hc using hmem
  have hcne : ∀ g : ↥(Pstab σ (W₀ F)), c g ≠ 0 := by
    intro g h0
    apply hne
    apply (A (g : SUid σ 6)).injective
    rw [map_zero, ← hc g, h0, zero_smul]
  have hmul' : ∀ g h : ↥(Pstab σ (W₀ F)), c (g * h) = c g * c h := by
    intro g h
    apply smul_left_injective K hne
    show c (g * h) • v₀ = (c g * c h) • v₀
    rw [hc (g * h), Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, ← hc h, map_smul, ← hc g,
      smul_smul, mul_comm]
  refine ⟨{ toFun := fun g => Units.mk0 (c g) (hcne g)
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · apply Units.ext
    show c 1 = 1
    apply smul_left_injective K hne
    show c 1 • v₀ = (1 : K) • v₀
    rw [hc 1, one_smul]
    simp
  · intro g h
    apply Units.ext
    show c (g * h) = c g * c h
    exact hmul' g h
  · intro g
    exact (hc g).symm

variable (hσ : IsUnitaryInvolution σ) (hf : Frame σ e3uT0Vec b) (e₀ e' : K ≃+* Fσ σ)

include hσ hf

private theorem blkA_det_mul_P0 (g h : ↥(Pstab σ (W₀ F))) :
    (blkA hσ.invol hf ((g * h : ↥(Pstab σ (W₀ F))) : SUid σ 6)).det =
      (blkA hσ.invol hf (g : SUid σ 6)).det * (blkA hσ.invol hf (h : SUid σ 6)).det := by
  rw [Subgroup.coe_mul, blkA_mul hσ.invol hf g.2 h.2, Matrix.det_mul]

@[expose] noncomputable def chiM : ↥(Pstab σ (W₀ F)) →* Kˣ where
  toFun g := Units.mk0 (e'.symm ⟨(blkA hσ.invol hf g).det, blkA_det_fixed hσ.invol hf g.2⟩) (by
    intro h0
    apply blkA_det_ne hσ.invol hf g.2
    have h2 := congrArg e' h0
    rw [map_zero, RingEquiv.apply_symm_apply] at h2
    exact congrArg Subtype.val h2)
  map_one' := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_one]
    rw [← map_one e'.symm]
    congr 1
    apply Subtype.ext
    simp [blkA_one hσ.invol hf]
  map_mul' g h := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [← map_mul e'.symm]
    congr 1
    apply Subtype.ext
    exact blkA_det_mul_P0 hσ hf g h

private theorem chiM_val (g : ↥(Pstab σ (W₀ F))) :
    ((chiM hσ hf e' g : Kˣ) : K) = e'.symm ⟨(blkA hσ.invol hf (g : SUid σ 6)).det, blkA_det_fixed hσ.invol hf g.2⟩ :=
  rfl

theorem chiM_eigen (g : ↥(Pstab σ (W₀ F))) :
    e3uWact σ e' (g : SUid σ 6) (e3uP0 σ e') = ((chiM hσ hf e' g : Kˣ) : K) • e3uP0 σ e' := by
  have hdet : ((e' ((chiM hσ hf e' g : Kˣ) : K) : Fσ σ) : F) = (blkA hσ.invol hf (g : SUid σ 6)).det := by
    rw [chiM_val, RingEquiv.apply_symm_apply]
  apply Subtype.ext
  show rho F ((g : SUid σ 6) : GL (Fin 6) F) (pt0 F) =
    ((e' ((chiM hσ hf e' g : Kˣ) : K) : Fσ σ) : F) • pt0 F
  rw [rho_pt0_of_mem_Pstab hσ.invol hf g.2, hdet]

theorem chiM_triv {g : ↥(Pstab σ (W₀ F))} (hg : (g : SUid σ 6) ∈ PtStab σ (W₀ F)) :
    chiM hσ hf e' g = 1 := by
  obtain ⟨H, hH⟩ := exists_uK_of_mem_PtStab hσ.invol hf (e₀ := e') hg
  have hblk : blkA hσ.invol hf (g : SUid σ 6) = 1 := by
    rw [hH]
    exact blkA_uK hσ.invol hf e' H
  apply Units.ext
  rw [chiM_val, Units.val_one, ← map_one e'.symm]
  congr 1
  apply Subtype.ext
  simp [hblk]

theorem chiM_dKhom (c : Kˣ) :
    ((chiM hσ hf e' (dKhom hσ.invol hf e₀ c) : Kˣ) : K) = e'.symm (e₀ (c : K)) := by
  refine (chiM_val hσ hf e' (dKhom hσ.invol hf e₀ c)).trans (congrArg e'.symm ?_)
  apply Subtype.ext
  show (blkA hσ.invol hf (dK hσ.invol hf e₀ c)).det = ((e₀ (c : K) : Fσ σ) : F)
  rw [blkA_dK, dmat_det]

theorem chi_eq_of_torus [Fintype K] [CharP K 2] (χ χ' : ↥(Pstab σ (W₀ F)) →* Kˣ)
    (h0 : ∀ g : ↥(Pstab σ (W₀ F)), (g : SUid σ 6) ∈ PtStab σ (W₀ F) → χ g = 1)
    (h0' : ∀ g : ↥(Pstab σ (W₀ F)), (g : SUid σ 6) ∈ PtStab σ (W₀ F) → χ' g = 1)
    (ht : ∀ c : Kˣ, χ (dKhom hσ.invol hf e₀ c) = χ' (dKhom hσ.invol hf e₀ c)) : χ = χ' := by
  refine MonoidHom.ext fun g => ?_
  exact (levi_char hσ.invol hf e₀ χ h0 g).trans
    ((ht _).trans (levi_char hσ.invol hf e₀ χ' h0' g).symm)

theorem hhom_U (A : SUid σ 6 →* (V ≃ₗ[K] V)) {v₀ : V} (χV : ↥(Pstab σ (W₀ F)) →* Kˣ)
    (hχV : ∀ g : ↥(Pstab σ (W₀ F)), A (g : SUid σ 6) v₀ = ((χV g : Kˣ) : K) • v₀)
    (heq : χV = chiM hσ hf e') (g g' : SUid σ 6) (hgg : ptU g = ptU g') :
    ∃ c : K, c ≠ 0 ∧ e3uWact σ e' g (e3uP0 σ e') = c • e3uWact σ e' g' (e3uP0 σ e') ∧
      A g v₀ = c • A g' v₀ := by
  have hh : g'⁻¹ * g ∈ Pstab σ (W₀ F) := (ptU_eq_iff g g').1 hgg
  have hA : A (g'⁻¹ * g) v₀ = ((χV ⟨g'⁻¹ * g, hh⟩ : Kˣ) : K) • v₀ := hχV ⟨g'⁻¹ * g, hh⟩
  have hE : e3uWact σ e' (g'⁻¹ * g) (e3uP0 σ e') =
      ((chiM hσ hf e' ⟨g'⁻¹ * g, hh⟩ : Kˣ) : K) • e3uP0 σ e' :=
    chiM_eigen hσ hf e' ⟨g'⁻¹ * g, hh⟩
  have hchi : ((χV ⟨g'⁻¹ * g, hh⟩ : Kˣ) : K) = ((chiM hσ hf e' ⟨g'⁻¹ * g, hh⟩ : Kˣ) : K) := by
    rw [heq]
  refine ⟨((χV ⟨g'⁻¹ * g, hh⟩ : Kˣ) : K), Units.ne_zero _, ?_, ?_⟩
  · have h1 : e3uWact σ e' g (e3uP0 σ e') =
        e3uWact σ e' g' (e3uWact σ e' (g'⁻¹ * g) (e3uP0 σ e')) := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [h1, hE, map_smul, hchi]
  · have h2 : A g v₀ = A g' (A (g'⁻¹ * g) v₀) := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [h2, hA, map_smul]

end CFSG.RankThree.GF2n.Smith81.S81V
