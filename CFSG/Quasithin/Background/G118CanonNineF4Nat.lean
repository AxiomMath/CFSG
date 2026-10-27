module

public import CFSG.Quasithin.Background.SzG11TensorD
public import CFSG.Quasithin.Background.G118CanonNineF2TensorPts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F4Tensor

open F2Tensor Matrix

section SL2

variable {K : Type} [Field K]

theorem exists_sl_e0 {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0.symm
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl_mulVec_eq {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v = w := by
  obtain ⟨Av, hAv⟩ := exists_sl_e0 hv
  obtain ⟨Aw, hAw⟩ := exists_sl_e0 hw
  refine ⟨Aw * Av⁻¹, ?_⟩
  have h1 : (((Av⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v =
      ![1, 0] := by
    rw [← hAv, Matrix.mulVec_mulVec]
    have : (((Av⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        (Av : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [this, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hAw]

end SL2

section Restrict

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def restrictAlg {K : Type} [Field K] [Algebra (ZMod 2) K]
    (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) V) (B : Submodule (ZMod 2) V)
    (hB : ∀ k : K, ∀ b ∈ B, κ k b ∈ B) : K →ₐ[ZMod 2] Module.End (ZMod 2) ↥B where
  toFun k := (κ k).restrict (hB k)
  map_one' := by
    refine LinearMap.ext fun b => Subtype.ext ?_
    simp
  map_mul' := fun k l => by
    refine LinearMap.ext fun b => Subtype.ext ?_
    simp
  map_zero' := by
    refine LinearMap.ext fun b => Subtype.ext ?_
    simp
  map_add' := fun k l => by
    refine LinearMap.ext fun b => Subtype.ext ?_
    simp
  commutes' := fun r => by
    refine LinearMap.ext fun b => Subtype.ext ?_
    simp [Module.algebraMap_end_apply]

end Restrict

section Natural

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {H : Subgroup (GLV V)}
  {I : Submodule (ZMod 2) V}

theorem exists_moved_of_finrank_four (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) {B : Submodule (ZMod 2) V}
    (hB4 : Module.finrank (ZMod 2) B = 4) : ∃ h ∈ H, ∃ b ∈ B, h b ≠ b := by
  by_contra hcon
  push Not at hcon
  haveI : Module.Finite (ZMod 2) ↥B := Module.Finite.of_finite
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1
    (by omega : 0 < Module.finrank (ZMod 2) B)
  have hx0 : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
  have hinv : Invariant H (Submodule.span (ZMod 2) {(x : V)}) := by
    intro h hh u hu
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, hcon h hh x x.2]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  obtain ⟨k, hk⟩ := F2Tensor.four_dvd D hU hdim hinv
  rw [finrank_span_singleton hx0] at hk
  omega

theorem restrictHom_injective_B (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) (φH : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    {B : Submodule (ZMod 2) V} (hBH : Invariant H B) (hB4 : Module.finrank (ZMod 2) B = 4) :
    Function.Injective (restrictHom H B hBH) := by
  haveI : IsSimpleGroup ↥H := φH.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top (restrictHom H B hBH).ker with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff _).1 hbot
  · exfalso
    obtain ⟨h, hh, b, hb, hne⟩ := exists_moved_of_finrank_four D hU hdim hB4
    have hg : (⟨h, hh⟩ : ↥H) ∈ (restrictHom H B hBH).ker := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hne (restrictHom_eq_one_iff.1 (MonoidHom.mem_ker.1 hg) b hb)

theorem exists_natural_B (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) (hF : Nat.card D.F = 4)
    (φH : ↥H ≃* ↥(alternatingGroup (Fin 5))) {B : Submodule (ZMod 2) V} (hBH : Invariant H B)
    (hB4 : Module.finrank (ZMod 2) B = 4) (hκB : ∀ (f : D.F), ∀ b ∈ B, D.κ f b ∈ B) :
    ∃ (α : ↥H ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2))
      (ι : ↥B ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2)), ∀ (h : ↥H) (b : ↥B),
        ι (restrictHom H B hBH h b) =
          ((α h : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ ι b := by
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let eF : D.F ≃ₐ[ZMod 2] GaloisField 2 2 :=
    GaloisField.algEquivGaloisField 2 2 (by rw [hF]; norm_num)
  let κV : GaloisField 2 2 →ₐ[ZMod 2] Module.End (ZMod 2) V := D.κ.comp eF.symm.toAlgHom
  have hκV : ∀ k : GaloisField 2 2, ∀ b ∈ B, κV k b ∈ B := fun k b hb => hκB (eF.symm k) b hb
  let κB : GaloisField 2 2 →ₐ[ZMod 2] Module.End (ZMod 2) ↥B := restrictAlg κV B hκV
  refine SzG11S.Tensor.natural_module hK4 hB4 κB
    (SzG11S.Tensor.commutator_eq_top_of_alt_five φH) (SzG11S.Tensor.natCard_of_alt_five φH)
    (restrictHom H B hBH) (restrictHom_injective_B D hU hdim φH hBH hB4) ?_
  intro k g x
  refine Subtype.ext ?_
  have h1 := D.κ_comm (eF.symm k) (g : GLV V) g.2
  have h2 := congrArg (fun T : Module.End (ZMod 2) V => T (x : V)) h1
  exact h2

theorem exists_action_eq {α : ↥H ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2)}
    {B : Submodule (ZMod 2) V} {hBH : Invariant H B}
    {ι : ↥B ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2)}
    (hι : ∀ (h : ↥H) (b : ↥B), ι (restrictHom H B hBH h b) =
      ((α h : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ ι b)
    {b b' : ↥B} (hb : b ≠ 0) (hb' : b' ≠ 0) : ∃ h : ↥H, restrictHom H B hBH h b = b' := by
  obtain ⟨A, hA⟩ := exists_sl_mulVec_eq (fun h => hb (ι.map_eq_zero_iff.1 h))
    (fun h => hb' (ι.map_eq_zero_iff.1 h)) (v := ι b) (w := ι b')
  refine ⟨α.symm A, ι.injective ?_⟩
  rw [hι, MulEquiv.apply_symm_apply]
  exact hA

end Natural

end F4Tensor

end Canon

end G11

end CFSG.Quasithin
