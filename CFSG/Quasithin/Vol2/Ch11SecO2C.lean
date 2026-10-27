module

public import CFSG.Quasithin.Vol2.Ch11SecO2B
public import CFSG.Quasithin.Vol2.Ch11SecAKA15
public import CFSG.Quasithin.Vol2.Ch11SecO1D
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spMat spMat_leviSp_one spLevi_mem_perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (eq_map_psiSp_of_sylow inf_normalizer_eq_sp
  exists_eq_map_torus_sp)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {G : Type} [Group G]

theorem commutator_le_of_le_normalizer {V Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) : ⁅V, Y⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv y hy
  rw [commutatorElement_eq_inv (hY hy) ⟨v, hv⟩]
  exact V.inv_mem (Subtype.mem _)

end O2

open O2 in
theorem factSp4CartanFree_holds : FactSp4CartanFree := by
  intro G _ _ T L I n X hS hk hX
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, -, hg, -⟩ := exists_coord hS hk
  obtain ⟨c, hc⟩ := SecO1.exists_units_ne_one hn hK
  have hD := SecO1.isHall_autOn_cartan hS hX
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x, -, hDx⟩ := exists_eq_map_torus_sp hf g hD
  have hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G) := fun y hy =>
    hS.le_normalizer (hX.1 hy).1
  have hmem : psiSp π (g * x) (torusHom (fun _ => c)) ∈ autOn X (fsuV T I) := by
    rw [hDx]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyV, hyeq⟩ := SecA.mem_autOn_iff.mp hmem
  refine le_antisymm (commutator_le_of_le_normalizer hXV) (le_commutator_of_fix hy hyV ?_)
  intro v hv
  rw [← hyeq] at hv
  have h1 := congrArg f hv
  rw [psiSp_apply, hf.act4] at h1
  have hc' : (c : K) ≠ 1 := fun h => hc (Units.ext h)
  have hc'' : ((c⁻¹ : Kˣ) : K) ≠ 1 := fun h => hc (inv_eq_one.mp (Units.ext h))
  have h2 : mat 2 K (torusHom (fun _ => c)) *ᵥ (mat 2 K (g * x)⁻¹ *ᵥ f v) =
      mat 2 K (g * x)⁻¹ *ᵥ f v := by
    rw [← conj_mulVec_sp, h1]
  rw [mat_apply, coe_torusHom] at h2
  have h0 : mat 2 K (g * x)⁻¹ *ᵥ f v = 0 := by
    funext k
    rcases k with i | i <;> fin_cases i
    · exact SecO1.eq_zero_of_mul_eq hc' (by simpa [mulVec_diagonal] using congrFun h2 (.inl 0))
    · exact SecO1.eq_zero_of_mul_eq hc' (by simpa [mulVec_diagonal] using congrFun h2 (.inl 1))
    · exact SecO1.eq_zero_of_mul_eq hc'' (by simpa [mulVec_diagonal] using congrFun h2 (.inr 0))
    · exact SecO1.eq_zero_of_mul_eq hc'' (by simpa [mulVec_diagonal] using congrFun h2 (.inr 1))
  have h3 : f v = f 1 := by
    rw [← mat_mulVec_inv (g * x) (f v), h0, Matrix.mulVec_zero, hf.map_one]
  exact SecO1.IsCoord.injective_of_bot hf h3

open O2 in
theorem factSp4VL2_holds : FactSp4VL2 := by
  intro G _ _ T L I n V₂ hS hk hV₂
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, -, -, -, hV₂g, -⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨c, hc⟩ := SecO1.exists_units_ne_one hn hK
  let A : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩
  have hL₂V : LOf L V₂ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hS.le_normalizer)
  have hmem : psiSp π g (spLevi 1 A) ∈ autOn (LOf L V₂) (fsuV T I) := by
    rw [SecA.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₂), hV₂g V₂ hV₂, KA.gamma2_eq hf g]
    exact ⟨_, spLevi_mem_perfectCore hK4 1 A, rfl⟩
  obtain ⟨l, hl, hlV, hleq⟩ := SecA.mem_autOn_iff.mp hmem
  refine le_antisymm (commutator_le_of_le_normalizer hL₂V) (le_commutator_of_fix hl hlV ?_)
  intro v hv
  rw [← hleq] at hv
  have h1 := congrArg (fun w => mat 2 K g⁻¹ *ᵥ f w) hv
  rw [KA.act_levi1 hf g A v] at h1
  have hc' : (c : K) ≠ 1 := fun h => hc (Units.ext h)
  have hc'' : ((c⁻¹ : Kˣ) : K) ≠ 1 := fun h => hc (inv_eq_one.mp (Units.ext h))
  rw [show mat 2 K (spLevi 1 A) = spMat (spLevi 1 A) from rfl, spMat_leviSp_one,
    Matrix.SpecialLinearGroup.coe_inv] at h1
  have h0 : mat 2 K g⁻¹ *ᵥ f v = 0 := by
    funext k
    rcases k with i | i <;> fin_cases i
    · refine SecO1.eq_zero_of_mul_eq hc' ?_
      simpa [A, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.adjugate_fin_two] using congrFun h1 (.inl 0)
    · refine SecO1.eq_zero_of_mul_eq hc'' ?_
      simpa [A, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.adjugate_fin_two] using congrFun h1 (.inl 1)
    · refine SecO1.eq_zero_of_mul_eq hc'' ?_
      simpa [A, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.adjugate_fin_two] using congrFun h1 (.inr 0)
    · refine SecO1.eq_zero_of_mul_eq hc' ?_
      simpa [A, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.adjugate_fin_two] using congrFun h1 (.inr 1)
  have h3 : f v = f 1 := by
    rw [← mat_mulVec_inv g (f v), h0, Matrix.mulVec_zero, hf.map_one]
  exact SecO1.IsCoord.injective_of_bot hf h3

end CFSG.Quasithin.Vol2.Ch11.SecF
