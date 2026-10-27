module

public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Vol2.Ch11SecEFacts
public import CFSG.ClassicalGroups.Alternating.Transvections

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.ClassicalGroups.Alternating
open Matrix

theorem exists_apply_eq_of_linModel {D : FFModel} {K M : Type} [Field K] [AddCommGroup M]
    [Module K M] (LM : LinModel D K M)
    (hΓ : ∀ x y : M, x ≠ 0 → y ≠ 0 → ∃ γ : D.Gam, LM.lin γ x = y)
    {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) (u w : W) (hu : u ≠ 1) (hw : w ≠ 1) :
    ∃ g ∈ H, g u = w := by
  obtain ⟨f, hmul, hker, -, hact⟩ := exists_coord LM h
  have hk : ∀ v : W, f v = 0 ↔ v = 1 := fun v => (hker v trivial).trans Subgroup.mem_bot
  obtain ⟨γ, hγ⟩ := hΓ (f u) (f w) (fun h0 => hu ((hk u).mp h0)) (fun h0 => hw ((hk w).mp h0))
  refine ⟨(π γ : MulAut W), (π γ).2, ?_⟩
  have hinj : ∀ a b : W, f a = f b → a = b := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 0 := by
      have := hmul (a * b⁻¹) trivial b trivial
      rw [inv_mul_cancel_right, hab] at this
      exact add_eq_right.mp this.symm
    exact mul_inv_eq_one.mp ((hk _).mp h1)
  exact hinj _ _ ((hact γ u trivial).trans hγ)

theorem exists_sl3_lin_eq {K : Type} [Field K] (x y : Fin 3 → K) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ γ : ↥(StatedSL 3 K), (linModelNat (StatedSL 3 K)).lin γ x = y := by
  obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit x hx)
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit y hy)
  refine ⟨specialLinearGroupEquivStatedSL 3 K (B * A⁻¹), ?_⟩
  rw [linModelNat_lin, specialLinearGroupEquivStatedSL_coe]
  change (B * A⁻¹) • x = y
  rw [← hA, ← hB, mul_smul, inv_smul_smul]

section Sp4

variable {K : Type} [Field K]

abbrev spJ (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem spJ_mulVec (x : Fin 2 ⊕ Fin 2 → K) :
    spJ K *ᵥ x = Sum.elim (fun i => x (.inr i)) (fun i => - x (.inl i)) := by
  funext k
  rcases k with i | i <;>
    simp [spJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem toBilin'_spJ_apply (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) x y = ∑ i, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i)) := by
  rw [Matrix.toBilin'_apply', spJ_mulVec, dotProduct, Fintype.sum_sum_type,
    Finset.sum_sub_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]

theorem toBilin'_spJ_isAlt : (Matrix.toBilin' (spJ K)).IsAlt := by
  intro x
  rw [toBilin'_spJ_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem toBilin'_spJ_nondegenerate : (Matrix.toBilin' (spJ K)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · funext k
    rcases k with i | i
    · have := hx (Pi.single (.inr i) 1)
      rw [toBilin'_spJ_apply] at this
      simpa [Pi.single_apply] using this
    · have := hx (Pi.single (.inl i) 1)
      rw [toBilin'_spJ_apply] at this
      simpa [Pi.single_apply] using this
  · funext k
    rcases k with i | i
    · have := hy (Pi.single (.inr i) 1)
      rw [toBilin'_spJ_apply] at this
      simpa [Pi.single_apply] using this
    · have := hy (Pi.single (.inl i) 1)
      rw [toBilin'_spJ_apply] at this
      simpa [Pi.single_apply] using this

theorem exists_sp4_lin_eq (x y : Fin 2 ⊕ Fin 2 → K) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ γ : ↥(StatedSp 2 K), (linModelNat (StatedSp 2 K)).lin γ x = y := by
  obtain ⟨g, hg, hgx⟩ :=
    (alternating_transvection_vector_transitivity toBilin'_spJ_isAlt toBilin'_spJ_nondegenerate).2
      x y hx hy
  have hiso := closure_symplecticTransvection_le_bilinIsometryGroup toBilin'_spJ_isAlt hg
  set A : GL (Fin 2 ⊕ Fin 2) K := Matrix.GeneralLinearGroup.toLin.symm g with hA
  have hgA : (g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)) =
      Matrix.mulVecLin (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← Matrix.GeneralLinearGroup.coe_toLin, hA, MulEquiv.apply_symm_apply]
  have hAsp : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ K * A = spJ K := by
    have hcomp : (Matrix.toBilin' (spJ K)).comp (Matrix.mulVecLin (A : Matrix _ _ K))
        (Matrix.mulVecLin (A : Matrix _ _ K)) = Matrix.toBilin' (spJ K) := by
      refine LinearMap.ext₂ fun u v => ?_
      rw [LinearMap.BilinForm.comp_apply, ← hgA]
      exact hiso u v
    have := congrArg LinearMap.BilinForm.toMatrix' hcomp
    rwa [LinearMap.BilinForm.toMatrix'_comp, LinearMap.BilinForm.toMatrix'_toBilin',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  refine ⟨⟨A, Subgroup.subset_closure hAsp⟩, ?_⟩
  rw [linModelNat_lin, ← hgx, hgA]
  rfl

end Sp4

section G2

variable {K : Type} [Field K] [CharP K 2]

theorem commutator_quasithinG2_le : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K := by
  rw [← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
    (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)

theorem commutator_quasithinG2_eq {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    cayley_commutator_eq hc0 hc1]

variable [Finite K]

@[expose] noncomputable def zLift (w : Ix3 → K) : quasithinZorn K :=
  zI w + (frobeniusEquiv K 2).symm (∑ k, w (.inl k) * w (.inr k)) • cayleyOne K

theorem zLift_eq (w : Ix3 → K) : zLift w =
    zmk ((frobeniusEquiv K 2).symm (∑ k, w (.inl k) * w (.inr k))) (w (.inl 0)) (w (.inl 1))
      (w (.inl 2)) (w (.inr 0)) (w (.inr 1)) (w (.inr 2))
      ((frobeniusEquiv K 2).symm (∑ k, w (.inl k) * w (.inr k))) := by
  rw [zLift, cayleyOne_eq, zmk_smul, zI, zmk_add]
  apply zmk_congr <;> ring

theorem zP_zLift (w : Ix3 → K) : zP (zLift w) = w := by
  rw [zLift, zP_add, zP_zI, zP_smul, zP_one, smul_zero, add_zero]

theorem cayleyTr_zLift (w : Ix3 → K) : cayleyTr (zLift w) = 0 := by
  rw [zLift_eq, cayleyTr_zmk]
  exact CharTwo.add_self_eq_zero _

theorem cayleyNorm_zLift (w : Ix3 → K) : cayleyNorm (zLift w) = 0 := by
  rw [zLift_eq, cayleyNorm_zmk]
  have h : (frobeniusEquiv K 2).symm (∑ k, w (.inl k) * w (.inr k)) *
      (frobeniusEquiv K 2).symm (∑ k, w (.inl k) * w (.inr k)) =
        ∑ k, w (.inl k) * w (.inr k) := by
    rw [← sq, ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  rw [h, Fin.sum_univ_three]
  exact CharTwo.add_self_eq_zero _

theorem zLift_ne_zero {w : Ix3 → K} (hw : w ≠ 0) : zLift w ≠ 0 := by
  intro h
  apply hw
  rw [← zP_zLift w, h, ← zmk_zero, zP_zmk, q6_zero]

theorem zI_eq_zLift_add (w : Ix3 → K) : zI w = zLift w +
    (frobeniusEquiv K 2).symm (∑ k, w (.inl k) * w (.inr k)) • cayleyOne K := by
  rw [zLift, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem exists_g2_lin_eq {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (x y : Ix3 → K) (hx : x ≠ 0)
    (hy : y ≠ 0) : ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆,
      (linModelZorn _ commutator_quasithinG2_le).lin γ x = y := by
  obtain ⟨g, hg, hgx⟩ := exists_closure_apply_zU0 (zLift_ne_zero hx) (cayleyTr_zLift x)
    (cayleyNorm_zLift x)
  obtain ⟨g', hg', hgy⟩ := exists_closure_apply_zU0 (zLift_ne_zero hy) (cayleyTr_zLift y)
    (cayleyNorm_zLift y)
  have hcl : Subgroup.closure (gensG2 K) ≤ cayleyGroup K :=
    (Subgroup.closure_le _).mpr gensG2_subset
  have hγC : g' * g⁻¹ ∈ cayleyGroup K := Subgroup.mul_mem _ (hcl hg') (Subgroup.inv_mem _ (hcl hg))
  refine ⟨⟨g' * g⁻¹, (commutator_quasithinG2_eq hc0 hc1).symm ▸ hγC⟩, ?_⟩
  rw [linModelZorn_lin]
  have h1 : (g' * g⁻¹ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (zLift x) = zLift y := by
    rw [← hgx, ← hgy]
    change g' (g.symm (g (zU0 K))) = g' (zU0 K)
    rw [LinearEquiv.symm_apply_apply]
  have h2 : (g' * g⁻¹ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (cayleyOne K) = cayleyOne K :=
    hγC.1
  change zP ((g' * g⁻¹ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (zI x)) = y
  rw [zI_eq_zLift_add, map_add, map_smul, h1, h2, zP_add, zP_smul, zP_one, smul_zero, add_zero,
    zP_zLift]

end G2

theorem vecTransFacts_holds : Ch11.SecE.VecTransFacts where
  sl3 := fun _ _ _ _ _ _ _ _ _ _ _ _ hπ u w hu hw =>
    exists_apply_eq_of_linModel (linModelNat _) exists_sl3_lin_eq hπ u w hu hw
  sp4 := fun _ _ _ _ _ _ _ _ _ _ _ _ hπ u w hu hw =>
    exists_apply_eq_of_linModel (linModelNat _) exists_sp4_lin_eq hπ u w hu hw
  g2 := fun K _ _ n hn hK _ _ _ _ _ _ hπ u w hu hw => by
    have : CharP K 2 := charP_two_of_card (by omega) hK
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (by rw [hK]; omega)
    exact exists_apply_eq_of_linModel (linModelZorn _ commutator_quasithinG2_le)
      (exists_g2_lin_eq hc0 hc1) hπ u w hu hw

end CFSG.Quasithin.Vol2.KGNat
