module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def projEquivSp : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
  MulEquiv.ofBijective (proj 2 F) ⟨proj_injective_charTwo, proj_surjective⟩

omit [Finite F] in
theorem exists_not_comm_projSp :
    ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
  refine ⟨projEquivSp (CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.lam (1 : F)),
    projEquivSp (tau (sym2_transpose (0 : F) 0 1)), fun h => ?_⟩
  rw [← map_mul, ← map_mul] at h
  have h1 := projEquivSp.injective h
  have h2 : CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.lam (1 : F) *
      tau (sym2_transpose (0 : F) 0 1) *
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.lam (1 : F))⁻¹ =
        tau (sym2_transpose (0 : F) 0 1) := by
    rw [h1, mul_inv_cancel_right]
  rw [lam_mul_tau_mul_inv] at h2
  have h3 := tau_injective _ _ h2
  rw [unitri_mul_sym2_mul_transpose] at h3
  have h4 := congrFun (congrFun h3 0) 0
  simp [sym2] at h4

theorem exists_equiv_perfectCore_Q2 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (ε : X ≃* ↥(StatedSp 2 F)) {U B : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) :
    ∃ (ψ : X ≃* ↥(StatedSp 2 F)) (j : Fin 2), B.map ψ.toMonoidHom = perfectCore (Q2 F j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hF⟩
  have hK4' : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four hK4'
  set e₁ : X ≃* StatedProj (StatedSp 2 F) := ε.trans projEquivSp with he₁
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := F) 2 (r := 2) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnipotent 2 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hU₁ : CFSG.QuasithinUnique.IsSylowTwoOf (U.map e₁.toMonoidHom) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e₁.toMonoidHom e₁.surjective hU
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hU₁ hU₀
  set e₂ : X ≃* StatedProj (StatedSp 2 F) := e₁.trans (MulAut.conj g) with he₂
  have hU₂ : U.map e₂.toMonoidHom = projUnipotent 2 F := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hB₂ : B.map e₂.toMonoidHom ∈ lFamily (projUnipotent 2 F) := by
    have h1 := cComp_map_mulEquiv e₂ (show B ∈ cComp (B ⊔ U) from hB)
    rw [Subgroup.map_sup, hU₂] at h1
    exact h1
  have hB₂top : B.map e₂.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have h1 := congrArg (Subgroup.map e₂.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e₂.symm.surjective] at h1
    exact h1
  have hsimp : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr hK4'))
  have hq : CFSG.IsQuasisimple (StatedProj (StatedSp 2 F)) :=
    CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup exists_not_comm_projSp
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 F)) (projUnipotent 2 F)
      (fun j : Fin 2 => (Q2 F j).map (proj 2 F)) := symplectic_two_residualOvergroupsAt hK
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 F j), ∀ y ∈ perfectCore (Q2 F j),
      proj 2 F x = proj 2 F y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  obtain ⟨j, hj⟩ := rank2_eq_perfectCore hq hres (fun j => ⟨SpecialLinearGroup (Fin 2) F,
    inferInstance, sl2_isSimple hK4, sl2_nonabelian hK4,
    (blkN j).comp (perfectCoreMapEquiv (proj 2 F) (Q2 F j) (hinj j)).symm.toMonoidHom,
    (blkN_surjective hK4 j).comp (perfectCoreMapEquiv (proj 2 F) (Q2 F j) (hinj j)).symm.surjective,
    by
      have hp : IsPGroup 2 ((blkN j).comp
          (perfectCoreMapEquiv (proj 2 F) (Q2 F j) (hinj j)).symm.toMonoidHom).ker := by
        rw [← MonoidHom.comap_ker]
        exact (blkN_ker_isPGroup hK j).comap_of_injective _
          (perfectCoreMapEquiv (proj 2 F) (Q2 F j) (hinj j)).symm.injective
      have := hp.isNilpotent
      infer_instance⟩) hB₂ hB₂top
  refine ⟨e₂.trans projEquivSp.symm, j, ?_⟩
  have e : (e₂.trans projEquivSp.symm).toMonoidHom =
      projEquivSp.symm.toMonoidHom.comp e₂.toMonoidHom := rfl
  rw [e, ← Subgroup.map_map, hj, map_perfectCore, Subgroup.map_map]
  congr 1
  have hid : projEquivSp.symm.toMonoidHom.comp (proj 2 F) = MonoidHom.id (StatedSp 2 F) :=
    MonoidHom.ext fun x => projEquivSp.symm_apply_apply x
  rw [hid, Subgroup.map_id]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
