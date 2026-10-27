module

public import CFSG.Quasithin.Vol2.KGNatSL3Flag
public import CFSG.Quasithin.Vol2.KGNatLevi
public import CFSG.LieType.SteinbergBRParabolicTransport
public import CFSG.LieType.SteinbergBRBlockParabolicDInf

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem stdLine_eq_flagSpace : stdLine K = flagSpace 3 K 1 := by
  ext v
  rw [mem_stdLine, mem_flagSpace]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide)⟩

theorem stdPlane_eq_flagSpace : stdPlane K = flagSpace 3 K 2 := by
  ext v
  rw [mem_stdPlane, mem_flagSpace]
  constructor
  · intro h2 j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact h2
  · intro h
    exact h 2 (by decide)

theorem mem_iff_of_mem_stabilizer {n : ℕ} {W : Submodule K (Fin n → K)}
    {A : Matrix.SpecialLinearGroup (Fin n) K} (hA : A ∈ stabilizer W) (x : Fin n → K) :
    x ∈ W ↔ (A : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W := by
  have hA' : W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K)) = W := hA
  constructor
  · intro hx
    rw [← hA']
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hA'] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have : y = x := by
      have := congrArg (fun z => ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ z) hxy
      rw [Matrix.mulVecLin_apply] at this
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
        Matrix.one_mulVec] at this
    rwa [← this]

theorem mem_stabilizer_of_iff {n : ℕ} {W : Submodule K (Fin n → K)}
    {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hA : ∀ x, x ∈ W ↔ (A : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W) : A ∈ stabilizer W := by
  rw [mem_stabilizer_iff_map_le]
  rintro _ ⟨x, hx, rfl⟩
  exact (hA x).mp hx

section Levi

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

@[expose] noncomputable def psiPar (π : ↥(StatedSL 3 K) →* ↥H)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {d e : ℕ} (h : d + e = 3) :
    Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) K →* MulAut W :=
  H.subtype.comp ((rho3 π).comp ((MulAut.conj g).toMonoidHom.comp (reindexSL K h).toMonoidHom))

theorem psiPar_apply (π : ↥(StatedSL 3 K) →* ↥H) (g : Matrix.SpecialLinearGroup (Fin 3) K)
    {d e : ℕ} (h : d + e = 3) (M : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) K) :
    psiPar π g h M = ((rho3 π (g * reindexSL K h M * g⁻¹) : ↥H) : MulAut W) := rfl

theorem psiPar_injective (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {d e : ℕ} (h : d + e = 3) :
    Function.Injective (psiPar π g h) :=
  H.subtype_injective.comp ((rho3_bijective hf).1.comp
    ((MulAut.conj g).injective.comp (reindexSL K h).injective))

theorem mulVec_gconj (g A : Matrix.SpecialLinearGroup (Fin 3) K) (y : Fin 3 → K) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y)) =
      ((g⁻¹ * A * g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem map_parQ_psiPar (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {d e : ℕ} (h : d + e = 3) :
    (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) K)).map (psiPar π g h) =
      H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K d)).toAddSubgroup) := by
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    refine ⟨(rho3 π _).2,
      (hf.rho3_mem_stabW_iff (hf.le_pre _) (g * reindexSL K h M * g⁻¹)).mpr ?_⟩
    rw [hf.img_pre]
    intro y
    change y ∈ gmap g _ ↔ _ ∈ gmap g _
    rw [mem_gmap, mem_gmap, conj_mulVec]
    exact mem_iff_of_mem_stabilizer ((mem_parQ_iff_reindex h M).mp hM) _
  · rintro ⟨hxH, hxs⟩
    obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨x, hxH⟩
    have hx : x = ((rho3 π A : ↥H) : MulAut W) := by rw [hA]
    have hxs' := (hf.rho3_mem_stabW_iff (hf.le_pre _) A).mp (by rw [← hx]; exact hxs)
    rw [hf.img_pre] at hxs'
    have hB : g⁻¹ * A * g ∈ stabilizer (flagSpace 3 K d) := by
      refine mem_stabilizer_of_iff fun y => ?_
      have h1 := hxs' ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y)
      change _ ∈ gmap g _ ↔ _ ∈ gmap g _ at h1
      rw [mem_gmap, mem_gmap, mulVec_gconj, Matrix.mulVec_mulVec,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mulVec] at h1
      exact h1
    refine ⟨(reindexSL K h).symm (g⁻¹ * A * g),
      (mem_parQ_iff_reindex h _).mpr (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    rw [psiPar_apply, MulEquiv.apply_symm_apply, show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hx]

end Levi

theorem factLeviSL3_holds : Ch11.SecA.FactLeviSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP i U hi hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact (CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩).commutator_eq_top
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW hW hf hg hU
  rcases hi with rfl | rfl
  · rw [(eq_std_of_stable hS).1 (by rw [hc, pow_one]), stdLine_eq_flagSpace]
    have h12 : (1 : ℕ) + 2 = 3 := rfl
    let e₁ := ((parQ : Subgroup (Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) K)).equivMapOfInjective
      _ (psiPar_injective hf g h12)).trans (MulEquiv.subgroupCongr (map_parQ_psiPar hf g h12))
    exact levi_of_semidirect h4 isPGroup_mult_matrix
      ((MonoidHom.ofInjective (thetaR_injective (F := K) (a := Fin 1) (b := Fin 2))).trans
        ((Subgroup.subgroupOfEquivOfLe parJR_le_parQ).symm.trans
          ((MulEquiv.subgroupCongr (perfectResidual_parQ_eq_parJR hSL).symm).trans
            ((perfectResidualCongr e₁).trans (perfectCoreEquiv _).symm))))
  · rw [(eq_std_of_stable hS).2.1 hc, stdPlane_eq_flagSpace]
    have h21 : (2 : ℕ) + 1 = 3 := rfl
    let e₁ := ((parQ : Subgroup (Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) K)).equivMapOfInjective
      _ (psiPar_injective hf g h21)).trans (MulEquiv.subgroupCongr (map_parQ_psiPar hf g h21))
    exact levi_of_semidirect h4 isPGroup_mult_matrix
      ((MonoidHom.ofInjective (thetaL_injective (F := K) (a := Fin 2) (b := Fin 1))).trans
        ((Subgroup.subgroupOfEquivOfLe parJL_le_parQ).symm.trans
          ((MulEquiv.subgroupCongr (perfectResidual_parQ_eq_parJL hSL).symm).trans
            ((perfectResidualCongr e₁).trans (perfectCoreEquiv _).symm))))

end CFSG.Quasithin.Vol2.KGNat
