module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts15b
public import CFSG.Quasithin.Vol2.KGNatSL3Lev

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped MatrixGroups

namespace PointStab

section Radical

variable {K : Type} [Field K]

theorem uSL_mem_stabE0 (a b c : K) : uSL a b c ∈ stabE0 K := by
  show ((uSL a b c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
    ![1, 0, 0]
  rw [coe_uSL]
  exact uMat_mulVec_e0 a b c

theorem leviHom_uSL (a b : K) : leviHom K ⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩ = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [leviHom_coe, lev_apply]
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat]

theorem eq_uSL_of_mem_ker {B : ↥(stabE0 K)} (hB : leviHom K B = 1) :
    (B : SpecialLinearGroup (Fin 3) K) =
      uSL (((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1)
        (((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) 0 := by
  obtain ⟨h00, h10, h20⟩ := stabE0_entries B.2
  have hl : lev ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← leviHom_coe, hB, Matrix.SpecialLinearGroup.coe_one]
  have h11 := congrFun (congrFun hl 0) 0
  have h12 := congrFun (congrFun hl 0) 1
  have h21 := congrFun (congrFun hl 1) 0
  have h22 := congrFun (congrFun hl 1) 1
  simp only [lev_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h11 h12 h21 h22
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat, h00, h10, h20, h11, h12, h21, h22]

theorem isPGroup_ker_leviHom [CharP K 2] : IsPGroup 2 (leviHom K).ker := by
  intro B
  refine ⟨1, ?_⟩
  have hB := eq_uSL_of_mem_ker (MonoidHom.mem_ker.mp B.2)
  apply Subtype.ext
  apply Subtype.ext
  rw [pow_one, sq]
  show ((B : ↥(stabE0 K)) : SpecialLinearGroup (Fin 3) K) *
    ((B : ↥(stabE0 K)) : SpecialLinearGroup (Fin 3) K) = 1
  rw [hB, uSL_mul, CharTwo.add_self_eq_zero, mul_zero, add_zero, CharTwo.add_self_eq_zero,
    add_zero, uSL_zero]

end Radical

section HU1

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem exists_equiv_stabE0 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K) :
    ∃ e : ↥(stabE0 K) ≃* ↥(perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))),
      ∀ B : ↥(stabE0 K), ((e B : MulAut W)) =
        ((rho3 π (g * (B : SpecialLinearGroup (Fin 3) K) * g⁻¹) : ↥H) : MulAut W) := by
  set L := perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))
    with hL
  let φ : ↥(stabE0 K) →* ↥L := MonoidHom.codRestrict
    (H.subtype.comp ((rho3 π).comp ((MulAut.conj g).toMonoidHom.comp (stabE0 K).subtype))) L
    (fun B => (mem_perfectCore_HU1_iff hSL hf g _).mpr
      ⟨(B : SpecialLinearGroup (Fin 3) K), B.2, rfl⟩)
  have hφinj : Function.Injective φ := by
    intro B B' h
    have h1 : rho3 π (g * (B : SpecialLinearGroup (Fin 3) K) * g⁻¹) =
        rho3 π (g * (B' : SpecialLinearGroup (Fin 3) K) * g⁻¹) :=
      Subtype.ext (congrArg (fun z : ↥L => (z : MulAut W)) h)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel ((rho3_bijective hf).1 h1)))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU1_iff hSL hf g y).mp hy
    exact ⟨⟨B, hB⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩, fun B => rfl⟩

theorem radical_mem_pCore [CharP K 2] (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    (a b : K) :
    ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))) ∧
      (y : MulAut W) = ((rho3 π (g * uSL a b 0 * g⁻¹) : ↥H) : MulAut W) := by
  obtain ⟨e, he⟩ := exists_equiv_stabE0 hSL hf g
  have hN : ((leviHom K).ker.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hle : (leviHom K).ker.map e.toMonoidHom ≤ CFSG.pCore 2 ↥(perfectCore (H ⊓
      Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))) :=
    le_sSup ⟨hN, isPGroup_ker_leviHom.map e.toMonoidHom⟩
  refine ⟨e ⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩, hle ⟨_, leviHom_uSL a b, rfl⟩, ?_⟩
  rw [he]

end HU1

end PointStab

open PointStab in
theorem factRadicalFixedSL3_holds : Ch11.SecA.FactRadicalFixedSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU]
  intro w hw
  have hfix : ∀ a b : K, uMat a b 0 *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f w) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w := by
    intro a b
    obtain ⟨y, hy, hyeq⟩ := radical_mem_pCore hSL hf g a b
    have h1 := hw y hy
    rw [← hf.ker, hf.map_mul_inv, hyeq, hf.act3, gconj_mulVec, sub_eq_zero] at h1
    have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simp only [ginv_g_mulVec] at h2
    rwa [coe_uSL] at h2
  have e1 := congrFun (hfix 1 0) 0
  have e2 := congrFun (hfix 0 1) 0
  rw [uMat_mulVec] at e1 e2
  simp at e1 e2
  show f w ∈ gmap g (flagSpace 3 K 1)
  rw [mem_gmap, ← stdLine_eq_flagSpace]
  exact ⟨e1, e2⟩

end CFSG.Quasithin.Vol2.KGNat
