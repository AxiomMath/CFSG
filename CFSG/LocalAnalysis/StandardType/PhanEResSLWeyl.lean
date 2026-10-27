module

public import CFSG.LocalAnalysis.StandardType.PhanEResSLRoots

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {M : ChevModel2 D n H Fld} {m : ℕ}

private theorem hmbSL_permMatrix_mul_permMatrix {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    LinearFlag.permMatrix n Fld σ * LinearFlag.permMatrix n Fld τ =
      LinearFlag.permMatrix n Fld (σ * τ) := by
  rw [LinearFlag.permMatrix_eq, LinearFlag.permMatrix_eq, LinearFlag.permMatrix_eq,
    ← Matrix.permMatrix_mul, _root_.mul_inv_rev]

private theorem hmbSL_signedPermMatrix_eq_permMatrix [CharP Fld 2] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    LinearFlag.signedPermMatrix n Fld σ = LinearFlag.permMatrix n Fld σ := by
  have hfun : (fun a : Fin n => if (a : ℕ) = 0 then ((Equiv.Perm.sign σ : ℤ) : Fld)
      else 1) = fun _ => 1 := by
    funext a
    by_cases h0 : (a : ℕ) = 0
    · rw [if_pos h0]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h]; simp
      · rw [h]; simp [CharTwo.neg_eq]
    · rw [if_neg h0]
  rw [LinearFlag.signedPermMatrix, hfun, Matrix.diagonal_one, Matrix.one_mul]

private theorem hmbSL_signedPermutation_mul [CharP Fld 2] {m : ℕ}
    (w w' : Equiv.Perm (Fin (m + 1))) :
    LinearFlag.signedPermutation (m + 1) Fld (w * w') =
      LinearFlag.signedPermutation (m + 1) Fld w *
        LinearFlag.signedPermutation (m + 1) Fld w' := by
  apply Subtype.ext
  show LinearFlag.signedPermMatrix (m + 1) Fld (w * w') =
    LinearFlag.signedPermMatrix (m + 1) Fld w * LinearFlag.signedPermMatrix (m + 1) Fld w'
  rw [hmbSL_signedPermMatrix_eq_permMatrix, hmbSL_signedPermMatrix_eq_permMatrix,
    hmbSL_signedPermMatrix_eq_permMatrix, hmbSL_permMatrix_mul_permMatrix]

private theorem hmbSL_signedPermutation_one [CharP Fld 2] {m : ℕ} :
    LinearFlag.signedPermutation (m + 1) Fld (1 : Equiv.Perm (Fin (m + 1))) = 1 := by
  ext a b
  rw [LinearFlag.coe_signedPermutation, hmbSL_signedPermMatrix_eq_permMatrix,
    Matrix.SpecialLinearGroup.coe_one, LinearFlag.permMatrix_apply, Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

private theorem hmbSL_weylSign_eq_one [CharP Fld 2] {m : ℕ} (s t : Fin (m + 1)) :
    CFSG.LieType.Universal.SpecialLinear.weylSign (R := Fld) s t = 1 := by
  have h : CFSG.LieType.Universal.SpecialLinear.weylSign (R := Fld) s t *
      CFSG.LieType.Universal.SpecialLinear.weylSign (R := Fld) s t = 1 :=
    CFSG.LieType.Universal.SpecialLinear.weylSign_mul_self s t
  rcases (mul_self_eq_one_iff.mp h) with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

private theorem hmbSL_weylMatrix_eq_permMatrix [CharP Fld 2] {m : ℕ}
    (a b : Fin (m + 1)) :
    CFSG.LieType.Universal.SpecialLinear.weylMatrix (R := Fld) a b =
      LinearFlag.permMatrix (m + 1) Fld (Equiv.swap a b) := by
  ext r s
  rw [CFSG.LieType.Universal.SpecialLinear.weylMatrix,
    CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, LinearFlag.permMatrix_apply,
    hmbSL_weylSign_eq_one a s]

private theorem hmbSL_transvection_triple_eq_weylMatrix [CharP Fld 2] {m : ℕ}
    {a b : Fin (m + 1)} (hab : a ≠ b) :
    ((SpecialLinearGroup.transvection hab (1 : Fld) *
        SpecialLinearGroup.transvection hab.symm 1 *
        SpecialLinearGroup.transvection hab 1 : SpecialLinearGroup (Fin (m + 1)) Fld) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
      CFSG.LieType.Universal.SpecialLinear.weylMatrix (R := Fld) a b := by
  have hm : SpecialLinearGroup.transvection hab.symm (1 : Fld) =
      SpecialLinearGroup.transvection hab.symm (-1) := by
    congr 1
    rw [CharTwo.neg_eq]
  rw [hm]
  exact CFSG.LieType.Universal.SpecialLinear.coe_transvection_mul_transvection_mul_transvection hab

private theorem hmbSL_signedPermutation_adjSwap [CharP Fld 2] {m : ℕ} (k : Fin m) :
    LinearFlag.signedPermutation (m + 1) Fld (adjSwap k) =
      tv Fld k.castSucc k.succ 1 * tv Fld k.succ k.castSucc 1 * tv Fld k.castSucc k.succ 1 := by
  have hpq : k.castSucc ≠ k.succ := hmbSL_castSucc_ne_succ k
  apply Subtype.ext
  rw [LinearFlag.coe_signedPermutation, hmbSL_signedPermMatrix_eq_permMatrix]
  rw [tv_of_ne hpq, tv_of_ne hpq.symm]
  rw [hmbSL_transvection_triple_eq_weylMatrix hpq, hmbSL_weylMatrix_eq_permMatrix]
  rfl

private theorem hmbSL_ε_simple {M : ChevModel2 D n H Fld} {m : ℕ} [CharP Fld 2]
    (L : SLPath M m) (k : Fin m) :
    L.ε (LinearFlag.signedPermutation (m + 1) Fld ((symCox m).simple k)) = n (L.e k) := by
  rw [symCox_simple, hmbSL_signedPermutation_adjSwap k]
  rw [map_mul, map_mul,
    L.tv_eq k.castSucc k.succ (hmbSL_castSucc_ne_succ k) 1,
    L.tv_eq k.succ k.castSucc (hmbSL_castSucc_ne_succ k).symm 1,
    hmbSL_pathRoot_castSucc_succ, hmbSL_pathRoot_succ_castSucc, M.nm_def,
    CharTwo.neg_eq (1 : Fld)]

private theorem hmbSL_actsAs_n {M : ChevModel2 D n H Fld} (i : Fin D.rank) :
    ActsAs D (n i) ((cs).simple i) := by
  intro γ hγ
  apply le_antisymm
  · rintro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := (M.x_mem γ hγ y).mp hy
    change (MulAut.conj (n i)) (M.x γ c) ∈
      D.rootGroup (weylAction D.isFiniteType ((cs).simple i) γ)
    rw [MulAut.conj_apply, M.nm_conj i γ hγ c]
    exact (M.x_mem _ (weylAction_mem_roots hγ ((cs).simple i)) _).mpr ⟨c, rfl⟩
  · rintro z hz
    obtain ⟨c, rfl⟩ := (M.x_mem _ (weylAction_mem_roots hγ ((cs).simple i)) z).mp hz
    rw [Subgroup.mem_map]
    refine ⟨M.x γ c, (M.x_mem γ hγ _).mpr ⟨c, rfl⟩, ?_⟩
    change (MulAut.conj (n i)) (M.x γ c) =
      M.x (weylAction D.isFiniteType ((cs).simple i) γ) c
    rw [MulAut.conj_apply, M.nm_conj i γ hγ c]

theorem ε_signedPermutation_mem_weylN [CharP Fld 2] (L : SLPath M m)
    (w : Equiv.Perm (Fin (m + 1))) :
    L.ε (LinearFlag.signedPermutation (m + 1) Fld w) ∈ weylN n H ∧
      ActsAs D (L.ε (LinearFlag.signedPermutation (m + 1) Fld w)) (pathWeyl L w) := by
  obtain ⟨ω, rfl⟩ := (symCox m).wordProd_surjective w
  induction ω with
  | nil =>
    rw [CoxeterSystem.wordProd_nil, hmbSL_signedPermutation_one, map_one]
    refine ⟨Subgroup.one_mem _, ?_⟩
    rw [map_one]
    exact ActsAs.one
  | cons k ω ih =>
    rw [CoxeterSystem.wordProd_cons, hmbSL_signedPermutation_mul, map_mul, map_mul]
    refine ⟨?_, ?_⟩
    · rw [hmbSL_ε_simple]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨L.e k, rfl⟩)) ih.1
    · rw [hmbSL_ε_simple, pathWeyl_simple]
      exact (hmbSL_actsAs_n (M := M) (L.e k)).mul ih.2

include hext in
theorem stdδ_mk_mul_ε [CharP Fld 2] (L : SLPath M m) (g : K)
    (A A' : SpecialLinearGroup (Fin (m + 1)) Fld) :
    stdδ hct ((g * L.ε A : K) : K ⧸ borel D H) ((g * L.ε A' : K) : K ⧸ borel D H) =
      pathWeyl L (flagδ m (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)))
        (flagAct (SpecialLinearGroup.toGL A') (stdFlag Fld (m + 1)))) := by
  classical
  set C : SpecialLinearGroup (Fin (m + 1)) Fld := A⁻¹ * A' with hC
  set w : Equiv.Perm (Fin (m + 1)) :=
    flagδ m (stdFlag Fld (m + 1)) (flagAct (SpecialLinearGroup.toGL C) (stdFlag Fld (m + 1)))
    with hw
  have hflag : flagδ m (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)))
      (flagAct (SpecialLinearGroup.toGL A') (stdFlag Fld (m + 1))) = w := by
    have h := flagδ_flagAct ((SpecialLinearGroup.toGL A)⁻¹)
      (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)))
      (flagAct (SpecialLinearGroup.toGL A') (stdFlag Fld (m + 1)))
    rw [← h, hw]
    congr 1
    · rw [← flagAct_mul, ← map_inv, ← map_mul, inv_mul_cancel, map_one, flagAct_one]
    · rw [← flagAct_mul, ← map_inv, ← map_mul, ← hC]
  have hCmem : C ∈ LinearFlag.bruhatCell w := by
    rw [hw]
    exact (flagδ_stdFlag_eq_iff C _).mp rfl
  have hεC : L.ε C ∈ bruhatCell hct (pathWeyl L w) := by
    obtain ⟨b₁, hb₁, b₂, hb₂, hCeq⟩ := LinearFlag.mem_bruhatCell.mp hCmem
    rw [bruhatCell_eq_of_actsAs hct hext (ε_signedPermutation_mem_weylN L w).1
      (ε_signedPermutation_mem_weylN L w).2]
    exact ⟨L.ε b₁, ε_mem_borel L hb₁, L.ε b₂, ε_mem_borel L hb₂, by
      rw [hCeq, map_mul, map_mul]⟩
  have hstd : stdδ hct (L.ε A : K ⧸ borel D H) (L.ε A' : K ⧸ borel D H) = pathWeyl L w := by
    refine (stdδ_mk_eq_iff hct hext (L.ε A) (L.ε A') (pathWeyl L w)).mpr ?_
    have hA : (L.ε A)⁻¹ * L.ε A' = L.ε C := by rw [hC, map_mul, map_inv]
    rw [hA]
    exact hεC
  have hsmul := stdδ_smul hct hext g (L.ε A : K ⧸ borel D H) (L.ε A' : K ⧸ borel D H)
  rw [MulAction.Quotient.smul_coe, MulAction.Quotient.smul_coe, smul_eq_mul, smul_eq_mul] at hsmul
  rw [hflag, hsmul, hstd]

include hext in
theorem mk_mul_ε_mem_residue [CharP Fld 2] (L : SLPath M m) {J : Set (Fin D.rank)}
    (hJ : Set.range L.e = J)
    (g : K) (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    ((g * L.ε A : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H) := by
  rw [mem_residue_iff_mem_parabolic (hδ := stdBuilding hct hext)]
  have hδ := stdδ_mk_mul_ε hct hext L g 1 A
  simp only [map_one, mul_one] at hδ
  rw [hδ]
  have hp := pathWeyl_mem_parabolic L
    (flagδ m (flagAct 1 (stdFlag Fld (m + 1)))
      (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))))
  simpa [hJ] using hp
end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
