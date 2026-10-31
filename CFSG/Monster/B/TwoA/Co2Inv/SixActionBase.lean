
module

public import CFSG.Monster.B.TwoA.Co2Inv.SixCertBase
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

def Zsp : Submodule (ZMod 2) (Wv v0) := Submodule.span (ZMod 2) (Set.range zVec)

theorem zComb_eq (c : ℕ) :
    decW (Native.actD 6 zBasis c) = ∑ s : Fin 6, bvec 6 c s • zVec s := by
  rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add, Finset.sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [bvec_apply, zVec]
  split_ifs <;> simp

theorem zComb_mem (c : ℕ) : decW (Native.actD 6 zBasis c) ∈ Zsp := by
  rw [zComb_eq]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

theorem mem_Zsp_iff
    {x : Wv v0} : x ∈ Zsp ↔ ∃ c < 64, x = decW (Native.actD 6 zBasis c) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine ⟨1 <<< (t : ℕ), (zBasis_comb_single t t.2).1, ?_⟩
      rw [(zBasis_comb_single t t.2).2]
      rfl
    | zero => exact ⟨0, by norm_num, by rw [zBasis_comb_zero, decW_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      refine ⟨c ^^^ c', Nat.xor_lt_two_pow (n := 6) hc hc', ?_⟩
      rw [← decW_xor, zBasis_comb_xor c hc c' hc']
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) t with rfl | rfl
      · exact ⟨0, by norm_num, by rw [zero_smul, zBasis_comb_zero, decW_zero]⟩
      · exact ⟨c, hc, by rw [one_smul]⟩
  · rintro ⟨c, -, rfl⟩
    exact zComb_mem c

theorem decW_ne_zero {c : ℕ} (h0 : 0 < c) (hc : c < 2 ^ 22) : decW c ≠ 0 := by
  intro h
  rw [← decW_zero] at h
  have := decW_injective hc (by norm_num) h
  omega

theorem wFr_mem_Zsp :
    wFr ∈ Zsp := by
  rw [wFr_eq_decW]
  exact Submodule.subset_span ⟨0, rfl⟩

theorem linearIndependent_zVec : LinearIndependent (ZMod 2) zVec := by
  refine LinearIndependent.of_comp (zDualMat.mulVecLin ∘ₗ qbWBasis.equivFun.toLinearMap) ?_
  have : (zDualMat.mulVecLin ∘ₗ qbWBasis.equivFun.toLinearMap) ∘ zVec =
      ⇑(Pi.basisFun (ZMod 2) (Fin 6)) := by
    funext j
    change zDualMat.mulVec (qbWBasis.equivFun (decW zBasis[(j : ℕ)]!)) = _
    rw [decW_eq_equivFun, LinearEquiv.apply_symm_apply, zDualMat_zBasis, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 2) (Fin 6)).linearIndependent

theorem finrank_Zsp : Module.finrank (ZMod 2) Zsp = 6 := by
  rw [Zsp, finrank_span_eq_card linearIndependent_zVec, Fintype.card_fin]

def zB : Module.Basis (Fin 6) (ZMod 2) Zsp := Module.Basis.span linearIndependent_zVec

theorem coe_zB (t : Fin 6) : (zB t : Wv v0) = zVec t :=
  congrArg Subtype.val (Module.Basis.span_apply linearIndependent_zVec t)

instance finiteDimensional_Zsp : FiniteDimensional (ZMod 2) Zsp := Module.Finite.of_basis zB

theorem zB_comb
    (c : ℕ) :
    (⟨_, zComb_mem c⟩ : Zsp) = ∑ s, bvec 6 c s • zB s := by
  apply Subtype.ext
  change decW (Native.actD 6 zBasis c) = ((∑ s, bvec 6 c s • zB s : Zsp) : Wv v0)
  rw [Submodule.coe_sum, zComb_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Submodule.coe_smul, coe_zB]

def bZ : LinearMap.BilinForm (ZMod 2) Zsp := Matrix.toBilin zB gramMat

theorem bZ_apply (x y : Zsp) :
    bZ x y = ∑ i, ∑ j, zB.repr x i * gramMat i j * zB.repr y j :=
  Matrix.toBilin_apply zB gramMat x y

theorem bZ_zB (i j : Fin 6) : bZ (zB i) (zB j) = gramMat i j :=
  (LinearMap.BilinForm.toMatrix_apply zB bZ i j).symm.trans
    (LinearMap.BilinForm.toMatrix_toBilin zB gramMat ▸ rfl)

theorem bZ_sum (f g : Fin 6 → ZMod 2) :
    bZ (∑ s, f s • zB s) (∑ s, g s • zB s) = ∑ i, ∑ j, f i * gramMat i j * g j := by
  rw [bZ_apply]
  simp only [Module.Basis.repr_sum_self]

theorem bZ_comb
    (c c' : ℕ) : bZ ⟨_, zComb_mem c⟩ ⟨_, zComb_mem c'⟩ =
    ∑ i, ∑ j, bvec 6 c i * gramMat i j * bvec 6 c' j := by
  rw [zB_comb c, zB_comb c']
  exact bZ_sum _ _

theorem bZ_isAlt :
    bZ.IsAlt := by
  intro x
  obtain ⟨c, hc, e⟩ := mem_Zsp_iff.1 x.2
  have hx : x = ⟨_, zComb_mem c⟩ := Subtype.ext e
  rw [hx, bZ_comb]
  exact gramMat_alt c hc

theorem gramMat_det_ne_zero : gramMat.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det gramMat_mul_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem bZ_nondegenerate : bZ.Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff zB).2
    (Matrix.Nondegenerate.of_det_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero gramMat_det_ne_zero))

theorem natCard_isometryGroup_bZ :
    Nat.card (TauCeti.BilinForm.isometryGroup bZ) = 1451520 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup 3 bZ bZ_isAlt
    bZ_nondegenerate finrank_Zsp, Nat.card_zmod]
  decide

instance finite_isometryGroup_bZ :
    Finite (TauCeti.BilinForm.isometryGroup bZ) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_isometryGroup_bZ]; norm_num)

def resLin
    {g : Kstab v0} (hg : g ∈ wSetStab Zsp) : Zsp →ₗ[ZMod 2] Zsp :=
  (wAct v0 g).restrict fun x hx => hg x hx

theorem coe_resLin
    {g : Kstab v0} (hg : g ∈ wSetStab Zsp) (x : Zsp) :
    (resLin hg x : Wv v0) = wAct v0 g x := rfl

def resGL :
    wSetStab Zsp →* (Zsp ≃ₗ[ZMod 2] Zsp) where
  toFun g := LinearEquiv.ofLinearMap (resLin ((wSetStab Zsp).inv_mem g.2)) (resLin g.2)
    (LinearMap.ext fun x => Subtype.ext (wAct_inv_apply (g : Kstab v0) x))
    (LinearMap.ext fun x => Subtype.ext (wAct_apply_inv (g : Kstab v0) x))
  map_one' := LinearEquiv.ext fun x => Subtype.ext (by
    change wAct v0 (1 : Kstab v0)⁻¹ x = x
    rw [inv_one, wAct_one, Module.End.one_apply])
  map_mul' g g' := LinearEquiv.ext fun x => Subtype.ext (by
    change wAct v0 ((g : Kstab v0) * g')⁻¹ x =
      wAct v0 (g : Kstab v0)⁻¹ (wAct v0 (g' : Kstab v0)⁻¹ x)
    rw [mul_inv_rev, wAct_mul, Module.End.mul_apply])

theorem coe_resGL_apply
    (g : wSetStab Zsp) (x : Zsp) :
    (resGL g x : Wv v0) = wAct v0 (g : Kstab v0)⁻¹ x := rfl

theorem bZ_map_eq_of_basis (φ : Zsp ≃ₗ[ZMod 2] Zsp)
    (h : ∀ i j, bZ (φ (zB i)) (φ (zB j)) = bZ (zB i) (zB j)) (x y : Zsp) :
    bZ (φ x) (φ y) = bZ x y := by
  have e := LinearMap.BilinForm.ext_basis zB (B := bZ.compl₁₂ φ.toLinearMap φ.toLinearMap)
    (F₂ := bZ) h
  exact LinearMap.congr_fun₂ e x y

theorem natCard_ker_mul_range {G N : Type*} [Group G] [Group N] (f : G →* N) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem nonempty_isometryGroup_bZ_equiv :
    Nonempty
    (TauCeti.BilinForm.isometryGroup bZ ≃* CFSG.Assembly.LowTwoRank.StatedSp 3 (ZMod 2)) := by
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis bZ bZ_isAlt
      bZ_nondegenerate
  have hm3 : m = 3 := by
    rw [finrank_Zsp] at hm
    omega
  subst hm3
  exact ⟨(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b bZ
    hb).trans
      (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)⟩

end CFSG.Monster.B.TwoA.Co2Inv
