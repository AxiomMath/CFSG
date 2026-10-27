module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpDiag
import CFSG.LieType.SeitzGeneration.RootPairSpConj
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpElt

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm spForm_apply spForm_isAlt spEnd spEnd_apply spLin
  spLin_injective)
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull

variable {F : Type} [Field F]

theorem spForm_mulVec_skew {r : ℕ} {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F} {ν : F}
    (hν : ν ≠ 0) (hform : Mᵀ * formJ r F * M = ν • formJ r F) (hsq : M * M = (-ν) • 1)
    (y z : Fin r ⊕ Fin r → F) :
    spForm r F (M *ᵥ y) z = -spForm r F y (M *ᵥ z) := by
  have hsp : ∀ u v : Fin r ⊕ Fin r → F, spForm r F u v = u ⬝ᵥ (formJ r F *ᵥ v) := by
    intro u v
    rw [spForm_apply]
    rfl
  have hMinv : M * ((-ν)⁻¹ • M) = 1 := by
    rw [Matrix.mul_smul, hsq, smul_smul]
    rw [show (-ν)⁻¹ * (-ν) = 1 by field_simp]
    rw [one_smul]
  have hskew : Mᵀ * formJ r F = -(formJ r F * M) := by
    calc Mᵀ * formJ r F = (Mᵀ * formJ r F) * 1 := by rw [Matrix.mul_one]
      _ = (Mᵀ * formJ r F) * (M * ((-ν)⁻¹ • M)) := by rw [hMinv]
      _ = ((Mᵀ * formJ r F) * M) * ((-ν)⁻¹ • M) :=
            (Matrix.mul_assoc (Mᵀ * formJ r F) M ((-ν)⁻¹ • M)).symm
      _ = (ν • formJ r F) * ((-ν)⁻¹ • M) := by rw [hform]
      _ = ν • (formJ r F * ((-ν)⁻¹ • M)) := by rw [Matrix.smul_mul]
      _ = ν • ((-ν)⁻¹ • (formJ r F * M)) := by rw [Matrix.mul_smul]
      _ = (ν * (-ν)⁻¹) • (formJ r F * M) := by rw [smul_smul]
      _ = (-1 : F) • (formJ r F * M) := by
          rw [show ν * (-ν)⁻¹ = -1 by field_simp]
      _ = -(formJ r F * M) := by rw [neg_one_smul]
  have hdot : ∀ (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) (u v : Fin r ⊕ Fin r → F),
      (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
    intro A u v
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [hsp, hsp, hdot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hskew,
    Matrix.neg_mulVec, dotProduct_neg]

theorem mem_comap_of_commute_inner {r : ℕ}
    {E : Subgroup (MulAut (StatedProj (StatedSp r F)))} {a : StatedSp r F}
    (ha : MulAut.conj (proj r F a) ∈ E) (ha1 : MulAut.conj (proj r F a) ≠ 1)
    {g : StatedSp r F} (hg : ∀ y, spEnd g (spEnd a y) = spEnd a (spEnd g y)) :
    g ∈ (planeClosure E).comap (proj r F) := by
  rw [Subgroup.mem_comap]
  have hsp : spLin r F (g * a) = spLin r F (a * g) := by
    rw [map_mul, map_mul]
    refine Units.ext (LinearMap.ext fun y => ?_)
    change spEnd g (spEnd a y) = spEnd a (spEnd g y)
    exact hg y
  have hcomm : g * a = a * g := spLin_injective hsp
  refine mem_planeClosure_of_fixed ha ha1 ?_
  have h : a * g * a⁻¹ = g := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [MulAut.conj_apply]
  change proj r F a * proj r F g * (proj r F a)⁻¹ = proj r F g
  calc proj r F a * proj r F g * (proj r F a)⁻¹
      = proj r F (a * g) * (proj r F a)⁻¹ := by rw [map_mul]
    _ = proj r F g := by
        rw [← map_inv, ← map_mul, h]

theorem mem_comap_of_commute_gsp {r : ℕ}
    {E : Subgroup (MulAut (StatedProj (StatedSp r F)))} {B : gsp r F}
    (hb : conjAut r F B ∈ E) (hb1 : conjAut r F B ≠ 1) {g : StatedSp r F}
    (hg : ∀ y, spEnd g (((B : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ y) =
      ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ spEnd g y) :
    g ∈ (planeClosure E).comap (proj r F) := by
  rw [Subgroup.mem_comap]
  set Bm : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hBm
  set Gm : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hGm
  have hBG : Gm * Bm = Bm * Gm := by
    rw [Matrix.ext_iff_mulVec]
    intro y
    simpa only [spEnd_apply, Matrix.mulVec_mulVec, hGm, hBm] using hg y
  have hGL : (B : GL (Fin r ⊕ Fin r) F) * (g : GL (Fin r ⊕ Fin r) F) =
      (g : GL (Fin r ⊕ Fin r) F) * (B : GL (Fin r ⊕ Fin r) F) := by
    apply Units.ext
    simpa only [Units.val_mul, hGm, hBm] using hBG.symm
  have hconj : conjSp r F B g = g := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_conjSp]
    calc (((B : GL (Fin r ⊕ Fin r) F) * (g : GL (Fin r ⊕ Fin r) F) *
          (B : GL (Fin r ⊕ Fin r) F)⁻¹ : GL (Fin r ⊕ Fin r) F) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
        = (((g : GL (Fin r ⊕ Fin r) F) * (B : GL (Fin r ⊕ Fin r) F) *
            (B : GL (Fin r ⊕ Fin r) F)⁻¹ : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by rw [← hGL]
      _ = (((g : GL (Fin r ⊕ Fin r) F)) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
  refine mem_planeClosure_of_fixed hb hb1 ?_
  rw [conjAut_proj, hconj]

theorem conjAut_ne_one_of_anticommute {r : ℕ} (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    {a : StatedSp r F} {B : gsp r F}
    (hAB : ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
          -(((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) :
    conjAut r F B ≠ 1 := by
  classical
  have hnr : NeZero r := ⟨by omega⟩
  let _ : NeZero r := hnr
  intro hB
  set MB : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hMB
  have hline : ∀ v : Fin r ⊕ Fin r → F, v ≠ 0 → ∃ μ : F, MB *ᵥ v = μ • v := by
    intro v hv
    let T : StatedSp r F := spTransvection v (1 : F)
    let x : StatedSp r F := conjSp r F B T
    have hT : proj r F x = proj r F T := by
      have h := congrArg (fun e : MulAut (StatedProj (StatedSp r F)) => e (proj r F T)) hB
      rw [conjAut_proj] at h
      simpa [x] using h
    have hzmem : x * T⁻¹ ∈ spScalars r F := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hT, mul_inv_cancel]
    let z : StatedSp r F := x * T⁻¹
    have hzx : z * T = x := by
      change (x * T⁻¹) * T = x
      group
    have hzmem' : z ∈ spScalars r F := hzmem
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hzmem
    obtain ⟨c, hc⟩ := hzmem
    have hzsp : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r F := by
      rw [hc]
      exact z.2
    have hc2 : c * c = 1 := by
      have := (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hr c).mp hzsp
      simpa [sq] using this
    have hz2 : z * z = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      have hc' : (z : GL (Fin r ⊕ Fin r) F) =
          GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := hc.symm
      rw [hc', ← map_mul, hc2, map_one]
      rfl
    have hx2 : x * x = T * T := by
      have hzcenter : z ∈ Subgroup.center (StatedSp r F) := spScalars_le_center hzmem'
      have hcomm : z * T = T * z := (Subgroup.mem_center_iff.mp hzcenter T).symm
      rw [← hzx]
      calc (z * T) * (z * T) = z * (T * z) * T := by group
        _ = z * (z * T) * T := by rw [hcomm]
        _ = (z * z) * (T * T) := by group
        _ = T * T := by rw [hz2, one_mul]
    have hxform : x = spTransvection (MB *ᵥ v) (((multiplier r F B)⁻¹ : Fˣ) : F) := by
      rw [show x = conjSp r F B (spTransvection v 1) from rfl]
      rw [CFSG.LieType.SeitzGeneration.RootPair.conjSp_spTransvection]
      rw [mul_one]
    have hsqx : x * x = spTransvection (MB *ᵥ v)
        (2 * (((multiplier r F B)⁻¹ : Fˣ) : F)) := by
      rw [hxform, spConf_transvection_mul]
      congr 1
      ring
    have hsqT : T * T = spTransvection v (2 : F) := by
      rw [show T = spTransvection v 1 from rfl, spConf_transvection_mul]
      congr 1
      norm_num
    have heq : spTransvection (MB *ᵥ v)
        (2 * (((multiplier r F B)⁻¹ : Fˣ) : F)) = spTransvection v (2 : F) := by
      rw [← hsqx, hx2, hsqT]
    exact (borel86_spn_exists_smul_of_spTransvection_eq (a := v) (b := MB *ᵥ v)
      (s := 2 * (((multiplier r F B)⁻¹ : Fˣ) : F)) (t := (2 : F)) hv h2 heq).elim
      (fun μ hμ => ⟨μ, hμ.2.1⟩)
  obtain ⟨-, c, hcB⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.eq_one_and_scalar_of_forall_line
      (K := F) hr ((B : GL (Fin r ⊕ Fin r) F)) 1 (by
        intro v hv
        obtain ⟨μ, hμ⟩ := hline v hv
        exact ⟨μ, by simpa using hμ⟩)
  set MA : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hMA
  have hMBscalar : MB = (c : F) • 1 := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) hcB
    rw [GeneralLinearGroup.coe_scalar] at h
    rw [show (Matrix.scalar (Fin r ⊕ Fin r) (c : F)) = (c : F) • 1 by
      rw [Matrix.smul_one_eq_diagonal]; rfl] at h
    simpa [hMB] using h
  have hMAzero : MA = 0 := by
    have h := hAB
    change MA * MB = -(MB * MA) at h
    rw [hMBscalar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul] at h
    have h2c : (2 * (c : F)) • MA = 0 := by
      have := congrArg (fun X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
        X + (c : F) • MA) h
      simpa [two_mul, add_smul] using this
    exact (smul_eq_zero.mp h2c).resolve_left (mul_ne_zero h2 (Units.ne_zero c))
  have hMA1 : MA * ((((a : GL (Fin r ⊕ Fin r) F)⁻¹ : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) = 1 := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) (mul_inv_cancel (a : GL (Fin r ⊕ Fin r) F))
    rw [hMA]
    simpa only [Units.val_mul, Units.val_one, GeneralLinearGroup.coe_mul,
      GeneralLinearGroup.coe_inv] using h
  rw [hMAzero, Matrix.zero_mul] at hMA1
  have hentry := congrFun (congrFun hMA1 (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
  simp at hentry

theorem false_of_isotropic_pair [Finite F] {r : ℕ} (hr : 1 ≤ r)
    {E : Subgroup (MulAut (StatedProj (StatedSp r F)))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {a : StatedSp r F} {B : gsp r F}
    (ha : MulAut.conj (proj r F a) ∈ E) (ha1 : MulAut.conj (proj r F a) ≠ 1)
    (hb : conjAut r F B ∈ E) (hb1 : conjAut r F B ≠ 1)
    (hab : MulAut.conj (proj r F a) ≠ conjAut r F B)
    (hnoW : ∀ W : Submodule F (Fin r ⊕ Fin r → F), (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) →
      (∀ A : gsp r F, conjAut r F A ∈ E →
        ∀ w ∈ W, ((A : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W) → W = ⊥)
    {x y : Fin r ⊕ Fin r → F} (hx0 : x ≠ 0) (hxy : spForm r F x y = 0)
    (hax : ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ x ∈
      Submodule.span F {x, y})
    (hay : ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ y ∈
      Submodule.span F {x, y})
    (hbx : ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ x ∈
      Submodule.span F {x, y})
    (hby : ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ y ∈
      Submodule.span F {x, y}) :
    False := by
  classical
  set W : Submodule F (Fin r ⊕ Fin r → F) := Submodule.span F {x, y} with hW
  have hxx : spForm r F x x = 0 := spForm_isAlt.self_eq_zero x
  have hyy : spForm r F y y = 0 := spForm_isAlt.self_eq_zero y
  have hyx : spForm r F y x = 0 := by
    rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt x y, hxy, neg_zero]
  have hiso : ∀ u ∈ W, ∀ v ∈ W, spForm r F u v = 0 := by
    intro u hu v hv
    rw [hW] at hu hv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hv
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxx, hyy, hxy, hyx, mul_zero, add_zero]
  have hWa : ∀ w ∈ W, ((a : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W := by
    intro w hw
    rw [hW] at hw ⊢
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ α hax) (Submodule.smul_mem _ β hay)
  have hWB : ∀ w ∈ W, ((B : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W := by
    intro w hw
    rw [hW] at hw ⊢
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ α hbx) (Submodule.smul_mem _ β hby)
  have hstable' : ∀ A : gsp r F, conjAut r F A ∈ E →
      ∀ w ∈ W, ((A : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W :=
    lift_mulVec_mem_of_stable (F := F) (r := r) hr hE h4 ha ha1 hb hb1 hab hWa hWB
  have hbot : W = ⊥ := hnoW W hiso hstable'
  have hxW : x ∈ W := by rw [hW]; exact Submodule.subset_span (by simp)
  rw [hbot] at hxW
  exact hx0 (by simpa using hxW)

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
