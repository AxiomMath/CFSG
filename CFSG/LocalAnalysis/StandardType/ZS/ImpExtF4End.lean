module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtDeg
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Irred
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankThree
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankThreeCard
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankFour
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Weyl
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtAdapted
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4B3
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtH3Gen
import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtNonMonomial
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelBasic
import CFSG.LocalAnalysis.StandardType.ZS.InitialPair
import Mathlib.Tactic.ReduceModChar

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem toMatrix_inj_four [Module.Finite (ZMod p) U] {f : Module.Basis (Fin 4) (ZMod p) U}
    {x y : U ≃ₗ[ZMod p] U}
    (h : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (y : U →ₗ[ZMod p] U)) : x = y :=
  LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix f f).injective h)

private theorem zs4k_toMatrix_unitsSMul_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (w : Fin n → (ZMod p)ˣ) (x : U →ₗ[ZMod p] U) (r c : Fin n) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) x r c =
      (((w r)⁻¹ : (ZMod p)ˣ) : ZMod p) * LinearMap.toMatrix f f x r c *
        ((w c : (ZMod p)ˣ) : ZMod p) := by
  simp only [LinearMap.toMatrix_apply, Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply,
    Units.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

private theorem zs4k_toMatrix_unitsSMul_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (w : Fin n → (ZMod p)ˣ) (x : U →ₗ[ZMod p] U)
    (hw : ∀ r c, LinearMap.toMatrix f f x r c ≠ 0 → w r = w c) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) x = LinearMap.toMatrix f f x := by
  ext r c
  rw [zs4k_toMatrix_unitsSMul_apply]
  by_cases h : LinearMap.toMatrix f f x r c = 0
  · rw [h, mul_zero, zero_mul]
  · rw [hw r c h, mul_right_comm, Units.inv_mul, one_mul]

private lemma zs4k_w_eq (ε : (ZMod p)ˣ) {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hM : ∀ i : Fin 4, i ≠ 3 → M i 3 = 0 ∧ M 3 i = 0) (r c : Fin 4) (h : M r c ≠ 0) :
    (![1, 1, 1, ε] : Fin 4 → (ZMod p)ˣ) r = ![1, 1, 1, ε] c := by
  have key : ∀ i : Fin 4, i ≠ 3 → (![1, 1, 1, ε] : Fin 4 → (ZMod p)ˣ) i = 1 := by
    intro i hi
    fin_cases i <;> first | rfl | exact absurd rfl hi
  by_cases hr : r = 3 <;> by_cases hc : c = 3
  · rw [hr, hc]
  · subst hr
    exact absurd (hM c hc).2 h
  · subst hc
    exact absurd (hM r hr).1 h
  · rw [key r hr, key c hc]

private lemma zs4k_block_diagSign :
    ∀ i : Fin 4, i ≠ 3 → (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) i 3 = 0 ∧
      (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) 3 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all [diagSignMat]

private lemma zs4k_block_pij01 :
    ∀ i : Fin 4, i ≠ 3 → (pijMat (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) i 3 = 0 ∧
      (pijMat (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 3 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all [pijMat]

private lemma zs4k_block_pij12 :
    ∀ i : Fin 4, i ≠ 3 → (pijMat (1 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) i 3 = 0 ∧
      (pijMat (1 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 3 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all [pijMat]

private lemma zs4k_unitsSMul_castSucc (f : Module.Basis (Fin 4) (ZMod p) U) (ε : (ZMod p)ˣ)
    (i : Fin 3) : (f.unitsSMul ![1, 1, 1, ε]) i.castSucc = f i.castSucc := by
  rw [Module.Basis.unitsSMul_apply]
  fin_cases i <;> simp

private lemma zs4k_unitsSMul_three (f : Module.Basis (Fin 4) (ZMod p) U) (ε : (ZMod p)ˣ) :
    (f.unitsSMul ![1, 1, 1, ε]) (3 : Fin 4) = ε • f (3 : Fin 4) := by
  rw [Module.Basis.unitsSMul_apply]; simp

private lemma zs4k_span_eq (f : Module.Basis (Fin 4) (ZMod p) U) (ε : (ZMod p)ˣ) :
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => (f.unitsSMul ![1, 1, 1, ε]) i.castSucc) =
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  congr 1
  ext v
  simp only [Set.mem_range]
  constructor <;> rintro ⟨i, rfl⟩
  · exact ⟨i, by rw [zs4k_unitsSMul_castSucc]⟩
  · exact ⟨i, by rw [zs4k_unitsSMul_castSucc]⟩

private lemma zs4k_apply_not_mem (f : Module.Basis (Fin 4) (ZMod p) U) (ε : (ZMod p)ˣ)
    {g : U ≃ₗ[ZMod p] U} (h : g (f 3) ∉ Submodule.span (ZMod p) {f 3}) :
    g ((f.unitsSMul ![1, 1, 1, ε]) 3) ∉
      Submodule.span (ZMod p) {(f.unitsSMul ![1, 1, 1, ε]) 3} := by
  rw [zs4k_unitsSMul_three]
  intro hmem
  apply h
  rw [Units.smul_def, map_smul] at hmem
  have hspan : Submodule.span (ZMod p) {(ε : ZMod p) • f 3} =
      Submodule.span (ZMod p) {f 3} :=
    Submodule.span_singleton_smul_eq (Units.isUnit ε) (f 3)
  rw [hspan] at hmem
  simpa using (Submodule.smul_mem_iff' (p := Submodule.span (ZMod p) {f 3}) ε).mp hmem

private theorem zs4k_movedSpace_conj (x r : U ≃ₗ[ZMod p] U) :
    HardMathSupport.Kantor79.movedSpace (x * r * x⁻¹) =
      (HardMathSupport.Kantor79.movedSpace r).map (x : U →ₗ[ZMod p] U) := by
  ext v
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨r (x⁻¹ y) - x⁻¹ y, ⟨x⁻¹ y, rfl⟩, by simp [mul_assoc]⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨x z, by simp [mul_assoc]⟩

private theorem zs4k_movedSpace_map_of_commute (x r : U ≃ₗ[ZMod p] U)
    (hcomm : x * r = r * x) :
    (HardMathSupport.Kantor79.movedSpace r).map (x : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.movedSpace r := by
  have hx : x * r * x⁻¹ = r := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [← zs4k_movedSpace_conj x r, hx]

private lemma zs4k_card_of_433 [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (hU : Module.finrank (ZMod p) U = 4)
    {x y z : U ≃ₗ[ZMod p] U} {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hx : IsRefl p x) (hy : IsRefl p y) (hz : IsRefl p z)
    (hX : X = Subgroup.closure {x, y, z})
    (hAt : QTwoLin.TransvectionFree X)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3)
    (hd : DMax p X 4)
    (hxy : orderOf (x * y) = 4) (hxz : orderOf (x * z) = 3) (hyz : orderOf (y * z) = 3) :
    SplitSupport X 3 ∧ 48 < Nat.card X := by
  obtain ⟨hm2, hm4⟩ := two_le_orderOf_cacb hp hU hx hy hz hX hdim hd
  have hmne2 := orderOf_cacb_ne_two_of_433 hp hU hx hy hz hX hAt hdim hd hxy hxz hyz
  have hm : orderOf (z * x * z * y) = 3 ∨ orderOf (z * x * z * y) = 4 := by omega
  rcases hm with hm3 | hm4eq
  · obtain ⟨hss, e, ζ, hζ, hmg⟩ :=
      eq_gmmn_of_433 hp hU hx hy hz hX hAt hdim hd hxy hxz hyz hm3
    have h96 : Nat.card X = 96 := by
      rw [← card_movedGroup_of_splitSupport hss, hmg, card_gmmn (by norm_num) e (by decide) ζ,
        hζ]
      norm_num
    exact ⟨hss, by omega⟩
  · obtain ⟨hss, h336⟩ :=
      card_eq_of_433 hp hU hx hy hz hX hAt hdim hd hxy hxz hyz hm4eq
    exact ⟨hss, by omega⟩

structure FFourData (f : Module.Basis (Fin 4) (ZMod p) U) (a b c g : U ≃ₗ[ZMod p] U)
    (H G : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  toMatrix_a : LinearMap.toMatrix f f a.toLinearMap = diagSignMat 0
  toMatrix_b : LinearMap.toMatrix f f b.toLinearMap = pijMat 0 1 1
  toMatrix_c : LinearMap.toMatrix f f c.toLinearMap = pijMat 1 2 1
  H_eq : H = Subgroup.closure {a, b, c}
  H_le : H ≤ G
  g_mem : g ∈ G
  isRefl_g : IsRefl p g
  map_ne : (Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)).map
    g.toLinearMap ≠ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)
  apply_not_mem : g (f 3) ∉ Submodule.span (ZMod p) {f 3}
  irred : ∀ W : Submodule (ZMod p) U,
    (∀ x ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, x w ∈ W) →
      W = ⊥ ∨ W = ⊤
  reflGen : ReflGen p G
  primitive : ¬ Quasithin.SimsG4.IsImprimitiveOnV G
  transvectionFree : QTwoLin.TransvectionFree G
  dmax : DMax p G 4
  splitOfIrred : SplitOfIrred p G 3
  maximal : ∀ X ≤ G, ReflGen p X → SplitSupport X 3 → DMax p X 4 → Nat.card X ≤ 48
  inH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H

private def zs4kV (f : Module.Basis (Fin 4) (ZMod p) U) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)

private lemma zs4k_apply_eq (f : Module.Basis (Fin 4) (ZMod p) U) {x : U ≃ₗ[ZMod p] U}
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hx : LinearMap.toMatrix f f x.toLinearMap = M) (j : Fin 4) :
    (x : U →ₗ[ZMod p] U) (f j) = ∑ i, M i j • f i := by
  rw [← Matrix.toLin_toMatrix f f (x : U →ₗ[ZMod p] U), hx, Matrix.toLin_self]

private lemma zs4k_apply_three (f : Module.Basis (Fin 4) (ZMod p) U) {x : U ≃ₗ[ZMod p] U}
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hx : LinearMap.toMatrix f f x.toLinearMap = M)
    (hcol : ∀ i : Fin 4, i ≠ 3 → M i 3 = 0) (h33 : M (3 : Fin 4) 3 = 1) :
    x (f 3) = f 3 := by
  change (x : U →ₗ[ZMod p] U) (f 3) = f 3
  rw [zs4k_apply_eq f hx 3, Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin 3, M i.castSucc 3 = 0 := fun i => hcol i.castSucc (Fin.castSucc_ne_last i)
  have h33' : M (Fin.last 3) 3 = 1 := by simpa using h33
  simp only [h0, zero_smul, Finset.sum_const_zero, zero_add, h33', one_smul]
  congr 1

private lemma zs4k_apply_castSucc_mem (f : Module.Basis (Fin 4) (ZMod p) U)
    {x : U ≃ₗ[ZMod p] U} {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hx : LinearMap.toMatrix f f x.toLinearMap = M)
    (h34 : ∀ i : Fin 3, M (3 : Fin 4) i.castSucc = 0) (j : Fin 3) :
    x (f j.castSucc) ∈
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  change (x : U →ₗ[ZMod p] U) (f j.castSucc) ∈
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)
  rw [zs4k_apply_eq f hx j.castSucc, Fin.sum_univ_castSucc]
  have h : M (Fin.last 3) j.castSucc = 0 := by simpa using h34 j
  rw [h, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma zs4k_H_invariant {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c : U ≃ₗ[ZMod p] U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : H = Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)))
    (hsa : a * a = 1) (hsb : b * b = 1) (hsc : c * c = 1)
    (ha : (zs4kV f).map (a : U →ₗ[ZMod p] U) ≤ zs4kV f) (ha3 : a (f 3) = f 3)
    (hb : (zs4kV f).map (b : U →ₗ[ZMod p] U) ≤ zs4kV f) (hb3 : b (f 3) = f 3)
    (hc : (zs4kV f).map (c : U →ₗ[ZMod p] U) ≤ zs4kV f) (hc3 : c (f 3) = f 3) :
    ∀ k ∈ H, (zs4kV f).map (k : U →ₗ[ZMod p] U) ≤ zs4kV f ∧
      (zs4kV f).map ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤ zs4kV f ∧
        k (f 3) = f 3 := by
  rw [hH]
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [((inv_eq_iff_mul_eq_one).mpr hsa)]; exact ⟨ha, ha, ha3⟩
    · rw [((inv_eq_iff_mul_eq_one).mpr hsb)]; exact ⟨hb, hb, hb3⟩
    · rw [((inv_eq_iff_mul_eq_one).mpr hsc)]; exact ⟨hc, hc, hc3⟩
  | one => exact ⟨by simp, by simp, rfl⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨?_, ?_, ?_⟩
    · rw [LinearEquiv.coe_toLinearMap_mul]
      change (zs4kV f).map ((x : U →ₗ[ZMod p] U).comp (y : U →ₗ[ZMod p] U)) ≤ zs4kV f
      rw [Submodule.map_comp]
      exact (Submodule.map_mono ihy.1).trans ihx.1
    · have h1 : ((x * y)⁻¹ : U ≃ₗ[ZMod p] U) = y⁻¹ * x⁻¹ := mul_inv_rev x y
      rw [h1]
      rw [LinearEquiv.coe_toLinearMap_mul]
      change (zs4kV f).map (((y⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
        ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) ≤ zs4kV f
      rw [Submodule.map_comp]
      exact (Submodule.map_mono ihx.2.1).trans ihy.2.1
    · show (x * y) (f 3) = f 3
      rw [LinearEquiv.mul_apply, ihy.2.2, ihx.2.2]
  | inv x _ ihx =>
    refine ⟨ihx.2.1, ihx.1, ?_⟩
    have h := congrArg (fun v => (x⁻¹ : U ≃ₗ[ZMod p] U) v) ihx.2.2
    simpa [LinearEquiv.symm_apply_apply] using h.symm

private lemma zs4k_gen_data {f : Module.Basis (Fin 4) (ZMod p) U} {x : U ≃ₗ[ZMod p] U}
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hx : LinearMap.toMatrix f f x.toLinearMap = M)
    (hM : ∀ i : Fin 4, i ≠ 3 → M i 3 = 0 ∧ M 3 i = 0) (h33 : M (3 : Fin 4) 3 = 1) :
    x (f 3) = f 3 ∧ (zs4kV f).map (x : U →ₗ[ZMod p] U) ≤ zs4kV f := by
  have hcol : ∀ i : Fin 4, i ≠ 3 → M i 3 = 0 := fun i hi => (hM i hi).1
  have hrow : ∀ i : Fin 3, M (3 : Fin 4) i.castSucc = 0 :=
    fun i => (hM i.castSucc (Fin.castSucc_ne_last i)).2
  refine ⟨zs4k_apply_three f hx hcol h33, ?_⟩
  simp only [zs4kV]
  rw [Submodule.map_span, Submodule.span_le]
  rintro v ⟨u, ⟨j, rfl⟩, rfl⟩
  exact zs4k_apply_castSucc_mem f hx hrow j

private lemma zs4k_a_sq {f : Module.Basis (Fin 4) (ZMod p) U} {a : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f a.toLinearMap = diagSignMat 0) : a * a = 1 := by
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul, ha, diagSignMat_mul_self]
  simp

private lemma zs4k_b_sq {f : Module.Basis (Fin 4) (ZMod p) U} {b : U ≃ₗ[ZMod p] U}
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 0 1 1) : b * b = 1 := by
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul, hb, pijMat_mul_self (i := 0) (j := 1) (by decide) one_ne_zero]
  simp

private lemma zs4k_c_sq {f : Module.Basis (Fin 4) (ZMod p) U} {c : U ≃ₗ[ZMod p] U}
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 1 2 1) : c * c = 1 := by
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul, hc, pijMat_mul_self (i := 1) (j := 2) (by decide) one_ne_zero]
  simp

namespace FFourData

variable [Module.Finite (ZMod p) U] {f : Module.Basis (Fin 4) (ZMod p) U}
  {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}

private lemma zs4k_commutatorSpace_closure_three_eq {x y g : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({x, y, g} : Set (U ≃ₗ[ZMod p] U))) =
      HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y ⊔
        HardMathSupport.Kantor79.movedSpace g := by
  have hx : ({x, y, g} : Set (U ≃ₗ[ZMod p] U)) =
      Set.range (![x, y, g] : Fin 3 → U ≃ₗ[ZMod p] U) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hx, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace, iSup_fin_three]
  simp

private lemma zs4k_finrank_sup_two {x y : U ≃ₗ[ZMod p] U} (hx : IsRefl p x) (hy : IsRefl p y)
    (hxy : HardMathSupport.Kantor79.movedSpace x ≠ HardMathSupport.Kantor79.movedSpace y) :
    Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y) = 2 := by
  have hx1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace x) = 1 := hx.2
  have hy1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace y) = 1 := hy.2
  have hinf0 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace x ⊓
      HardMathSupport.Kantor79.movedSpace y) = 0 := by
    rcases Nat.eq_zero_or_pos _ with h0 | hpos
    · exact h0
    · exfalso
      have hle1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace x ⊓
          HardMathSupport.Kantor79.movedSpace y) ≤ 1 := by
        rw [← hx1]; exact Submodule.finrank_mono inf_le_left
      have h1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace x ⊓
          HardMathSupport.Kantor79.movedSpace y) = 1 := by omega
      have heq : HardMathSupport.Kantor79.movedSpace x ⊓ HardMathSupport.Kantor79.movedSpace y =
          HardMathSupport.Kantor79.movedSpace x :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hx1])
      exact hxy (Submodule.eq_of_le_of_finrank_eq (heq ▸ inf_le_right) (by rw [hx1, hy1]))
  have hfs := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.movedSpace x) (HardMathSupport.Kantor79.movedSpace y)
  rw [hx1, hy1, hinf0, add_zero] at hfs
  omega

private lemma zs4k_inf_sup_two_moved {x y g : U ≃ₗ[ZMod p] U}
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ zs4kV f)
    (hyV : HardMathSupport.Kantor79.movedSpace y ≤ zs4kV f) (hg : IsRefl p g)
    (hgnot : ¬ HardMathSupport.Kantor79.movedSpace g ≤ zs4kV f) :
    (HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y) ⊓
      HardMathSupport.Kantor79.movedSpace g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_contra hz0
  have hzg : z ∈ HardMathSupport.Kantor79.movedSpace g := hz.2
  have hzP : z ∈ HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y :=
    hz.1
  have hg1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace g) = 1 := hg.2
  have heq : Submodule.span (ZMod p) {z} = HardMathSupport.Kantor79.movedSpace g :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzg))
      (by rw [finrank_span_singleton hz0, hg1])
  have hle : HardMathSupport.Kantor79.movedSpace g ≤
      HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y := by
    rw [← heq]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzP)
  exact hgnot (hle.trans (sup_le hxV hyV))

private lemma zs4k_finrank_closure_two_VH
    {x y g : U ≃ₗ[ZMod p] U} (hx : IsRefl p x) (hy : IsRefl p y) (hg : IsRefl p g)
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ zs4kV f)
    (hyV : HardMathSupport.Kantor79.movedSpace y ≤ zs4kV f)
    (hxy : HardMathSupport.Kantor79.movedSpace x ≠ HardMathSupport.Kantor79.movedSpace y)
    (hgnot : ¬ HardMathSupport.Kantor79.movedSpace g ≤ zs4kV f) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({x, y, g} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
  rw [zs4k_commutatorSpace_closure_three_eq]
  have h2 := zs4k_finrank_sup_two hx hy hxy
  have hinf := zs4k_inf_sup_two_moved hxV hyV hg hgnot
  have hg1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace g) = 1 := hg.2
  have hfs := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y)
    (HardMathSupport.Kantor79.movedSpace g)
  rw [h2, hg1, hinf, finrank_bot, add_zero] at hfs
  omega

private lemma zs4k_finrank_closure_three (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hgR : IsRefl p g := h.isRefl_g
  obtain ⟨v, w, hgm, hwv⟩ := FFourCoord.exists_toMatrix_of_isRefl hp f hgR
  have hv3 : v 3 ≠ 0 := FFourCoord.apply_three_ne_zero_of_map_ne f hgm hwv h.map_ne
  have hgnot : ¬ HardMathSupport.Kantor79.movedSpace g ≤ zs4kV f :=
    FFourCoord.not_movedSpace_le_span_of_toMatrix hp f hgm hwv hv3
  have haVH : HardMathSupport.Kantor79.movedSpace a ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]) (by simp)
  have hbVH : HardMathSupport.Kantor79.movedSpace b ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]) (by simp)
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hab : a ≠ b := by
    intro hab
    have hmat : (diagSignMat 0 : Matrix (Fin 4) (Fin 4) (ZMod p)) = pijMat 0 1 1 := by
      rw [← h.toMatrix_a, ← h.toMatrix_b, hab]
    have h00 := congrFun (congrFun hmat 0) 0
    simp [diagSignMat, pijMat] at h00
  have hma_ne : HardMathSupport.Kantor79.movedSpace a ≠
      HardMathSupport.Kantor79.movedSpace b := fun heq =>
    hab (eq_of_movedSpace_eq hp h.transvectionFree (h.H_le haH) (h.H_le hbH) haR hbR heq)
  exact zs4k_finrank_closure_two_VH haR hbR hgR haVH hbVH hma_ne hgnot

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_not_movedSpace_g (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    ¬ HardMathSupport.Kantor79.movedSpace g ≤ zs4kV f := by
  obtain ⟨v, w, hgm, hwv⟩ := FFourCoord.exists_toMatrix_of_isRefl hp f h.isRefl_g
  have hv3 : v 3 ≠ 0 := FFourCoord.apply_three_ne_zero_of_map_ne f hgm hwv h.map_ne
  exact FFourCoord.not_movedSpace_le_span_of_toMatrix hp f hgm hwv hv3

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_map_castSucc_le {f : Module.Basis (Fin 4) (ZMod p) U} {x : U ≃ₗ[ZMod p] U}
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hx : LinearMap.toMatrix f f x.toLinearMap = M)
    (h34 : ∀ i : Fin 3, M (3 : Fin 4) i.castSucc = 0) :
    (zs4kV f).map (x : U →ₗ[ZMod p] U) ≤ zs4kV f := by
  rw [zs4kV, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
  exact zs4k_apply_castSucc_mem f hx h34 i

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_conj_data {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) {k : U ≃ₗ[ZMod p] U} (hk : k ∈ H) :
    (zs4kV f).map (k : U →ₗ[ZMod p] U) = zs4kV f ∧
      (zs4kV f).map ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = zs4kV f ∧
      k (f 3) = f 3 ∧ (k⁻¹ : U ≃ₗ[ZMod p] U) (f 3) = f 3 := by
  obtain ⟨ha3, haW⟩ :=
    zs4k_gen_data (f := f) h.toMatrix_a zs4k_block_diagSign (by simp [diagSignMat])
  obtain ⟨hb3, hbW⟩ := zs4k_gen_data (f := f) h.toMatrix_b zs4k_block_pij01 (by simp [pijMat])
  obtain ⟨hc3, hcW⟩ := zs4k_gen_data (f := f) h.toMatrix_c zs4k_block_pij12 (by simp [pijMat])
  have hP := zs4k_H_invariant (f := f) h.H_eq (zs4k_a_sq (f := f) h.toMatrix_a)
    (zs4k_b_sq (f := f) h.toMatrix_b) (zs4k_c_sq (f := f) h.toMatrix_c) haW ha3 hbW hb3 hcW hc3
  obtain ⟨hkW, hkWinv, hk3⟩ := hP k hk
  obtain ⟨_, _, hk3inv⟩ := hP k⁻¹ (H.inv_mem hk)
  have hkWeq : (zs4kV f).map (k : U →ₗ[ZMod p] U) = zs4kV f := by
    refine le_antisymm hkW ?_
    have h1 : (zs4kV f).map ((k : U →ₗ[ZMod p] U).comp
        ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) = zs4kV f := by
      have h2 : ((k : U →ₗ[ZMod p] U).comp ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) =
          LinearMap.id := by
        change (k : U →ₗ[ZMod p] U) * ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id
        rw [← LinearEquiv.coe_toLinearMap_mul]; simp
      rw [h2, Submodule.map_id]
    rw [Submodule.map_comp] at h1
    exact h1.symm.le.trans (Submodule.map_mono hkWinv)
  have hkWinvEq : (zs4kV f).map ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = zs4kV f := by
    refine le_antisymm hkWinv ?_
    have h1 : (zs4kV f).map (((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
        (k : U →ₗ[ZMod p] U)) = zs4kV f := by
      have h2 : (((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp (k : U →ₗ[ZMod p] U)) =
          LinearMap.id := by
        change ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) * (k : U →ₗ[ZMod p] U) = LinearMap.id
        rw [← LinearEquiv.coe_toLinearMap_mul]; simp
      rw [h2, Submodule.map_id]
    rw [Submodule.map_comp] at h1
    exact h1.symm.le.trans (Submodule.map_mono hkW)
  exact ⟨hkWeq, hkWinvEq, hk3, hk3inv⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_conj_map_ne {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) {k : U ≃ₗ[ZMod p] U}
    (hkWeq : (zs4kV f).map (k : U →ₗ[ZMod p] U) = zs4kV f)
    (hkWinvEq : (zs4kV f).map ((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = zs4kV f) :
    (zs4kV f).map ((k * g * k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≠ zs4kV f := by
  intro hc
  have e : k⁻¹ * (k * g * k⁻¹) * k = g := by group
  have hc' : (zs4kV f).map ((k * g * k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = zs4kV f := hc
  have hthis : (zs4kV f).map (g : U →ₗ[ZMod p] U) = zs4kV f := by
    rw [← e]
    change (zs4kV f).map (((k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
      (((k * g * k⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp (k : U →ₗ[ZMod p] U))) = zs4kV f
    rw [Submodule.map_comp, Submodule.map_comp, hkWeq, hc', hkWinvEq]
  exact h.map_ne hthis

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_conj_apply_not_mem {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) {k : U ≃ₗ[ZMod p] U}
    (hk3inv : (k⁻¹ : U ≃ₗ[ZMod p] U) (f 3) = f 3) :
    (k * g * k⁻¹) (f 3) ∉ Submodule.span (ZMod p) {f 3} := by
  intro hm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hm
  refine h.apply_not_mem (Submodule.mem_span_singleton.2 ⟨t, ?_⟩)
  have h1 : (k * g * k⁻¹) (f 3) = k (g (f 3)) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hk3inv]
  have h3 := congrArg (fun v => (k⁻¹ : U ≃ₗ[ZMod p] U) v) ht
  rw [h1] at h3
  have hkapp : (k⁻¹ : U ≃ₗ[ZMod p] U) (k (g (f 3))) = g (f 3) :=
    LinearEquiv.symm_apply_apply k (g (f 3))
  rw [hkapp] at h3
  simpa only [map_smul, hk3inv] using h3

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_conj_irred {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) {k : U ≃ₗ[ZMod p] U} (hk : k ∈ H) :
    ∀ W : Submodule (ZMod p) U,
      (∀ x ∈ Subgroup.closure (insert (k * g * k⁻¹) (H : Set (U ≃ₗ[ZMod p] U))),
        ∀ w ∈ W, x w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hWinv
  apply h.irred W
  intro x hx w hw
  apply hWinv x ?_ w hw
  have hle : Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))) ≤
      Subgroup.closure (insert (k * g * k⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | hy)
    · rw [hy]
      have h1 : (k * g * k⁻¹) ∈
          Subgroup.closure (insert (k * g * k⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have h2 : k ∈ Subgroup.closure (insert (k * g * k⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ hk)
      have h3 : k⁻¹ ∈ Subgroup.closure (insert (k * g * k⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (H.inv_mem hk))
      have hgk : g = k⁻¹ * (k * g * k⁻¹) * k := by group
      have hmem : k⁻¹ * (k * g * k⁻¹) * k ∈
          Subgroup.closure (insert (k * g * k⁻¹) (H : Set (U ≃ₗ[ZMod p] U))) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 h1) h2
      rwa [← hgk] at hmem
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hy)
  exact hle hx

omit [Module.Finite (ZMod p) U] in
theorem conj (h : FFourData f a b c g H G) {k : U ≃ₗ[ZMod p] U} (hk : k ∈ H) :
    FFourData f a b c (k * g * k⁻¹) H G := by
  obtain ⟨hkWeq, hkWinvEq, _, hk3inv⟩ := zs4k_conj_data h hk
  refine ⟨h.toMatrix_a, h.toMatrix_b, h.toMatrix_c, h.H_eq, h.H_le,
    G.mul_mem (G.mul_mem (h.H_le hk) h.g_mem) (G.inv_mem (h.H_le hk)), ?_, ?_, ?_, ?_,
    h.reflGen, h.primitive, h.transvectionFree, h.dmax, h.splitOfIrred, h.maximal, h.inH⟩
  · exact IsRefl.conj h.isRefl_g k
  · exact zs4k_conj_map_ne h hkWeq hkWinvEq
  · exact zs4k_conj_apply_not_mem h hk3inv
  · exact zs4k_conj_irred h hk

omit [Module.Finite (ZMod p) U] in
theorem rescale (h : FFourData f a b c g H G) (ε : (ZMod p)ˣ) :
    FFourData (f.unitsSMul ![1, 1, 1, ε]) a b c g H G := by
  have hspan := zs4k_span_eq f ε
  refine ⟨?_, ?_, ?_, h.H_eq, h.H_le, h.g_mem, h.isRefl_g, ?_, ?_, h.irred, h.reflGen,
    h.primitive, h.transvectionFree, h.dmax, h.splitOfIrred, h.maximal, ?_⟩
  · rw [zs4k_toMatrix_unitsSMul_eq f _ a
      (fun r c hrc => zs4k_w_eq ε zs4k_block_diagSign r c (by rwa [h.toMatrix_a] at hrc))]
    exact h.toMatrix_a
  · rw [zs4k_toMatrix_unitsSMul_eq f _ b
      (fun r c hrc => zs4k_w_eq ε zs4k_block_pij01 r c (by rwa [h.toMatrix_b] at hrc))]
    exact h.toMatrix_b
  · rw [zs4k_toMatrix_unitsSMul_eq f _ c
      (fun r c hrc => zs4k_w_eq ε zs4k_block_pij12 r c (by rwa [h.toMatrix_c] at hrc))]
    exact h.toMatrix_c
  · rw [hspan]; exact h.map_ne
  · exact zs4k_apply_not_mem f ε h.apply_not_mem
  · intro x hx hxr hxle
    exact h.inH x hx hxr (by rwa [hspan] at hxle)

private noncomputable def zs4kW (_f : Module.Basis (Fin 4) (ZMod p) U) (a b c : U ≃ₗ[ZMod p] U) :
    Submodule (ZMod p) U :=
  HardMathSupport.Kantor79.movedSpace (a * b * a) ⊔
    HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) ⊔
    HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c)

private lemma zs4k_moved_aba (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) :
    HardMathSupport.Kantor79.movedSpace (a * b * a) = Submodule.span (ZMod p) {f 0 + f 1} ∧
    HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∧
    HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by
  have hRa : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hRb : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hRa.1
  have hRr : IsRefl p (a * b * a) := by
    have h' := hRb.conj a
    rwa [ha_inv] at h'
  have hmat_r : LinearMap.toMatrix f f ((a * b * a : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      diagSignMat 0 * pijMat 0 1 1 * diagSignMat 0 := by
    rw [toMatrix_coe_mul f, toMatrix_coe_mul f, h.toMatrix_a, h.toMatrix_b]
  have hr0 : (a * b * a) (f 0) = - f 1 := by
    show ((a * b * a : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (f 0) = - f 1
    rw [zs4k_apply_eq f hmat_r 0, Fin.sum_univ_four]
    simp [Matrix.mul_apply, Fin.sum_univ_four, diagSignMat, pijMat]
  have he0 : f 0 + f 1 ≠ 0 := by
    intro hzero
    have hc := congrArg f.repr hzero
    simp only [map_add, map_zero, Module.Basis.repr_self] at hc
    have h0 := congrArg (fun w : Fin 4 →₀ ZMod p => w 0) hc
    simp at h0
  refine ⟨?_, ?_, ?_⟩
  · have hmem : f 0 + f 1 ∈ HardMathSupport.Kantor79.movedSpace (a * b * a) := by
      refine ⟨-f 0, ?_⟩
      change (a * b * a) (-f 0) - (-f 0) = f 0 + f 1
      rw [map_neg, hr0]
      abel
    have hle : Submodule.span (ZMod p) {f 0 + f 1} ≤
        HardMathSupport.Kantor79.movedSpace (a * b * a) :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace (a * b * a)) = 1 :=
      hRr.2
    rw [hfin, finrank_span_singleton he0]
  · simpa using zs4k_movedSpace_conj a⁻¹ (a * b * a)
  · simpa using zs4k_movedSpace_conj c⁻¹ (a * b * a)

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_a_c_actions {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) :
    a (f 0) = - f 0 ∧ a (f 1) = f 1 ∧ c (f 0) = f 0 ∧ c (f 1) = f 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((a : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (f 0) = - f 0
    rw [zs4k_apply_eq f h.toMatrix_a 0, Fin.sum_univ_four]
    simp [diagSignMat]
  · show ((a : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (f 1) = f 1
    rw [zs4k_apply_eq f h.toMatrix_a 1, Fin.sum_univ_four]
    simp [diagSignMat]
  · show ((c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (f 0) = f 0
    rw [zs4k_apply_eq f h.toMatrix_c 0, Fin.sum_univ_four]
    simp [pijMat]
  · show ((c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (f 1) = f 2
    rw [zs4k_apply_eq f h.toMatrix_c 1, Fin.sum_univ_four]
    simp [pijMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_finrank_VH (f : Module.Basis (Fin 4) (ZMod p) U) :
    Module.finrank (ZMod p) (zs4kV f) = 3 := by
  have hLI : LinearIndependent (ZMod p) (fun i : Fin 3 => f i.castSucc) :=
    f.linearIndependent.comp (fun i : Fin 3 => i.castSucc) (Fin.castSucc_injective 3)
  have h := finrank_span_eq_card hLI
  change Module.finrank (ZMod p) (Submodule.span (ZMod p)
    (Set.range fun i : Fin 3 => f i.castSucc)) = 3
  exact h

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_sup_abc_eq_VH (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace b ⊔
      HardMathSupport.Kantor79.movedSpace c = zs4kV f := by
  obtain ⟨ha0, ha1, hc0, hc1⟩ := zs4k_a_c_actions h
  have hb0 : b (f 0) = f 1 := by
    show ((b : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (f 0) = f 1
    rw [zs4k_apply_eq f h.toMatrix_b 0, Fin.sum_univ_four]
    simp [pijMat]
  have haVH : HardMathSupport.Kantor79.movedSpace a ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]) (by simp)
  have hbVH : HardMathSupport.Kantor79.movedSpace b ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]) (by simp)
  have hcVH : HardMathSupport.Kantor79.movedSpace c ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]) (by simp)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hf0 : f 0 ∈ HardMathSupport.Kantor79.movedSpace a := by
    refine ⟨-((2 : ZMod p)⁻¹) • f 0, ?_⟩
    change a ((-(2 : ZMod p)⁻¹) • f 0) - ((-(2 : ZMod p)⁻¹) • f 0) = f 0
    rw [neg_smul, map_neg, map_smul, ha0, smul_neg, neg_neg, sub_neg_eq_add, ← add_smul,
      show (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 by rw [← two_mul, mul_inv_cancel₀ h2],
      one_smul]
  have hf1 : f 1 ∈ HardMathSupport.Kantor79.movedSpace a ⊔
      HardMathSupport.Kantor79.movedSpace b := by
    have h1 : f 1 - f 0 ∈ HardMathSupport.Kantor79.movedSpace b :=
      ⟨f 0, by change b (f 0) - f 0 = f 1 - f 0; rw [hb0]⟩
    rw [show f 1 = f 0 + (f 1 - f 0) by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hf0) (Submodule.mem_sup_right h1)
  have hf2 : f 2 ∈ HardMathSupport.Kantor79.movedSpace a ⊔
      HardMathSupport.Kantor79.movedSpace b ⊔ HardMathSupport.Kantor79.movedSpace c := by
    have h1 : f 2 - f 1 ∈ HardMathSupport.Kantor79.movedSpace c :=
      ⟨f 1, by change c (f 1) - f 1 = f 2 - f 1; rw [hc1]⟩
    rw [show f 2 = f 1 + (f 2 - f 1) by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hf1) (Submodule.mem_sup_right h1)
  refine le_antisymm (sup_le (sup_le haVH hbVH) hcVH) ?_
  rw [zs4kV]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left hf0)
  · exact Submodule.mem_sup_left hf1
  · exact hf2

private lemma zs4k_VH_inf_movedSpace_g (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    zs4kV f ⊓ HardMathSupport.Kantor79.movedSpace g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  have hg1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace g) = 1 :=
    h.isRefl_g.2
  have heq : Submodule.span (ZMod p) {x} = HardMathSupport.Kantor79.movedSpace g :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx.2))
      (by rw [finrank_span_singleton hx0, hg1])
  have hle : HardMathSupport.Kantor79.movedSpace g ≤ zs4kV f := by
    rw [← heq]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx.1)
  exact zs4k_not_movedSpace_g hp h hle

private lemma zs4k_finrank_closure_four (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U)))) = 4 := by
  have hVH := zs4k_sup_abc_eq_VH hp h
  have hinf := zs4k_VH_inf_movedSpace_g hp h
  have hA : a ∈ Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hB : b ∈ Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hC : c ∈ Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hG : g ∈ Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hle : zs4kV f ⊔ HardMathSupport.Kantor79.movedSpace g ≤
      HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U))) := by
    refine sup_le ?_ ?_
    · rw [← hVH]
      exact sup_le (sup_le (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hA)
        (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hB))
        (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hC)
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hG
  have hg1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace g) = 1 :=
    h.isRefl_g.2
  have hfs := Submodule.finrank_sup_add_finrank_inf_eq (zs4kV f)
    (HardMathSupport.Kantor79.movedSpace g)
  rw [hinf, finrank_bot, add_zero, zs4k_finrank_VH f, hg1] at hfs
  have hU : Module.finrank (ZMod p) U = 4 := by
    simpa using Module.finrank_eq_card_basis f
  have hmono := Submodule.finrank_mono hle
  rw [hfs] at hmono
  have hle4 := Submodule.finrank_le
    (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U))))
  rw [hU] at hle4
  omega

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_e0W (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)} (h : FFourData f a b c g H G)
    (hMr : HardMathSupport.Kantor79.movedSpace (a * b * a) =
      Submodule.span (ZMod p) {f 0 + f 1})
    (hMra : HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U))
    (hMrc : HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) :
    f 0 + f 1 ∈ zs4kW f a b c ∧ a (f 0 + f 1) ∈ zs4kW f a b c ∧
      c (f 0 + f 1) ∈ zs4kW f a b c := by
  have ha_inv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a).1
  have hc_inv : c⁻¹ = c :=
    inv_eq_of_mul_eq_one_right
      (isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c).1
  have he0M1 : f 0 + f 1 ∈ HardMathSupport.Kantor79.movedSpace (a * b * a) := by
    rw [hMr]; exact Submodule.subset_span (Set.mem_singleton _)
  have hae0M2 : a (f 0 + f 1) ∈ HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) := by
    rw [hMra, hMr]
    have h' : a (f 0 + f 1) = (a⁻¹ : U ≃ₗ[ZMod p] U) (f 0 + f 1) := by rw [ha_inv]
    rw [h']
    exact Submodule.mem_map_of_mem (by rw [← hMr]; exact he0M1)
  have hce0M3 : c (f 0 + f 1) ∈ HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) := by
    rw [hMrc, hMr]
    have h' : c (f 0 + f 1) = (c⁻¹ : U ≃ₗ[ZMod p] U) (f 0 + f 1) := by rw [hc_inv]
    rw [h']
    exact Submodule.mem_map_of_mem (by rw [← hMr]; exact he0M1)
  exact ⟨Submodule.mem_sup_left (Submodule.mem_sup_left he0M1),
    Submodule.mem_sup_left (Submodule.mem_sup_right hae0M2), Submodule.mem_sup_right hce0M3⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_mem_zs4kW (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)} (h : FFourData f a b c g H G)
    (hMr : HardMathSupport.Kantor79.movedSpace (a * b * a) =
      Submodule.span (ZMod p) {f 0 + f 1})
    (hMra : HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U))
    (hMrc : HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) :
    f 0 ∈ zs4kW f a b c ∧ f 1 ∈ zs4kW f a b c ∧ f 2 ∈ zs4kW f a b c := by
  obtain ⟨ha0, ha1, hc0, hc1⟩ := zs4k_a_c_actions h
  obtain ⟨he0W, hae0W, hce0W⟩ := zs4k_e0W hp h hMr hMra hMrc
  have hae0 : a (f 0 + f 1) = -f 0 + f 1 := by rw [map_add, ha0, ha1]
  have hce0 : c (f 0 + f 1) = f 0 + f 2 := by rw [map_add, hc0, hc1]
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hf0W : f 0 ∈ zs4kW f a b c := by
    have h2 : (2 : ZMod p) • f 0 = (f 0 + f 1) - a (f 0 + f 1) := by
      rw [hae0, two_smul]
      abel
    have hf0eq : f 0 = (2 : ZMod p)⁻¹ • ((f 0 + f 1) - a (f 0 + f 1)) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
    rw [hf0eq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ he0W hae0W)
  have hf1W : f 1 ∈ zs4kW f a b c := by
    have h : f 1 = (f 0 + f 1) - f 0 := by abel
    rw [h]
    exact Submodule.sub_mem _ he0W hf0W
  have hf2W : f 2 ∈ zs4kW f a b c := by
    have h : f 2 = c (f 0 + f 1) - f 0 := by rw [hce0]; abel
    rw [h]
    exact Submodule.sub_mem _ hce0W hf0W
  exact ⟨hf0W, hf1W, hf2W⟩
omit [Module.Finite (ZMod p) U] in
private lemma zs4k_V_le_moved (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)} (h : FFourData f a b c g H G)
    (hMr : HardMathSupport.Kantor79.movedSpace (a * b * a) =
      Submodule.span (ZMod p) {f 0 + f 1})
    (hMra : HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U))
    (hMrc : HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) :
    zs4kV f ≤ zs4kW f a b c := by
  obtain ⟨hf0W, hf1W, hf2W⟩ := zs4k_mem_zs4kW hp h hMr hMra hMrc
  rw [zs4kV]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa using hf0W
  · simpa using hf1W
  · simpa using hf2W
omit [Module.Finite (ZMod p) U] in
private lemma zs4k_moved_le_V (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)} (h : FFourData f a b c g H G)
    (hMr : HardMathSupport.Kantor79.movedSpace (a * b * a) =
      Submodule.span (ZMod p) {f 0 + f 1})
    (hMra : HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U))
    (hMrc : HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) :
    zs4kW f a b c ≤ zs4kV f := by
  have hRa : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hRc : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hRa.1
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hRc.1
  have haV : (zs4kV f).map (a : U →ₗ[ZMod p] U) ≤ zs4kV f :=
    zs4k_map_castSucc_le h.toMatrix_a (fun i => by fin_cases i <;> simp [diagSignMat])
  have hcV : (zs4kV f).map (c : U →ₗ[ZMod p] U) ≤ zs4kV f :=
    zs4k_map_castSucc_le h.toMatrix_c (fun i => by fin_cases i <;> simp [pijMat])
  have haVinv : (zs4kV f).map ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤ zs4kV f := by
    rw [ha_inv]; exact haV
  have hcVinv : (zs4kV f).map ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤ zs4kV f := by
    rw [hc_inv]; exact hcV
  have he0V : f 0 + f 1 ∈ zs4kV f :=
    Submodule.add_mem _
      (Submodule.subset_span (by exact ⟨0, rfl⟩))
      (Submodule.subset_span (by exact ⟨1, rfl⟩))
  have he0span : Submodule.span (ZMod p) {f 0 + f 1} ≤ zs4kV f :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr he0V)
  have hM1le : HardMathSupport.Kantor79.movedSpace (a * b * a) ≤ zs4kV f := by
    rw [hMr]; exact he0span
  have hM2le : HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) ≤ zs4kV f := by
    rw [hMra, hMr]
    exact (Submodule.map_mono he0span).trans haVinv
  have hM3le : HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) ≤ zs4kV f := by
    rw [hMrc, hMr]
    exact (Submodule.map_mono he0span).trans hcVinv
  change (HardMathSupport.Kantor79.movedSpace (a * b * a) ⊔
      HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) ⊔
      HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c)) ≤ zs4kV f
  exact sup_le (sup_le hM1le hM2le) hM3le

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_map_V_eq (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)} (h : FFourData f a b c g H G)
    (hMr : HardMathSupport.Kantor79.movedSpace (a * b * a) =
      Submodule.span (ZMod p) {f 0 + f 1})
    (hMra : HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((a⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U))
    (hMrc : HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c) =
      (HardMathSupport.Kantor79.movedSpace (a * b * a)).map
        ((c⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U))
    (hg_r : g * (a * b * a) = (a * b * a) * g)
    (hg_ra : g * (a⁻¹ * (a * b * a) * a) = (a⁻¹ * (a * b * a) * a) * g)
    (hg_rc : g * (c⁻¹ * (a * b * a) * c) = (c⁻¹ * (a * b * a) * c) * g) :
    (zs4kV f).map (g : U →ₗ[ZMod p] U) = zs4kV f := by
  have hmap_r := zs4k_movedSpace_map_of_commute g (a * b * a) hg_r
  have hmap_ra := zs4k_movedSpace_map_of_commute g (a⁻¹ * (a * b * a) * a) hg_ra
  have hmap_rc := zs4k_movedSpace_map_of_commute g (c⁻¹ * (a * b * a) * c) hg_rc
  have hVeq : zs4kV f = zs4kW f a b c :=
    le_antisymm (zs4k_V_le_moved hp h hMr hMra hMrc) (zs4k_moved_le_V hp h hMr hMra hMrc)
  rw [hVeq]
  change (((HardMathSupport.Kantor79.movedSpace (a * b * a) ⊔
      HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a)) ⊔
      HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c)).map
        (g : U →ₗ[ZMod p] U)) =
    (HardMathSupport.Kantor79.movedSpace (a * b * a) ⊔
      HardMathSupport.Kantor79.movedSpace (a⁻¹ * (a * b * a) * a)) ⊔
      HardMathSupport.Kantor79.movedSpace (c⁻¹ * (a * b * a) * c)
  rw [Submodule.map_sup, Submodule.map_sup, hmap_r, hmap_ra, hmap_rc]

theorem exists_conj_ne_comm_aba (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    ∃ k ∈ H, k * g * k⁻¹ * (a * b * a) ≠ a * b * a * (k * g * k⁻¹) := by
  by_contra hcon
  push Not at hcon
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  obtain ⟨hMr, hMra, hMrc⟩ := zs4k_moved_aba hp h
  have hg_r : g * (a * b * a) = (a * b * a) * g := by
    simpa using hcon 1 H.one_mem
  have hg_ra : g * (a⁻¹ * (a * b * a) * a) = (a⁻¹ * (a * b * a) * a) * g := by
    have h1 := hcon a haH
    calc g * (a⁻¹ * (a * b * a) * a)
        = a⁻¹ * (a * g * a⁻¹ * (a * b * a)) * a := by group
      _ = a⁻¹ * ((a * b * a) * a * g * a⁻¹) * a := by rw [h1]; group
      _ = (a⁻¹ * (a * b * a) * a) * g := by group
  have hg_rc : g * (c⁻¹ * (a * b * a) * c) = (c⁻¹ * (a * b * a) * c) * g := by
    have h1 := hcon c hcH
    calc g * (c⁻¹ * (a * b * a) * c)
        = c⁻¹ * (c * g * c⁻¹ * (a * b * a)) * c := by group
      _ = c⁻¹ * ((a * b * a) * c * g * c⁻¹) * c := by rw [h1]; group
      _ = (c⁻¹ * (a * b * a) * c) * g := by group
  exact h.map_ne (zs4k_map_V_eq hp h hMr hMra hMrc hg_r hg_ra hg_rc)

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_orderOf_ab (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    orderOf (a * b) = 4 := by
  have hwv : (∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i *
      (![1, 0, 0, 0] : Fin 4 → ZMod p) i) = 2 := by simp [Fin.sum_univ_four]
  have hκρ : (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i) = 2 := by
    norm_num [Fin.sum_univ_four]
  have hbond : (∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i) *
      (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
        (![1, 0, 0, 0] : Fin 4 → ZMod p) i) = 2 := by simp [Fin.sum_univ_four]
  exact FFourCoord.orderOf_mul_eq_four_of_toMatrix hp f
    (by rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]) hwv
    (by rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]) hκρ hbond

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_orderOf_ba (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    orderOf (b * a) = 4 := by
  have ha_inv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a).1
  have hb_inv : b⁻¹ = b :=
    inv_eq_of_mul_eq_one_right
      (isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b).1
  have h1 : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, ha_inv, hb_inv]
  rw [← h1, orderOf_inv, zs4k_orderOf_ab hp h]

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_orderOf_mul_comm (x y : U ≃ₗ[ZMod p] U) :
    orderOf (x * y) = orderOf (y * x) := by
  have h : SemiconjBy y (x * y) (y * x) := by
    show y * (x * y) = (y * x) * y
    group
  exact SemiconjBy.orderOf_eq y h

private lemma zs4n_orderOf_pos (x : U ≃ₗ[ZMod p] U) : 0 < orderOf x := by
  have hfinU : Finite U := Module.finite_of_finite (R := ZMod p) (M := U)
  have hfinGL : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  exact (isOfFinOrder_of_finite x).orderOf_pos

private lemma zs4n_p_eq_three_gammaP (hp : p ≠ 2) {a b c : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c)
    (hab : orderOf (a * b) = 4) (hbc : orderOf (b * c) = 4) (hac : orderOf (a * c) = 2)
    {Γ : Subgroup (U ≃ₗ[ZMod p] U)} (hΓ : Γ = Subgroup.closure {a, b, c})
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Γ) = 3)
    (hD : DMax p Γ 4) : p = 3 := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ :=
    exists_orderOf_mul_eq_max_gammaP hp ha hb hc hab hbc hac hΓ hdim
  have hmax4 : max 4 p ≤ 4 := by rw [← hxy]; exact hD.1 x hx y hy hxr hyr
  have hp_le : p ≤ 4 := le_trans (le_max_right 4 p) hmax4
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  interval_cases p
  · exact absurd rfl hp
  · rfl
  · exact absurd (Fact.out : Nat.Prime 4) (by norm_num)

omit [Module.Finite (ZMod p) U] in
private theorem zs4n_reflection_congr {a : U} {φ : Module.Dual (ZMod p) U} {h₁ h₂ : φ a = 2} :
    Module.reflection h₁ = Module.reflection h₂ := by
  ext v
  rw [Module.reflection_apply]

omit [Module.Finite (ZMod p) U] in
private theorem zs4n_reflection_range_fin_three {r₁ r₂ t : U ≃ₗ[ZMod p] U} {u : Fin 3 → U}
    {φ : Fin 3 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hr₁ : r₁ = Module.reflection (hφ 0)) (hr₂ : r₂ = Module.reflection (hφ 1))
    (ht : t = Module.reflection (hφ 2)) :
    Set.range (fun i : Fin 3 => Module.reflection (hφ i)) = {r₁, r₂, t} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (zs4n_reflection_congr.trans hr₁.symm)
    · exact Or.inr (Or.inl (zs4n_reflection_congr.trans hr₂.symm))
    · exact Or.inr (Or.inr (zs4n_reflection_congr.trans ht.symm))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, zs4n_reflection_congr.trans hr₁.symm⟩
    · exact ⟨1, zs4n_reflection_congr.trans hr₂.symm⟩
    · exact ⟨2, zs4n_reflection_congr.trans ht.symm⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_connected_fin_three {u : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    (ha : φ 0 (u 1) ≠ 0) (hb : φ 1 (u 0) ≠ 0)
    (hcd : φ 0 (u 2) ≠ 0 ∨ φ 1 (u 2) ≠ 0)
    (hef : φ 2 (u 0) ≠ 0 ∨ φ 2 (u 1) ≠ 0) :
    ∀ I : Finset (Fin 3), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0 := by
  intro I hIne hIproper
  by_cases h0 : (0 : Fin 3) ∈ I
  · by_cases h1 : (1 : Fin 3) ∈ I
    · have h2 : (2 : Fin 3) ∉ I := by
        intro h2
        apply hIproper
        apply Finset.eq_univ_of_forall
        intro i; fin_cases i
        · exact h0
        · exact h1
        · exact h2
      rcases hef with he | hf
      · exact ⟨0, h0, 2, h2, he⟩
      · exact ⟨1, h1, 2, h2, hf⟩
    · exact ⟨0, h0, 1, h1, hb⟩
  · by_cases h1 : (1 : Fin 3) ∈ I
    · exact ⟨1, h1, 0, h0, ha⟩
    · have h2 : (2 : Fin 3) ∈ I := by
        obtain ⟨i, hi⟩ := hIne
        fin_cases i
        · exact absurd hi h0
        · exact absurd hi h1
        · exact hi
      rcases hcd with hc | hd
      · exact ⟨2, h2, 0, h0, hc⟩
      · exact ⟨2, h2, 1, h1, hd⟩

private lemma zs4n_det_three (x y z w : ZMod p) :
    (!![2, x, 0; y, 2, z; 0, w, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)).det =
      8 - 2 * z * w - 2 * x * y := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_commute_of_orderOf_eq_two {x y : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    (hy : y * y = 1) (h : orderOf (x * y) = 2) : x * y = y * x := by
  have h2 : (x * y) * (x * y) = 1 := by
    have := pow_orderOf_eq_one (x * y); rw [h, pow_two] at this; exact this
  calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h2
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right hx]

private lemma zs4n_coeff_ne_zero (hp : p ≠ 2) {v w : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ v = 2) (hψ : ψ w = 2)
    (hord : orderOf (Module.reflection hφ * Module.reflection hψ) ≠ 2)
    (hle : orderOf (Module.reflection hφ * Module.reflection hψ) ≤ 4)
    (hne1 : orderOf (Module.reflection hφ * Module.reflection hψ) ≠ 1) :
    φ w ≠ 0 ∧ ψ v ≠ 0 := by
  have h34 : orderOf (Module.reflection hφ * Module.reflection hψ) = 3 ∨
      orderOf (Module.reflection hφ * Module.reflection hψ) = 4 := by
    have hfinU : Finite U := Module.finite_of_finite (R := ZMod p) (M := U)
    have hfinGL : Finite (U ≃ₗ[ZMod p] U) :=
      Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
        (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
    have hpos : 0 < orderOf (Module.reflection hφ * Module.reflection hψ) :=
      (isOfFinOrder_of_finite _).orderOf_pos
    omega
  have hne : φ w * ψ v ≠ 0 := by
    rcases h34 with h3 | h4
    · rw [apply_mul_apply_eq_one_of_orderOf_eq_three hp hφ hψ h3]; exact one_ne_zero
    · rw [apply_mul_apply_eq_two_of_orderOf_eq_four hp hφ hψ h4]; exact ZMod.prime_ne_zero p 2 hp
  exact ⟨(mul_ne_zero_iff.mp hne).1, (mul_ne_zero_iff.mp hne).2⟩

private lemma zs4n_det_zero {va vb vg : U} {φa φb φg : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφg : φg vg = 2)
    (hab1 : φa vb ≠ 0) (hab2 : φb va ≠ 0)
    (hcd : φa vg ≠ 0 ∨ φb vg ≠ 0) (hef : φg va ≠ 0 ∨ φg vb ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hAeq : A = Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
      Module.reflection hφg} : Set (U ≃ₗ[ZMod p] U)))
    (hirr : ¬ IrredOnSection A ⊥ (HardMathSupport.Kantor79.commutatorSpace A)) :
    (Matrix.of fun i j => (![φa, φb, φg] : Fin 3 → Module.Dual (ZMod p) U) i
      ((![va, vb, vg] : Fin 3 → U) j)).det = 0 := by
  by_contra hdet
  have hφ : ∀ i, (![φa, φb, φg] : Fin 3 → Module.Dual (ZMod p) U) i
      ((![va, vb, vg] : Fin 3 → U) i) = 2 := fun i => by
    fin_cases i <;> simp [hφa, hφb, hφg]
  have hconn := zs4n_connected_fin_three (u := ![va, vb, vg]) (φ := ![φa, φb, φg])
    (by simpa using hab1) (by simpa using hab2) hcd hef
  have hss := splitSupport_of_det_ne_zero (u := ![va, vb, vg]) (φ := ![φa, φb, φg]) hφ hdet hconn
  have hrange : Set.range (fun i : Fin 3 => Module.reflection (hφ i)) =
      {Module.reflection hφa, Module.reflection hφb, Module.reflection hφg} :=
    zs4n_reflection_range_fin_three (u := ![va, vb, vg]) (φ := ![φa, φb, φg]) hφ rfl rfl rfl
  rw [hrange, ← hAeq] at hss
  exact hirr hss.2.2

private lemma zs4n_basic (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    IsRefl p a ∧ IsRefl p b ∧ IsRefl p g ∧ Module.finrank (ZMod p) U = 4 ∧
      Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) ≤ G ∧ orderOf (a * b) = 4 ∧
      DMax p (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) 4 ∧
      QTwoLin.TransvectionFree (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hAle : Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact h.H_le haH
    · exact h.H_le hbH
    · exact h.g_mem
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hab4 : orderOf (a * b) = 4 := zs4k_orderOf_ab hp h
  have hD : DMax p (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) 4 :=
    ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hAle hx) y (hAle hy) hxr hyr,
      a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), haR, hbR, hab4⟩
  exact ⟨haR, hbR, h.isRefl_g, by simpa using Module.finrank_eq_card_basis f, hAle, hab4, hD,
    fun x hx => h.transvectionFree x (hAle hx), zs4k_finrank_closure_three hp h⟩

private lemma zs4n_orders (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g) :
    orderOf (g * a) ≤ 4 ∧ orderOf (g * b) ≤ 4 ∧ orderOf (g * a) ≠ 1 ∧
      orderOf (g * b) ≠ 1 ∧ ¬ (orderOf (g * a) = 2 ∧ orderOf (g * b) = 2) := by
  obtain ⟨haR, hbR, hgR, -, -, -, -, -, -⟩ := zs4n_basic hp h
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hga_le : orderOf (g * a) ≤ 4 := h.dmax.1 g h.g_mem a (h.H_le haH) hgR haR
  have hgb_le : orderOf (g * b) ≤ 4 := h.dmax.1 g h.g_mem b (h.H_le hbH) hgR hbR
  have hga_ne1 : orderOf (g * a) ≠ 1 := by
    intro h1
    have hg_eq_a : g = a := by
      have h' := orderOf_eq_one_iff.mp h1
      calc g = g * (a * a) := by rw [haR.1, mul_one]
        _ = (g * a) * a := by group
        _ = a := by rw [h', one_mul]
    exact h.map_ne (by rw [hg_eq_a]; exact (zs4k_conj_data h haH).1)
  have hgb_ne1 : orderOf (g * b) ≠ 1 := by
    intro h1
    have hg_eq_b : g = b := by
      have h' := orderOf_eq_one_iff.mp h1
      calc g = g * (b * b) := by rw [hbR.1, mul_one]
        _ = (g * b) * b := by group
        _ = b := by rw [h', one_mul]
    exact h.map_ne (by rw [hg_eq_b]; exact (zs4k_conj_data h hbH).1)
  refine ⟨hga_le, hgb_le, hga_ne1, hgb_ne1, fun hb2 => ?_⟩
  obtain ⟨h1, h2⟩ := hb2
  have hag : g * a = a * g := zs4n_commute_of_orderOf_eq_two hgR.1 haR.1 h1
  have hbg : g * b = b * g := zs4n_commute_of_orderOf_eq_two hgR.1 hbR.1 h2
  exact hg (by
    calc g * (a * b * a) = (g * a) * b * a := by group
      _ = (a * g) * b * a := by rw [hag]
      _ = a * (g * b) * a := by group
      _ = a * (b * g) * a := by rw [hbg]
      _ = a * b * (g * a) := by group
      _ = a * b * (a * g) := by rw [hag]
      _ = (a * b * a) * g := by group)

private lemma zs4n_det_prod (hp : p ≠ 2)
    {vx : U} {φx : Module.Dual (ZMod p) U} {vy : U} {φy : Module.Dual (ZMod p) U}
    {vg : U} {φg : Module.Dual (ZMod p) U}
    (hφx : φx vx = 2) (hφy : φy vy = 2) (hφg : φg vg = 2)
    (hxy : φx vy * φy vx = 2) (hzxy : φx vg = 0) (hzgy : φg vx = 0)
    (hyg1 : φy vg ≠ 0) (hyg2 : φg vy ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hAeq : A = Subgroup.closure ({Module.reflection hφx, Module.reflection hφy,
      Module.reflection hφg} : Set (U ≃ₗ[ZMod p] U)))
    (hA : ¬ IrredOnSection A ⊥ (HardMathSupport.Kantor79.commutatorSpace A)) :
    φy vg * φg vy = 2 := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hab1 : φx vy ≠ 0 := (mul_ne_zero_iff.mp (by rw [hxy]; exact h2ne)).1
  have hab2 : φy vx ≠ 0 := (mul_ne_zero_iff.mp (by rw [hxy]; exact h2ne)).2
  have hzero := zs4n_det_zero (A := A) hφx hφy hφg hab1 hab2 (Or.inr hyg1) (Or.inr hyg2) hAeq hA
  have hC : (Matrix.of fun i j => (![φx, φy, φg] : Fin 3 → Module.Dual (ZMod p) U) i
      ((![vx, vy, vg] : Fin 3 → U) j)) = !![2, φx vy, 0; φy vx, 2, φy vg; 0, φg vy, 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hφx, hφy, hφg, hzxy, hzgy]
  rw [hC, zs4n_det_three] at hzero
  have h4 : 2 * (φy vg * φg vy) = 2 * 2 := by
    linear_combination -hzero - 2 * hxy
  exact mul_left_cancel₀ h2ne h4

private lemma zs4n_order_four_of_prod (hp : p ≠ 2) {x y : U ≃ₗ[ZMod p] U}
    {vx : U} {φx : Module.Dual (ZMod p) U} {vy : U} {φy : Module.Dual (ZMod p) U}
    (hφx : φx vx = 2) (hφy : φy vy = 2) (hx_eq : x = Module.reflection hφx)
    (hy_eq : y = Module.reflection hφy) (hle : orderOf (y * x) ≤ 4) (hne1 : orderOf (y * x) ≠ 1)
    (hne2 : orderOf (y * x) ≠ 2) (hprod : φx vy * φy vx = 2) : orderOf (y * x) = 4 := by
  have h34 : orderOf (y * x) = 3 ∨ orderOf (y * x) = 4 := by
    have hpos := zs4n_orderOf_pos (y * x); omega
  rcases h34 with h3 | h4
  · exfalso
    have h3' : orderOf (Module.reflection hφx * Module.reflection hφy) = 3 := by
      rw [← hx_eq, ← hy_eq, zs4n_orderOf_mul_comm x y]; exact h3
    rw [apply_mul_apply_eq_one_of_orderOf_eq_three hp hφx hφy h3'] at hprod
    have h := congrArg (fun t : ZMod p => t - 1) hprod
    rw [show (1 : ZMod p) - 1 = 0 by ring, show (2 : ZMod p) - 1 = 1 by ring] at h
    exact one_ne_zero h.symm
  · exact h4

private lemma zs4n_exclude_33 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hga3 : orderOf (g * a) = 3) (hgb3 : orderOf (g * b) = 3) :
    IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})) := by
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, hAt, hdim⟩ := zs4n_basic hp h
  have hga3' : orderOf (a * g) = 3 := by rw [zs4n_orderOf_mul_comm a g]; exact hga3
  have hgb3' : orderOf (b * g) = 3 := by rw [zs4n_orderOf_mul_comm b g]; exact hgb3
  have hmne2 := orderOf_cacb_ne_two_of_433 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl
    hAt hdim hD hab4 hga3' hgb3'
  have hm34 : orderOf (g * a * g * b) = 3 ∨ orderOf (g * a * g * b) = 4 := by
    obtain ⟨hge, hle⟩ := two_le_orderOf_cacb (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR
      rfl hdim hD
    have hpos := zs4n_orderOf_pos (g * a * g * b)
    omega
  rcases hm34 with hm3 | hm4
  · exact (eq_gmmn_of_433 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl hAt hdim hD
      hab4 hga3' hgb3' hm3).1.2.2
  · exact (card_eq_of_433 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl hAt hdim hD
      hab4 hga3' hgb3' hm4).1.2.2

private lemma zs4n_exclude_44 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hga4 : orderOf (g * a) = 4) (hgb4 : orderOf (g * b) = 4) :
    IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})) := by
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, hAt, hdim⟩ := zs4n_basic hp h
  have hga4' : orderOf (a * g) = 4 := by rw [zs4n_orderOf_mul_comm a g]; exact hga4
  have hgb4' : orderOf (b * g) = 4 := by rw [zs4n_orderOf_mul_comm b g]; exact hgb4
  exact (card_eq_of_444 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl hAt hdim hD
    hab4 hga4' hgb4').2.1.2.2

private lemma zs4n_disj_34 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hga3 : orderOf (g * a) = 3) (hgb4 : orderOf (g * b) = 4) :
    orderOf (g * a * g * b) = 4 := by
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, hAt, hdim⟩ := zs4n_basic hp h
  have hga3' : orderOf (a * g) = 3 := by rw [zs4n_orderOf_mul_comm a g]; exact hga3
  have hgb4' : orderOf (b * g) = 4 := by rw [zs4n_orderOf_mul_comm b g]; exact hgb4
  have hm234 : orderOf (g * a * g * b) = 2 ∨ orderOf (g * a * g * b) = 3 ∨
      orderOf (g * a * g * b) = 4 := by
    obtain ⟨hge, hle⟩ := two_le_orderOf_cacb (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR
      rfl hdim hD
    omega
  rcases hm234 with hm2 | hm3 | hm4
  · exact absurd (eq_g2mmn_of_434 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl hAt hdim
      hD hab4 hga3' hgb4' hm2).1.2.2 hA
  · exact absurd (card_eq_of_434 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl hAt hdim
      hD hab4 hga3' hgb4' hm3).1.2.2 hA
  · exact hm4

private lemma zs4n_disj_43 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hga4 : orderOf (g * a) = 4) (hgb3 : orderOf (g * b) = 3) :
    orderOf (g * b * g * a) = 4 := by
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, hAt, hdim⟩ := zs4n_basic hp h
  have hba4 : orderOf (b * a) = 4 := zs4k_orderOf_ba hp h
  have hbg3 : orderOf (b * g) = 3 := by rw [zs4n_orderOf_mul_comm b g]; exact hgb3
  have hag4 : orderOf (a * g) = 4 := by rw [zs4n_orderOf_mul_comm a g]; exact hga4
  have hset : ({b, a, g} : Set (U ≃ₗ[ZMod p] U)) = {a, b, g} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl | rfl) <;> simp
  have hclos : Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U)) =
      Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) := by rw [hset]
  have hdim' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by rw [hclos]; exact hdim
  have hD' : DMax p (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) 4 := by
    rw [hclos]; exact hD
  have hAt' : QTwoLin.TransvectionFree (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) := by
    rw [hclos]; exact hAt
  have hA' : ¬ IrredOnSection (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) ⊥
      (HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U)))) := by rw [hclos]; exact hA
  have hm234 : orderOf (g * b * g * a) = 2 ∨ orderOf (g * b * g * a) = 3 ∨
      orderOf (g * b * g * a) = 4 := by
    obtain ⟨hge, hle⟩ := two_le_orderOf_cacb
      (A := Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) hp hU hbR haR hgR rfl hdim' hD'
    omega
  rcases hm234 with hm2 | hm3 | hm4
  · exact absurd (eq_g2mmn_of_434 (A := Subgroup.closure ({b, a, g} : Set _)) hp hU hbR haR hgR rfl
      hAt' hdim' hD' hba4 hbg3 hag4 hm2).1.2.2 hA'
  · exact absurd (card_eq_of_434 (A := Subgroup.closure ({b, a, g} : Set _)) hp hU hbR haR hgR rfl
      hAt' hdim' hD' hba4 hbg3 hag4 hm3).1.2.2 hA'
  · exact hm4

private lemma zs4n_order_disj (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    orderOf (g * a) = 2 ∨ orderOf (g * b) = 2 ∨
      (orderOf (g * a) = 3 ∧ orderOf (g * b) = 4 ∧ orderOf (g * a * g * b) = 4) ∨
      (orderOf (g * a) = 4 ∧ orderOf (g * b) = 3 ∧ orderOf (g * b * g * a) = 4) := by
  obtain ⟨hga_le, hgb_le, hga_ne1, hgb_ne1, -⟩ := zs4n_orders hp h hg
  by_cases hga2 : orderOf (g * a) = 2
  · exact Or.inl hga2
  · by_cases hgb2 : orderOf (g * b) = 2
    · exact Or.inr (Or.inl hgb2)
    · have hga34 : orderOf (g * a) = 3 ∨ orderOf (g * a) = 4 := by
        have hpos := zs4n_orderOf_pos (g * a); omega
      have hgb34 : orderOf (g * b) = 3 ∨ orderOf (g * b) = 4 := by
        have hpos := zs4n_orderOf_pos (g * b); omega
      rcases hga34 with hga3 | hga4
      · rcases hgb34 with hgb3 | hgb4
        · exact absurd (zs4n_exclude_33 hp h hga3 hgb3) hA
        · exact Or.inr (Or.inr (Or.inl ⟨hga3, hgb4, zs4n_disj_34 hp h hA hga3 hgb4⟩))
      · rcases hgb34 with hgb3 | hgb4
        · exact Or.inr (Or.inr (Or.inr ⟨hga4, hgb3, zs4n_disj_43 hp h hA hga4 hgb3⟩))
        · exact absurd (zs4n_exclude_44 hp h hga4 hgb4) hA

private lemma zs4n_p3_ga2 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hga2 : orderOf (g * a) = 2) : p = 3 := by
  let A : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, -, hdim⟩ := zs4n_basic hp h
  obtain ⟨-, hgb_le, -, hgb_ne1, hnot_both⟩ := zs4n_orders hp h hg
  obtain ⟨va, φa, hφa, ha_eq⟩ := (isRefl_iff hp a).mp haR
  obtain ⟨vb, φb, hφb, hb_eq⟩ := (isRefl_iff hp b).mp hbR
  obtain ⟨vg, φg, hφg, hg_eq⟩ := (isRefl_iff hp g).mp hgR
  have hab_prod : φa vb * φb va = 2 := by
    refine apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb ?_
    rw [← ha_eq, ← hb_eq]; exact hab4
  have hAeq : A = Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
      Module.reflection hφg} : Set (U ≃ₗ[ZMod p] U)) := by
    change Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) = _
    rw [← ha_eq, ← hb_eq, ← hg_eq]
  have hoga_eq : orderOf (Module.reflection hφa * Module.reflection hφg) = 2 := by
    rw [← ha_eq, ← hg_eq, zs4n_orderOf_mul_comm a g]; exact hga2
  have hzag : φa vg = 0 := (apply_eq_zero_of_orderOf_eq_two hp hφa hφg hoga_eq).1
  have hzga : φg va = 0 := (apply_eq_zero_of_orderOf_eq_two hp hφa hφg hoga_eq).2
  have hgb_ne2 : orderOf (g * b) ≠ 2 := fun h2 => hnot_both ⟨hga2, h2⟩
  have hbg_ne2 : orderOf (Module.reflection hφb * Module.reflection hφg) ≠ 2 := by
    rw [← hb_eq, ← hg_eq, zs4n_orderOf_mul_comm b g]; exact hgb_ne2
  have hbg_le : orderOf (Module.reflection hφb * Module.reflection hφg) ≤ 4 := by
    rw [← hb_eq, ← hg_eq, zs4n_orderOf_mul_comm b g]; exact hgb_le
  have hbg_ne1 : orderOf (Module.reflection hφb * Module.reflection hφg) ≠ 1 := by
    rw [← hb_eq, ← hg_eq, zs4n_orderOf_mul_comm b g]; exact hgb_ne1
  obtain ⟨hφb_vg, hφg_vb⟩ := zs4n_coeff_ne_zero hp hφb hφg hbg_ne2 hbg_le hbg_ne1
  have hprod := zs4n_det_prod hp hφa hφb hφg hab_prod hzag hzga hφb_vg hφg_vb hAeq hA
  have hgb4 := zs4n_order_four_of_prod hp hφb hφg hb_eq hg_eq hgb_le hgb_ne1 hgb_ne2 hprod
  exact zs4n_p_eq_three_gammaP hp haR hbR hgR hab4 (by rw [zs4n_orderOf_mul_comm b g]; exact hgb4)
    (by rw [zs4n_orderOf_mul_comm a g]; exact hga2) (Γ := A) rfl hdim hD

private lemma zs4n_p3_gb2 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hgb2 : orderOf (g * b) = 2) : p = 3 := by
  let A : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, -, hdim⟩ := zs4n_basic hp h
  obtain ⟨hga_le, -, hga_ne1, -, hnot_both⟩ := zs4n_orders hp h hg
  obtain ⟨va, φa, hφa, ha_eq⟩ := (isRefl_iff hp a).mp haR
  obtain ⟨vb, φb, hφb, hb_eq⟩ := (isRefl_iff hp b).mp hbR
  obtain ⟨vg, φg, hφg, hg_eq⟩ := (isRefl_iff hp g).mp hgR
  have hab_prod : φa vb * φb va = 2 := by
    refine apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb ?_
    rw [← ha_eq, ← hb_eq]; exact hab4
  have hAeq : A = Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
      Module.reflection hφg} : Set (U ≃ₗ[ZMod p] U)) := by
    change Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) = _
    rw [← ha_eq, ← hb_eq, ← hg_eq]
  have hbg_eq : orderOf (Module.reflection hφb * Module.reflection hφg) = 2 := by
    rw [← hb_eq, ← hg_eq, zs4n_orderOf_mul_comm b g]; exact hgb2
  have hzbg : φb vg = 0 := (apply_eq_zero_of_orderOf_eq_two hp hφb hφg hbg_eq).1
  have hzgb : φg vb = 0 := (apply_eq_zero_of_orderOf_eq_two hp hφb hφg hbg_eq).2
  have hga_ne2 : orderOf (g * a) ≠ 2 := fun h2 => hnot_both ⟨h2, hgb2⟩
  have hag_ne2 : orderOf (Module.reflection hφa * Module.reflection hφg) ≠ 2 := by
    rw [← ha_eq, ← hg_eq, zs4n_orderOf_mul_comm a g]; exact hga_ne2
  have hag_le : orderOf (Module.reflection hφa * Module.reflection hφg) ≤ 4 := by
    rw [← ha_eq, ← hg_eq, zs4n_orderOf_mul_comm a g]; exact hga_le
  have hag_ne1 : orderOf (Module.reflection hφa * Module.reflection hφg) ≠ 1 := by
    rw [← ha_eq, ← hg_eq, zs4n_orderOf_mul_comm a g]; exact hga_ne1
  obtain ⟨hφa_vg, hφg_va⟩ := zs4n_coeff_ne_zero hp hφa hφg hag_ne2 hag_le hag_ne1
  have hset_ba : ({Module.reflection hφa, Module.reflection hφb, Module.reflection hφg} :
      Set (U ≃ₗ[ZMod p] U)) =
      {Module.reflection hφb, Module.reflection hφa, Module.reflection hφg} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl | rfl) <;> simp
  have hAeq' : A = Subgroup.closure ({Module.reflection hφb, Module.reflection hφa,
      Module.reflection hφg} : Set (U ≃ₗ[ZMod p] U)) := by rw [hAeq, hset_ba]
  have hprod := zs4n_det_prod hp hφb hφa hφg (by rw [mul_comm]; exact hab_prod) hzbg hzgb
    hφa_vg hφg_va hAeq' hA
  have hga4 := zs4n_order_four_of_prod hp hφa hφg ha_eq hg_eq hga_le hga_ne1 hga_ne2 hprod
  have hset_gab : ({g, a, b} : Set (U ≃ₗ[ZMod p] U)) = {a, b, g} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl | rfl) <;> simp
  have hclos_gab : Subgroup.closure ({g, a, b} : Set (U ≃ₗ[ZMod p] U)) = A := by rw [hset_gab]
  exact zs4n_p_eq_three_gammaP hp hgR haR hbR hga4 hab4 hgb2 (Γ := A) hclos_gab.symm hdim hD

private lemma zs4n_p3_34 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hga3 : orderOf (g * a) = 3) (hgb4 : orderOf (g * b) = 4)
    (hm : orderOf (g * a * g * b) = 4) : p = 3 := by
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, hAt, hdim⟩ := zs4n_basic hp h
  have hga3' : orderOf (a * g) = 3 := by rw [zs4n_orderOf_mul_comm a g]; exact hga3
  have hgb4' : orderOf (b * g) = 4 := by rw [zs4n_orderOf_mul_comm b g]; exact hgb4
  exact (commute_of_434 (A := Subgroup.closure {a, b, g}) hp hU haR hbR hgR rfl hAt hdim hD
    hab4 hga3' hgb4' hm).1

private lemma zs4n_p3_43 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hga4 : orderOf (g * a) = 4) (hgb3 : orderOf (g * b) = 3)
    (hm : orderOf (g * b * g * a) = 4) : p = 3 := by
  obtain ⟨haR, hbR, hgR, hU, -, hab4, hD, hAt, hdim⟩ := zs4n_basic hp h
  have hba4 : orderOf (b * a) = 4 := zs4k_orderOf_ba hp h
  have hbg3 : orderOf (b * g) = 3 := by rw [zs4n_orderOf_mul_comm b g]; exact hgb3
  have hag4 : orderOf (a * g) = 4 := by rw [zs4n_orderOf_mul_comm a g]; exact hga4
  have hset : ({b, a, g} : Set (U ≃ₗ[ZMod p] U)) = {a, b, g} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> rintro (rfl | rfl | rfl) <;> simp
  have hclos : Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U)) =
      Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) := by rw [hset]
  have hdim' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by rw [hclos]; exact hdim
  have hD' : DMax p (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) 4 := by
    rw [hclos]; exact hD
  have hAt' : QTwoLin.TransvectionFree (Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) := by
    rw [hclos]; exact hAt
  exact (commute_of_434 (A := Subgroup.closure ({b, a, g} : Set (U ≃ₗ[ZMod p] U))) hp hU hbR haR
    hgR rfl hAt' hdim' hD' hba4 hbg3 hag4 hm).1

private lemma zs4n_order_pair (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    p = 3 ∧ (orderOf (g * a) = 2 ∨ orderOf (g * b) = 2 ∨
      (orderOf (g * a) = 3 ∧ orderOf (g * b) = 4 ∧ orderOf (g * a * g * b) = 4) ∨
      (orderOf (g * a) = 4 ∧ orderOf (g * b) = 3 ∧ orderOf (g * b * g * a) = 4)) := by
  have hd := zs4n_order_disj hp h hg hA
  refine ⟨?_, hd⟩
  rcases hd with hga2 | hgb2 | ⟨hga3, hgb4, hm⟩ | ⟨hga4, hgb3, hm⟩
  · exact zs4n_p3_ga2 hp h hg hA hga2
  · exact zs4n_p3_gb2 hp h hg hA hgb2
  · exact zs4n_p3_34 hp h hga3 hgb4 hm
  · exact zs4n_p3_43 hp h hga4 hgb3 hm

theorem eq_three_of_not_irred (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) : p = 3 :=
  (zs4n_order_pair hp h hg hA).1

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_conj_mat {k y : U ≃ₗ[ZMod p] U} {u v ρ κ : Fin 4 → ZMod p}
    (hk : LinearMap.toMatrix f f k.toLinearMap = 1 - Matrix.vecMulVec u v)
    (hy : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hvu : ∑ i, v i * u i = 2) :
    LinearMap.toMatrix f f (k * y * k).toLinearMap =
      1 - Matrix.vecMulVec (ρ - (∑ i, v i * ρ i) • u) (κ - (∑ i, κ i * u i) • v) := by
  rw [toMatrix_coe_mul, toMatrix_coe_mul, hk, hy,
    FFourCoord.one_sub_vecMulVec_conj hvu]

private lemma zs4n_scal_244 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha1 : w0 = 0) (ha2 : v0 = 0)
    (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc : (w1 + -w2) * (v1 + -v2) = 2)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hnot : w0 + w1 ≠ 0 ∨ v0 + v1 ≠ 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0) :
    v1 * w0 = 0 ∧ v0 * w1 = 0 ∧
      (2 + 2 * v1 * w2 + v1 * w1) = 0 ∧ (1 + v2 * w1 + 2 * v1 * w1) = 0 ∧
      (2 + 2 * v1 * w1 + 2 * v1 * w0 + 2 * v1^2 * w1^2 + v1^2 * w0 * w1 + 2 * v0 * w1 +
        v0 * v1 * w1^2 + 2 * v0 * v1 * w0 * w1) = 2 ∧
      2 * w1 ≠ 0 := by
  decide +kernel +revert

private lemma zs4n_scal_422 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : v0 * w0 = 1)
    (hb1 : w0 - w1 = 0) (hb2 : v0 - v1 = 0)
    (hc1 : w1 - w2 = 0) (hc2 : v1 - v2 = 0)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hnot : w0 + w1 ≠ 0 ∨ v0 + v1 ≠ 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0) :
    (2 + v0 * w0) = 0 ∧ v0 * (w1 + 2 * w2) = 0 ∧ w0 * (v2 + 2 * v1) = 0 ∧
      (2 + 2 * v1 * w0 + 2 * v0 * w1 + 2 * v0 * w0 + 2 * v0 * v1 * w0 * w1 +
        v0 * v1 * w0^2 + v0^2 * w0 * w1 + 2 * v0^2 * w0^2) = 2 ∧
      2 * w0 ≠ 0 := by
  decide +kernel +revert

private lemma zs4n_scal_344a (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 1)
    (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc : (w1 + -w2) * (v1 + -v2) = 2)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hnot : w0 + w1 ≠ 0 ∨ v0 + v1 ≠ 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0)
    (hsub1 : w0 - w2 = 0) (hsub2 : v0 - v2 = 0) :
    w1 = 0 ∧ 2 * v1 = 0 ∧ w0 + 2 * w2 = 0 ∧ v0 + 2 * v2 = 0 ∧
      (w0 + -w1) * (v0 + -v1) = 2 := by
  decide +kernel +revert

private lemma zs4n_scal_344b (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 1)
    (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc : (w1 + -w2) * (v1 + -v2) = 2)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hnot : w0 + w1 ≠ 0 ∨ v0 + v1 ≠ 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0)
    (hsub : (w0 - w2) * (v0 - v2) = 2) :
    w1 = 0 ∧ 2 * v1 = 0 ∧ w0 + w2 = 0 ∧ v0 + v2 = 0 ∧
      (w0 + -w1) * (v0 + -v1) = 2 := by
  decide +kernel +revert

private lemma zs4n_scal_423 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : v0 * w0 = 1)
    (hb1 : w0 - w1 = 0) (hb2 : v0 - v1 = 0)
    (hc : (w1 + -w2) * (v1 + -v2) = 1)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hnot : w0 + w1 ≠ 0 ∨ v0 + v1 ≠ 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0) :
    (2 + v0 * w0) = 0 ∧ v0 * (w1 + w2) = 0 ∧ w0 * (v1 + v2) = 0 ∧
      (2 + v1 * w0 + v0 * w1 + 2 * v0 * w0 + 2 * v0 * v1 * w0 * w1 + 2 * v0 * v1 * w0^2 +
        2 * v0^2 * w0 * w1 + 2 * v0^2 * w0^2) = 2 ∧ 2 * w0 ≠ 0 := by
  decide +kernel +revert

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_pairing_two (hp : p ≠ 2) {v w ρ κ : Fin 4 → ZMod p}
    {g r : U ≃ₗ[ZMod p] U}
    (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (hord : orderOf (g * r) = 2) :
    (∑ i, w i * ρ i) = 0 ∧ (∑ i, κ i * v i) = 0 := by
  obtain ⟨hg_f, hg_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hgm hwv
  obtain ⟨hr_f, hr_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hrm hκρ
  have hord' : orderOf (Module.reflection hg_f * Module.reflection hr_f) = 2 := by
    rw [← hg_eq, ← hr_eq]; exact hord
  obtain ⟨h1, h2⟩ := apply_eq_zero_of_orderOf_eq_two hp hg_f hr_f hord'
  rw [FFourCoord.sum_smul_coord_apply_sum] at h1 h2
  exact ⟨h1, h2⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_pairing_three (hp : p ≠ 2) {v w ρ κ : Fin 4 → ZMod p}
    {g r : U ≃ₗ[ZMod p] U}
    (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (hord : orderOf (g * r) = 3) :
    (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 1 := by
  obtain ⟨hg_f, hg_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hgm hwv
  obtain ⟨hr_f, hr_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hrm hκρ
  have hord' : orderOf (Module.reflection hg_f * Module.reflection hr_f) = 3 := by
    rw [← hg_eq, ← hr_eq]; exact hord
  have h := apply_mul_apply_eq_one_of_orderOf_eq_three hp hg_f hr_f hord'
  rwa [FFourCoord.sum_smul_coord_apply_sum, FFourCoord.sum_smul_coord_apply_sum] at h

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_pairing_four (hp : p ≠ 2) {v w ρ κ : Fin 4 → ZMod p}
    {g r : U ≃ₗ[ZMod p] U}
    (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (hord : orderOf (g * r) = 4) :
    (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 2 := by
  obtain ⟨hg_f, hg_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hgm hwv
  obtain ⟨hr_f, hr_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hrm hκρ
  have hord' : orderOf (Module.reflection hg_f * Module.reflection hr_f) = 4 := by
    rw [← hg_eq, ← hr_eq]; exact hord
  have h := apply_mul_apply_eq_two_of_orderOf_eq_four hp hg_f hr_f hord'
  rwa [FFourCoord.sum_smul_coord_apply_sum, FFourCoord.sum_smul_coord_apply_sum] at h

private lemma zs4n_scal_432 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 2) (hb : (w0 + -w1) * (v0 + -v1) = 1)
    (hc1 : v1 - v2 = 0) (hc2 : w1 - w2 = 0)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0) :
    v0 + v1 = 0 ∧ w0 + w1 = 0 := by
  decide +kernel +revert

private lemma zs4n_scal_433 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 2) (hb : (w0 + -w1) * (v0 + -v1) = 1)
    (hc : (w1 + -w2) * (v1 + -v2) = 1)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0) :
    v0 + v1 = 0 ∧ w0 + w1 = 0 := by
  decide +kernel +revert

private lemma zs4n_scal_343 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 1) (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc : (w1 + -w2) * (v1 + -v2) = 1)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0) :
    ((w0 + 2 * w2 = 0 ∧ (v0 + 2 * v2 = 1 ∨ v0 + 2 * v2 = 2)) ∨
      ((w0 + 2 * w2 = 1 ∨ w0 + 2 * w2 = 2) ∧ v0 + 2 * v2 = 0)) := by
  revert v0 v1 v2 w0 w1 w2
  decide +kernel

private lemma zs4n_scal_23x (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha0 : v0 = 0) (ha1 : w0 = 0)
    (hb : (w0 + -w1) * (v0 + -v1) = 1)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0) :
    False := by
  rw [ha0, ha1] at hb hdet
  fin_cases v1 <;> fin_cases w1 <;> norm_num at hb hdet <;> contradiction

private lemma zs4n_scal_32x (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 1) (hb1 : w0 - w1 = 0) (hb2 : v0 - v1 = 0)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    :
    (v0 + v1 = 0 ∧ w0 + w1 = 0) ∨ (2 - w0 * v0 - w1 * v1 - w2 * v2 = 0) := by
  revert v0 v1 v2 w0 w1 w2
  decide +kernel

private lemma zs4n_scal_243 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha1 : w0 = 0) (ha2 : v0 = 0)
    (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc : (w1 + -w2) * (v1 + -v2) = 1)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    :
    (v0 + v1 = 0 ∧ w0 + w1 = 0) ∨ (2 - w0 * v0 - w1 * v1 - w2 * v2 = 0) := by
  revert v0 v1 v2 w0 w1 w2
  simp only [imp_iff_not_or]
  decide +kernel

private lemma zs4n_scal_342 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 1)
    (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc1 : w1 - w2 = 0) (hc2 : v1 - v2 = 0)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    :
    (v0 + v1 = 0 ∧ w0 + w1 = 0) ∨ (2 - w0 * v0 - w1 * v1 - w2 * v2 = 0) := by
  revert v0 v1 v2 w0 w1 w2
  simp only [imp_iff_not_or]
  decide +kernel

private lemma zs4n_scal_424 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 2)
    (hb1 : w0 - w1 = 0) (hb2 : v0 - v1 = 0)
    (hc : (w1 + -w2) * (v1 + -v2) = 2)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    :
    (v0 + v1 = 0 ∧ w0 + w1 = 0) ∨ (2 - w0 * v0 - w1 * v1 - w2 * v2 = 0) := by
  revert v0 v1 v2 w0 w1 w2
  simp only [imp_iff_not_or]
  decide +kernel

private lemma zs4n_scal_434 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 2)
    (hb : (w0 + -w1) * (v0 + -v1) = 1)
    (hc : (w1 + -w2) * (v1 + -v2) = 2)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    :
    (v0 + v1 = 0 ∧ w0 + w1 = 0) ∨ (2 - w0 * v0 - w1 * v1 - w2 * v2 = 0) := by
  revert v0 v1 v2 w0 w1 w2
  simp only [imp_iff_not_or]
  decide +kernel

private lemma zs4n_conj_pairing {u v ρ κ : Fin 4 → ZMod p} (hvu : ∑ i, v i * u i = 2)
    (hκρ : ∑ i, κ i * ρ i = 2) :
    ∑ i, (κ i - (∑ j, κ j * u j) * v i) * (ρ i - (∑ j, v j * ρ j) * u i) = 2 := by
  have key : ∑ i, (κ i - (∑ j, κ j * u j) * v i) * (ρ i - (∑ j, v j * ρ j) * u i) =
      ∑ i, κ i * ρ i + (∑ j, κ j * u j) * (∑ j, v j * ρ j) * ((∑ i, v i * u i) - 2) := by
    simp only [Fin.sum_univ_four]
    ring
  rw [key, hvu, hκρ]
  ring

private lemma zs4n_normalize {v w : Fin 4 → ZMod 3} (hv3 : v 3 ≠ 0) :
    (∑ i, (v 3 • w) i * ((v 3)⁻¹ • v) i = ∑ i, w i * v i) ∧
      ((v 3)⁻¹ • v) 3 = 1 ∧
      Matrix.vecMulVec ((v 3)⁻¹ • v) (v 3 • w) = Matrix.vecMulVec v w := by
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hv3
  · ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

private noncomputable abbrev zs4nDetMat (f : Module.Basis (Fin 4) (ZMod p) U)
    (v w : Fin 4 → ZMod p) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  Matrix.of fun i j => (![(∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i • f.coord i),
    (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i • f.coord i),
    (∑ i, w i • f.coord i)] : Fin 3 → Module.Dual (ZMod p) U) i
    ((![∑ i, (![1, 0, 0, 0] : Fin 4 → ZMod p) i • f i,
       ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i • f i,
       ∑ i, v i • f i] : Fin 3 → U) j)

private lemma zs4n_det_coord (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hcd : 2 * v 0 ≠ 0 ∨ v 0 - v 1 ≠ 0) (hef : w 0 ≠ 0 ∨ w 0 - w 1 ≠ 0) :
    (zs4nDetMat f v w).det = 0 := by
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod p) (![2, 0, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod p) (![1, -1, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hwva : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i * (![1, 0, 0, 0] : Fin 4 → ZMod p) i = 2 := by
    simp [Fin.sum_univ_four]
  have hwvb : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  obtain ⟨hφa, ha_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f ha_mat hwva
  obtain ⟨hφb, hb_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hb_mat hwvb
  obtain ⟨hφg, hg_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hgm hwv
  have hcd' : (∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i • f.coord i) (∑ i, v i • f i) ≠ 0 ∨
      (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i • f.coord i) (∑ i, v i • f i) ≠ 0 := by
    rcases hcd with hc | hc
    · left; simpa [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, sub_eq_add_neg] using hc
    · right; simpa [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, sub_eq_add_neg] using hc
  have hef' : (∑ i, w i • f.coord i) (∑ i, (![1, 0, 0, 0] : Fin 4 → ZMod p) i • f i) ≠ 0 ∨
      (∑ i, w i • f.coord i) (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i • f i) ≠ 0 := by
    rcases hef with hc | hc
    · left; simpa [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, sub_eq_add_neg] using hc
    · right; simpa [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, sub_eq_add_neg] using hc
  have hab1 : (∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i • f.coord i)
      (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i • f i) ≠ 0 := by
    simpa [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four] using
      ZMod.prime_ne_zero p 2 hp
  have hab2 : (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i • f.coord i)
      (∑ i, (![1, 0, 0, 0] : Fin 4 → ZMod p) i • f i) ≠ 0 := by
    simp [Fin.sum_univ_four]
  have hAeq : Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) =
      Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
        Module.reflection hφg} : Set (U ≃ₗ[ZMod p] U)) := by rw [ha_eq, hb_eq, hg_eq]
  have hdet := zs4n_det_zero (A := Subgroup.closure {a, b, g}) hφa hφb hφg hab1 hab2 hcd' hef'
    hAeq hA
  exact hdet

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_hA_matrix {v w : Fin 4 → ZMod p}
    (hwv' : w 0 * v 0 + w 1 * v 1 + w 2 * v 2 + w 3 * v 3 = 2) :
    zs4nDetMat f v w = !![2, 2, 2 * v 0; 1, 2, v 0 - v 1; w 0, w 0 - w 1, 2] := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Fin.sum_univ_four, sub_eq_add_neg, hwv']
  all_goals norm_num

private lemma zs4n_hdet_of_hA (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hcd : 2 * v 0 ≠ 0 ∨ v 0 - v 1 ≠ 0) (hef : w 0 ≠ 0 ∨ w 0 - w 1 ≠ 0) :
    4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 + -v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0 := by
  have hdet := zs4n_det_coord hp h hgm hwv hA hcd hef
  have hwv' : w 0 * v 0 + w 1 * v 1 + w 2 * v 2 + w 3 * v 3 = 2 := by
    simpa [Fin.sum_univ_four] using hwv
  have hC := zs4n_hA_matrix (f := f) hwv'
  rw [hC, Matrix.det_fin_three] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hdet
  linear_combination hdet

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_witness_comm (_hp : p ≠ 2) (h : FFourData f a b c g H G)
    {y : U ≃ₗ[ZMod p] U} {v' w' : Fin 4 → ZMod p}
    (hym : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec v' w')
    (hwv' : ∑ i, w' i * v' i = 2)
    (ha1 : w' 0 = 0) (ha2 : v' 0 = 0)
    (hc1 : w' 1 - w' 2 = 0) (hc2 : v' 1 - v' 2 = 0) :
    y * a = a * y ∧ y * c = c * y := by
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod p) (![2, 0, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have hc_mat : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, -1, 0] : Fin 4 → ZMod p) (![0, 1, -1, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]
  have ha_wv : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i *
      (![1, 0, 0, 0] : Fin 4 → ZMod p) i = 2 := by
    simp [Fin.sum_univ_four]
  have hc_wv : ∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod p) i *
      (![0, 1, -1, 0] : Fin 4 → ZMod p) i = 2 := by
    norm_num [Fin.sum_univ_four]
  obtain ⟨hy_f, hy_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hym hwv'
  obtain ⟨ha_f, ha_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f ha_mat ha_wv
  obtain ⟨hc_f, hc_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hc_mat hc_wv
  refine ⟨?_, ?_⟩
  · rw [hy_eq, ha_eq]
    refine reflection_mul_comm_of_apply_eq_zero hy_f ha_f ?_ ?_
    · rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four]; norm_num; exact ha1
    · rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, ha2]
      norm_num
  · rw [hy_eq, hc_eq]
    refine reflection_mul_comm_of_apply_eq_zero hy_f hc_f ?_ ?_
    · rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four]; norm_num
      linear_combination hc1
    · rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four]; norm_num
      linear_combination hc2

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_witness_order_moved (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {y : U ≃ₗ[ZMod p] U} {v' w' : Fin 4 → ZMod p}
    (hym : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec v' w')
    (hwv' : ∑ i, w' i * v' i = 2)
    (hb : (∑ i, w' i * (![1, -1, 0, 0] : Fin 4 → ZMod p) i) *
      (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i * v' i) = 2)
    (hv3 : v' 3 ≠ 0) :
    orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod p) (![1, -1, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i = 2 := by
    norm_num [Fin.sum_univ_four]
  exact ⟨FFourCoord.orderOf_mul_eq_four_of_toMatrix hp f hym hwv' hb_mat hb_wv hb,
    FFourCoord.not_movedSpace_le_span_of_toMatrix hp f hym hwv' hv3⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_witness_props (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {y : U ≃ₗ[ZMod p] U} {v' w' : Fin 4 → ZMod p}
    (hym : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec v' w')
    (hwv' : ∑ i, w' i * v' i = 2)
    (ha1 : w' 0 = 0) (ha2 : v' 0 = 0)
    (hc1 : w' 1 - w' 2 = 0) (hc2 : v' 1 - v' 2 = 0)
    (hb : (∑ i, w' i * (![1, -1, 0, 0] : Fin 4 → ZMod p) i) *
      (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i * v' i) = 2)
    (hv3 : v' 3 ≠ 0) :
    y * a = a * y ∧ y * c = c * y ∧ orderOf (y * b) = 4 ∧
      ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  obtain ⟨hca, hcc⟩ := zs4n_witness_comm hp h hym hwv' ha1 ha2 hc1 hc2
  obtain ⟨hcb, hcv⟩ := zs4n_witness_order_moved hp h hym hwv' hb hv3
  exact ⟨hca, hcc, hcb, hcv⟩

private lemma zs4n_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide
private lemma zs4n_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

private lemma zs4n_coord_base (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    ∃ v w : Fin 4 → ZMod p,
      LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w ∧
      (∑ i, w i * v i = 2) ∧ v 3 = 1 ∧
      (2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) ∧
      (w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0) := by
  subst p
  obtain ⟨v0, w0, hgm0, hwv0⟩ :=
    FFourCoord.exists_toMatrix_of_isRefl (by norm_num : (3:ℕ) ≠ 2) f h.isRefl_g
  have hv30 : v0 3 ≠ 0 := FFourCoord.apply_three_ne_zero_of_map_ne f hgm0 hwv0 h.map_ne
  have hw30 : w0 3 ≠ 0 := FFourCoord.coroot_three_ne_zero_of_apply_not_mem f hgm0 h.apply_not_mem
  obtain ⟨hsum, hv3', hvec⟩ := zs4n_normalize hv30
  have hgm' : LinearMap.toMatrix f f g.toLinearMap =
      1 - Matrix.vecMulVec ((v0 3)⁻¹ • v0) (v0 3 • w0) := by
    rw [hvec]; exact hgm0
  have hwv' : ∑ i, (v0 3 • w0) i * ((v0 3)⁻¹ • v0) i = 2 := by
    rw [hsum]; exact hwv0
  have hw3nz : (v0 3 • w0) 3 ≠ 0 := by
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hv30 hw30
  refine ⟨(v0 3)⁻¹ • v0, v0 3 • w0, hgm', hwv', hv3', ?_, ?_⟩
  · intro hcon
    apply hw3nz
    have hsum' : ∑ i, (v0 3 • w0) i * ((v0 3)⁻¹ • v0) i = 2 := hwv'
    rw [Fin.sum_univ_four, hv3', mul_one] at hsum'
    linear_combination hsum' + hcon
  · by_contra hcon
    push Not at hcon
    obtain ⟨hw01, hv01⟩ := hcon
    apply hg
    have haba_mat : LinearMap.toMatrix f f (a * b * a).toLinearMap =
        1 - Matrix.vecMulVec (![1, 1, 0, 0] : Fin 4 → ZMod 3) (![1, 1, 0, 0] : Fin 4 → ZMod 3) := by
      rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_a, h.toMatrix_b, FFourCoord.aba_mat_eq]
    have haba_wv : ∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod 3) i *
        (![1, 1, 0, 0] : Fin 4 → ZMod 3) i = 2 := by norm_num [Fin.sum_univ_four]
    obtain ⟨hg_f, hg_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f hgm' hwv'
    obtain ⟨haba_f, haba_eq⟩ := FFourCoord.eq_reflection_of_toMatrix f haba_mat haba_wv
    rw [hg_eq, haba_eq]
    refine reflection_mul_comm_of_apply_eq_zero hg_f haba_f ?_ ?_
    · rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four]
      simpa using hw01
    · rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four]
      simpa using hv01

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_a (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hga : orderOf (g * a) = 2 ∨ orderOf (g * a) = 3 ∨ orderOf (g * a) = 4) :
    (orderOf (g * a) = 2 ∧ w 0 = 0 ∧ v 0 = 0) ∨
      (orderOf (g * a) = 3 ∧ 2 * v 0 * w 0 = 1) ∨
      (orderOf (g * a) = 4 ∧ 2 * v 0 * w 0 = 2) := by
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod p) (![2, 0, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have ha_wv : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i *
      (![1, 0, 0, 0] : Fin 4 → ZMod p) i = 2 := by simp [Fin.sum_univ_four]
  rcases hga with h2 | h3 | h4
  · obtain ⟨h1, h2'⟩ := zs4n_pairing_two hp hgm hwv ha_mat ha_wv h2
    refine Or.inl ⟨h2, ?_, ?_⟩
    · simpa [Fin.sum_univ_four] using h1
    · have h20 : 2 * v 0 = 0 := by simpa [Fin.sum_univ_four] using h2'
      exact mul_left_cancel₀ (ZMod.prime_ne_zero p 2 hp) (by simpa using h20)
  · have h := zs4n_pairing_three hp hgm hwv ha_mat ha_wv h3
    refine Or.inr (Or.inl ⟨h3, ?_⟩)
    simpa [Fin.sum_univ_four, mul_comm, mul_left_comm, mul_assoc] using h
  · have h := zs4n_pairing_four hp hgm hwv ha_mat ha_wv h4
    refine Or.inr (Or.inr ⟨h4, ?_⟩)
    simpa [Fin.sum_univ_four, mul_comm, mul_left_comm, mul_assoc] using h

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_b (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hgb : orderOf (g * b) = 2 ∨ orderOf (g * b) = 3 ∨ orderOf (g * b) = 4) :
    (orderOf (g * b) = 2 ∧ w 0 - w 1 = 0 ∧ v 0 - v 1 = 0) ∨
      (orderOf (g * b) = 3 ∧ (w 0 + -w 1) * (v 0 + -v 1) = 1) ∨
      (orderOf (g * b) = 4 ∧ (w 0 + -w 1) * (v 0 + -v 1) = 2) := by
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod p) (![1, -1, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  rcases hgb with h2 | h3 | h4
  · obtain ⟨h1, h2'⟩ := zs4n_pairing_two hp hgm hwv hb_mat hb_wv h2
    refine Or.inl ⟨h2, ?_, ?_⟩
    · simpa [Fin.sum_univ_four, sub_eq_add_neg] using h1
    · simpa [Fin.sum_univ_four, sub_eq_add_neg] using h2'
  · have h := zs4n_pairing_three hp hgm hwv hb_mat hb_wv h3
    refine Or.inr (Or.inl ⟨h3, ?_⟩)
    simpa [Fin.sum_univ_four] using h
  · have h := zs4n_pairing_four hp hgm hwv hb_mat hb_wv h4
    refine Or.inr (Or.inr ⟨h4, ?_⟩)
    simpa [Fin.sum_univ_four] using h

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_c (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hgc : orderOf (g * c) = 2 ∨ orderOf (g * c) = 3 ∨ orderOf (g * c) = 4) :
    (orderOf (g * c) = 2 ∧ w 1 - w 2 = 0 ∧ v 1 - v 2 = 0) ∨
      (orderOf (g * c) = 3 ∧ (w 1 + -w 2) * (v 1 + -v 2) = 1) ∨
      (orderOf (g * c) = 4 ∧ (w 1 + -w 2) * (v 1 + -v 2) = 2) := by
  have hc_mat : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, -1, 0] : Fin 4 → ZMod p) (![0, 1, -1, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]
  have hc_wv : ∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod p) i *
      (![0, 1, -1, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  rcases hgc with h2 | h3 | h4
  · obtain ⟨h1, h2'⟩ := zs4n_pairing_two hp hgm hwv hc_mat hc_wv h2
    refine Or.inl ⟨h2, ?_, ?_⟩
    · simpa [Fin.sum_univ_four, sub_eq_add_neg] using h1
    · simpa [Fin.sum_univ_four, sub_eq_add_neg] using h2'
  · have h := zs4n_pairing_three hp hgm hwv hc_mat hc_wv h3
    refine Or.inr (Or.inl ⟨h3, ?_⟩)
    simpa [Fin.sum_univ_four] using h
  · have h := zs4n_pairing_four hp hgm hwv hc_mat hc_wv h4
    refine Or.inr (Or.inr ⟨h4, ?_⟩)
    simpa [Fin.sum_univ_four] using h

private noncomputable abbrev zs4n_kappaRot (κ v w : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  fun i => κ i - (∑ j, κ j * v j) * w i

private noncomputable abbrev zs4n_rhoRot (ρ v w : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  fun i => ρ i - (∑ j, w j * ρ j) * v i

private noncomputable abbrev zs4n_w244 (v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_kappaRot (![0, 2, 0, 0] : Fin 4 → ZMod 3) v w

private noncomputable abbrev zs4n_v244 (v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_rhoRot (![0, 1, 0, 0] : Fin 4 → ZMod 3) v w

private lemma zs4n_wit_244_facts (v w : Fin 4 → ZMod 3) (hv3 : v 3 = 1)
    (ha1 : w 0 = 0) (ha2 : v 0 = 0)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 2)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    zs4n_w244 v w 0 = 0 ∧ zs4n_v244 v w 0 = 0 ∧
      zs4n_w244 v w 1 - zs4n_w244 v w 2 = 0 ∧
      zs4n_v244 v w 1 - zs4n_v244 v w 2 = 0 ∧
      (∑ i, zs4n_w244 v w i * (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) *
        (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i * zs4n_v244 v w i) = 2 ∧
      zs4n_v244 v w 3 ≠ 0 := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ :=
    zs4n_scal_244 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha1 ha2 hb hc hdet hnot hw3
  have hS1 : (∑ j, w j * (![0, 1, 0, 0] : Fin 4 → ZMod 3) j) = w 1 := by simp [Fin.sum_univ_four]
  have hx3 : (![0, 1, 0, 0] : Fin 4 → ZMod 3) 3 = 0 := by simp [Matrix.cons_val]
  have hy3 : (![0, 2, 0, 0] : Fin 4 → ZMod 3) 3 = 0 := by simp [Matrix.cons_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zs4n_w244, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val, hy3,
      zero_mul, add_zero, zero_add]
    linear_combination (norm := ring_nf) (-2) * s1
  · simp only [zs4n_v244, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val, hx3,
      mul_zero, add_zero, zero_add]
    linear_combination (norm := ring_nf) (-1) * s2
  · simp only [zs4n_w244, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val, hy3,
      zero_mul, add_zero, zero_add]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s3
  · simp only [zs4n_v244, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val, hx3,
      mul_zero, add_zero, zero_add]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s4
  · simp only [zs4n_w244, zs4n_v244, zs4n_kappaRot, zs4n_rhoRot, Fin.sum_univ_four,
      Matrix.cons_val, hx3, hy3, zero_mul, mul_zero, add_zero, zero_add]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s5
  · show (![0, 1, 0, 0] : Fin 4 → ZMod 3) 3 -
      (∑ j, w j * (![0, 1, 0, 0] : Fin 4 → ZMod 3) j) * v 3 ≠ 0
    rw [hx3, hS1, hv3, mul_one, zero_sub]
    intro h
    exact s6 (by linear_combination (norm := (ring_nf; reduce_mod_char)) h)

private lemma zs4n_wit_244 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (ha1 : w 0 = 0) (ha2 : v 0 = 0)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 2)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  have hbab : LinearMap.toMatrix f f (b * a * b).toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, 0, 0] : Fin 4 → ZMod 3) (![0, 2, 0, 0] : Fin 4 → ZMod 3) := by
    rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_b, h.toMatrix_a, FFourCoord.bab_mat_eq]
  have hκρ : ∑ i, (![0, 2, 0, 0] : Fin 4 → ZMod 3) i * (![0, 1, 0, 0] : Fin 4 → ZMod 3) i = 2 := by
    norm_num [Fin.sum_univ_four]
  have hym := zs4h_conj_mat (f := f) hgm hbab hwv
  have hpair := zs4n_conj_pairing (u := v) (v := w) (ρ := (![0, 1, 0, 0] : Fin 4 → ZMod 3))
    (κ := (![0, 2, 0, 0] : Fin 4 → ZMod 3)) hwv hκρ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := zs4n_wit_244_facts v w hv3 ha1 ha2 hb hc hdet hnot hw3
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbab_mem : b * a * b ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (H.mul_mem (H.mul_mem hbH haH) hbH))
  have hg_mem : g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmem : g * (b * a * b) * g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg_mem hbab_mem) hg_mem
  obtain ⟨hca, hcc, hcb, hcv⟩ := zs4n_witness_props hp h hym hpair h1 h2 h3 h4 h5 h6
  exact ⟨g * (b * a * b) * g, hmem, FFourCoord.isRefl_of_toMatrix hp f hym hpair,
    hca, hcc, hcb, hcv⟩

private noncomputable abbrev zs4n_w422 (v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_kappaRot (![2, 0, 0, 0] : Fin 4 → ZMod 3) v w

private noncomputable abbrev zs4n_v422 (v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_rhoRot (![1, 0, 0, 0] : Fin 4 → ZMod 3) v w

private lemma zs4n_wit_422_facts (v w : Fin 4 → ZMod 3) (hv3 : v 3 = 1)
    (ha : v 0 * w 0 = 1)
    (hb1 : w 0 - w 1 = 0) (hb2 : v 0 - v 1 = 0)
    (hc1 : w 1 - w 2 = 0) (hc2 : v 1 - v 2 = 0)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    zs4n_w422 v w 0 = 0 ∧ zs4n_v422 v w 0 = 0 ∧
      zs4n_w422 v w 1 - zs4n_w422 v w 2 = 0 ∧
      zs4n_v422 v w 1 - zs4n_v422 v w 2 = 0 ∧
      (∑ i, zs4n_w422 v w i * (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) *
        (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i * zs4n_v422 v w i) = 2 ∧
      zs4n_v422 v w 3 ≠ 0 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ :=
    zs4n_scal_422 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb1 hb2 hc1 hc2 hdet hnot hw3
  have hS1 : (∑ j, w j * (![1, 0, 0, 0] : Fin 4 → ZMod 3) j) = w 0 := by simp [Fin.sum_univ_four]
  have hx3 : (![1, 0, 0, 0] : Fin 4 → ZMod 3) 3 = 0 := by simp [Matrix.cons_val]
  have hy3 : (![2, 0, 0, 0] : Fin 4 → ZMod 3) 3 = 0 := by simp [Matrix.cons_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zs4n_w422, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val, hy3,
      zero_mul, add_zero]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s1
  · simp only [zs4n_v422, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val, hx3,
      mul_zero, add_zero]
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * s1
  · simp only [zs4n_w422, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val, hy3,
      zero_mul, add_zero]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s2
  · simp only [zs4n_v422, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val, hx3,
      mul_zero, add_zero]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s3
  · simp only [zs4n_w422, zs4n_v422, zs4n_kappaRot, zs4n_rhoRot, Fin.sum_univ_four,
      Matrix.cons_val, hx3, hy3, zero_mul, mul_zero, add_zero]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s4
  · show (![1, 0, 0, 0] : Fin 4 → ZMod 3) 3 -
      (∑ j, w j * (![1, 0, 0, 0] : Fin 4 → ZMod 3) j) * v 3 ≠ 0
    rw [hx3, hS1, hv3, mul_one, zero_sub]
    intro hh
    exact s5 (by linear_combination (norm := (ring_nf; reduce_mod_char)) hh)

private lemma zs4n_wit_422 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (ha : v 0 * w 0 = 1)
    (hb1 : w 0 - w 1 = 0) (hb2 : v 0 - v 1 = 0)
    (hc1 : w 1 - w 2 = 0) (hc2 : v 1 - v 2 = 0)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod 3) (![2, 0, 0, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have hκρ : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod 3) i * (![1, 0, 0, 0] : Fin 4 → ZMod 3) i = 2 := by
    simp [Fin.sum_univ_four]
  have hym := zs4h_conj_mat (f := f) hgm ha_mat hwv
  have hpair := zs4n_conj_pairing (u := v) (v := w) (ρ := (![1, 0, 0, 0] : Fin 4 → ZMod 3))
    (κ := (![2, 0, 0, 0] : Fin 4 → ZMod 3)) hwv hκρ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    zs4n_wit_422_facts v w hv3 ha hb1 hb2 hc1 hc2 hdet hnot hw3
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have ha_mem : a ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ haH)
  have hg_mem : g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmem : g * a * g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg_mem ha_mem) hg_mem
  obtain ⟨hca, hcc, hcb, hcv⟩ := zs4n_witness_props hp h hym hpair h1 h2 h3 h4 h5 h6
  exact ⟨g * a * g, hmem, FFourCoord.isRefl_of_toMatrix hp f hym hpair, hca, hcc, hcb, hcv⟩

private noncomputable abbrev zs4n_w344a (_v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_kappaRot w (![1, -1, 0, 0] : Fin 4 → ZMod 3) (![1, -1, 0, 0] : Fin 4 → ZMod 3)

private noncomputable abbrev zs4n_v344a (v _w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_rhoRot v (![1, -1, 0, 0] : Fin 4 → ZMod 3) (![1, -1, 0, 0] : Fin 4 → ZMod 3)

private lemma zs4n_wit_344a_facts (v w : Fin 4 → ZMod 3) (hv3 : v 3 = 1)
    (hw1 : w 1 = 0) (hv1 : 2 * v 1 = 0)
    (hsub1 : w 0 - w 2 = 0) (hsub2 : v 0 - v 2 = 0)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2) :
    zs4n_w344a v w 0 = 0 ∧ zs4n_v344a v w 0 = 0 ∧
      zs4n_w344a v w 1 - zs4n_w344a v w 2 = 0 ∧
      zs4n_v344a v w 1 - zs4n_v344a v w 2 = 0 ∧
      (∑ i, zs4n_w344a v w i * (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) *
        (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i * zs4n_v344a v w i) = 2 ∧
      zs4n_v344a v w 3 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [zs4n_w344a, zs4n_kappaRot, Fin.sum_univ_four] using hw1
  · simp [zs4n_v344a, zs4n_rhoRot, Fin.sum_univ_four]
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * hv1
  · simpa [zs4n_w344a, zs4n_kappaRot, Fin.sum_univ_four] using hsub1
  · simpa [zs4n_v344a, zs4n_rhoRot, Fin.sum_univ_four] using hsub2
  · have h : (w 1 + -w 0) * (v 1 + -v 0) =
        (w 0 + -w 1) * (v 0 + -v 1) := by ring
    simpa [zs4n_w344a, zs4n_v344a, zs4n_kappaRot, zs4n_rhoRot, Fin.sum_univ_four, h]
  · have h3 : zs4n_v344a v w 3 = v 3 := by
      simp [zs4n_v344a, zs4n_rhoRot, Fin.sum_univ_four]
    rw [h3, hv3]
    exact one_ne_zero

private lemma zs4n_wit_344a (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (ha : 2 * v 0 * w 0 = 1)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 2)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hsub1 : w 0 - w 2 = 0) (hsub2 : v 0 - v 2 = 0) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨s1, s2, _, _, s5⟩ :=
    zs4n_scal_344a (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc hdet hnot hw3 hsub1 hsub2
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod 3) (![1, -1, 0, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod 3) i = 2 := by norm_num [Fin.sum_univ_four]
  have hym := zs4h_conj_mat (f := f) hb_mat hgm hb_wv
  have hpair := zs4n_conj_pairing (u := (![1, -1, 0, 0] : Fin 4 → ZMod 3))
    (v := (![1, -1, 0, 0] : Fin 4 → ZMod 3)) (ρ := v) (κ := w) hb_wv hwv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    zs4n_wit_344a_facts v w hv3 s1 s2 hsub1 hsub2 s5
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hbH)
  have hg_mem : g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmem : b * g * b ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hb_mem hg_mem) hb_mem
  obtain ⟨hca, hcc, hcb, hcv⟩ := zs4n_witness_props hp h hym hpair h1 h2 h3 h4 h5 h6
  exact ⟨b * g * b, hmem, FFourCoord.isRefl_of_toMatrix hp f hym hpair, hca, hcc, hcb, hcv⟩

private noncomputable abbrev zs4n_vbgb (v : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  zs4n_rhoRot v (![1, -1, 0, 0] : Fin 4 → ZMod p) (![1, -1, 0, 0] : Fin 4 → ZMod p)

private noncomputable abbrev zs4n_wbgb (w : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  zs4n_kappaRot w (![1, -1, 0, 0] : Fin 4 → ZMod p) (![1, -1, 0, 0] : Fin 4 → ZMod p)

private noncomputable abbrev zs4n_v344b (v : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  zs4n_rhoRot (zs4n_vbgb v) (![0, 0, 1, 0] : Fin 4 → ZMod p) (![0, 0, 2, 0] : Fin 4 → ZMod p)

private noncomputable abbrev zs4n_w344b (w : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  zs4n_kappaRot (zs4n_wbgb w) (![0, 0, 1, 0] : Fin 4 → ZMod p) (![0, 0, 2, 0] : Fin 4 → ZMod p)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_mat_344b (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) :
    LinearMap.toMatrix f f ((c * (b * a * b) * c) * (b * g * b) *
        (c * (b * a * b) * c)).toLinearMap =
      1 - Matrix.vecMulVec (zs4n_v344b v) (zs4n_w344b w) ∧
      (∑ i, zs4n_w344b w i * zs4n_v344b v i) = 2 := by
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod p)
        (![1, -1, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  have hbab : LinearMap.toMatrix f f (b * a * b).toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, 0, 0] : Fin 4 → ZMod p)
        (![0, 2, 0, 0] : Fin 4 → ZMod p) := by
    rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_b, h.toMatrix_a, FFourCoord.bab_mat_eq]
  have hc_mat : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, -1, 0] : Fin 4 → ZMod p)
        (![0, 1, -1, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]
  have hc_wv : ∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod p) i *
      (![0, 1, -1, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  have heps : LinearMap.toMatrix f f (c * (b * a * b) * c).toLinearMap =
      1 - Matrix.vecMulVec (![0, 0, 1, 0] : Fin 4 → ZMod p)
        (![0, 0, 2, 0] : Fin 4 → ZMod p) := by
    rw [toMatrix_coe_mul, toMatrix_coe_mul, toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_c,
      h.toMatrix_b, h.toMatrix_a, FFourCoord.cbabc_mat_eq]
  have heps_wv : ∑ i, (![0, 0, 2, 0] : Fin 4 → ZMod p) i *
      (![0, 0, 1, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  have hbgb := zs4h_conj_mat (f := f) (u := (![1, -1, 0, 0] : Fin 4 → ZMod p))
    (v := (![1, -1, 0, 0] : Fin 4 → ZMod p)) (ρ := v) (κ := w) hb_mat hgm hb_wv
  have hbgb_pair := zs4n_conj_pairing (u := (![1, -1, 0, 0] : Fin 4 → ZMod p))
    (v := (![1, -1, 0, 0] : Fin 4 → ZMod p)) (ρ := v) (κ := w) hb_wv hwv
  have hy := zs4h_conj_mat (f := f) (u := (![0, 0, 1, 0] : Fin 4 → ZMod p))
    (v := (![0, 0, 2, 0] : Fin 4 → ZMod p)) (ρ := zs4n_vbgb v) (κ := zs4n_wbgb w)
    heps hbgb heps_wv
  have hpair := zs4n_conj_pairing (u := (![0, 0, 1, 0] : Fin 4 → ZMod p))
    (v := (![0, 0, 2, 0] : Fin 4 → ZMod p)) (ρ := zs4n_vbgb v) (κ := zs4n_wbgb w)
    heps_wv hbgb_pair
  exact ⟨hy, hpair⟩

private lemma zs4n_wit_344b_facts (v w : Fin 4 → ZMod 3) (hv3 : v 3 = 1)
    (ha : 2 * v 0 * w 0 = 1)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 2)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 -
      2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hsub : (w 0 - w 2) * (v 0 - v 2) = 2) :
    zs4n_w344b w 0 = 0 ∧ zs4n_v344b v 0 = 0 ∧
      zs4n_w344b w 1 - zs4n_w344b w 2 = 0 ∧
      zs4n_v344b v 1 - zs4n_v344b v 2 = 0 ∧
      (∑ i, zs4n_w344b w i * (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) *
        (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i * zs4n_v344b v i) = 2 ∧
      zs4n_v344b v 3 ≠ 0 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ :=
    zs4n_scal_344b (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc hdet hnot hw3 hsub
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zs4n_w344b, zs4n_wbgb, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := ring_nf) s1
  · simp only [zs4n_v344b, zs4n_vbgb, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * s2
  · simp only [zs4n_w344b, zs4n_wbgb, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := ring_nf) s3
  · simp only [zs4n_v344b, zs4n_vbgb, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := ring_nf) s4
  · simp only [zs4n_w344b, zs4n_v344b, zs4n_wbgb, zs4n_vbgb, zs4n_kappaRot, zs4n_rhoRot,
      Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := ring_nf) s5
  · have h6 : zs4n_v344b v 3 = v 3 := by
      simp only [zs4n_v344b, zs4n_vbgb, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val]
      ring
    rw [h6, hv3]
    exact zs4n_one_ne_zero

private lemma zs4n_wit_344b (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (ha : 2 * v 0 * w 0 = 1)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 2)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hsub : (w 0 - w 2) * (v 0 - v 2) = 2) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨hy, hpair⟩ := zs4n_mat_344b h hgm hwv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    zs4n_wit_344b_facts v w hv3 ha hb hc hdet hnot hw3 hsub
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbabH : b * a * b ∈ H := H.mul_mem (H.mul_mem hbH haH) hbH
  have hepsH : c * (b * a * b) * c ∈ H := H.mul_mem (H.mul_mem hcH hbabH) hcH
  have heps_mem : c * (b * a * b) * c ∈
      Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hepsH)
  have hb_mem : b ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hbH)
  have hg_mem : g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbgb_mem : b * g * b ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hb_mem hg_mem) hb_mem
  have hmem : (c * (b * a * b) * c) * (b * g * b) * (c * (b * a * b) * c) ∈
      Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ heps_mem hbgb_mem) heps_mem
  obtain ⟨hca, hcc, hcb, hcv⟩ := zs4n_witness_props hp h hy hpair h1 h2 h3 h4 h5 h6
  exact ⟨(c * (b * a * b) * c) * (b * g * b) * (c * (b * a * b) * c), hmem,
    FFourCoord.isRefl_of_toMatrix hp f hy hpair, hca, hcc, hcb, hcv⟩

private noncomputable abbrev zs4n_w423 (v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_kappaRot (zs4n_w422 v w) (![0, 1, 0, 0] : Fin 4 → ZMod 3)
    (![0, 2, 0, 0] : Fin 4 → ZMod 3)

private noncomputable abbrev zs4n_v423 (v w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  zs4n_rhoRot (zs4n_v422 v w) (![0, 1, 0, 0] : Fin 4 → ZMod 3)
    (![0, 2, 0, 0] : Fin 4 → ZMod 3)

private lemma zs4n_wit_423_facts (v w : Fin 4 → ZMod 3) (hv3 : v 3 = 1)
    (ha : v 0 * w 0 = 1)
    (hb1 : w 0 - w 1 = 0) (hb2 : v 0 - v 1 = 0)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 1)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 -
      2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    zs4n_w423 v w 0 = 0 ∧ zs4n_v423 v w 0 = 0 ∧
      zs4n_w423 v w 1 - zs4n_w423 v w 2 = 0 ∧
      zs4n_v423 v w 1 - zs4n_v423 v w 2 = 0 ∧
      (∑ i, zs4n_w423 v w i * (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) *
        (∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i * zs4n_v423 v w i) = 2 ∧
      zs4n_v423 v w 3 ≠ 0 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ :=
    zs4n_scal_423 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb1 hb2 hc hdet hnot hw3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zs4n_w423, zs4n_w422, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := (ring_nf; reduce_mod_char)) (-2) * s1
  · simp only [zs4n_v423, zs4n_v422, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := (ring_nf; reduce_mod_char)) (-1) * s1
  · simp only [zs4n_w423, zs4n_w422, zs4n_kappaRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := (ring_nf; reduce_mod_char)) (-1) * s2
  · simp only [zs4n_v423, zs4n_v422, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := ring_nf) s3
  · simp only [zs4n_w423, zs4n_v423, zs4n_w422, zs4n_v422, zs4n_kappaRot, zs4n_rhoRot,
      Fin.sum_univ_four, Matrix.cons_val]
    linear_combination (norm := (ring_nf; reduce_mod_char)) s4
  · have h6 : zs4n_v423 v w 3 = -w 0 * v 3 := by
      simp only [zs4n_v423, zs4n_v422, zs4n_rhoRot, Fin.sum_univ_four, Matrix.cons_val]
      ring
    rw [h6, hv3, mul_one]
    intro h
    exact s5 (by linear_combination (norm := (ring_nf; reduce_mod_char)) h)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_mat_423 (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) :
    LinearMap.toMatrix f f ((b * a * b) * (g * a * g) * (b * a * b)).toLinearMap =
      1 - Matrix.vecMulVec
        (zs4n_rhoRot (zs4n_rhoRot (![1, 0, 0, 0] : Fin 4 → ZMod p) v w)
          (![0, 1, 0, 0] : Fin 4 → ZMod p) (![0, 2, 0, 0] : Fin 4 → ZMod p))
        (zs4n_kappaRot (zs4n_kappaRot (![2, 0, 0, 0] : Fin 4 → ZMod p) v w)
          (![0, 1, 0, 0] : Fin 4 → ZMod p) (![0, 2, 0, 0] : Fin 4 → ZMod p)) ∧
      (∑ i, zs4n_kappaRot (zs4n_kappaRot (![2, 0, 0, 0] : Fin 4 → ZMod p) v w)
          (![0, 1, 0, 0] : Fin 4 → ZMod p) (![0, 2, 0, 0] : Fin 4 → ZMod p) i *
        zs4n_rhoRot (zs4n_rhoRot (![1, 0, 0, 0] : Fin 4 → ZMod p) v w)
          (![0, 1, 0, 0] : Fin 4 → ZMod p) (![0, 2, 0, 0] : Fin 4 → ZMod p) i) = 2 := by
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod p)
        (![2, 0, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have ha_wv : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i *
      (![1, 0, 0, 0] : Fin 4 → ZMod p) i = 2 := by simp [Fin.sum_univ_four]
  have hbab : LinearMap.toMatrix f f (b * a * b).toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, 0, 0] : Fin 4 → ZMod p)
        (![0, 2, 0, 0] : Fin 4 → ZMod p) := by
    rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_b, h.toMatrix_a, FFourCoord.bab_mat_eq]
  have hbab_wv : ∑ i, (![0, 2, 0, 0] : Fin 4 → ZMod p) i *
      (![0, 1, 0, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  have hgag := zs4h_conj_mat (f := f) (u := v) (v := w)
    (ρ := (![1, 0, 0, 0] : Fin 4 → ZMod p)) (κ := (![2, 0, 0, 0] : Fin 4 → ZMod p))
    hgm ha_mat hwv
  have hpairgag := zs4n_conj_pairing (u := v) (v := w)
    (ρ := (![1, 0, 0, 0] : Fin 4 → ZMod p)) (κ := (![2, 0, 0, 0] : Fin 4 → ZMod p))
    hwv ha_wv
  have hy := zs4h_conj_mat (f := f) (u := (![0, 1, 0, 0] : Fin 4 → ZMod p))
    (v := (![0, 2, 0, 0] : Fin 4 → ZMod p))
    (ρ := zs4n_rhoRot (![1, 0, 0, 0] : Fin 4 → ZMod p) v w)
    (κ := zs4n_kappaRot (![2, 0, 0, 0] : Fin 4 → ZMod p) v w) hbab hgag hbab_wv
  have hpair := zs4n_conj_pairing (u := (![0, 1, 0, 0] : Fin 4 → ZMod p))
    (v := (![0, 2, 0, 0] : Fin 4 → ZMod p))
    (ρ := zs4n_rhoRot (![1, 0, 0, 0] : Fin 4 → ZMod p) v w)
    (κ := zs4n_kappaRot (![2, 0, 0, 0] : Fin 4 → ZMod p) v w) hbab_wv hpairgag
  exact ⟨hy, hpair⟩

private lemma zs4n_wit_423 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (ha : v 0 * w 0 = 1)
    (hb1 : w 0 - w 1 = 0) (hb2 : v 0 - v 1 = 0)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 1)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨hy, hpair⟩ := zs4n_mat_423 h hgm hwv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    zs4n_wit_423_facts v w hv3 ha hb1 hb2 hc hdet hnot hw3
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have ha_mem : a ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ haH)
  have hg_mem : g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbab_mem : b * a * b ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (H.mul_mem (H.mul_mem hbH haH) hbH))
  have hgag_mem : g * a * g ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg_mem ha_mem) hg_mem
  have hmem : (b * a * b) * (g * a * g) * (b * a * b) ∈
      Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod 3] U))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hbab_mem hgag_mem) hbab_mem
  obtain ⟨hca, hcc, hcb, hcv⟩ := zs4n_witness_props hp h hy hpair h1 h2 h3 h4 h5 h6
  exact ⟨(b * a * b) * (g * a * g) * (b * a * b), hmem,
    FFourCoord.isRefl_of_toMatrix hp f hy hpair, hca, hcc, hcb, hcv⟩

private lemma zs4n_etaOK_four_zero {s : ZMod 3} (h : EtaOK 4 s 0) : s = 0 := by
  unfold EtaOK at h
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · rw [mul_zero] at h; exact absurd h (Ne.symm zs4n_one_ne_zero)
  · rw [mul_zero] at h; exact absurd h (Ne.symm zs4n_two_ne_zero)
  · exact absurd h (by omega)

private lemma zs4n_eta343_setup (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) :
    EtaOK 4 (∑ i, zs4n_kappaRot w (![1, -1, 0, 0] : Fin 4 → ZMod p)
        (![1, -1, 0, 0] : Fin 4 → ZMod p) i * (![0, 1, -1, 0] : Fin 4 → ZMod p) i)
      (∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod p) i *
        zs4n_rhoRot v (![1, -1, 0, 0] : Fin 4 → ZMod p)
          (![1, -1, 0, 0] : Fin 4 → ZMod p) i) := by
  subst p
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod 3) (![1, -1, 0, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod 3) i = 2 := by norm_num [Fin.sum_univ_four]
  have hy0m := zs4h_conj_mat (f := f) hb_mat hgm hb_wv
  have hc_mat : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, -1, 0] : Fin 4 → ZMod 3) (![0, 1, -1, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]
  have hc_wv : ∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod 3) i *
      (![0, 1, -1, 0] : Fin 4 → ZMod 3) i = 2 := by norm_num [Fin.sum_univ_four]
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hy0G : b * g * b ∈ G := G.mul_mem (G.mul_mem (h.H_le hbH) h.g_mem) (h.H_le hbH)
  have hcG : c ∈ G := h.H_le hcH
  have hgH : g ∉ H := fun hgH => h.map_ne (zs4k_conj_data h hgH).1
  have hne : b * g * b ≠ c := by
    intro heq
    apply hgH
    have hb2 : b * b = 1 := zs4k_b_sq (f := f) h.toMatrix_b
    have : g = b * c * b := by
      calc g = b * (b * g * b) * b := by
            rw [show b * (b * g * b) * b = (b * b) * g * (b * b) by group, hb2,
              one_mul, mul_one]
        _ = b * c * b := by rw [heq]
    rw [this]
    exact H.mul_mem (H.mul_mem hbH hcH) hbH
  have hy0pair : (∑ i, (fun i => w i -
      (∑ j, w j * (![1, -1, 0, 0] : Fin 4 → ZMod 3) j) * (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) i *
      (fun i => v i -
      (∑ j, (![1, -1, 0, 0] : Fin 4 → ZMod 3) j * v j) *
        (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) i) = 2 :=
    zs4n_conj_pairing (u := (![1, -1, 0, 0] : Fin 4 → ZMod 3))
      (v := (![1, -1, 0, 0] : Fin 4 → ZMod 3)) (ρ := v) (κ := w) hb_wv hwv
  have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hy0G hcG hne hy0m hy0pair hc_mat hc_wv
  exact heta

private lemma zs4n_eta343 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) :
    EtaOK 4 (w 0 + 2 * w 2) (v 0 + 2 * v 2) := by
  subst p
  have heta := zs4n_eta343_setup hp rfl h hgm hwv
  have hpair1 : (∑ i, zs4n_kappaRot w (![1, -1, 0, 0] : Fin 4 → ZMod 3)
      (![1, -1, 0, 0] : Fin 4 → ZMod 3) i * (![0, 1, -1, 0] : Fin 4 → ZMod 3) i) =
      w 0 + 2 * w 2 := by
    simp only [Fin.sum_univ_four, Matrix.cons_val, mul_zero, add_zero, zero_add,
      zs4n_kappaRot]
    ring_nf; reduce_mod_char; ring
  have hpair2 : (∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod 3) i *
      zs4n_rhoRot v (![1, -1, 0, 0] : Fin 4 → ZMod 3) (![1, -1, 0, 0] : Fin 4 → ZMod 3) i) =
      v 0 + 2 * v 2 := by
    simp only [Fin.sum_univ_four, Matrix.cons_val, zero_mul, mul_zero, add_zero, zero_add,
      zs4n_rhoRot]
    ring_nf; reduce_mod_char; ring
  rwa [hpair1, hpair2] at heta

private lemma zs4n_case_343 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (hga : orderOf (g * a) = 3) (hgb : orderOf (g * b) = 4) (hgc : orderOf (g * c) = 3)
    (ha : 2 * v 0 * w 0 = 1)
    (hb : (w 0 + -w 1) * (v 0 + -v 1) = 2)
    (hc : (w 1 + -w 2) * (v 1 + -v 2) = 1)
    (hdet : 4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  have hdich := zs4n_scal_343 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc hdet
  exfalso
  have heta := zs4n_eta343 hp rfl h hgm hwv
  rcases hdich with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2' : v 0 + 2 * v 2 ≠ 0 := by
      intro h0
      rcases h2 with h2 | h2
      · rw [h2] at h0; exact zs4n_one_ne_zero h0
      · rw [h2] at h0; exact zs4n_two_ne_zero h0
    rcases FFourCoord.mul_eq_one_or_two_of_etaOK_four heta h2' with hh | hh
    · rw [h1, zero_mul] at hh; exact absurd hh.symm zs4n_one_ne_zero
    · rw [h1, zero_mul] at hh; exact absurd hh.symm zs4n_two_ne_zero
  · have h1' : w 0 + 2 * w 2 ≠ 0 := by
      intro h0
      rcases h1 with h1 | h1
      · rw [h1] at h0; exact zs4n_one_ne_zero h0
      · rw [h1] at h0; exact zs4n_two_ne_zero h0
    have hp10 : w 0 + 2 * w 2 = 0 := by
      have hh := heta
      rw [h2] at hh
      exact zs4n_etaOK_four_zero hh
    exact h1' hp10

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_conn_a (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (ha : orderOf (g * a) = 3 ∨ orderOf (g * a) = 4) : 2 * v 0 ≠ 0 ∧ w 0 ≠ 0 := by
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod p) (![2, 0, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have ha_wv : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod p) i *
      (![1, 0, 0, 0] : Fin 4 → ZMod p) i = 2 := by simp [Fin.sum_univ_four]
  rcases ha with h3 | h4
  · have hh : w 0 * (2 * v 0) = 1 := by
      simpa [Fin.sum_univ_four] using zs4n_pairing_three hp hgm hwv ha_mat ha_wv h3
    refine ⟨?_, ?_⟩
    · intro h0; rw [h0, mul_zero] at hh; exact one_ne_zero hh.symm
    · intro h0; rw [h0, zero_mul] at hh; exact one_ne_zero hh.symm
  · have hh : w 0 * (2 * v 0) = 2 := by
      simpa [Fin.sum_univ_four] using zs4n_pairing_four hp hgm hwv ha_mat ha_wv h4
    refine ⟨?_, ?_⟩
    · intro h0; rw [h0, mul_zero] at hh; exact ZMod.prime_ne_zero p 2 hp hh.symm
    · intro h0; rw [h0, zero_mul] at hh
      exact ZMod.prime_ne_zero p 2 hp hh.symm

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_conn_b (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hb : orderOf (g * b) = 3 ∨ orderOf (g * b) = 4) : v 0 - v 1 ≠ 0 ∧ w 0 - w 1 ≠ 0 := by
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod p) (![1, -1, 0, 0] : Fin 4 → ZMod p) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod p) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod p) i = 2 := by norm_num [Fin.sum_univ_four]
  rcases hb with h3 | h4
  · have hh : (w 0 + -w 1) * (v 0 + -v 1) = 1 := by
      simpa [Fin.sum_univ_four] using zs4n_pairing_three hp hgm hwv hb_mat hb_wv h3
    refine ⟨?_, ?_⟩
    · intro h0; rw [sub_eq_add_neg] at h0; rw [h0, mul_zero] at hh; exact one_ne_zero hh.symm
    · intro h0; rw [sub_eq_add_neg] at h0; rw [h0, zero_mul] at hh; exact one_ne_zero hh.symm
  · have hh : (w 0 + -w 1) * (v 0 + -v 1) = 2 := by
      simpa [Fin.sum_univ_four] using zs4n_pairing_four hp hgm hwv hb_mat hb_wv h4
    refine ⟨?_, ?_⟩
    · intro h0; rw [sub_eq_add_neg] at h0; rw [h0, mul_zero] at hh
      exact ZMod.prime_ne_zero p 2 hp hh.symm
    · intro h0; rw [sub_eq_add_neg] at h0; rw [h0, zero_mul] at hh
      exact ZMod.prime_ne_zero p 2 hp hh.symm

private lemma zs4n_hdet_a (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (ha : orderOf (g * a) = 3 ∨ orderOf (g * a) = 4) :
    4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0 := by
  obtain ⟨hv, hw⟩ := zs4n_conn_a hp h hgm hwv ha
  simpa [sub_eq_add_neg] using zs4n_hdet_of_hA hp h hgm hwv hA (Or.inl hv) (Or.inl hw)

private lemma zs4n_hdet_b (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    (hb : orderOf (g * b) = 3 ∨ orderOf (g * b) = 4) :
    4 - 2 * (w 0 + -w 1) * (v 0 + -v 1) + 2 * (v 0 - v 1) * w 0 - 2 * v 0 * (w 0 + w 1) = 0 := by
  obtain ⟨hv, hw⟩ := zs4n_conn_b hp h hgm hwv hb
  simpa [sub_eq_add_neg] using zs4n_hdet_of_hA hp h hgm hwv hA (Or.inr hv) (Or.inr hw)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_a2 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hga : orderOf (g * a) = 2) : w 0 = 0 ∧ v 0 = 0 := by
  rcases zs4n_fact_a hp h hgm hwv (Or.inl hga) with ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨h1, h2⟩
  · exact absurd (hga.symm.trans h) (by decide)
  · exact absurd (hga.symm.trans h) (by decide)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_a3 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hga : orderOf (g * a) = 3) : 2 * v 0 * w 0 = 1 := by
  rcases zs4n_fact_a hp h hgm hwv (Or.inr (Or.inl hga)) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd (hga.symm.trans h) (by decide)
  · exact h
  · exact absurd (hga.symm.trans h) (by decide)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_a4 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hga : orderOf (g * a) = 4) : 2 * v 0 * w 0 = 2 := by
  rcases zs4n_fact_a hp h hgm hwv (Or.inr (Or.inr hga)) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd (hga.symm.trans h) (by decide)
  · exact absurd (hga.symm.trans h) (by decide)
  · exact h

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_b2 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hgb : orderOf (g * b) = 2) : w 0 - w 1 = 0 ∧ v 0 - v 1 = 0 := by
  rcases zs4n_fact_b hp h hgm hwv (Or.inl hgb) with ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨h1, h2⟩
  · exact absurd (hgb.symm.trans h) (by decide)
  · exact absurd (hgb.symm.trans h) (by decide)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_b3 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hgb : orderOf (g * b) = 3) :
    (w 0 + -w 1) * (v 0 + -v 1) = 1 := by
  rcases zs4n_fact_b hp h hgm hwv (Or.inr (Or.inl hgb)) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd (hgb.symm.trans h) (by decide)
  · exact h
  · exact absurd (hgb.symm.trans h) (by decide)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_b4 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hgb : orderOf (g * b) = 4) :
    (w 0 + -w 1) * (v 0 + -v 1) = 2 := by
  rcases zs4n_fact_b hp h hgm hwv (Or.inr (Or.inr hgb)) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd (hgb.symm.trans h) (by decide)
  · exact absurd (hgb.symm.trans h) (by decide)
  · exact h

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_c2 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hgc : orderOf (g * c) = 2) : w 1 - w 2 = 0 ∧ v 1 - v 2 = 0 := by
  rcases zs4n_fact_c hp h hgm hwv (Or.inl hgc) with ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨h1, h2⟩
  · exact absurd (hgc.symm.trans h) (by decide)
  · exact absurd (hgc.symm.trans h) (by decide)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_c3 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hgc : orderOf (g * c) = 3) :
    (w 1 + -w 2) * (v 1 + -v 2) = 1 := by
  rcases zs4n_fact_c hp h hgm hwv (Or.inr (Or.inl hgc)) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd (hgc.symm.trans h) (by decide)
  · exact h
  · exact absurd (hgc.symm.trans h) (by decide)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_fact_c4 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hgc : orderOf (g * c) = 4) :
    (w 1 + -w 2) * (v 1 + -v 2) = 2 := by
  rcases zs4n_fact_c hp h hgm hwv (Or.inr (Or.inr hgc)) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd (hgc.symm.trans h) (by decide)
  · exact absurd (hgc.symm.trans h) (by decide)
  · exact h

private lemma zs4n_case_242 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (hga : orderOf (g * a) = 2) (hgb : orderOf (g * b) = 4) (hgc : orderOf (g * c) = 2) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  have ha_mat : LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (![1, 0, 0, 0] : Fin 4 → ZMod 3) (![2, 0, 0, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]
  have hb_mat : LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (![1, -1, 0, 0] : Fin 4 → ZMod 3) (![1, -1, 0, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]
  have hc_mat : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (![0, 1, -1, 0] : Fin 4 → ZMod 3) (![0, 1, -1, 0] : Fin 4 → ZMod 3) := by
    rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]
  have ha_wv : ∑ i, (![2, 0, 0, 0] : Fin 4 → ZMod 3) i *
      (![1, 0, 0, 0] : Fin 4 → ZMod 3) i = 2 := by
    simp [Fin.sum_univ_four]
  have hb_wv : ∑ i, (![1, -1, 0, 0] : Fin 4 → ZMod 3) i *
      (![1, -1, 0, 0] : Fin 4 → ZMod 3) i = 2 := by
    norm_num [Fin.sum_univ_four]
  have hc_wv : ∑ i, (![0, 1, -1, 0] : Fin 4 → ZMod 3) i *
      (![0, 1, -1, 0] : Fin 4 → ZMod 3) i = 2 := by
    norm_num [Fin.sum_univ_four]
  obtain ⟨ha1, ha2⟩ := zs4n_pairing_two hp hgm hwv ha_mat ha_wv hga
  have hb4 := zs4n_pairing_four hp hgm hwv hb_mat hb_wv hgb
  obtain ⟨hc1, hc2⟩ := zs4n_pairing_two hp hgm hwv hc_mat hc_wv hgc
  have ha1' : w 0 = 0 := by simpa [Fin.sum_univ_four] using ha1
  have ha2' : v 0 = 0 := by
    have h2 : 2 * v 0 = 0 := by simpa [Fin.sum_univ_four] using ha2
    exact mul_left_cancel₀ zs4n_two_ne_zero (by simpa using h2)
  have hb4' : (w 0 + -w 1) * (v 0 + -v 1) = 2 := by simpa [Fin.sum_univ_four] using hb4
  have hc1' : w 1 - w 2 = 0 := by
    rw [sub_eq_add_neg]
    simpa [Fin.sum_univ_four] using hc1
  have hc2' : v 1 - v 2 = 0 := by
    rw [sub_eq_add_neg]
    simpa [Fin.sum_univ_four] using hc2
  have hv3' : v 3 ≠ 0 := by rw [hv3]; exact zs4n_one_ne_zero
  obtain ⟨hca, hcc, hcb, hcv⟩ := zs4n_witness_props hp h hgm hwv ha1' ha2' hc1' hc2' hb4 hv3'
  exact ⟨g, Subgroup.subset_closure (Set.mem_insert _ _), h.isRefl_g, hca, hcc, hcb, hcv⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n_orders_c (_hp : p ≠ 2) (h : FFourData f a b c g H G) :
    orderOf (g * c) ≤ 4 ∧ orderOf (g * c) ≠ 1 := by
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  refine ⟨h.dmax.1 g h.g_mem c (h.H_le hcH) h.isRefl_g hcR, ?_⟩
  intro h1
  have hg_eq_c : g = c := by
    have h' := orderOf_eq_one_iff.mp h1
    calc g = g * (c * c) := by rw [hcR.1, mul_one]
      _ = (g * c) * c := by group
      _ = c := by rw [h', one_mul]
  exact h.map_ne (by rw [hg_eq_c]; exact (zs4k_conj_data h hcH).1)

private lemma zs4n_scal_344 (v0 v1 v2 w0 w1 w2 : ZMod 3)
    (ha : 2 * v0 * w0 = 1)
    (hb : (w0 + -w1) * (v0 + -v1) = 2)
    (hc : (w1 + -w2) * (v1 + -v2) = 2)
    (hdet : 4 - 2 * (w0 + -w1) * (v0 + -v1) + 2 * (v0 - v1) * w0 - 2 * v0 * (w0 + w1) = 0)
    (hnot : w0 + w1 ≠ 0 ∨ v0 + v1 ≠ 0)
    (hw3 : 2 - w0 * v0 - w1 * v1 - w2 * v2 ≠ 0) :
    (w0 - w2 = 0 ∧ v0 - v2 = 0) ∨ ((w0 - w2) * (v0 - v2) = 2) := by
  revert v0 v1 v2 w0 w1 w2
  decide +kernel

private lemma zs4n_order34_of_le {x : U ≃ₗ[ZMod p] U} (hle : orderOf x ≤ 4)
    (hne : orderOf x ≠ 1) : orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by
  have hpos := zs4n_orderOf_pos x
  omega

private lemma zs4n_main_ga2 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hga : orderOf (g * a) = 2) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨-, hgb_le, -, hgb_ne1, hnot_both⟩ := zs4n_orders hp h hg
  obtain ⟨hgc_le, hgc_ne1⟩ := zs4n_orders_c hp h
  have hgb34 := zs4n_order34_of_le hgb_le hgb_ne1
  have hgc34 := zs4n_order34_of_le hgc_le hgc_ne1
  obtain ⟨ha1, ha2⟩ := zs4n_fact_a2 hp h hgm hwv hga
  rcases hgb34 with hgb2 | hgb3 | hgb4
  · exact (hnot_both ⟨hga, hgb2⟩).elim
  · have hb := zs4n_fact_b3 hp h hgm hwv hgb3
    have hdet := zs4n_hdet_b hp h hgm hwv hA (Or.inl hgb3)
    exact (zs4n_scal_23x (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha2 ha1 hb hdet hw3).elim
  · have hb := zs4n_fact_b4 hp h hgm hwv hgb4
    have hdet := zs4n_hdet_b hp h hgm hwv hA (Or.inr hgb4)
    rcases hgc34 with hgc2 | hgc3 | hgc4
    · exact zs4n_case_242 hp rfl h hgm hwv hv3 hga hgb4 hgc2
    · have hc := zs4n_fact_c3 hp h hgm hwv hgc3
      rcases zs4n_scal_243 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha1 ha2 hb hc hdet with
        ⟨h1, h2⟩ | h3
      · exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
      · exact (hw3 h3).elim
    · have hc := zs4n_fact_c4 hp h hgm hwv hgc4
      exact zs4n_wit_244 hp rfl h hgm hwv hv3 ha1 ha2 hb hc hdet hnot hw3

private lemma zs4n_main_ga3 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hga : orderOf (g * a) = 3) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨-, hgb_le, -, hgb_ne1, -⟩ := zs4n_orders hp h hg
  obtain ⟨hgc_le, hgc_ne1⟩ := zs4n_orders_c hp h
  have hgb34 := zs4n_order34_of_le hgb_le hgb_ne1
  have hgc34 := zs4n_order34_of_le hgc_le hgc_ne1
  have ha := zs4n_fact_a3 hp h hgm hwv hga
  have hdet := zs4n_hdet_a hp h hgm hwv hA (Or.inl hga)
  rcases hgb34 with hgb2 | hgb3 | hgb4
  · have hb := zs4n_fact_b2 hp h hgm hwv hgb2
    rcases zs4n_scal_32x (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb.1 hb.2 hdet with
      ⟨h1, h2⟩ | h3
    · exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
    · exact (hw3 h3).elim
  · exact (hA (zs4n_exclude_33 hp h hga hgb3)).elim
  · have hb := zs4n_fact_b4 hp h hgm hwv hgb4
    have hdet' := zs4n_hdet_b hp h hgm hwv hA (Or.inr hgb4)
    rcases hgc34 with hgc2 | hgc3 | hgc4
    · have hc := zs4n_fact_c2 hp h hgm hwv hgc2
      rcases zs4n_scal_342 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc.1 hc.2 hdet' with
        ⟨h1, h2⟩ | h3
      · exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
      · exact (hw3 h3).elim
    · have hc := zs4n_fact_c3 hp h hgm hwv hgc3
      exact zs4n_case_343 hp rfl h hgm hwv hv3 hga hgb4 hgc3 ha hb hc hdet' hnot hw3
    · have hc := zs4n_fact_c4 hp h hgm hwv hgc4
      rcases zs4n_scal_344 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc hdet' hnot hw3 with
        ⟨hsub1, hsub2⟩ | hsub
      · exact zs4n_wit_344a hp rfl h hgm hwv hv3 ha hb hc hdet' hnot hw3 hsub1 hsub2
      · exact zs4n_wit_344b hp rfl h hgm hwv hv3 ha hb hc hdet' hnot hw3 hsub

private lemma zs4n_ga4_gb3 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hga : orderOf (g * a) = 4) (hgb : orderOf (g * b) = 3)
    (ha : 2 * v 0 * w 0 = 2) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨hgc_le, hgc_ne1⟩ := zs4n_orders_c hp h
  have hgc34 := zs4n_order34_of_le hgc_le hgc_ne1
  have hb := zs4n_fact_b3 hp h hgm hwv hgb
  have hdet := zs4n_hdet_a hp h hgm hwv hA (Or.inr hga)
  rcases hgc34 with hgc2 | hgc3 | hgc4
  · have hc := zs4n_fact_c2 hp h hgm hwv hgc2
    rcases zs4n_scal_432 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc.2 hc.1 hdet with ⟨h1, h2⟩
    exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
  · have hc := zs4n_fact_c3 hp h hgm hwv hgc3
    rcases zs4n_scal_433 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc hdet with ⟨h1, h2⟩
    exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
  · have hc := zs4n_fact_c4 hp h hgm hwv hgc4
    rcases zs4n_scal_434 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb hc hdet with
      ⟨h1, h2⟩ | h3
    · exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
    · exact (hw3 h3).elim

private lemma zs4n_main_ga4 (hp : p ≠ 2) (hp3 : p = 3) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})))
    {v w : Fin 4 → ZMod p} (hgm : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hv3 : v 3 = 1)
    (hw3 : 2 - w 0 * v 0 - w 1 * v 1 - w 2 * v 2 ≠ 0)
    (hnot : w 0 + w 1 ≠ 0 ∨ v 0 + v 1 ≠ 0)
    (hga : orderOf (g * a) = 4) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  subst p
  obtain ⟨-, hgb_le, -, hgb_ne1, -⟩ := zs4n_orders hp h hg
  obtain ⟨hgc_le, hgc_ne1⟩ := zs4n_orders_c hp h
  have hgb34 := zs4n_order34_of_le hgb_le hgb_ne1
  have hgc34 := zs4n_order34_of_le hgc_le hgc_ne1
  have ha := zs4n_fact_a4 hp h hgm hwv hga
  have ha' : v 0 * w 0 = 1 := by
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * ha
  have hdet := zs4n_hdet_a hp h hgm hwv hA (Or.inr hga)
  rcases hgb34 with hgb2 | hgb3 | hgb4
  · have hb := zs4n_fact_b2 hp h hgm hwv hgb2
    rcases hgc34 with hgc2 | hgc3 | hgc4
    · have hc := zs4n_fact_c2 hp h hgm hwv hgc2
      exact zs4n_wit_422 hp rfl h hgm hwv hv3 ha' hb.1 hb.2 hc.1 hc.2 hdet hnot hw3
    · have hc := zs4n_fact_c3 hp h hgm hwv hgc3
      exact zs4n_wit_423 hp rfl h hgm hwv hv3 ha' hb.1 hb.2 hc hdet hnot hw3
    · have hc := zs4n_fact_c4 hp h hgm hwv hgc4
      rcases zs4n_scal_424 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) ha hb.1 hb.2 hc hdet with
        ⟨h1, h2⟩ | h3
      · exact (hnot.elim (fun h => h h2) (fun h => h h1)).elim
      · exact (hw3 h3).elim
  · exact zs4n_ga4_gb3 hp rfl h hA hgm hwv hw3 hnot hga hgb3 ha
  · exact (hA (zs4n_exclude_44 hp h hga hgb4)).elim

theorem exists_commute_ac_of_not_irred (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    ∃ y ∈ Subgroup.closure (insert g (H : Set (U ≃ₗ[ZMod p] U))), IsRefl p y ∧ y * a = a * y ∧
      y * c = c * y ∧ orderOf (y * b) = 4 ∧ ¬ HardMathSupport.Kantor79.movedSpace y ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  have hp3 : p = 3 := h.eq_three_of_not_irred hp hg hA
  obtain ⟨v, w, hgm, hwv, hv3, hw3, hnot⟩ := zs4n_coord_base hp hp3 h hg hA
  obtain ⟨hga_le, -, hga_ne1, -, -⟩ := zs4n_orders hp h hg
  have hga34 := zs4n_order34_of_le hga_le hga_ne1
  rcases hga34 with hga2 | hga3 | hga4
  · exact zs4n_main_ga2 hp hp3 h hg hA hgm hwv hv3 hw3 hnot hga2
  · exact zs4n_main_ga3 hp hp3 h hg hA hgm hwv hv3 hw3 hnot hga3
  · exact zs4n_main_ga4 hp hp3 h hg hA hgm hwv hv3 hw3 hnot hga4

theorem oPhi_le_of_not_irred (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : ¬ IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    p = 3 ∧ ∃ ε : (ZMod p)ˣ, basisClosure (f.unitsSMul ![1, 1, 1, ε]) oPhiOneMats ≤ G := by
  have hp3 := h.eq_three_of_not_irred hp hg hA
  obtain ⟨y, hy_mem, hy_refl, hya, hyc, hyb, hyV⟩ :=
    h.exists_commute_ac_of_not_irred hp hg hA
  obtain ⟨ε, hε⟩ :=
    toMatrix_oPhiMat_of_commute hp3 f h.toMatrix_a h.toMatrix_b h.toMatrix_c hy_refl hya hyc hyb hyV
  refine ⟨hp3, ε, ?_⟩
  have h' : FFourData (f.unitsSMul ![1, 1, 1, ε]) a b c g H G := h.rescale ε
  have hyG : y ∈ G := by
    refine (Subgroup.closure_le _).mpr ?_ hy_mem
    rintro z (rfl | hz)
    · exact h.g_mem
    · exact h.H_le hz
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  rw [basisClosure, Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_setOf_eq, oPhiOneMats, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz | hz
  · rw [toMatrix_inj_four (hz.trans h'.toMatrix_a.symm)]; exact h.H_le haH
  · rw [toMatrix_inj_four (hz.trans h'.toMatrix_b.symm)]; exact h.H_le hbH
  · rw [toMatrix_inj_four (hz.trans h'.toMatrix_c.symm)]; exact h.H_le hcH
  · rw [toMatrix_inj_four (hz.trans hε.symm)]; exact hyG

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_orderOf_bc (h : FFourData f a b c g H G) :
    orderOf (b * c) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · apply eq_of_toMatrix_eq f
    rw [show (b * c : U ≃ₗ[ZMod p] U) ^ 3 = ((b * c) * (b * c)) * (b * c) by
      rw [pow_succ, pow_succ, pow_one]]
    rw [toMatrix_coe_mul, toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_b, h.toMatrix_c]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat]
  · intro hbc
    have hmat : (pijMat 0 1 1 * pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 := by
      rw [← h.toMatrix_b, ← h.toMatrix_c, ← toMatrix_coe_mul, hbc]
      simp
    have h00 := congrFun (congrFun hmat 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat] at h00

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_orderOf_ac (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    orderOf (a * c) = 2 := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hac : a * c = c * a := by
    apply eq_of_toMatrix_eq f
    rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_a, h.toMatrix_c]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]
  refine orderOf_eq_prime (p := 2) ?_ ?_
  · rw [pow_two, mul_assoc, ← mul_assoc c a c, hac.symm, mul_assoc, hcR.1, mul_one, haR.1]
  · intro h1
    have hmat : (diagSignMat 0 * pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 := by
      rw [← h.toMatrix_a, ← h.toMatrix_c, ← toMatrix_coe_mul, h1]
      simp
    have h11 := congrFun (congrFun hmat 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat] at h11

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_orderOf_ga (hp : p ≠ 2) (h : FFourData f a b c g H G) (hga : g * a = a * g) :
    orderOf (g * a) = 2 := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hgR : IsRefl p g := h.isRefl_g
  have haVH : HardMathSupport.Kantor79.movedSpace a ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_a, FFourCoord.diagSignMat_zero_eq]) (by simp)
  have hg_ne_a : g ≠ a := fun heq => zs4k_not_movedSpace_g hp h (heq ▸ haVH)
  refine orderOf_eq_prime (p := 2) ?_ ?_
  · rw [pow_two, mul_assoc, ← mul_assoc a g a, hga.symm, mul_assoc, haR.1, mul_one, hgR.1]
  · intro h1
    exact hg_ne_a (by rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right haR.1])

private lemma zs4k_fourRefl_gbca (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    FourRefl g b c a (Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U))) := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hXG : Subgroup.closure ({g, b, c, a} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl | rfl)
    · exact h.g_mem
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  refine ⟨by simpa using Module.finrank_eq_card_basis f, h.isRefl_g, hbR, hcR, haR, rfl, ?_, ?_,
    zs4k_finrank_closure_four hp h⟩
  · exact fun x hx => h.transvectionFree x (hXG hx)
  · refine ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hXG hx) y (hXG hy) hxr hyr,
      a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), haR, hbR,
      zs4k_orderOf_ab hp h⟩

private lemma zs4k_splitSupport_of_irred (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hA : IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    SplitSupport (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) 3 := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hgR : IsRefl p g := h.isRefl_g
  have hAle : Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.g_mem
  have hRefl : ReflGen p (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) := by
    rw [ReflGen]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), haR⟩
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hbR⟩
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hgR⟩
    · exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)
  have horder : ∃ x ∈ Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)),
      ∃ y ∈ Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)),
        IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    ⟨a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), haR, hbR,
      by rw [zs4k_orderOf_ab hp h]; norm_num⟩
  exact h.splitOfIrred _ hAle hRefl hA (zs4k_finrank_closure_three hp h) horder

theorem card_le_48_of_irred (hp : p ≠ 2) (h : FFourData f a b c g H G) (hT : TFSmallThree p)
    (hA : IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    Nat.card (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) ≤ 48 ∧
      ∃ e : Module.Basis (Fin 3) (ZMod p)
          (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g})),
        movedGroup (Subgroup.closure {a, b, g}) = g2mmn p e 0 1 1 := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hgR : IsRefl p g := h.isRefl_g
  have hSplit : SplitSupport (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) 3 :=
    zs4k_splitSupport_of_irred hp h hA
  have hAle : Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.g_mem
  have hRefl : ReflGen p (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) := by
    rw [ReflGen]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), haR⟩
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hbR⟩
      · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hgR⟩
    · exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)
  have horder : ∃ x ∈ Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)),
      ∃ y ∈ Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U)),
        IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    ⟨a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), haR, hbR,
      by rw [zs4k_orderOf_ab hp h]; norm_num⟩
  have hDMax : DMax p (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) 4 :=
    ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hAle hx) y (hAle hy) hxr hyr,
      a, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), haR, hbR,
      zs4k_orderOf_ab hp h⟩
  have hTF : QTwoLin.TransvectionFree (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) :=
    fun x hx => h.transvectionFree x (hAle hx)
  have hcard : Nat.card (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) ≤ 48 :=
    h.maximal _ hAle hRefl hSplit hDMax
  obtain ⟨e, he⟩ := hT U _ hp hRefl hTF hSplit horder hcard
  exact ⟨hcard, e, he⟩

theorem irred_cases (hp : p ≠ 2) (h : FFourData f a b c g H G) (hT : TFSmallThree p)
    (hg : g * (a * b * a) ≠ a * b * a * g)
    (hA : IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))) :
    (b * g * b * a = a * (b * g * b) ∧ orderOf (g * b) = 3) ∨
      (g * a = a * g ∧ orderOf (g * b) = 3) ∨ (orderOf (a * g) = 3 ∧ b * g = g * b) := by
  obtain ⟨-, e, he⟩ := card_le_48_of_irred hp h hT hA
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hgR : IsRefl p g := h.isRefl_g
  have hSplit : SplitSupport (Subgroup.closure ({a, b, g} : Set (U ≃ₗ[ZMod p] U))) 3 :=
    zs4k_splitSupport_of_irred hp h hA
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbaH : a * b * a ∈ H := H.mul_mem (H.mul_mem haH hbH) haH
  have hbabH : b * a * b ∈ H := H.mul_mem (H.mul_mem hbH haH) hbH
  have hga : g ≠ a := fun heq => h.map_ne (by rw [heq]; exact (zs4k_conj_data h haH).1)
  have hgb : g ≠ b := fun heq => h.map_ne (by rw [heq]; exact (zs4k_conj_data h hbH).1)
  have hgaba : g ≠ a * b * a := fun heq =>
    h.map_ne (by rw [heq]; exact (zs4k_conj_data h hbaH).1)
  have hgbab : g ≠ b * a * b := fun heq =>
    h.map_ne (by rw [heq]; exact (zs4k_conj_data h hbabH).1)
  exact FFourCoord.irred_cases_of_g2mmn hp haR hbR hgR hSplit e he (zs4k_orderOf_ab hp h)
    hga hgb hgaba hgbab hg

private lemma zs4k_gc_ne_two (hp : p ≠ 2) (h : FFourData f a b c g H G) (hga : g * a = a * g)
    (hgb : orderOf (g * b) = 3) (hgc2 : orderOf (g * c) = 2) : False := by
  have haR : IsRefl p a := isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hca : orderOf (c * a) = 2 := by
    have h1 : (a * c)⁻¹ = c * a := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haR.1, inv_eq_of_mul_eq_one_right hcR.1]
    rw [← h1, orderOf_inv, zs4k_orderOf_ac hp h]
  exact FourRefl.false_i hp (zs4k_fourRefl_gbca hp h) (zs4k_orderOf_ga hp h hga) hgc2 hca
    hgb (zs4k_orderOf_bc h) (zs4k_orderOf_ba hp h)

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_reflGen_closure_three {x y z : U ≃ₗ[ZMod p] U}
    (hx : IsRefl p x) (hy : IsRefl p y) (hz : IsRefl p z) :
    ReflGen p (Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U))) := by
  rw [ReflGen]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro w (rfl | rfl | rfl)
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hx⟩
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hy⟩
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), hz⟩
  · exact (Subgroup.closure_le _).mpr (fun w hw => hw.1)

private lemma zs4k_finrank_closure_gcb (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hbR : IsRefl p b) (hcR : IsRefl p c) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({g, c, b} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbVH : HardMathSupport.Kantor79.movedSpace b ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]) (by simp)
  have hcVH : HardMathSupport.Kantor79.movedSpace c ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]) (by simp)
  have hb_ne_c : b ≠ c := by
    intro hbc
    have hmat : (pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = pijMat 1 2 1 := by
      rw [← h.toMatrix_b, ← h.toMatrix_c, hbc]
    have h01 := congrFun (congrFun hmat 0) 1
    simp [pijMat] at h01
  have hbc_ne : HardMathSupport.Kantor79.movedSpace b ≠
      HardMathSupport.Kantor79.movedSpace c := fun heq =>
    hb_ne_c (eq_of_movedSpace_eq hp h.transvectionFree (h.H_le hbH) (h.H_le hcH) hbR hcR heq)
  have hset : ({g, c, b} : Set (U ≃ₗ[ZMod p] U)) = {b, c, g} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact zs4k_finrank_closure_two_VH hbR hcR h.isRefl_g hbVH hcVH hbc_ne
    (zs4k_not_movedSpace_g hp h)

private lemma zs4k_gc_ne_four (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hgb : orderOf (g * b) = 3) (hgc4 : orderOf (g * c) = 4) : False := by
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hU : Module.finrank (ZMod p) U = 4 := by
    simpa using Module.finrank_eq_card_basis f
  have hcb : orderOf (c * b) = 3 := by
    have h1 : (b * c)⁻¹ = c * b := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hbR.1, inv_eq_of_mul_eq_one_right hcR.1]
    rw [← h1, orderOf_inv, zs4k_orderOf_bc h]
  have hXG : Subgroup.closure ({g, c, b} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact h.g_mem
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
    · exact h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hAt : QTwoLin.TransvectionFree (Subgroup.closure ({g, c, b} : Set (U ≃ₗ[ZMod p] U))) :=
    fun x hx => h.transvectionFree x (hXG hx)
  have hD : DMax p (Subgroup.closure ({g, c, b} : Set (U ≃ₗ[ZMod p] U))) 4 :=
    ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hXG hx) y (hXG hy) hxr hyr,
      g, Subgroup.subset_closure (by simp), c, Subgroup.subset_closure (by simp), h.isRefl_g, hcR,
      hgc4⟩
  obtain ⟨hSplit, hgt⟩ := zs4k_card_of_433 hp hU h.isRefl_g hcR hbR rfl hAt
    (zs4k_finrank_closure_gcb hp h hbR hcR) hD hgc4 hgb hcb
  have hcard := h.maximal _ hXG (zs4k_reflGen_closure_three h.isRefl_g hcR hbR) hSplit hD
  omega

theorem orderOf_gc_of_case_ii (hp : p ≠ 2) (h : FFourData f a b c g H G) (hga : g * a = a * g)
    (hgb : orderOf (g * b) = 3) : orderOf (g * c) = 3 := by
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hgc_le : orderOf (g * c) ≤ 4 := h.dmax.1 g h.g_mem c (h.H_le hcH) h.isRefl_g hcR
  have hgc_ne1 : orderOf (g * c) ≠ 1 := by
    intro h1
    have hgc : g * c = 1 := orderOf_eq_one_iff.mp h1
    have hg_eq_c : g = c := by
      rw [eq_inv_of_mul_eq_one_left hgc, inv_eq_of_mul_eq_one_right hcR.1]
    exact h.map_ne (by rw [hg_eq_c]; exact (zs4k_conj_data h hcH).1)
  have hgc_ne2 : orderOf (g * c) ≠ 2 := fun h2 => zs4k_gc_ne_two hp h hga hgb h2
  have : Finite U := Module.finite_of_finite (R := ZMod p) (M := U)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  have hpos : 0 < orderOf (g * c) := (isOfFinOrder_of_finite (g * c)).orderOf_pos
  by_cases hgc4 : orderOf (g * c) = 4
  · exact (zs4k_gc_ne_four hp h hgb hgc4).elim
  · omega

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_coord_apply_basis (k l : Fin 4) :
    f.coord k (f l) = if k = l then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : k = l
  · subst h; rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne h, if_neg h]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_sum_coord_apply_basis (w : Fin 4 → ZMod p) (k : Fin 4) :
    (∑ i, w i • f.coord i) (f k) = w k := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, zs4k_coord_apply_basis, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [hik]
  · intro hk; exact absurd (Finset.mem_univ k) hk

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_coord_apply_sum (v : Fin 4 → ZMod p) (k : Fin 4) :
    f.coord k (∑ i, v i • f i) = v k := by
  have hw : (∑ i, (Pi.single k (1 : ZMod p) : Fin 4 → ZMod p) i • f.coord i) = f.coord k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [hik]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [← hw, FFourCoord.sum_smul_coord_apply_sum]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [hik]
  · intro hk; exact absurd (Finset.mem_univ k) hk

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_repr_sum (v : Fin 4 → ZMod p) (k : Fin 4) :
    f.repr (∑ i, v i • f i) k = v k := by
  rw [← Module.Basis.coord_apply]
  exact zs4k_coord_apply_sum v k

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_pairing_pij_one {i j : Fin 4} (hij : i ≠ j) :
    (f.coord i - f.coord j) (f i - f j) = 2 := by
  have h1 : (f.coord i - f.coord j) (f i) = 1 := by
    rw [LinearMap.sub_apply, zs4k_coord_apply_basis, zs4k_coord_apply_basis,
      if_pos rfl, if_neg (Ne.symm hij), sub_zero]
  have h2 : (f.coord i - f.coord j) (f j) = -1 := by
    rw [LinearMap.sub_apply, zs4k_coord_apply_basis, zs4k_coord_apply_basis,
      if_neg hij, if_pos rfl, zero_sub]
  rw [map_sub, h1, h2]
  norm_num

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_pairing_diag (i : Fin 4) :
    ((2 : ZMod p) • f.coord i) (f i) = 2 := by
  rw [LinearMap.smul_apply, zs4k_coord_apply_basis, if_pos rfl, smul_eq_mul, mul_one]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_eq_reflection_of_pij_one {i j : Fin 4} (hij : i ≠ j)
    {x : U ≃ₗ[ZMod p] U}
    (hx : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) = pijMat i j 1) :
    x = Module.reflection (zs4k_pairing_pij_one (f := f) hij) := by
  apply eq_of_toMatrix_eq (f := f)
  have h1 : (fun k => f.repr (f i - f j) k) =
      (Pi.single i (1 : ZMod p) - Pi.single j 1) := by
    funext k
    simp only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Pi.sub_apply, Pi.single_apply]
    by_cases hki : i = k <;> by_cases hkj : j = k <;> simp_all [eq_comm]
  have h2 : (fun k => (f.coord i - f.coord j) (f k)) =
      (Pi.single i (1 : ZMod p) - Pi.single j 1) := by
    funext k
    simp only [LinearMap.sub_apply, zs4k_coord_apply_basis, Pi.sub_apply, Pi.single_apply]
    by_cases hki : i = k <;> by_cases hkj : j = k <;> simp_all [eq_comm]
  rw [hx, toMatrix_reflection (w := f i - f j) (ψ := f.coord i - f.coord j) f
    (zs4k_pairing_pij_one (f := f) hij), pijMat_eq_one_sub_vecMulVec (n := 4) hij
      (one_ne_zero : (1 : ZMod p) ≠ 0), inv_one, one_smul, h1, h2]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_eq_reflection_of_diagSignMat {i : Fin 4} {x : U ≃ₗ[ZMod p] U}
    (hx : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) = diagSignMat i) :
    x = Module.reflection (zs4k_pairing_diag (f := f) i) := by
  apply eq_of_toMatrix_eq (f := f)
  have h1 : (fun k => f.repr (f i) k) = (Pi.single i (1 : ZMod p)) := by
    funext k
    simp only [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
    by_cases h : i = k <;> simp_all [eq_comm]
  have h2 : (fun k => ((2 : ZMod p) • f.coord i) (f k)) = (Pi.single i (2 : ZMod p)) := by
    funext k
    simp only [LinearMap.smul_apply, zs4k_coord_apply_basis, Pi.single_apply, smul_eq_mul]
    by_cases h : i = k <;> simp_all [eq_comm]
  rw [hx, toMatrix_reflection (w := f i) (ψ := (2 : ZMod p) • f.coord i) f
    (zs4k_pairing_diag (f := f) i), diagSignMat_eq_one_sub_vecMulVec (n := 4) i, h1, h2]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_a_eq (h : FFourData f a b c g H G) :
    a = Module.reflection (zs4k_pairing_diag (f := f) 0) :=
  zs4k_eq_reflection_of_diagSignMat (f := f) h.toMatrix_a

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_b_eq (h : FFourData f a b c g H G) :
    b = Module.reflection (zs4k_pairing_pij_one (f := f) (by decide : (0 : Fin 4) ≠ 1)) :=
  zs4k_eq_reflection_of_pij_one (f := f) (by decide) h.toMatrix_b

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_c_eq (h : FFourData f a b c g H G) :
    c = Module.reflection (zs4k_pairing_pij_one (f := f) (by decide : (1 : Fin 4) ≠ 2)) :=
  zs4k_eq_reflection_of_pij_one (f := f) (by decide) h.toMatrix_c

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_case_ii_coords (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hga : g * a = a * g) (hgb : orderOf (g * b) = 3) :
    ∃ (v w : Fin 4 → ZMod p) (hφg : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2),
      g = Module.reflection hφg ∧ v 0 = 0 ∧ w 0 = 0 ∧ w 1 * v 1 = 1 ∧
        v 3 ≠ 0 ∧ w 3 ≠ 0 ∧ ∑ i, w i * v i = 2 := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hg_ne_a : g ≠ a := fun heq => h.map_ne (by rw [heq]; exact (zs4k_conj_data h haH).1)
  have hg_ne_b : g ≠ b := fun heq => h.map_ne (by rw [heq]; exact (zs4k_conj_data h hbH).1)
  obtain ⟨v, w, hgm, hwv⟩ := FFourCoord.exists_toMatrix_of_isRefl hp f h.isRefl_g
  obtain ⟨hφg, hgeq⟩ := FFourCoord.eq_reflection_of_toMatrix (f := f) hgm hwv
  have hφa := zs4k_pairing_diag (f := f) 0
  have haeq := zs4k_a_eq (f := f) h
  have hcomm_a : Commute (Module.reflection hφg) (Module.reflection hφa) := by
    show Module.reflection hφg * Module.reflection hφa =
      Module.reflection hφa * Module.reflection hφg
    rw [← hgeq, ← haeq]; exact hga
  have hne_a : Module.reflection hφg ≠ Module.reflection hφa := by
    intro heq; exact hg_ne_a (by rw [hgeq, haeq]; exact heq)
  have hv0 : v 0 = 0 := by
    have hz := apply_eq_zero_of_commute hp hφa hφg hcomm_a.symm hne_a.symm
    rw [LinearMap.smul_apply, zs4k_coord_apply_sum, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ZMod.prime_ne_zero p 2 hp)
  have hw0 : w 0 = 0 := by
    have hz := apply_eq_zero_of_commute hp hφg hφa hcomm_a hne_a
    rwa [zs4k_sum_coord_apply_basis w 0] at hz
  have hw1v1 : w 1 * v 1 = 1 := by
    have hφb := zs4k_pairing_pij_one (f := f) (by decide : (0 : Fin 4) ≠ 1)
    have hbeq := zs4k_b_eq (f := f) h
    have h3 : orderOf (Module.reflection hφg * Module.reflection hφb) = 3 := by
      rw [← hgeq, ← hbeq]; exact hgb
    have hz := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφg hφb h3
    have hA : (∑ i, w i • f.coord i) (f 0 - f 1) = w 0 - w 1 := by
      rw [map_sub, zs4k_sum_coord_apply_basis, zs4k_sum_coord_apply_basis]
    have hB : (f.coord 0 - f.coord 1) (∑ i, v i • f i) = v 0 - v 1 := by
      rw [LinearMap.sub_apply, zs4k_coord_apply_sum, zs4k_coord_apply_sum]
    rw [hA, hB, hv0, hw0] at hz
    ring_nf at hz
    exact hz
  refine ⟨v, w, hφg, hgeq, hv0, hw0, hw1v1, ?_, ?_, hwv⟩
  · exact FFourCoord.apply_three_ne_zero_of_map_ne f hgm hwv h.map_ne
  · intro hw3'
    apply h.apply_not_mem
    have hg3 : g (f 3) = f 3 := by
      rw [hgeq, Module.reflection_apply, zs4k_sum_coord_apply_basis w 3, hw3', zero_smul,
        sub_zero]
    rw [hg3]; exact Submodule.mem_span_singleton_self _

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_closure_xbc_eq {g c b x : U ≃ₗ[ZMod p] U} (hxdef : x = c * g * c)
    (hcc : c * c = 1) :
    Subgroup.closure ({x, b, c} : Set (U ≃ₗ[ZMod p] U)) =
      Subgroup.closure ({g, c, b} : Set (U ≃ₗ[ZMod p] U)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    · rw [hxdef]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzg | hzc | hzb
    · rw [hzg]
      have hg : g = c * x * c := by
        rw [hxdef]
        rw [show c * (c * g * c) * c = (c * c) * g * (c * c) by group, hcc]
        simp
      rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
    · rw [hzc]; exact Subgroup.subset_closure (by simp)
    · rw [hzb]; exact Subgroup.subset_closure (by simp)

private lemma zs4k_not_orderOf_xb_four (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hga : g * a = a * g) (hgb : orderOf (g * b) = 3) {x : U ≃ₗ[ZMod p] U}
    (hxdef : x = c * g * c) (hxR : IsRefl p x) (hxb4 : orderOf (x * b) = 4) : False := by
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbR : IsRefl p b := isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide)
    one_ne_zero h.toMatrix_b
  have hcR : IsRefl p c := isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide)
    one_ne_zero h.toMatrix_c
  have hU : Module.finrank (ZMod p) U = 4 := by simpa using Module.finrank_eq_card_basis f
  have hxc3 : orderOf (x * c) = 3 := by
    have hxcg : x * c = c * g := by
      rw [hxdef]
      calc c * g * c * c = c * g * (c * c) := by group
        _ = c * g := by rw [hcR.1, mul_one]
    have hcg : orderOf (c * g) = orderOf (g * c) := by
      have h1 : c * g = (g * c)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.isRefl_g.1,
          inv_eq_of_mul_eq_one_right hcR.1]
      rw [h1, orderOf_inv]
    rw [hxcg, hcg, orderOf_gc_of_case_ii hp h hga hgb]
  have hXeq : Subgroup.closure ({x, b, c} : Set (U ≃ₗ[ZMod p] U)) =
      Subgroup.closure ({g, c, b} : Set (U ≃ₗ[ZMod p] U)) :=
    zs4k_closure_xbc_eq hxdef hcR.1
  have hXG : Subgroup.closure ({x, b, c} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z (rfl | rfl | rfl)
    · rw [hxdef]
      exact G.mul_mem (G.mul_mem (h.H_le hcH) h.g_mem) (h.H_le hcH)
    · exact h.H_le hbH
    · exact h.H_le hcH
  have hAt : QTwoLin.TransvectionFree (Subgroup.closure ({x, b, c} : Set (U ≃ₗ[ZMod p] U))) :=
    fun y hy => h.transvectionFree y (hXG hy)
  have hD : DMax p (Subgroup.closure ({x, b, c} : Set (U ≃ₗ[ZMod p] U))) 4 :=
    ⟨fun y hy z hz hyr hzr => h.dmax.1 y (hXG hy) z (hXG hz) hyr hzr,
      x, Subgroup.subset_closure (by simp), b, Subgroup.subset_closure (by simp), hxR, hbR, hxb4⟩
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({x, b, c} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
    rw [hXeq]; exact zs4k_finrank_closure_gcb hp h hbR hcR
  obtain ⟨hSplit, hgt⟩ := zs4k_card_of_433 hp hU hxR hbR hcR rfl hAt hdim hD hxb4 hxc3
    (zs4k_orderOf_bc h)
  exact absurd (h.maximal _ hXG (zs4k_reflGen_closure_three hxR hbR hcR) hSplit hD) (by omega)

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_cgc_eta (v w : Fin 4 → ZMod p) :
    ((∑ i, w i • f.coord i - (∑ i, w i • f.coord i) (f 1 - f 2) •
        (f.coord 1 - f.coord 2)) (f 0 - f 1) = w 0 - w 2) ∧
    ((f.coord 0 - f.coord 1) ((∑ i, v i • f i) -
        (f.coord 1 - f.coord 2) (∑ i, v i • f i) • (f 1 - f 2)) = v 0 - v 2) := by
  have hA1 : (∑ i, w i • f.coord i) (f 0 - f 1) = w 0 - w 1 := by
    rw [map_sub, zs4k_sum_coord_apply_basis, zs4k_sum_coord_apply_basis]
  have hA2 : (∑ i, w i • f.coord i) (f 1 - f 2) = w 1 - w 2 := by
    rw [map_sub, zs4k_sum_coord_apply_basis, zs4k_sum_coord_apply_basis]
  have hB1 : (f.coord 0 - f.coord 1) (∑ i, v i • f i) = v 0 - v 1 := by
    rw [LinearMap.sub_apply, zs4k_coord_apply_sum, zs4k_coord_apply_sum]
  have hB2 : (f.coord 1 - f.coord 2) (∑ i, v i • f i) = v 1 - v 2 := by
    rw [LinearMap.sub_apply, zs4k_coord_apply_sum, zs4k_coord_apply_sum]
  have hC1 : (f.coord 1 - f.coord 2) (f 0 - f 1) = -1 := by
    norm_num [LinearMap.sub_apply, map_sub, zs4k_coord_apply_basis]
  have hC3 : (f.coord 0 - f.coord 1) (f 1 - f 2) = -1 := by
    norm_num [LinearMap.sub_apply, map_sub, zs4k_coord_apply_basis]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.smul_apply, hA1, hA2, hC1, smul_eq_mul]
    ring
  · rw [map_sub, map_smul, hB1, hB2, hC3, smul_eq_mul]
    ring

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_eq_cbc_of_xb {g c b x : U ≃ₗ[ZMod p] U} (hxdef : x = c * g * c)
    (hcc : c * c = 1) (hxb : x = b) : g = c * b * c := by
  have hxcb : c * g * c = b := by rw [← hxdef]; exact hxb
  have hg : g = c * (c * g * c) * c := by
    have h2 : (c * c) * g * (c * c) = g := by rw [hcc]; simp
    rw [show c * (c * g * c) * c = (c * c) * g * (c * c) by group]
    exact h2.symm
  rw [hg, hxcb]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_contra_of_xb_one (h : FFourData f a b c g H G) {x : U ≃ₗ[ZMod p] U}
    (hcH : c ∈ H) (hbH : b ∈ H) (hxdef : x = c * g * c) (hcc : c * c = 1) (hxb : x = b) :
    False := by
  have hg_eq : g = c * b * c := zs4k_eq_cbc_of_xb hxdef hcc hxb
  have hgH : g ∈ H := by rw [hg_eq]; exact H.mul_mem (H.mul_mem hcH hbH) hcH
  exact h.map_ne (zs4k_conj_data h hgH).1

private lemma zs4k_no_w3v3 (v w : Fin 4 → ZMod p) (hw0 : w 0 = 0) (hv0 : v 0 = 0)
    (hw1v1 : w 1 * v 1 = 1) (hw3 : w 3 ≠ 0) (hv3 : v 3 ≠ 0)
    (hwv : ∑ i, w i * v i = 2) (hw2v2 : w 2 * v 2 = 1) : False := by
  have hE : w 2 * v 2 + w 3 * v 3 = 1 := by
    have hsum := hwv
    rw [Fin.sum_univ_four] at hsum
    rw [hw0, hv0, hw1v1] at hsum
    linear_combination hsum
  have hzero : w 3 * v 3 = 0 := by linear_combination hE - hw2v2
  exact mul_ne_zero hw3 hv3 hzero

private lemma zs4k_unit_facts (v w : Fin 4 → ZMod p) (hw0 : w 0 = 0) (hv0 : v 0 = 0)
    (hw1v1 : w 1 * v 1 = 1) (hwv : ∑ i, w i * v i = 2) (hw2 : w 2 = 0) (hv2 : v 2 = 0) :
    v 1 ≠ 0 ∧ w 3 * v 3 = 1 := by
  have hv1 : v 1 ≠ 0 := by
    intro h1; rw [h1, mul_zero] at hw1v1; exact zero_ne_one hw1v1
  have hw3v3 : w 3 * v 3 = 1 := by
    have hsum := hwv
    rw [Fin.sum_univ_four] at hsum
    rw [hw0, hv0, hw2, hv2, hw1v1] at hsum
    linear_combination hsum
  exact ⟨hv1, hw3v3⟩

theorem commute_of_case_ii (hp : p ≠ 2) (h : FFourData f a b c g H G) (hga : g * a = a * g)
    (hgb : orderOf (g * b) = 3) : c * g * c * b = b * (c * g * c) := by
  obtain ⟨v, w, hφg, hgeq, hv0, hw0, hw1v1, hv3, hw3, hwv⟩ :=
    zs4k_case_ii_coords hp h hga hgb
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbR : IsRefl p b := isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide)
    one_ne_zero h.toMatrix_b
  have hcR : IsRefl p c := isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide)
    one_ne_zero h.toMatrix_c
  have hφb := zs4k_pairing_pij_one (f := f) (by decide : (0 : Fin 4) ≠ 1)
  have hbeq := zs4k_b_eq (f := f) h
  have hφc := zs4k_pairing_pij_one (f := f) (by decide : (1 : Fin 4) ≠ 2)
  have hceq := zs4k_c_eq (f := f) h
  have hφx := conj_pairing hφc hφg
  set x : U ≃ₗ[ZMod p] U := c * g * c with hxdef
  have hxeq : x = Module.reflection hφx := by
    rw [hxdef, hceq, hgeq]; exact reflection_conj_reflection hφc hφg
  have hxR : IsRefl p x := (isRefl_iff hp x).mpr ⟨_, _, hφx, hxeq⟩
  have hxG : x ∈ G := by
    rw [hxdef]; exact G.mul_mem (G.mul_mem (h.H_le hcH) h.g_mem) (h.H_le hcH)
  obtain ⟨hηx, hηb⟩ := zs4k_cgc_eta (f := f) v w
  have hle4 : orderOf (x * b) ≤ 4 := h.dmax.1 x hxG b (h.H_le hbH) hxR hbR
  have : Finite U := Module.finite_of_finite (R := ZMod p) (M := U)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  have hpos : 0 < orderOf (x * b) := (isOfFinOrder_of_finite (x * b)).orderOf_pos
  have hcases : orderOf (x * b) = 1 ∨ orderOf (x * b) = 2 ∨ orderOf (x * b) = 3 ∨
      orderOf (x * b) = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · have hxb1 : x * b = 1 := orderOf_eq_one_iff.mp h1
    have hxb : x = b := by rw [eq_inv_of_mul_eq_one_left hxb1, inv_eq_of_mul_eq_one_right hbR.1]
    exact (zs4k_contra_of_xb_one h hcH hbH hxdef hcR.1 hxb).elim
  · have hsq : (x * b) * (x * b) = 1 := by
      have := pow_orderOf_eq_one (x * b); rw [h2, pow_two] at this; exact this
    have hcomm : x * b = b * x := by
      have h1 : x * b = (x * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hxR.1,
        inv_eq_of_mul_eq_one_right hbR.1]
    exact hcomm
  · have h3' : orderOf (Module.reflection hφx * Module.reflection hφb) = 3 := by
      rw [← hxeq, ← hbeq]; exact h3
    have hz := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφx hφb h3'
    rw [hηx, hηb, hw0, hv0] at hz
    ring_nf at hz
    exact (zs4k_no_w3v3 v w hw0 hv0 hw1v1 hw3 hv3 hwv hz).elim
  · exact (zs4k_not_orderOf_xb_four hp h hga hgb hxdef hxR h4).elim

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_cgc_root_repr (v : Fin 4 → ZMod p) (hv0 : v 0 = 0) (hv2 : v 2 = 0) :
    (fun k => f.repr ((∑ i, v i • f i) -
      (f.coord 1 - f.coord 2) (∑ i, v i • f i) • (f 1 - f 2)) k) =
      ![0, 0, v 1, v 3] := by
  have hq : (f.coord 1 - f.coord 2) (∑ i, v i • f i) = v 1 - v 2 := by
    rw [LinearMap.sub_apply, zs4k_coord_apply_sum, zs4k_coord_apply_sum]
  funext k
  rw [map_sub, map_smul, hq, Finsupp.sub_apply, Finsupp.smul_apply, zs4k_repr_sum]
  fin_cases k <;>
    simp [map_sub, hv0, hv2]

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_cgc_coroot_repr (w : Fin 4 → ZMod p) (hw0 : w 0 = 0) (hw2 : w 2 = 0) :
    (fun k => (∑ i, w i • f.coord i - (∑ i, w i • f.coord i) (f 1 - f 2) •
      (f.coord 1 - f.coord 2)) (f k)) = ![0, 0, w 1, w 3] := by
  have ht : (∑ i, w i • f.coord i) (f 1 - f 2) = w 1 - w 2 := by
    rw [map_sub, zs4k_sum_coord_apply_basis, zs4k_sum_coord_apply_basis]
  funext k
  rw [LinearMap.sub_apply, LinearMap.smul_apply, ht]
  fin_cases k <;>
    simp [LinearMap.sub_apply, zs4k_sum_coord_apply_basis, hw0, hw2]

private lemma zs4k_pij_matrix (v w : Fin 4 → ZMod p) (hv1 : v 1 ≠ 0) (hw3 : w 3 ≠ 0)
    (hw1v1 : w 1 * v 1 = 1) (hw3v3 : w 3 * v 3 = 1) :
    Matrix.vecMulVec ![0, 0, v 1, v 3] ![0, 0, w 1, w 3] =
      Matrix.vecMulVec
        (Pi.single 2 (1 : ZMod p) -
          ((Units.mk0 (-(v 1 * w 3)) (neg_ne_zero.mpr (mul_ne_zero hv1 hw3)) : (ZMod p)ˣ) :
            ZMod p)⁻¹ • Pi.single 3 1)
        (Pi.single 2 (1 : ZMod p) -
          ((Units.mk0 (-(v 1 * w 3)) (neg_ne_zero.mpr (mul_ne_zero hv1 hw3)) : (ZMod p)ˣ) :
            ZMod p) • Pi.single 3 1) := by
  have hβ0 : -(v 1 * w 3) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hv1 hw3)
  have hβval : ((Units.mk0 (-(v 1 * w 3)) hβ0 : (ZMod p)ˣ) : ZMod p) = -(v 1 * w 3) := rfl
  have hv1inv : (v 1)⁻¹ = w 1 := (eq_inv_of_mul_eq_one_left hw1v1).symm
  have hw3inv : (w 3)⁻¹ = v 3 := by
    rw [show w 3 = (v 3)⁻¹ from eq_inv_of_mul_eq_one_left hw3v3, inv_inv]
  have hβneg : -((Units.mk0 (-(v 1 * w 3)) hβ0 : (ZMod p)ˣ) : ZMod p) = v 1 * w 3 := by
    rw [hβval]; ring
  have hβinv : ((Units.mk0 (-(v 1 * w 3)) hβ0 : (ZMod p)ˣ) : ZMod p)⁻¹ = -(v 3 * w 1) := by
    rw [hβval, inv_neg, mul_inv_rev, hv1inv, hw3inv]
  have hβneginv : -((Units.mk0 (-(v 1 * w 3)) hβ0 : (ZMod p)ˣ) : ZMod p)⁻¹ = v 3 * w 1 := by
    rw [hβinv]; ring
  have hw1v1' : v 1 * w 1 = 1 := by rw [mul_comm]; exact hw1v1
  have hU : ![0, 0, v 1, v 3] =
      v 1 • (Pi.single 2 (1 : ZMod p) - ((Units.mk0 (-(v 1 * w 3)) hβ0 : (ZMod p)ˣ) :
        ZMod p)⁻¹ • Pi.single 3 1) := by
    funext k
    fin_cases k
    · simp
    · simp
    · simp
    · simp [Pi.smul_apply, smul_eq_mul, hv1inv, hw3inv]
      linear_combination -(v 3) * hw1v1'
  have hV : ![0, 0, w 1, w 3] =
      (v 1)⁻¹ • (Pi.single 2 (1 : ZMod p) - ((Units.mk0 (-(v 1 * w 3)) hβ0 : (ZMod p)ˣ) :
        ZMod p) • Pi.single 3 1) := by
    funext k
    fin_cases k
    · simp
    · simp
    · simp [hv1inv]
    · simp [Pi.smul_apply, smul_eq_mul, hv1inv]
      linear_combination -(w 3) * hw1v1
  rw [hU, hV]
  ext r c
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hv1]

theorem pi34_of_case_ii (hp : p ≠ 2) (h : FFourData f a b c g H G) (hga : g * a = a * g)
    (hgb : orderOf (g * b) = 3) :
    ∃ β : (ZMod p)ˣ, LinearMap.toMatrix f f (c * g * c).toLinearMap = pijMat 2 3 (β : ZMod p) := by
  obtain ⟨v, w, hφg, hgeq, hv0, hw0, hw1v1, hv3, hw3, hwv⟩ := zs4k_case_ii_coords hp h hga hgb
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbR : IsRefl p b := isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide)
    one_ne_zero h.toMatrix_b
  have hcR : IsRefl p c := isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide)
    one_ne_zero h.toMatrix_c
  have hφb := zs4k_pairing_pij_one (f := f) (by decide : (0 : Fin 4) ≠ 1)
  have hbeq := zs4k_b_eq (f := f) h
  have hφc := zs4k_pairing_pij_one (f := f) (by decide : (1 : Fin 4) ≠ 2)
  have hceq := zs4k_c_eq (f := f) h
  have hφx := conj_pairing hφc hφg
  set x : U ≃ₗ[ZMod p] U := c * g * c with hxdef
  have hxeq : x = Module.reflection hφx := by
    rw [hxdef, hceq, hgeq]; exact reflection_conj_reflection hφc hφg
  have hxb : x * b = b * x := by
    have hcomm := commute_of_case_ii hp h hga hgb
    rw [← hxdef] at hcomm; exact hcomm
  have hcomm_xb : Commute (Module.reflection hφx) (Module.reflection hφb) := by
    show Module.reflection hφx * Module.reflection hφb =
      Module.reflection hφb * Module.reflection hφx
    rw [← hxeq, ← hbeq]; exact hxb
  have hne_xb : Module.reflection hφx ≠ Module.reflection hφb := by
    intro heq
    have hxb_eq : x = b := by rw [hxeq, hbeq]; exact heq
    have hg_eq : g = c * b * c := zs4k_eq_cbc_of_xb hxdef hcR.1 hxb_eq
    have hgH : g ∈ H := by rw [hg_eq]; exact H.mul_mem (H.mul_mem hcH hbH) hcH
    exact h.map_ne (zs4k_conj_data h hgH).1
  obtain ⟨hηx, hηb⟩ := zs4k_cgc_eta (f := f) v w
  have hzw2 := apply_eq_zero_of_commute hp hφx hφb hcomm_xb hne_xb
  have hw2 : w 2 = 0 := by
    rw [hηx, hw0] at hzw2
    linear_combination -hzw2
  have hzv2 := apply_eq_zero_of_commute hp hφb hφx hcomm_xb.symm hne_xb.symm
  have hv2 : v 2 = 0 := by
    rw [hηb, hv0] at hzv2
    linear_combination -hzv2
  obtain ⟨hv1, hw3v3⟩ := zs4k_unit_facts v w hw0 hv0 hw1v1 hwv hw2 hv2
  have hβ0 : -(v 1 * w 3) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hv1 hw3)
  refine ⟨Units.mk0 (-(v 1 * w 3)) hβ0, ?_⟩
  rw [hxeq, toMatrix_reflection (f := f) hφx, zs4k_cgc_root_repr v hv0 hv2,
    zs4k_cgc_coroot_repr w hw0 hw2,
    pijMat_eq_one_sub_vecMulVec (n := 4) (i := 2) (j := 3) (by decide) (Units.ne_zero _)]
  congr 1
  exact zs4k_pij_matrix v w hv1 hw3 hw1v1 hw3v3

private lemma zs4k_finrank_closure_bc_aga (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hbR : IsRefl p b) (hcR : IsRefl p c) (hagaR : IsRefl p (a * g * a)) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({b, a * g * a, c} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbVH : HardMathSupport.Kantor79.movedSpace b ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_b, FFourCoord.pijMat_zero_one_eq]) (by simp)
  have hcVH : HardMathSupport.Kantor79.movedSpace c ≤ zs4kV f :=
    FFourCoord.movedSpace_le_span_of_toMatrix f
      (by rw [h.toMatrix_c, FFourCoord.pijMat_one_two_eq]) (by simp)
  have hb_ne_c : b ≠ c := by
    intro hbc
    have hmat : (pijMat 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = pijMat 1 2 1 := by
      rw [← h.toMatrix_b, ← h.toMatrix_c, hbc]
    have h01 := congrFun (congrFun hmat 0) 1
    simp [pijMat] at h01
  have hbc_ne : HardMathSupport.Kantor79.movedSpace b ≠
      HardMathSupport.Kantor79.movedSpace c := fun heq =>
    hb_ne_c (eq_of_movedSpace_eq hp h.transvectionFree (h.H_le hbH) (h.H_le hcH) hbR hcR heq)
  have haVH : (zs4kV f).map (a : U →ₗ[ZMod p] U) = zs4kV f := (zs4k_conj_data h haH).1
  have ha2 : a * a = 1 := (isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a).1
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj : HardMathSupport.Kantor79.movedSpace (a * g * a) =
      (HardMathSupport.Kantor79.movedSpace g).map (a : U →ₗ[ZMod p] U) := by
    have h := zs4k_movedSpace_conj a g
    rwa [ha_inv] at h
  have haganot : ¬ HardMathSupport.Kantor79.movedSpace (a * g * a) ≤ zs4kV f := by
    rw [hconj]
    intro hle
    have h2 : HardMathSupport.Kantor79.movedSpace g ≤ zs4kV f := by
      have hmap := Submodule.map_mono (f := (a : U →ₗ[ZMod p] U)) hle
      rw [← Submodule.map_comp] at hmap
      have hcomp : ((a : U →ₗ[ZMod p] U).comp (a : U →ₗ[ZMod p] U)) = LinearMap.id := by
        change (a : U →ₗ[ZMod p] U) * (a : U →ₗ[ZMod p] U) = LinearMap.id
        rw [← LinearEquiv.coe_toLinearMap_mul, ha2, LinearEquiv.coe_toLinearMap_one]
      rw [hcomp, Submodule.map_id] at hmap
      rwa [haVH] at hmap
    exact zs4k_not_movedSpace_g hp h h2
  have hset : ({b, a * g * a, c} : Set (U ≃ₗ[ZMod p] U)) = {b, c, a * g * a} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact zs4k_finrank_closure_two_VH hbR hcR hagaR hbVH hcVH hbc_ne haganot

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_aga_orders (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b) (hgc : orderOf (g * c) = 3) :
    IsRefl p (a * g * a) ∧ orderOf (b * (a * g * a)) = 4 ∧
      orderOf ((a * g * a) * c) = 3 := by
  have ha2 : a * a = 1 := (isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a).1
  have hg2 : g * g = 1 := h.isRefl_g.1
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haga : a * g * a = g * a * g := by
    have h3 : (a * g) ^ 3 = 1 := by rw [← hag]; exact pow_orderOf_eq_one (a * g)
    have hsq : a * g * a * g = g * a := by
      have h : (a * g) ^ 2 * (a * g) = 1 := by rw [← pow_succ, h3]
      have h' : (a * g) ^ 2 = (a * g)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [pow_two, mul_inv_rev, inv_eq_of_mul_eq_one_right ha2,
        inv_eq_of_mul_eq_one_right hg2] at h'
      simpa [mul_assoc] using h'
    calc a * g * a = (a * g * a * g) * g := by simp [mul_assoc, hg2]
      _ = g * a * g := by rw [hsq]
  have hac : a * c = c * a := by
    apply eq_of_toMatrix_eq f
    rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_a, h.toMatrix_c]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]
  refine ⟨?_, ?_, ?_⟩
  · have h' := h.isRefl_g.conj a
    rwa [ha_inv] at h'
  · have h1 : b * (a * g * a) = g * (b * a) * g := by
      rw [haga]
      calc b * (g * a * g) = (b * g) * a * g := by group
        _ = (g * b) * a * g := by rw [hbg]
        _ = g * (b * a) * g := by group
    rw [h1, show g * (b * a) * g = g * (b * a) * g⁻¹ by
      rw [inv_eq_of_mul_eq_one_right hg2]]
    exact (SemiconjBy.orderOf_eq g
      (show g * (b * a) = (g * (b * a) * g⁻¹) * g by group)).symm.trans (zs4k_orderOf_ba hp h)
  · have h1 : (a * g * a) * c = a * (g * c) * a := by
      calc (a * g * a) * c = a * g * (a * c) := by group
        _ = a * g * (c * a) := by rw [hac]
        _ = a * (g * c) * a := by group
    rw [h1, show a * (g * c) * a = a * (g * c) * a⁻¹ by rw [ha_inv]]
    exact (SemiconjBy.orderOf_eq a
      (show a * (g * c) = (a * (g * c) * a⁻¹) * a by group)).symm.trans hgc

theorem orderOf_gc_ne_three_of_case_iii (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b) : orderOf (g * c) ≠ 3 := by
  intro hgc3
  obtain ⟨hagaR, hbaga, hcaga⟩ := zs4k_aga_orders hp h hag hbg hgc3
  have hbR : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  have hcR : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hbc : orderOf (b * c) = 3 := zs4k_orderOf_bc h
  have hU : Module.finrank (ZMod p) U = 4 := by
    simpa using Module.finrank_eq_card_basis f
  let X : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure ({b, a * g * a, c} : Set (U ≃ₗ[ZMod p] U))
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hXG : X ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact h.H_le hbH
    · exact G.mul_mem (G.mul_mem (h.H_le haH) h.g_mem) (h.H_le haH)
    · exact h.H_le hcH
  have hAt : QTwoLin.TransvectionFree X := fun x hx => h.transvectionFree x (hXG hx)
  have hD : DMax p X 4 :=
    ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hXG hx) y (hXG hy) hxr hyr,
      b, Subgroup.subset_closure (by simp), a * g * a, Subgroup.subset_closure (by simp), hbR,
      hagaR, hbaga⟩
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3 :=
    zs4k_finrank_closure_bc_aga hp h hbR hcR hagaR
  obtain ⟨hSplit, hgt⟩ :=
    zs4k_card_of_433 hp hU hbR hagaR hcR rfl hAt hdim hD hbaga hbc hcaga
  have hgtX : 48 < Nat.card X := hgt
  have hcard := h.maximal X hXG (zs4k_reflGen_closure_three hbR hagaR hcR) hSplit hD
  omega

omit [Module.Finite (ZMod p) U] in
omit [Module.Finite (ZMod p) U] in
private lemma zs4k_repr_iii_root (v w : Fin 4 → ZMod p) (hv : v 0 = v 1) (hv' : v 1 = v 2)
    (hw : w 0 = w 1) (h : w 0 * (2 * v 0) = 1) :
    (fun k => f.repr ((∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f i) -
      ((∑ i, w i • f.coord i) (∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f i)) •
        (∑ i, v i • f i)) k) = ![0, 0, -1, -2 * w 0 * v 3] := by
  have e0 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 0 = 1 := rfl
  have e1 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 1 = 1 := rfl
  have e2 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 2 = 0 := rfl
  have e3 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 3 = 0 := rfl
  have hq : (∑ i, w i • f.coord i) (∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f i) =
      2 * w 0 := by
    rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, e0, e1, e2, e3]
    rw [hw]; ring
  have h1 : 2 * w 0 * v 0 = 1 := by linear_combination h
  have h1' : 2 * w 0 * v 1 = 1 := by rw [← hv]; exact h1
  have h1'' : 2 * w 0 * v 2 = 1 := by rw [← hv']; exact h1'
  funext k
  have h2 : f.repr (∑ i, v i • f i) k = v k := zs4k_repr_sum v k
  have h3 : f.repr (∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f i) k =
      (![1, 1, 0, 0] : Fin 4 → ZMod p) k :=
    zs4k_repr_sum (fun i => (![1, 1, 0, 0] : Fin 4 → ZMod p) i) k
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h3, h2, hq]
  fin_cases k <;> simp [h1, h1', h1'']

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_repr_iii_coroot (v w : Fin 4 → ZMod p) (hv : v 0 = v 1)
    (hw : w 0 = w 1) (hw' : w 1 = w 2) (h : w 0 * (2 * v 0) = 1) :
    (fun k => ((∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f.coord i) -
      ((∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f.coord i) (∑ i, v i • f i)) •
        (∑ i, w i • f.coord i)) (f k)) = ![0, 0, -1, -2 * v 0 * w 3] := by
  have e0 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 0 = 1 := rfl
  have e1 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 1 = 1 := rfl
  have e2 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 2 = 0 := rfl
  have e3 : (![1, 1, 0, 0] : Fin 4 → ZMod p) 3 = 0 := rfl
  have hq : (∑ i, (![1, 1, 0, 0] : Fin 4 → ZMod p) i • f.coord i) (∑ i, v i • f i) =
      2 * v 0 := by
    rw [FFourCoord.sum_smul_coord_apply_sum, Fin.sum_univ_four, e0, e1, e2, e3]
    rw [hv]; ring
  have h1 : 2 * v 0 * w 0 = 1 := by linear_combination h
  have h1' : 2 * v 0 * w 1 = 1 := by rw [← hw]; exact h1
  have h1'' : 2 * v 0 * w 2 = 1 := by rw [← hw']; exact h1'
  funext k
  rw [LinearMap.sub_apply, LinearMap.smul_apply, hq]
  fin_cases k <;> simp [zs4k_sum_coord_apply_basis, h1, h1', h1'']

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_pij_matrix_iii (v w : Fin 4 → ZMod p)
    (hβ : -(2 * v 0 * w 3) ≠ 0)
    (hv : v 0 = v 1) (hv' : v 1 = v 2) (hw : w 0 = w 1) (hw' : w 1 = w 2)
    (h : w 0 * (2 * v 0) = 1)
    (hwv : ∑ i, w i * v i = 2) :
    Matrix.vecMulVec ![0, 0, -1, -2 * w 0 * v 3] ![0, 0, -1, -2 * v 0 * w 3] =
      Matrix.vecMulVec
        (Pi.single 2 1 - ((Units.mk0 (-(2 * v 0 * w 3)) hβ : (ZMod p)ˣ) : ZMod p)⁻¹ •
          Pi.single 3 1)
        (Pi.single 2 1 - ((Units.mk0 (-(2 * v 0 * w 3)) hβ : (ZMod p)ˣ) : ZMod p) •
          Pi.single 3 1) := by
  have hv0 : v 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero, mul_zero] at h
    exact one_ne_zero h.symm
  have hβval : ((Units.mk0 (-(2 * v 0 * w 3)) hβ : (ZMod p)ˣ) : ZMod p) = -(2 * v 0 * w 3) := rfl
  have hsum : w 0 * v 0 + w 0 * v 0 + w 0 * v 0 + w 3 * v 3 = 2 := by
    have hs := hwv
    rw [Fin.sum_univ_four, ← hv, ← hv.trans hv', ← hw, ← hw.trans hw'] at hs
    exact hs
  have h1 : 2 * w 0 * v 0 = 1 := by linear_combination h
  have hwv' : 2 * v 3 * w 3 = 1 := by linear_combination 2 * hsum - 3 * h1
  have hprod : (2 * v 0 * w 3) * (2 * w 0 * v 3) = 1 := by
    calc (2 * v 0 * w 3) * (2 * w 0 * v 3)
        = (2 * w 0 * v 0) * (2 * v 3 * w 3) := by ring
      _ = 1 := by rw [h1, hwv', mul_one]
  have hβinv : ((Units.mk0 (-(2 * v 0 * w 3)) hβ : (ZMod p)ˣ) : ZMod p)⁻¹ = -2 * w 0 * v 3 := by
    rw [hβval, inv_neg, inv_eq_of_mul_eq_one_right hprod]
    ring
  have ha : (![0, 0, -1, -2 * w 0 * v 3] : Fin 4 → ZMod p) =
      -1 • (Pi.single 2 1 - ((Units.mk0 (-(2 * v 0 * w 3)) hβ : (ZMod p)ˣ) : ZMod p)⁻¹ •
        Pi.single 3 1) := by
    rw [hβinv]
    funext k
    fin_cases k <;> simp [Pi.smul_apply]
  have hb : (![0, 0, -1, -2 * v 0 * w 3] : Fin 4 → ZMod p) =
      -1 • (Pi.single 2 1 - ((Units.mk0 (-(2 * v 0 * w 3)) hβ : (ZMod p)ˣ) : ZMod p) •
        Pi.single 3 1) := by
    rw [hβval]
    funext k
    fin_cases k <;> simp [Pi.smul_apply]
  rw [ha, hb]
  ext r c
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply]
  ring

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_case_iii_order (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) {v w : Fin 4 → ZMod p}
    {hφg : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2}
    (hgeq : g = Module.reflection hφg) : w 0 * (2 * v 0) = 1 := by
  have hφa := zs4k_pairing_diag (f := f) 0
  have haeq := zs4k_a_eq (f := f) h
  have h3 : orderOf (Module.reflection hφg * Module.reflection hφa) = 3 := by
    rw [← hgeq, ← haeq]
    have h1 : g * a = (a * g)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.isRefl_g.1,
        inv_eq_of_mul_eq_one_right (isRefl_of_toMatrix_eq_diagSignMat hp f h.toMatrix_a).1]
    rw [h1, orderOf_inv, hag]
  have hz := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφg hφa h3
  have hA : (∑ i, w i • f.coord i) (f 0) = w 0 := zs4k_sum_coord_apply_basis w 0
  have hB : ((2 : ZMod p) • f.coord 0) (∑ i, v i • f i) = 2 * v 0 := by
    rw [LinearMap.smul_apply, zs4k_coord_apply_sum, smul_eq_mul]
  rwa [hA, hB] at hz

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_coroot_three_ne_zero (h : FFourData f a b c g H G) {v w : Fin 4 → ZMod p}
    {hφg : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2}
    (hgeq : g = Module.reflection hφg) : w 3 ≠ 0 := by
  intro hw3
  apply h.apply_not_mem
  have hg3 : g (f 3) = f 3 := by
    rw [hgeq, Module.reflection_apply, zs4k_sum_coord_apply_basis w 3, hw3, zero_smul,
      sub_zero]
  rw [hg3]; exact Submodule.mem_span_singleton_self _

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_case_iii_coords (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b) (hgc : orderOf (g * c) = 2) :
    ∃ (v w : Fin 4 → ZMod p) (hφg : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2),
      g = Module.reflection hφg ∧ v 0 = v 1 ∧ v 1 = v 2 ∧ w 0 = w 1 ∧ w 1 = w 2 ∧
        w 0 * (2 * v 0) = 1 ∧ v 3 ≠ 0 ∧ w 3 ≠ 0 := by
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hgb_ne : g ≠ b := fun heq => h.map_ne (by rw [heq]; exact (zs4k_conj_data h hbH).1)
  have hgc_ne : g ≠ c := fun heq => h.map_ne (by rw [heq]; exact (zs4k_conj_data h hcH).1)
  obtain ⟨v, w, hgm, hwv⟩ := FFourCoord.exists_toMatrix_of_isRefl hp f h.isRefl_g
  obtain ⟨hφg, hgeq⟩ := FFourCoord.eq_reflection_of_toMatrix (f := f) hgm hwv
  have hφb := zs4k_pairing_pij_one (f := f) (by decide : (0 : Fin 4) ≠ 1)
  have hbeq := zs4k_b_eq (f := f) h
  have hφc := zs4k_pairing_pij_one (f := f) (by decide : (1 : Fin 4) ≠ 2)
  have hceq := zs4k_c_eq (f := f) h
  have hcomm_b : Commute (Module.reflection hφg) (Module.reflection hφb) := by
    show Module.reflection hφg * Module.reflection hφb =
      Module.reflection hφb * Module.reflection hφg
    rw [← hgeq, ← hbeq]; exact hbg.symm
  have hne_b : Module.reflection hφg ≠ Module.reflection hφb := fun heq =>
    hgb_ne (by rw [hgeq, hbeq]; exact heq)
  have hw01 : w 0 = w 1 := by
    have hz := apply_eq_zero_of_commute hp hφg hφb hcomm_b hne_b
    rw [map_sub, zs4k_sum_coord_apply_basis, zs4k_sum_coord_apply_basis] at hz
    exact sub_eq_zero.mp hz
  have hv01 : v 0 = v 1 := by
    have hz := apply_eq_zero_of_commute hp hφb hφg hcomm_b.symm (Ne.symm hne_b)
    rw [LinearMap.sub_apply, zs4k_coord_apply_sum, zs4k_coord_apply_sum] at hz
    exact sub_eq_zero.mp hz
  have hz2 := apply_eq_zero_of_orderOf_eq_two hp hφg hφc
    (by rw [← hgeq, ← hceq]; exact hgc)
  have hw12 : w 1 = w 2 := by
    have hz := hz2.1
    rw [map_sub, zs4k_sum_coord_apply_basis, zs4k_sum_coord_apply_basis] at hz
    exact sub_eq_zero.mp hz
  have hv12 : v 1 = v 2 := by
    have hz := hz2.2
    rw [LinearMap.sub_apply, zs4k_coord_apply_sum, zs4k_coord_apply_sum] at hz
    exact sub_eq_zero.mp hz
  refine ⟨v, w, hφg, hgeq, hv01, hv12, hw01, hw12,
    zs4k_case_iii_order hp h hag hgeq, ?_, zs4k_coroot_three_ne_zero h hgeq⟩
  exact FFourCoord.apply_three_ne_zero_of_map_ne f hgm hwv h.map_ne

omit [Module.Finite (ZMod p) U] in
theorem pi34_of_case_iii_two (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b) (hgc : orderOf (g * c) = 2) :
    ∃ β : (ZMod p)ˣ,
      LinearMap.toMatrix f f (g * a * b * a * g).toLinearMap = pijMat 2 3 (β : ZMod p) := by
  obtain ⟨v, w, hφg, hgeq, hv01, hv12, hw01, hw12, hz, hv3, hw3⟩ :=
    zs4k_case_iii_coords hp h hag hbg hgc
  have hwv : ∑ i : Fin 4, w i * v i = 2 := by
    rw [← FFourCoord.sum_smul_coord_apply_sum f w v]; exact hφg
  have haba_mat : LinearMap.toMatrix f f (a * b * a).toLinearMap =
      1 - Matrix.vecMulVec (![1, 1, 0, 0] : Fin 4 → ZMod p) (![1, 1, 0, 0] : Fin 4 → ZMod p) := by
    rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_a, h.toMatrix_b]
    exact FFourCoord.aba_mat_eq
  obtain ⟨hφaba, habaeq⟩ := FFourCoord.eq_reflection_of_toMatrix (n := 4) (f := f) haba_mat
    (by norm_num [Fin.sum_univ_four])
  have hxeq : g * a * b * a * g = Module.reflection (conj_pairing hφg hφaba) := by
    calc g * a * b * a * g = Module.reflection hφg * (a * b * a) * Module.reflection hφg := by
          rw [hgeq]; group
      _ = Module.reflection hφg * Module.reflection hφaba * Module.reflection hφg := by
          rw [habaeq]
      _ = Module.reflection (conj_pairing hφg hφaba) := reflection_conj_reflection hφg hφaba
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hv0 : v 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero, mul_zero] at hz
    exact one_ne_zero hz.symm
  have hβ : -(2 * v 0 * w 3) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h2 hv0) hw3)
  refine ⟨Units.mk0 (-(2 * v 0 * w 3)) hβ, ?_⟩
  rw [hxeq, toMatrix_reflection (f := f) (conj_pairing hφg hφaba),
    zs4k_repr_iii_root (f := f) v w hv01 hv12 hw01 hz,
    zs4k_repr_iii_coroot (f := f) v w hv01 hw01 hw12 hz,
    zs4k_pij_matrix_iii v w hβ hv01 hv12 hw01 hw12 hz hwv,
    pijMat_eq_one_sub_vecMulVec (n := 4) (i := 2) (j := 3) (by decide) (Units.ne_zero _)]

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_orderOf_conj_eq (k x : U ≃ₗ[ZMod p] U) :
    orderOf (k * x * k⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq k (show k * x = (k * x * k⁻¹) * k by group)).symm

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_ac_comm (h : FFourData f a b c g H G) :
    a * c = c * a := by
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_a, h.toMatrix_c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_c_inv (h : FFourData f a b c g H G) : c⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (zs4k_c_sq h.toMatrix_c)

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_cbc (h : FFourData f a b c g H G) :
    c * b * c = b * c * b := by
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul, toMatrix_coe_mul, toMatrix_coe_mul, toMatrix_coe_mul,
    h.toMatrix_b, h.toMatrix_c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_orders_gprime (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b) (hgc : orderOf (g * c) = 4) :
    orderOf (a * (c * g * c)) = 3 ∧ orderOf ((c * g * c) * c) = 4 ∧
      orderOf ((c * g * c) * b) = 4 := by
  have hac : a * c = c * a := zs4p_ac_comm h
  have hc2 : c * c = 1 := zs4k_c_sq h.toMatrix_c
  have hci : c⁻¹ = c := zs4p_c_inv h
  have hbc : c * b * c = b * c * b := zs4p_cbc h
  have hb2 : b * b = 1 := zs4k_b_sq h.toMatrix_b
  refine ⟨?_, ?_, ?_⟩
  · have h1 : a * (c * g * c) = c * (a * g) * c := by
      calc a * (c * g * c) = (a * c) * g * c := by group
        _ = (c * a) * g * c := by rw [hac]
        _ = c * (a * g) * c := by group
    rw [h1]
    simpa [hci, hag] using zs4p_orderOf_conj_eq c (a * g)
  · have h1 : (c * g * c) * c = c * g := by rw [mul_assoc, hc2, mul_one]
    have h2 : orderOf (c * g) = orderOf (g * c) :=
      SemiconjBy.orderOf_eq c (by
        show c * (c * g) = (g * c) * c
        rw [← mul_assoc, hc2, one_mul, mul_assoc, hc2, mul_one])
    rw [h1]
    exact h2.trans hgc
  · have hs1 : SemiconjBy c ((c * g * c) * b) (g * (c * b * c)) := by
      show c * ((c * g * c) * b) = (g * (c * b * c)) * c
      calc c * ((c * g * c) * b) = (c * c) * (g * c * b) := by group
        _ = g * c * b := by rw [hc2, one_mul]
        _ = (g * (c * b * c)) * c := by
              rw [show (g * (c * b * c)) * c = (g * c * b) * (c * c) by group,
                hc2, mul_one]
    have hs3 : g * (b * c * b) = b * (g * c) * b := by
      calc g * (b * c * b) = g * b * c * b := by group
        _ = b * g * c * b := by rw [← hbg]
        _ = b * (g * c) * b := by group
    have hs4 : SemiconjBy b (b * (g * c) * b) (g * c) := by
      show b * (b * (g * c) * b) = (g * c) * b
      rw [show b * (b * (g * c) * b) = (b * b) * (g * c * b) by group, hb2, one_mul]
    calc orderOf ((c * g * c) * b) = orderOf (g * (c * b * c)) :=
          SemiconjBy.orderOf_eq c hs1
      _ = orderOf (g * (b * c * b)) := by rw [hbc]
      _ = orderOf (b * (g * c) * b) := by rw [hs3]
      _ = orderOf (g * c) := SemiconjBy.orderOf_eq b hs4
      _ = 4 := hgc

private lemma zs4p_noncomm_branch (hp : p ≠ 2) {g' : U ≃ₗ[ZMod p] U}
    (h' : FFourData f a b c g' H G) (hT : TFSmallThree p)
    (hgb' : orderOf (g' * b) = 4) (hg' : g' * (a * b * a) ≠ (a * b * a) * g') :
    (p = 3 ∧ ∃ ε : (ZMod p)ˣ, basisClosure (f.unitsSMul ![1, 1, 1, ε]) oPhiOneMats ≤ G) ∨
      ∃ β : (ZMod p)ˣ, ∃ r ∈ G,
        LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 (β : ZMod p) := by
  have hb2 : b * b = 1 := zs4k_b_sq h'.toMatrix_b
  have hg'2 : g' * g' = 1 := h'.isRefl_g.1
  by_cases hA : IrredOnSection (Subgroup.closure {a, b, g'}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g'}))
  · rcases h'.irred_cases hp hT hg' hA with ⟨-, h3⟩ | ⟨-, h3⟩ | ⟨-, h6⟩
    · exact absurd h3 (by rw [hgb']; norm_num)
    · exact absurd h3 (by rw [hgb']; norm_num)
    · exfalso
      have hsq : (g' * b) ^ 2 = 1 := by
        rw [pow_two]
        calc (g' * b) * (g' * b) = g' * (b * g') * b := by group
          _ = g' * (g' * b) * b := by rw [h6]
          _ = (g' * g') * (b * b) := by group
          _ = 1 := by rw [hg'2, hb2, mul_one]
      have hne : g' * b ≠ 1 := by
        intro h1
        rw [h1] at hgb'
        simp at hgb'
      have h2 : orderOf (g' * b) = 2 := orderOf_eq_prime hsq hne
      rw [hgb'] at h2
      omega
  · exact Or.inl (h'.oPhi_le_of_not_irred hp hg' hA)

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_k_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (c * b * a * b * c).toLinearMap = diagSignMat 2 := by
  rw [toMatrix_coe_mul f (c * b * a * b) c, toMatrix_coe_mul f (c * b * a) b,
    toMatrix_coe_mul f (c * b) a, toMatrix_coe_mul f c b,
    h.toMatrix_c, h.toMatrix_b, h.toMatrix_a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_m_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (c * (a * b * a) * c).toLinearMap =
      1 - Matrix.vecMulVec ![1, 0, 1, 0] ![1, 0, 1, 0] := by
  rw [toMatrix_coe_mul f (c * (a * b * a)) c, toMatrix_coe_mul f c (a * b * a),
    toMatrix_coe_mul f (a * b) a, toMatrix_coe_mul f a b,
    h.toMatrix_a, h.toMatrix_b, h.toMatrix_c]
  exact FFourCoord.cabac_mat_eq

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_k_data (h : FFourData f a b c g H G) :
    (c * b * a * b * c)⁻¹ = c * b * a * b * c ∧
      a * (c * b * a * b * c) = (c * b * a * b * c) * a ∧
      b * (c * b * a * b * c) = (c * b * a * b * c) * b := by
  set k : U ≃ₗ[ZMod p] U := c * b * a * b * c with hk_def
  have hk_mat : LinearMap.toMatrix f f k.toLinearMap = diagSignMat 2 := by
    simpa [hk_def] using zs4p_k_mat h
  have hk_sq : k * k = 1 := by
    apply eq_of_toMatrix_eq f
    rw [toMatrix_coe_mul f k k, hk_mat, diagSignMat_mul_self]
    simp
  have hk_inv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk_sq
  have hak : a * k = k * a := by
    apply eq_of_toMatrix_eq f
    rw [toMatrix_coe_mul f a k, toMatrix_coe_mul f k a, h.toMatrix_a, hk_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, diagSignMat]
  have hbk : b * k = k * b := by
    apply eq_of_toMatrix_eq f
    rw [toMatrix_coe_mul f b k, toMatrix_coe_mul f k b, h.toMatrix_b, hk_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]
  exact ⟨hk_inv, hak, hbk⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_kck (h : FFourData f a b c g H G) :
    (c * b * a * b * c) * c * (c * b * a * b * c) =
      b * (c * (a * b * a) * c) * b := by
  set k : U ≃ₗ[ZMod p] U := c * b * a * b * c with hk_def
  set m : U ≃ₗ[ZMod p] U := c * (a * b * a) * c with hm_def
  have hk_mat : LinearMap.toMatrix f f k.toLinearMap = diagSignMat 2 := by
    simpa [hk_def] using zs4p_k_mat h
  have hm_mat : LinearMap.toMatrix f f m.toLinearMap =
      1 - Matrix.vecMulVec ![1, 0, 1, 0] ![1, 0, 1, 0] := by
    simpa [hm_def] using zs4p_m_mat h
  apply eq_of_toMatrix_eq f
  rw [toMatrix_coe_mul f (k * c) k, toMatrix_coe_mul f k c,
    toMatrix_coe_mul f (b * m) b, toMatrix_coe_mul f b m,
    hk_mat, h.toMatrix_c, h.toMatrix_b, hm_mat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pijMat, diagSignMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_hgm (h : FFourData f a b c g H G)
    (hcomm : (c * g * c) * (a * b * a) = (a * b * a) * (c * g * c)) :
    g * (c * (a * b * a) * c) = (c * (a * b * a) * c) * g := by
  have hc2 : c * c = 1 := zs4k_c_sq h.toMatrix_c
  have h1 := congrArg (fun x => c * x * c) hcomm
  have hL : c * ((c * g * c) * (a * b * a)) * c = g * (c * (a * b * a) * c) := by
    calc c * ((c * g * c) * (a * b * a)) * c = (c * c) * g * c * (a * b * a) * c := by
          group
      _ = g * c * (a * b * a) * c := by rw [hc2, one_mul]
      _ = g * (c * (a * b * a) * c) := by group
  have hR : c * ((a * b * a) * (c * g * c)) * c = (c * (a * b * a) * c) * g := by
    calc c * ((a * b * a) * (c * g * c)) * c = c * (a * b * a) * c * g * (c * c) := by
          group
      _ = c * (a * b * a) * c * g := by rw [hc2, mul_one]
      _ = (c * (a * b * a) * c) * g := by group
  rw [hL, hR] at h1
  exact h1

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_hgc_eq (h : FFourData f a b c g H G)
    (hbg : b * g = g * b)
    (hcomm : (c * g * c) * (a * b * a) = (a * b * a) * (c * g * c)) :
    ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * c =
      c * ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) := by
  set k : U ≃ₗ[ZMod p] U := c * b * a * b * c with hk_def
  obtain ⟨hk_inv, -, hbk⟩ := zs4p_k_data h
  have hkck := zs4p_kck h
  have hgm := zs4p_hgm h hcomm
  rw [← hk_def] at hk_inv hkck
  have hg_bmb : g * (b * (c * (a * b * a) * c) * b) =
      (b * (c * (a * b * a) * c) * b) * g := by
    have h1 : Commute b g := hbg
    have h2 : Commute g (c * (a * b * a) * c) := hgm
    exact ((h1.symm.mul_right h2).mul_right h1.symm).eq
  have hck : c = k * (b * (c * (a * b * a) * c) * b) * k⁻¹ := by
    calc c = k⁻¹ * (k * c * k) * k⁻¹ := by group
      _ = k⁻¹ * (b * (c * (a * b * a) * c) * b) * k⁻¹ := by rw [hkck]
      _ = k * (b * (c * (a * b * a) * c) * b) * k⁻¹ := by rw [hk_inv]
  rw [hck]
  calc (k * g * k⁻¹) * (k * (b * (c * (a * b * a) * c) * b) * k⁻¹) =
        k * (g * (b * (c * (a * b * a) * c) * b)) * k⁻¹ := by group
    _ = k * ((b * (c * (a * b * a) * c) * b) * g) * k⁻¹ := by rw [hg_bmb]
    _ = (k * (b * (c * (a * b * a) * c) * b) * k⁻¹) * (k * g * k⁻¹) := by group

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_g''_sq (h : FFourData f a b c g H G) :
    ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) *
        ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) = 1 := by
  set k : U ≃ₗ[ZMod p] U := c * b * a * b * c with hk_def
  calc (k * g * k⁻¹) * (k * g * k⁻¹) = k * (g * g) * k⁻¹ := by group
    _ = 1 := by rw [h.isRefl_g.1]; group

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_hag'' (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) :
    orderOf (a * ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹)) = 3 := by
  obtain ⟨-, hak, -⟩ := zs4p_k_data h
  have h1 : a * ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) =
      (c * b * a * b * c) * (a * g) * (c * b * a * b * c)⁻¹ := by
    calc a * ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) =
          (a * (c * b * a * b * c)) * g * (c * b * a * b * c)⁻¹ := by group
      _ = ((c * b * a * b * c) * a) * g * (c * b * a * b * c)⁻¹ := by rw [hak]
      _ = (c * b * a * b * c) * (a * g) * (c * b * a * b * c)⁻¹ := by group
  rw [h1, zs4p_orderOf_conj_eq (c * b * a * b * c) (a * g), hag]

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_hbg'' (h : FFourData f a b c g H G)
    (hbg : b * g = g * b) :
    b * ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) =
      ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * b := by
  obtain ⟨-, -, hbk⟩ := zs4p_k_data h
  have h1 : Commute b (c * b * a * b * c) := hbk
  have h2 : Commute b g := hbg
  exact ((h1.mul_right h2).mul_right h1.inv_right).eq

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_hgc'' (h : FFourData f a b c g H G)
    (hbg : b * g = g * b)
    (hcomm : (c * g * c) * (a * b * a) = (a * b * a) * (c * g * c)) :
    orderOf (((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * c) = 2 := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hkH : c * b * a * b * c ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hcH hbH) haH) hbH) hcH
  have h'' : FFourData f a b c ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) H G :=
    h.conj hkH
  have hgc_eq := zs4p_hgc_eq h hbg hcomm
  have hg''2 := zs4p_g''_sq h
  have hc2 : c * c = 1 := zs4k_c_sq h.toMatrix_c
  have hgc_sq : (((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * c) ^ 2 = 1 := by
    calc (((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * c) ^ 2
        = (((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * c) *
            (c * ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹)) := by
          rw [pow_two, hgc_eq]
      _ = ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * (c * c) *
            ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) := by group
      _ = 1 := by rw [hc2, mul_one, hg''2]
  have hgc_ne1 : ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * c ≠ 1 := by
    intro h1
    have hg_eq_c : (c * b * a * b * c) * g * (c * b * a * b * c)⁻¹ = c := by
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hc2]
    apply h''.apply_not_mem
    rw [hg_eq_c, zs4k_apply_three f h.toMatrix_c (fun i hi => by simp [pijMat, hi])
      (by simp [pijMat])]
    exact Submodule.mem_span_singleton_self (f 3)
  exact orderOf_eq_prime hgc_sq hgc_ne1

omit [Module.Finite (ZMod p) U] in
private lemma zs4p_comm_branch (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b)
    (hcomm : (c * g * c) * (a * b * a) = (a * b * a) * (c * g * c)) :
    (p = 3 ∧ ∃ ε : (ZMod p)ˣ, basisClosure (f.unitsSMul ![1, 1, 1, ε]) oPhiOneMats ≤ G) ∨
      ∃ β : (ZMod p)ˣ, ∃ r ∈ G,
        LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 (β : ZMod p) := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hkH : c * b * a * b * c ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hcH hbH) haH) hbH) hcH
  have h'' : FFourData f a b c ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) H G :=
    h.conj hkH
  have hag'' := zs4p_hag'' h hag
  have hbg'' := zs4p_hbg'' h hbg
  have hgc'' := zs4p_hgc'' h hbg hcomm
  obtain ⟨β, hβ⟩ := pi34_of_case_iii_two hp h'' hag'' hbg'' hgc''
  refine Or.inr ⟨β, ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹) * a * b * a *
    ((c * b * a * b * c) * g * (c * b * a * b * c)⁻¹), ?_, hβ⟩
  have hkG : c * b * a * b * c ∈ G := h.H_le hkH
  have hgG : (c * b * a * b * c) * g * (c * b * a * b * c)⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem hkG h.g_mem) (G.inv_mem hkG)
  exact G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem hgG (h.H_le haH)) (h.H_le hbH))
    (h.H_le haH)) hgG

theorem pi34_or_oPhi_of_case_iii_four (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hT : TFSmallThree p)
    (hag : orderOf (a * g) = 3) (hbg : b * g = g * b) (hgc : orderOf (g * c) = 4) :
    (p = 3 ∧ ∃ ε : (ZMod p)ˣ, basisClosure (f.unitsSMul ![1, 1, 1, ε]) oPhiOneMats ≤ G) ∨
      ∃ β : (ZMod p)ˣ, ∃ r ∈ G, LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 (β : ZMod p) := by
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hci : c⁻¹ = c := zs4p_c_inv h
  have h' : FFourData f a b c (c * g * c) H G := by
    simpa [hci] using h.conj hcH
  obtain ⟨-, -, hgb'⟩ := zs4p_orders_gprime h hag hbg hgc
  by_cases hcomm : (c * g * c) * (a * b * a) = (a * b * a) * (c * g * c)
  · exact zs4p_comm_branch hp h hag hbg hcomm
  · exact zs4p_noncomm_branch hp h' hT hgb' hcomm

private lemma zs4k_case_iii_pi34 (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) U}
    {a b c g : U ≃ₗ[ZMod p] U} {H G : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FFourData f a b c g H G) (hT : TFSmallThree p) (hag : orderOf (a * g) = 3)
    (hbg : b * g = g * b) :
    (p = 3 ∧ ∃ ε : (ZMod p)ˣ, basisClosure (f.unitsSMul ![1, 1, 1, ε]) oPhiOneMats ≤ G) ∨
      ∃ β : (ZMod p)ˣ, ∃ r ∈ G, LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 (β : ZMod p) := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hRc : IsRefl p c :=
    isRefl_of_toMatrix_eq_pijMat f (i := 1) (j := 2) (by decide) one_ne_zero h.toMatrix_c
  have hgc4 : orderOf (g * c) ≤ 4 := h.dmax.1 g h.g_mem c (h.H_le hcH) h.isRefl_g hRc
  have hgcne3 : orderOf (g * c) ≠ 3 := orderOf_gc_ne_three_of_case_iii hp h hag hbg
  have hgcne1 : orderOf (g * c) ≠ 1 := by
    intro h1
    have hgc : g * c = 1 := orderOf_eq_one_iff.mp h1
    have hg_eq_c : g = c := by
      rw [eq_inv_of_mul_eq_one_left hgc, inv_eq_of_mul_eq_one_right hRc.1]
    have hc3 : c (f 3) = f 3 :=
      zs4k_apply_three f h.toMatrix_c (fun i hi => by simp [pijMat, hi]) (by simp [pijMat])
    apply h.apply_not_mem
    rw [hg_eq_c, hc3]
    exact Submodule.mem_span_singleton_self (f 3)
  have : Finite U := Module.finite_of_finite (R := ZMod p) (M := U)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  have hpos : 0 < orderOf (g * c) := (isOfFinOrder_of_finite (g * c)).orderOf_pos
  have hcases : orderOf (g * c) = 2 ∨ orderOf (g * c) = 4 := by omega
  rcases hcases with h2 | h4
  · obtain ⟨β, hβ⟩ := pi34_of_case_iii_two hp h hag hbg h2
    refine Or.inr ⟨β, g * a * b * a * g, ?_, hβ⟩
    exact G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem h.g_mem (h.H_le haH))
      (h.H_le hbH)) (h.H_le haH)) h.g_mem
  · exact pi34_or_oPhi_of_case_iii_four hp h hT hag hbg h4

theorem pi34_or_oPhi (hp : p ≠ 2) (h : FFourData f a b c g H G) (hT : TFSmallThree p)
    (hg : g * (a * b * a) ≠ a * b * a * g) :
    (p = 3 ∧ ∃ ε : (ZMod p)ˣ, basisClosure (f.unitsSMul ![1, 1, 1, ε]) oPhiOneMats ≤ G) ∨
      ∃ β : (ZMod p)ˣ, ∃ r ∈ G, LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 (β : ZMod p) := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hRb : IsRefl p b :=
    isRefl_of_toMatrix_eq_pijMat f (i := 0) (j := 1) (by decide) one_ne_zero h.toMatrix_b
  by_cases hA : IrredOnSection (Subgroup.closure {a, b, g}) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, b, g}))
  · rcases h.irred_cases hp hT hg hA with ⟨h1, h2⟩ | ⟨h3, h4⟩ | ⟨h5, h6⟩
    · have h' : FFourData f a b c (b * g * b) H G := by
        simpa [inv_eq_of_mul_eq_one_right hRb.1] using h.conj hbH
      have hgb' : orderOf ((b * g * b) * b) = 3 := by
        have hbb : b * b = 1 := hRb.1
        have hmul : (b * g * b) * b = b * g := by rw [mul_assoc, mul_assoc, hbb, mul_one]
        rw [hmul]
        exact (SemiconjBy.orderOf_eq b (by
          show b * (g * b) = (b * g) * b
          rw [mul_assoc])).symm.trans h2
      obtain ⟨β, hβ⟩ := pi34_of_case_ii hp h' h1 hgb'
      refine Or.inr ⟨β, c * (b * g * b) * c, ?_, hβ⟩
      exact G.mul_mem (G.mul_mem (h.H_le hcH)
        (G.mul_mem (G.mul_mem (h.H_le hbH) h.g_mem) (h.H_le hbH))) (h.H_le hcH)
    · obtain ⟨β, hβ⟩ := pi34_of_case_ii hp h h3 h4
      exact Or.inr ⟨β, c * g * c,
        G.mul_mem (G.mul_mem (h.H_le hcH) h.g_mem) (h.H_le hcH), hβ⟩
    · exact zs4k_case_iii_pi34 hp h hT h5 h6
  · exact Or.inl (h.oPhi_le_of_not_irred hp hg hA)

omit [Module.Finite (ZMod p) U] in
theorem eq_isIsom_of_oPhi_le (hp : p = 3) (h : FFourData f a b c g H G)
    (hO : basisClosure f oPhiOneMats ≤ G) (x : U ≃ₗ[ZMod p] U) :
    x ∈ G ↔ IsIsom p (phiForm f) x := by
  have hp2 : p ≠ 2 := by omega
  have ha' : a ∈ basisClosure f oPhiOneMats :=
    Subgroup.subset_closure (by simp [h.toMatrix_a, oPhiOneMats])
  have hb' : b ∈ basisClosure f oPhiOneMats :=
    Subgroup.subset_closure (by simp [h.toMatrix_b, oPhiOneMats])
  have hc' : c ∈ basisClosure f oPhiOneMats :=
    Subgroup.subset_closure (by simp [h.toMatrix_c, oPhiOneMats])
  have hHle : H ≤ basisClosure f oPhiOneMats := by
    rw [h.H_eq]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy : y ∈ ({a, b, c} : Set (U ≃ₗ[ZMod p] U)))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha'
    · exact hb'
    · exact hc'
  exact isIsom_iff_of_le hp2 f h.reflGen
    (fun y hy => hO ((mem_oPhiOne_iff hp f y).mpr hy))
    (fun y hy => isIsom_phiForm_of_mem_oPhiOne hp f (hHle hy)) h.inH x

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_monomial_a (h : FFourData f a b c g H G) : IsMonomialIn f a := by
  intro i
  refine ⟨i, (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) i i, ?_⟩
  change (a : U →ₗ[ZMod p] U) (f i) =
    (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) i i • f i
  rw [zs4k_apply_eq f h.toMatrix_a i, Finset.sum_eq_single i]
  · intro k _ hki
    have hk : (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) k i = 0 := by
      simp [diagSignMat, hki]
    rw [hk, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_monomial_b (h : FFourData f a b c g H G) : IsMonomialIn f b := by
  intro i
  fin_cases i <;> simp only []
  · refine ⟨1, 1, ?_⟩
    change (b : U →ₗ[ZMod p] U) (f (0 : Fin 4)) = (1 : ZMod p) • f 1
    rw [zs4k_apply_eq f h.toMatrix_b 0, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨0, 1, ?_⟩
    change (b : U →ₗ[ZMod p] U) (f (1 : Fin 4)) = (1 : ZMod p) • f 0
    rw [zs4k_apply_eq f h.toMatrix_b 1, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨2, 1, ?_⟩
    change (b : U →ₗ[ZMod p] U) (f (2 : Fin 4)) = (1 : ZMod p) • f 2
    rw [zs4k_apply_eq f h.toMatrix_b 2, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨3, 1, ?_⟩
    change (b : U →ₗ[ZMod p] U) (f (3 : Fin 4)) = (1 : ZMod p) • f 3
    rw [zs4k_apply_eq f h.toMatrix_b 3, Fin.sum_univ_four]; simp [pijMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_monomial_c (h : FFourData f a b c g H G) : IsMonomialIn f c := by
  intro i
  fin_cases i <;> simp only []
  · refine ⟨0, 1, ?_⟩
    change (c : U →ₗ[ZMod p] U) (f (0 : Fin 4)) = (1 : ZMod p) • f 0
    rw [zs4k_apply_eq f h.toMatrix_c 0, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨2, 1, ?_⟩
    change (c : U →ₗ[ZMod p] U) (f (1 : Fin 4)) = (1 : ZMod p) • f 2
    rw [zs4k_apply_eq f h.toMatrix_c 1, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨1, 1, ?_⟩
    change (c : U →ₗ[ZMod p] U) (f (2 : Fin 4)) = (1 : ZMod p) • f 1
    rw [zs4k_apply_eq f h.toMatrix_c 2, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨3, 1, ?_⟩
    change (c : U →ₗ[ZMod p] U) (f (3 : Fin 4)) = (1 : ZMod p) • f 3
    rw [zs4k_apply_eq f h.toMatrix_c 3, Fin.sum_univ_four]; simp [pijMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_H_monomial (h : FFourData f a b c g H G) :
    ∀ k ∈ H, IsMonomialIn f k := by
  intro k hk
  rw [h.H_eq] at hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact zs4h_monomial_a h
      · exact zs4h_monomial_b h
      · exact zs4h_monomial_c h
  | one => intro i; exact ⟨i, 1, by simp⟩
  | mul x y _ _ ihx ihy => exact ihx.mul ihy
  | inv x _ ihx => exact ihx.inv

private lemma zs4h_sum_single (w : Fin 4 → ZMod p) (i : Fin 4) :
    (∑ l, w l * (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l) = w i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hli; simp [hli]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma zs4h_sum_single_two (v : Fin 4 → ZMod p) (i : Fin 4) :
    (∑ l, (Pi.single i (2 : ZMod p) : Fin 4 → ZMod p) l * v l) = 2 * v i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hli; simp [hli]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma zs4h_pairing_diag (i : Fin 4) :
    (∑ l, (Pi.single i (2 : ZMod p) : Fin 4 → ZMod p) l *
      (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l) = 2 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hli; simp [hli]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma zs4h_pairing_sub (i j : Fin 4) (hij : i ≠ j) :
    (∑ l, ((Pi.single i 1 : Fin 4 → ZMod p) - (Pi.single j 1 : Fin 4 → ZMod p)) l *
      ((Pi.single i 1 : Fin 4 → ZMod p) - (Pi.single j 1 : Fin 4 → ZMod p)) l) = 2 := by
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp_all <;> ring

private lemma zs4h_pairing_add (i j : Fin 4) (hij : i ≠ j) :
    (∑ l, ((Pi.single i 1 : Fin 4 → ZMod p) + (Pi.single j 1 : Fin 4 → ZMod p)) l *
      ((Pi.single i 1 : Fin 4 → ZMod p) + (Pi.single j 1 : Fin 4 → ZMod p)) l) = 2 := by
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp_all <;> ring

private lemma zs4h_mat_congr {ρ κ ρ' κ' : Fin 4 → ZMod p} (hρ : ρ = ρ') (hκ : κ = κ') :
    (1 - Matrix.vecMulVec ρ κ : Matrix (Fin 4) (Fin 4) (ZMod p)) =
      1 - Matrix.vecMulVec ρ' κ' := by
  rw [hρ, hκ]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_e0_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f a.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p)) (Pi.single 0 (2 : ZMod p)) := by
  rw [h.toMatrix_a, diagSignMat_eq_one_sub_vecMulVec]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_e1_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (b * a * b).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 1 (1 : ZMod p)) (Pi.single 1 (2 : ZMod p)) := by
  rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_b, h.toMatrix_a, FFourCoord.bab_mat_eq]
  exact zs4h_mat_congr (by ext i; fin_cases i <;> simp)
    (by ext i; fin_cases i <;> simp)

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_e2_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (c * (b * a * b) * c).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 2 (1 : ZMod p)) (Pi.single 2 (2 : ZMod p)) := by
  have hc : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 1 (1 : ZMod p) - Pi.single 2 1)
        (Pi.single 1 1 - Pi.single 2 1) := by
    rw [h.toMatrix_c, pijMat_eq_one_sub_vecMulVec (i := 1) (j := 2) (by decide) one_ne_zero]
    simp
  rw [zs4h_conj_mat hc (zs4h_e1_mat h) (zs4h_pairing_sub 1 2 (by decide))]
  exact zs4h_mat_congr
    (by ext i; fin_cases i <;>
      simp [Pi.sub_apply, Pi.single_apply])
    (by ext i; fin_cases i <;>
      simp [Pi.sub_apply, Pi.smul_apply, Pi.single_apply])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_r_mat {r : U ≃ₗ[ZMod p] U}
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    LinearMap.toMatrix f f r.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 2 (1 : ZMod p) - Pi.single 3 1)
        (Pi.single 2 1 - Pi.single 3 1) := by
  rw [hrm, pijMat_eq_one_sub_vecMulVec (i := 2) (j := 3) (by decide) one_ne_zero]
  simp

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_e3_mat (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U}
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    LinearMap.toMatrix f f (r * (c * (b * a * b) * c) * r).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 3 (1 : ZMod p)) (Pi.single 3 (2 : ZMod p)) := by
  rw [zs4h_conj_mat (zs4h_r_mat hrm) (zs4h_e2_mat h) (zs4h_pairing_sub 2 3 (by decide))]
  exact zs4h_mat_congr
    (by ext i; fin_cases i <;>
      simp [Pi.sub_apply, Pi.single_apply])
    (by ext i; fin_cases i <;>
      simp [Pi.sub_apply, Pi.smul_apply, Pi.single_apply])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_p1_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f b.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p) - Pi.single 1 1)
        (Pi.single 0 1 - Pi.single 1 1) := by
  rw [h.toMatrix_b, pijMat_eq_one_sub_vecMulVec (i := 0) (j := 1) (by decide) one_ne_zero]
  simp

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_p2_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (b * c * b).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p) - Pi.single 2 1)
        (Pi.single 0 1 - Pi.single 2 1) := by
  rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_b, h.toMatrix_c, FFourCoord.bcb_mat_eq]
  exact zs4h_mat_congr (by ext i; fin_cases i <;> simp)
    (by ext i; fin_cases i <;> simp)

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_p3_mat (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U}
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    LinearMap.toMatrix f f (r * (b * c * b) * r).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p) - Pi.single 3 1)
        (Pi.single 0 1 - Pi.single 3 1) := by
  rw [zs4h_conj_mat (zs4h_r_mat hrm) (zs4h_p2_mat h) (zs4h_pairing_sub 2 3 (by decide))]
  exact zs4h_mat_congr
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_q1_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (a * b * a).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p) + Pi.single 1 1)
        (Pi.single 0 1 + Pi.single 1 1) := by
  rw [toMatrix_coe_mul, toMatrix_coe_mul, h.toMatrix_a, h.toMatrix_b, FFourCoord.aba_mat_eq]
  exact zs4h_mat_congr (by ext i; fin_cases i <;> simp)
    (by ext i; fin_cases i <;> simp)

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_q2_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f (c * (a * b * a) * c).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p) + Pi.single 2 1)
        (Pi.single 0 1 + Pi.single 2 1) := by
  have hc : LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 1 (1 : ZMod p) - Pi.single 2 1)
        (Pi.single 1 1 - Pi.single 2 1) := by
    rw [h.toMatrix_c, pijMat_eq_one_sub_vecMulVec (i := 1) (j := 2) (by decide) one_ne_zero]
    simp
  rw [zs4h_conj_mat hc (zs4h_q1_mat h) (zs4h_pairing_sub 1 2 (by decide))]
  exact zs4h_mat_congr
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_q3_mat (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U}
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    LinearMap.toMatrix f f (r * (c * (a * b * a) * c) * r).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 0 (1 : ZMod p) + Pi.single 3 1)
        (Pi.single 0 1 + Pi.single 3 1) := by
  rw [zs4h_conj_mat (zs4h_r_mat hrm) (zs4h_q2_mat h) (zs4h_pairing_sub 2 3 (by decide))]
  exact zs4h_mat_congr
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_sq_one {k : U ≃ₗ[ZMod p] U} {u : Fin 4 → ZMod p}
    (hk : LinearMap.toMatrix f f k.toLinearMap = 1 - Matrix.vecMulVec u u)
    (hu : ∑ i, u i * u i = 2) : k * k = 1 := by
  apply eq_of_toMatrix_eq (f := f)
  rw [toMatrix_coe_mul, hk, FFourCoord.one_sub_vecMulVec_mul_self hu]
  simp

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_monomial_r {r : U ≃ₗ[ZMod p] U}
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) : IsMonomialIn f r := by
  intro c
  fin_cases c <;> simp only []
  · refine ⟨0, 1, ?_⟩
    change (r : U →ₗ[ZMod p] U) (f (0 : Fin 4)) = (1 : ZMod p) • f 0
    rw [zs4k_apply_eq f hrm 0, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨1, 1, ?_⟩
    change (r : U →ₗ[ZMod p] U) (f (1 : Fin 4)) = (1 : ZMod p) • f 1
    rw [zs4k_apply_eq f hrm 1, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨3, 1, ?_⟩
    change (r : U →ₗ[ZMod p] U) (f (2 : Fin 4)) = (1 : ZMod p) • f 3
    rw [zs4k_apply_eq f hrm 2, Fin.sum_univ_four]; simp [pijMat]
  · refine ⟨2, 1, ?_⟩
    change (r : U →ₗ[ZMod p] U) (f (3 : Fin 4)) = (1 : ZMod p) • f 2
    rw [zs4k_apply_eq f hrm 3, Fin.sum_univ_four]; simp [pijMat]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_c_mat (h : FFourData f a b c g H G) :
    LinearMap.toMatrix f f c.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 1 (1 : ZMod p) - Pi.single 2 1)
        (Pi.single 1 1 - Pi.single 2 1) := by
  rw [h.toMatrix_c, pijMat_eq_one_sub_vecMulVec (i := 1) (j := 2) (by decide) one_ne_zero]
  simp

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_p13_mat {r : U ≃ₗ[ZMod p] U}
    (h : FFourData f a b c g H G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    LinearMap.toMatrix f f (r * c * r).toLinearMap =
      1 - Matrix.vecMulVec (Pi.single 1 (1 : ZMod p) - Pi.single 3 1)
        (Pi.single 1 1 - Pi.single 3 1) := by
  rw [zs4h_conj_mat (zs4h_r_mat hrm) (zs4h_c_mat h) (zs4h_pairing_sub 2 3 (by decide))]
  exact zs4h_mat_congr
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])
    (by ext i; fin_cases i <;>
      simp [Fin.sum_univ_four, Pi.sub_apply, Pi.single_apply])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_mono_of_conj_swap (h : FFourData f a b c g H G)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) (hxrefl : IsRefl p x) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k)
    {k : U ≃ₗ[ZMod p] U} (hkG : k ∈ G) (hkMono : IsMonomialIn f k)
    {u : Fin 4 → ZMod p} (hkmat : LinearMap.toMatrix f f k.toLinearMap = 1 - Matrix.vecMulVec u u)
    (hu : ∑ i, u i * u i = 2)
    (hroot : (v - (∑ i, u i * v i) • u) 3 = 0) :
    IsMonomialIn f x := by
  have hym : LinearMap.toMatrix f f (k * x * k).toLinearMap =
      1 - Matrix.vecMulVec (v - (∑ i, u i * v i) • u) (w - (∑ i, w i * u i) • u) :=
    zs4h_conj_mat hkmat hxm hu
  have hyVH : HardMathSupport.Kantor79.movedSpace (k * x * k) ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) :=
    FFourCoord.movedSpace_le_span_of_toMatrix f hym hroot
  have hyrefl : IsRefl p (k * x * k) := by
    have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right (zs4h_sq_one hkmat hu)
    have hc := IsRefl.conj hxrefl k
    rwa [hkinv] at hc
  have hyG : k * x * k ∈ G := G.mul_mem (G.mul_mem hkG hxG) hkG
  have hyMono : IsMonomialIn f (k * x * k) := hHmono _ (h.inH _ hyG hyrefl hyVH)
  have hk2 : k * k = 1 := zs4h_sq_one hkmat hu
  have heq : x = k * (k * x * k) * k := by
    rw [show k * (k * x * k) * k = (k * k) * x * (k * k) by group, hk2]
    group
  rw [heq]
  exact IsMonomialIn.mul (IsMonomialIn.mul hkMono hyMono) hkMono

private lemma zs4h_sum_single' (v : Fin 4 → ZMod p) (i : Fin 4) :
    (∑ l, (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l * v l) = v i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hli; simp [hli]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma zs4h_sum_sub (w : Fin 4 → ZMod p) (i j : Fin 4) :
    (∑ l, w l * ((Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) -
      (Pi.single j (1 : ZMod p) : Fin 4 → ZMod p)) l) = w i - w j := by
  simp only [Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib, zs4h_sum_single w i, zs4h_sum_single w j]

private lemma zs4h_sum_sub' (v : Fin 4 → ZMod p) (i j : Fin 4) :
    (∑ l, ((Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) -
      (Pi.single j (1 : ZMod p) : Fin 4 → ZMod p)) l * v l) = v i - v j := by
  simp only [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib, zs4h_sum_single' v i, zs4h_sum_single' v j]

private lemma zs4h_sum_add (w : Fin 4 → ZMod p) (i j : Fin 4) :
    (∑ l, w l * ((Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) +
      (Pi.single j (1 : ZMod p) : Fin 4 → ZMod p)) l) = w i + w j := by
  simp only [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, zs4h_sum_single w i, zs4h_sum_single w j]

private lemma zs4h_sum_add' (v : Fin 4 → ZMod p) (i j : Fin 4) :
    (∑ l, ((Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) +
      (Pi.single j (1 : ZMod p) : Fin 4 → ZMod p)) l * v l) = v i + v j := by
  simp only [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib, zs4h_sum_single' v i, zs4h_sum_single' v j]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_etaOK_diag (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) :
    ∀ i, EtaOK 4 (w i) (2 * v i) := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have haG : a ∈ G := h.H_le haH
  have hbG : b ∈ G := h.H_le hbH
  have hcG : c ∈ G := h.H_le hcH
  have haM : IsMonomialIn f a := hHmono a haH
  have hbM : IsMonomialIn f b := hHmono b hbH
  have hcM : IsMonomialIn f c := hHmono c hcH
  have hrM : IsMonomialIn f r := zs4h_monomial_r hrm
  have hb1G : b * a * b ∈ G := G.mul_mem (G.mul_mem hbG haG) hbG
  have hb1M : IsMonomialIn f (b * a * b) := IsMonomialIn.mul (IsMonomialIn.mul hbM haM) hbM
  have hb2G : c * (b * a * b) * c ∈ G := G.mul_mem (G.mul_mem hcG hb1G) hcG
  have hb2M : IsMonomialIn f (c * (b * a * b) * c) :=
    IsMonomialIn.mul (IsMonomialIn.mul hcM hb1M) hcM
  have hb3G : r * (c * (b * a * b) * c) * r ∈ G := G.mul_mem (G.mul_mem hr hb2G) hr
  have hb3M : IsMonomialIn f (r * (c * (b * a * b) * c) * r) :=
    IsMonomialIn.mul (IsMonomialIn.mul hrM hb2M) hrM
  intro i
  fin_cases i
  · have hne : x ≠ a := fun heq => hxnonmono (heq ▸ haM)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG haG hne hxm hwv
      (zs4h_e0_mat h) (zs4h_pairing_diag 0)
    rwa [zs4h_sum_single w 0, zs4h_sum_single_two v 0] at heta
  · have hne : x ≠ b * a * b := fun heq => hxnonmono (heq ▸ hb1M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hb1G hne hxm hwv
      (zs4h_e1_mat h) (zs4h_pairing_diag 1)
    rwa [zs4h_sum_single w 1, zs4h_sum_single_two v 1] at heta
  · have hne : x ≠ c * (b * a * b) * c := fun heq => hxnonmono (heq ▸ hb2M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hb2G hne hxm hwv
      (zs4h_e2_mat h) (zs4h_pairing_diag 2)
    rwa [zs4h_sum_single w 2, zs4h_sum_single_two v 2] at heta
  · have hne : x ≠ r * (c * (b * a * b) * c) * r := fun heq => hxnonmono (heq ▸ hb3M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hb3G hne hxm hwv
      (zs4h_e3_mat h hrm) (zs4h_pairing_diag 3)
    rwa [zs4h_sum_single w 3, zs4h_sum_single_two v 3] at heta

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_etaOK_p (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) :
    ∀ i, i ≠ 0 → EtaOK 4 (w 0 - w i) (v 0 - v i) := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbG : b ∈ G := h.H_le hbH
  have hcG : c ∈ G := h.H_le hcH
  have hbM : IsMonomialIn f b := hHmono b hbH
  have hcM : IsMonomialIn f c := hHmono c hcH
  have hrM : IsMonomialIn f r := zs4h_monomial_r hrm
  have hp2G : b * c * b ∈ G := G.mul_mem (G.mul_mem hbG hcG) hbG
  have hp2M : IsMonomialIn f (b * c * b) := IsMonomialIn.mul (IsMonomialIn.mul hbM hcM) hbM
  have hp3G : r * (b * c * b) * r ∈ G := G.mul_mem (G.mul_mem hr hp2G) hr
  have hp3M : IsMonomialIn f (r * (b * c * b) * r) :=
    IsMonomialIn.mul (IsMonomialIn.mul hrM hp2M) hrM
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · have hne : x ≠ b := fun heq => hxnonmono (heq ▸ hbM)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hbG hne hxm hwv
      (zs4h_p1_mat h) (zs4h_pairing_sub 0 1 (by decide))
    rwa [zs4h_sum_sub w 0 1, zs4h_sum_sub' v 0 1] at heta
  · have hne : x ≠ b * c * b := fun heq => hxnonmono (heq ▸ hp2M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hp2G hne hxm hwv
      (zs4h_p2_mat h) (zs4h_pairing_sub 0 2 (by decide))
    rwa [zs4h_sum_sub w 0 2, zs4h_sum_sub' v 0 2] at heta
  · have hne : x ≠ r * (b * c * b) * r := fun heq => hxnonmono (heq ▸ hp3M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hp3G hne hxm hwv
      (zs4h_p3_mat h hrm) (zs4h_pairing_sub 0 3 (by decide))
    rwa [zs4h_sum_sub w 0 3, zs4h_sum_sub' v 0 3] at heta

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_etaOK_pm (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) :
    ∀ i, i ≠ 0 → EtaOK 4 (w 0 + w i) (v 0 + v i) := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have haG : a ∈ G := h.H_le haH
  have hbG : b ∈ G := h.H_le hbH
  have hcG : c ∈ G := h.H_le hcH
  have haM : IsMonomialIn f a := hHmono a haH
  have hbM : IsMonomialIn f b := hHmono b hbH
  have hcM : IsMonomialIn f c := hHmono c hcH
  have hrM : IsMonomialIn f r := zs4h_monomial_r hrm
  have hq1G : a * b * a ∈ G := G.mul_mem (G.mul_mem haG hbG) haG
  have hq1M : IsMonomialIn f (a * b * a) := IsMonomialIn.mul (IsMonomialIn.mul haM hbM) haM
  have hq2G : c * (a * b * a) * c ∈ G := G.mul_mem (G.mul_mem hcG hq1G) hcG
  have hq2M : IsMonomialIn f (c * (a * b * a) * c) :=
    IsMonomialIn.mul (IsMonomialIn.mul hcM hq1M) hcM
  have hq3G : r * (c * (a * b * a) * c) * r ∈ G := G.mul_mem (G.mul_mem hr hq2G) hr
  have hq3M : IsMonomialIn f (r * (c * (a * b * a) * c) * r) :=
    IsMonomialIn.mul (IsMonomialIn.mul hrM hq2M) hrM
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · have hne : x ≠ a * b * a := fun heq => hxnonmono (heq ▸ hq1M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hq1G hne hxm hwv
      (zs4h_q1_mat h) (zs4h_pairing_add 0 1 (by decide))
    rwa [zs4h_sum_add w 0 1, zs4h_sum_add' v 0 1] at heta
  · have hne : x ≠ c * (a * b * a) * c := fun heq => hxnonmono (heq ▸ hq2M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hq2G hne hxm hwv
      (zs4h_q2_mat h) (zs4h_pairing_add 0 2 (by decide))
    rwa [zs4h_sum_add w 0 2, zs4h_sum_add' v 0 2] at heta
  · have hne : x ≠ r * (c * (a * b * a) * c) * r := fun heq => hxnonmono (heq ▸ hq3M)
    have heta := FFourCoord.etaOK_four_of_toMatrix hp h.dmax f hxG hq3G hne hxm hwv
      (zs4h_q3_mat h hrm) (zs4h_pairing_add 0 3 (by decide))
    rwa [zs4h_sum_add w 0 3, zs4h_sum_add' v 0 3] at heta

private lemma zs4h_bond_zero_of_d_ne {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {w0 wi v0 vi : ZMod p} (hv0 : v0 ≠ 0) (hvi : vi ≠ 0)
    (h0 : 2 * (w0 * v0) = 1) (hi : 2 * (wi * vi) = 2) :
    (w0 - wi) * (v0 - vi) = 0 := by
  subst hp3
  revert hv0 hvi h0 hi
  decide +revert

private lemma zs4h_bond_zero_of_d_ne' {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {w0 wi v0 vi : ZMod p} (hv0 : v0 ≠ 0) (hvi : vi ≠ 0)
    (h0 : 2 * (w0 * v0) = 2) (hi : 2 * (wi * vi) = 1) :
    (w0 - wi) * (v0 - vi) = 0 := by
  subst hp3
  revert hv0 hvi h0 hi
  decide +revert

private lemma zs4h_two_ne_one : (2 : ZMod p) ≠ 1 := by
  intro h
  have h1 : (1 : ZMod p) = 0 := by
    have h2 : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h
    rw [show (2 : ZMod p) - 1 = 1 by ring] at h2
    exact h2
  exact one_ne_zero h1

private lemma zs4h_d_card_cast_zero {v w : Fin 4 → ZMod p}
    (hD : ∀ i, 2 * (w i * v i) = 1 ∨ 2 * (w i * v i) = 2)
    (hsum : ∑ i, 2 * (w i * v i) = 4) :
    (((Finset.univ.filter (fun i : Fin 4 => 2 * (w i * v i) = 2)).card : ℕ) : ZMod p) = 0 := by
  let S := Finset.univ.filter (fun i : Fin 4 => 2 * (w i * v i) = 2)
  change ((S.card : ℕ) : ZMod p) = 0
  have h1 : (∑ i, (2 * (w i * v i) - 1)) = (S.card : ZMod p) := by
    have hcongr : (∑ i, (2 * (w i * v i) - 1)) =
        ∑ i, (if 2 * (w i * v i) = 2 then (1 : ZMod p) else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : 2 * (w i * v i) = 2
      · rw [if_pos hi, hi]; ring
      · have h1' : 2 * (w i * v i) = 1 := (hD i).resolve_right hi
        rw [if_neg hi, h1']; ring
    rw [hcongr, ← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (∑ i, (2 * (w i * v i) - 1)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← h1, h2]

private lemma zs4h_d_card_three (hp : p ≠ 2) {v w : Fin 4 → ZMod p}
    (hD : ∀ i, 2 * (w i * v i) = 1 ∨ 2 * (w i * v i) = 2)
    (hsum : ∑ i, 2 * (w i * v i) = 4) (hcon : ∃ i, 2 * (w i * v i) ≠ 1) :
    p = 3 ∧ (Finset.univ.filter (fun i : Fin 4 => 2 * (w i * v i) = 2)).card = 3 := by
  let S := Finset.univ.filter (fun i : Fin 4 => 2 * (w i * v i) = 2)
  have hScard : ((S.card : ℕ) : ZMod p) = 0 := by
    have := zs4h_d_card_cast_zero hD hsum
    simpa only [S] using this
  obtain ⟨i0, hi0⟩ := hcon
  have hSle : S.card ≤ 4 := by
    calc S.card ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 4 := by simp
  have hSpos : 0 < S.card := by
    refine Finset.card_pos.mpr ⟨i0, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hD i0).resolve_left hi0
  have hdvd : p ∣ S.card := (ZMod.natCast_eq_zero_iff S.card p).mp hScard
  have hp3 : p = 3 := by
    have hpprime : p.Prime := Fact.out
    have hple : p ≤ S.card := Nat.le_of_dvd hSpos hdvd
    have hp_le : p ≤ 4 := le_trans hple hSle
    have hp2le : 2 ≤ p := hpprime.two_le
    have hcases : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases hcases with h2 | h3 | h4
    · exact absurd h2 hp
    · exact h3
    · exact absurd (h4 ▸ hpprime) (by norm_num)
  have hScard3 : S.card = 3 := by
    have h3 : 3 ∣ S.card := by rwa [hp3] at hdvd
    obtain ⟨k, hk⟩ := h3
    omega
  exact ⟨hp3, by simpa only [S] using hScard3⟩

private lemma zs4h_d_pair_of_card_three {v w : Fin 4 → ZMod p}
    (hD : ∀ i, 2 * (w i * v i) = 1 ∨ 2 * (w i * v i) = 2)
    (hScard3 : (Finset.univ.filter (fun i : Fin 4 => 2 * (w i * v i) = 2)).card = 3) :
    ∃ i, i ≠ 0 ∧ 2 * (w 0 * v 0) ≠ 2 * (w i * v i) := by
  let S := Finset.univ.filter (fun i : Fin 4 => 2 * (w i * v i) = 2)
  have hScard3' : S.card = 3 := by simpa only [S] using hScard3
  have hSpos : 0 < S.card := by omega
  by_cases h0 : 2 * (w 0 * v 0) = 2
  · have hcard : (Finset.univ \ S).card = 1 := by
      rw [Finset.card_sdiff]
      simp [hScard3']
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hjnot : j ∉ S := by
      have : j ∈ Finset.univ \ S := by rw [hj]; simp
      exact (Finset.mem_sdiff.mp this).2
    have h0S : (0 : Fin 4) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact h0
    refine ⟨j, ?_, ?_⟩
    · intro hj0
      exact hjnot (hj0 ▸ h0S)
    · have hDj : 2 * (w j * v j) = 1 := (hD j).resolve_right (fun hh => hjnot (by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hh))
      rw [h0, hDj]; exact zs4h_two_ne_one
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp hSpos
    have hiS : 2 * (w i * v i) = 2 := (Finset.mem_filter.mp hi).2
    refine ⟨i, ?_, ?_⟩
    · intro hi0
      exact h0 (by rw [← hi0]; exact hiS)
    · rw [hiS]; exact h0

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_d_contra (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hv : ∀ i, v i ≠ 0)
    (hD : ∀ i, 2 * (w i * v i) = 1 ∨ 2 * (w i * v i) = 2)
    (hsum : ∑ i, 2 * (w i * v i) = 4) (hcon : ∃ i, 2 * (w i * v i) ≠ 1) : False := by
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨hp3, hScard3⟩ := zs4h_d_card_three hp hD hsum hcon
  obtain ⟨i, hi, hne⟩ := zs4h_d_pair_of_card_three hD hScard3
  have hbond : (w 0 - w i) * (v 0 - v i) = 0 := by
    rcases (hD 0) with h0 | h0 <;> rcases (hD i) with hi' | hi'
    · exact absurd (h0.trans hi'.symm) hne
    · exact zs4h_bond_zero_of_d_ne hp3 (hv 0) (hv i) h0 hi'
    · exact zs4h_bond_zero_of_d_ne' hp3 (hv 0) (hv i) h0 hi'
    · exact absurd (h0.trans hi'.symm) hne
  have heta_i := zs4h_etaOK_p hp h hr hrm hxG hxm hwv hxnonmono hHmono i hi
  have hst : w 0 - w i = 0 ∧ v 0 - v i = 0 := by
    rcases heta_i with ⟨hs, ht⟩ | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨h54, -⟩
    · exact ⟨hs, ht⟩
    · rw [hbond] at h1; exact absurd h1.symm one_ne_zero
    · rw [hbond] at h2; exact absurd h2.symm htwo
    · omega
  exact hne (by rw [sub_eq_zero.mp hst.1, sub_eq_zero.mp hst.2])

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_d_eq_one (hp : p ≠ 2) (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U}
    (hr : r ∈ G) (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hv : ∀ i, v i ≠ 0) :
    ∀ i, 2 * (w i * v i) = 1 := by
  have heta := zs4h_etaOK_diag hp h hr hrm hxG hxm hwv hxnonmono hHmono
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hD : ∀ i, 2 * (w i * v i) = 1 ∨ 2 * (w i * v i) = 2 := by
    intro i
    have ht : 2 * v i ≠ 0 := mul_ne_zero htwo (hv i)
    rcases FFourCoord.mul_eq_one_or_two_of_etaOK_four (heta i) ht with hh | hh
    · left; linear_combination hh
    · right; linear_combination hh
  have hsum : ∑ i, 2 * (w i * v i) = 4 := by
    rw [show (∑ i, 2 * (w i * v i)) = 2 * ∑ i, w i * v i by rw [Finset.mul_sum]]
    rw [hwv]; norm_num
  by_contra hcon
  push Not at hcon
  exact zs4h_d_contra hp h hr hrm hxG hxm hwv hxnonmono hHmono hv hD hsum hcon

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_sum_single_smul (i : Fin 4) :
    (∑ l, (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l • f l) = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hli; simp [hli]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_sum_sub_smul (i : Fin 4) :
    (∑ l, ((Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) -
      (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p)) l • f l) = f 0 - f i := by
  rw [show (∑ l, ((Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) -
      (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p)) l • f l) =
      (∑ l, (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) l • f l) -
        (∑ l, (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p) l • f l) by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun l _ => by simp [Pi.sub_apply, sub_smul])]
  rw [zs4h_sum_single_smul 0, zs4h_sum_single_smul i]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_movedSpace_le_span_of_vec {y : U ≃ₗ[ZMod p] U} {ρ κ : Fin 4 → ZMod p}
    (hy : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) :
    HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) {∑ l, ρ l • f l} := by
  obtain ⟨hφ, hyeq⟩ := FFourCoord.eq_reflection_of_toMatrix f hy hκρ
  rintro w ⟨z, rfl⟩
  have hz : ((Module.reflection hφ : U →ₗ[ZMod p] U) - 1) z = Module.reflection hφ z - z := by
    simp
  rw [hyeq, hz, Module.reflection_apply]
  rw [show z - ((∑ i, κ i • f.coord i) z) • (∑ l, ρ l • f l) - z =
      (-((∑ i, κ i • f.coord i) z)) • (∑ l, ρ l • f l) by rw [neg_smul]; abel]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_sum_smul_not_mem_span {v : Fin 4 → ZMod p} (hv : ∀ l, v l ≠ 0)
    {i : Fin 4} {j : Fin 4} (hj0 : j ≠ 0) (hji : j ≠ i) :
    (∑ l, v l • f l) ∉ Submodule.span (ZMod p) ({f 0, f i} : Set U) := by
  intro hmem
  have hker : Submodule.span (ZMod p) ({f 0, f i} : Set U) ≤ LinearMap.ker (f.coord j) := by
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, LinearMap.mem_ker, zs4k_coord_apply_basis, if_neg hj0]
    · rw [SetLike.mem_coe, LinearMap.mem_ker, zs4k_coord_apply_basis, if_neg hji]
  have h0 : f.coord j (∑ l, v l • f l) = 0 := hker hmem
  rw [zs4k_coord_apply_sum] at h0
  exact hv j h0

private lemma zs4h_inf_sup_two_moved {W : Submodule (ZMod p) U} {x y g : U ≃ₗ[ZMod p] U}
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ W)
    (hyV : HardMathSupport.Kantor79.movedSpace y ≤ W) (hg : IsRefl p g)
    (hgnot : ¬ HardMathSupport.Kantor79.movedSpace g ≤ W) :
    (HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y) ⊓
      HardMathSupport.Kantor79.movedSpace g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_contra hz0
  have hzg : z ∈ HardMathSupport.Kantor79.movedSpace g := hz.2
  have hzP : z ∈ HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y :=
    hz.1
  have hg1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace g) = 1 := hg.2
  have heq : Submodule.span (ZMod p) {z} = HardMathSupport.Kantor79.movedSpace g :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzg))
      (by rw [finrank_span_singleton hz0, hg1])
  have hle : HardMathSupport.Kantor79.movedSpace g ≤
      HardMathSupport.Kantor79.movedSpace x ⊔ HardMathSupport.Kantor79.movedSpace y := by
    rw [← heq]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hzP)
  exact hgnot (hle.trans (sup_le hxV hyV))

private lemma zs4h_finrank_three {W : Submodule (ZMod p) U} {π ε x : U ≃ₗ[ZMod p] U}
    (hπ : IsRefl p π) (hε : IsRefl p ε) (hx : IsRefl p x)
    (hπV : HardMathSupport.Kantor79.movedSpace π ≤ W)
    (hεV : HardMathSupport.Kantor79.movedSpace ε ≤ W)
    (hπε : HardMathSupport.Kantor79.movedSpace π ≠ HardMathSupport.Kantor79.movedSpace ε)
    (hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤ W) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({π, ε, x} : Set (U ≃ₗ[ZMod p] U)))) = 3 := by
  rw [zs4k_commutatorSpace_closure_three_eq]
  have h2 := zs4k_finrank_sup_two hπ hε hπε
  have hinf := zs4h_inf_sup_two_moved hπV hεV hx hxnot
  have hx1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace x) = 1 := hx.2
  have hfs := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.movedSpace π ⊔ HardMathSupport.Kantor79.movedSpace ε)
    (HardMathSupport.Kantor79.movedSpace x)
  rw [h2, hx1, hinf, finrank_bot, add_zero] at hfs
  omega

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_orderOf_mul_eq_three {x y : U ≃ₗ[ZMod p] U}
    (hy : IsRefl p y) (hne : x ≠ y) (h3 : (x * y) ^ 3 = 1) :
    orderOf (x * y) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne1 : x * y ≠ 1 := by
    intro h1
    exact hne (by rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hy.1])
  exact orderOf_eq_prime h3 hne1

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_orderOf_mul_eq_three_of_toMatrix (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {x y : U ≃ₗ[ZMod p] U} {v w ρ κ : Fin n → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hym : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (hne : x ≠ y)
    (h : (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 1) : orderOf (x * y) = 3 := by
  obtain ⟨hxr, rfl⟩ := FFourCoord.eq_reflection_of_toMatrix f hxm hwv
  obtain ⟨hyr, rfl⟩ := FFourCoord.eq_reflection_of_toMatrix f hym hκρ
  have hφψ : (∑ i, w i • f.coord i) (∑ i, ρ i • f i) *
      (∑ i, κ i • f.coord i) (∑ i, v i • f i) = 1 := by
    rwa [FFourCoord.sum_smul_coord_apply_sum f w ρ, FFourCoord.sum_smul_coord_apply_sum f κ v]
  have hxr' : IsRefl p (Module.reflection hxr) := FFourCoord.isRefl_of_toMatrix hp f hxm hwv
  have hyr' : IsRefl p (Module.reflection hyr) := FFourCoord.isRefl_of_toMatrix hp f hym hκρ
  exact zs4h_orderOf_mul_eq_three hyr' hne
    (reflection_mul_reflection_pow_three hxr hyr hφψ)

private lemma zs4h_false_of_bond_one (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {W : Submodule (ZMod p) U} {π ε x : U ≃ₗ[ZMod p] U}
    (hπG : π ∈ G) (hεG : ε ∈ G) (hxG : x ∈ G)
    (hπ : IsRefl p π) (hε : IsRefl p ε) (hxr : IsRefl p x)
    (hπV : HardMathSupport.Kantor79.movedSpace π ≤ W)
    (hεV : HardMathSupport.Kantor79.movedSpace ε ≤ W)
    (hπε : HardMathSupport.Kantor79.movedSpace π ≠ HardMathSupport.Kantor79.movedSpace ε)
    (hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤ W)
    (hπε4 : orderOf (π * ε) = 4) (hπx3 : orderOf (π * x) = 3) (hεx3 : orderOf (ε * x) = 3) :
    False := by
  have hU : Module.finrank (ZMod p) U = 4 := by simpa using Module.finrank_eq_card_basis f
  have hXG : Subgroup.closure ({π, ε, x} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact hπG
    · exact hεG
    · exact hxG
  have hAt : QTwoLin.TransvectionFree (Subgroup.closure ({π, ε, x} : Set (U ≃ₗ[ZMod p] U))) :=
    fun y hy => h.transvectionFree y (hXG hy)
  have hdim := zs4h_finrank_three hπ hε hxr hπV hεV hπε hxnot
  have hD : DMax p (Subgroup.closure ({π, ε, x} : Set (U ≃ₗ[ZMod p] U))) 4 :=
    ⟨fun y hy z hz hyr hzr => h.dmax.1 y (hXG hy) z (hXG hz) hyr hzr,
      π, Subgroup.subset_closure (by simp), ε, Subgroup.subset_closure (by simp), hπ, hε, hπε4⟩
  obtain ⟨hSplit, hgt⟩ := zs4k_card_of_433 hp hU hπ hε hxr rfl hAt hdim hD hπε4 hπx3 hεx3
  have hcard := h.maximal _ hXG (zs4k_reflGen_closure_three hπ hε hxr) hSplit hD
  omega

private lemma zs4h_three_ne_two : (3 : ZMod p) ≠ 2 := by
  intro h
  have h1 : (1 : ZMod p) = 0 := by
    have h3 : (3 : ZMod p) - 2 = 0 := sub_eq_zero.mpr h
    rwa [show (3 : ZMod p) - 2 = 1 by ring] at h3
  exact one_ne_zero h1

private lemma zs4h_four_ne_two (hp : p ≠ 2) : (4 : ZMod p) ≠ 2 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have h3 : (4 : ZMod p) - 2 = 0 := sub_eq_zero.mpr h
    rwa [show (4 : ZMod p) - 2 = 2 by ring] at h3
  exact (ZMod.prime_ne_zero p 2 hp) h2

private lemma zs4h_sign_bounds {v w : Fin 4 → ZMod p} {i : Fin 4}
    (hd : ∀ i, 2 * (w i * v i) = 1)
    (heta : EtaOK 4 (w 0 - w i) (v 0 - v i)) (hetam : EtaOK 4 (w 0 + w i) (v 0 + v i)) :
    ((w 0 - w i) * (v 0 - v i) = 0 ∨ (w 0 - w i) * (v 0 - v i) = 1 ∨
        (w 0 - w i) * (v 0 - v i) = 2) ∧
      ((w 0 + w i) * (v 0 + v i) = 0 ∨ (w 0 + w i) * (v 0 + v i) = 1 ∨
        (w 0 + w i) * (v 0 + v i) = 2) ∧
      (w 0 - w i) * (v 0 - v i) + (w 0 + w i) * (v 0 + v i) = 2 := by
  have hbm : (w 0 - w i) * (v 0 - v i) = 0 ∨ (w 0 - w i) * (v 0 - v i) = 1 ∨
      (w 0 - w i) * (v 0 - v i) = 2 := by
    rcases heta with ⟨hs, ht⟩ | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨h54, -⟩
    · left; rw [hs, ht]; ring
    · right; left; exact h1
    · right; right; exact h2
    · omega
  have hbp : (w 0 + w i) * (v 0 + v i) = 0 ∨ (w 0 + w i) * (v 0 + v i) = 1 ∨
      (w 0 + w i) * (v 0 + v i) = 2 := by
    rcases hetam with ⟨hs, ht⟩ | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨h54, -⟩
    · left; rw [hs, ht]; ring
    · right; left; exact h1
    · right; right; exact h2
    · omega
  have hsum : (w 0 - w i) * (v 0 - v i) + (w 0 + w i) * (v 0 + v i) = 2 := by
    have h0 := hd 0
    have h1 := hd i
    linear_combination h0 + h1
  exact ⟨hbm, hbp, hsum⟩

private lemma zs4h_sign_core (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {W : Submodule (ZMod p) U} {π x : U ≃ₗ[ZMod p] U} {v w : Fin 4 → ZMod p}
    (hπG : π ∈ G) (hεG : a ∈ G) (hxG : x ∈ G)
    (hπ : IsRefl p π) (hε : IsRefl p a) (hxr : IsRefl p x)
    (hπV : HardMathSupport.Kantor79.movedSpace π ≤ W)
    (hεV : HardMathSupport.Kantor79.movedSpace a ≤ W)
    (hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤ W)
    (hπε : HardMathSupport.Kantor79.movedSpace π ≠ HardMathSupport.Kantor79.movedSpace a)
    (hπε4 : orderOf (π * a) = 4)
    (i : Fin 4) (hd : ∀ i, 2 * (w i * v i) = 1)
    (heta : EtaOK 4 (w 0 - w i) (v 0 - v i)) (hetam : EtaOK 4 (w 0 + w i) (v 0 + v i))
    (hπx3 : (w 0 - w i) * (v 0 - v i) = 1 → orderOf (π * x) = 3)
    (hεx3 : (w 0 + w i) * (v 0 + v i) = 1 → orderOf (a * x) = 3) :
    v i = v 0 ∨ v i = - v 0 := by
  obtain ⟨hbm, hbp, hsum⟩ := zs4h_sign_bounds hd heta hetam
  rcases hbm with hbm0 | hbm1 | hbm2
  · left
    rcases heta with ⟨hs, ht⟩ | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨h54, -⟩
    · exact (sub_eq_zero.mp ht).symm
    · rw [hbm0] at h1; exact absurd h1.symm one_ne_zero
    · rw [hbm0] at h2; exact absurd h2.symm (ZMod.prime_ne_zero p 2 hp)
    · omega
  · rcases hbp with hbp0 | hbp1 | hbp2
    · rw [hbm1, hbp0] at hsum
      exact absurd (show (1 : ZMod p) = 2 by linear_combination hsum) (Ne.symm zs4h_two_ne_one)
    · exact (zs4h_false_of_bond_one hp h hπG hεG hxG hπ hε hxr hπV hεV hπε hxnot hπε4
        (hπx3 hbm1) (hεx3 hbp1)).elim
    · rw [hbm1, hbp2] at hsum
      exact absurd (show (3 : ZMod p) = 2 by linear_combination hsum) zs4h_three_ne_two
  · right
    rcases hbp with hbp0 | hbp1 | hbp2
    · rcases hetam with ⟨hs, ht⟩ | ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨h54, -⟩
      · exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact ht)
      · rw [hbp0] at h1; exact absurd h1.symm one_ne_zero
      · rw [hbp0] at h2; exact absurd h2.symm (ZMod.prime_ne_zero p 2 hp)
      · omega
    · rw [hbm2, hbp1] at hsum
      exact absurd (show (3 : ZMod p) = 2 by linear_combination hsum) zs4h_three_ne_two
    · rw [hbm2, hbp2] at hsum
      exact absurd (show (4 : ZMod p) = 2 by linear_combination hsum) (zs4h_four_ne_two hp)

private lemma zs4h_sign_case (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {W : Submodule (ZMod p) U} {π x : U ≃ₗ[ZMod p] U} {ρ κ : Fin 4 → ZMod p}
    {v w : Fin 4 → ZMod p}
    (hπm : LinearMap.toMatrix f f π.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ l, κ l * ρ l = 2)
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ l, w l * v l = 2)
    (hπG : π ∈ G) (hxG : x ∈ G) (hneπx : π ≠ x) (hneεx : a ≠ x)
    (hπ : IsRefl p π) (hxr : IsRefl p x)
    (hπV : HardMathSupport.Kantor79.movedSpace π ≤ W)
    (hεV : HardMathSupport.Kantor79.movedSpace a ≤ W)
    (hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤ W)
    (hπε : HardMathSupport.Kantor79.movedSpace π ≠ HardMathSupport.Kantor79.movedSpace a)
    (hπε4 : orderOf (π * a) = 4)
    (i : Fin 4) (hd : ∀ i, 2 * (w i * v i) = 1)
    (hs : ∑ l, w l * ρ l = w 0 - w i) (ht : ∑ l, κ l * v l = v 0 - v i)
    (heta : EtaOK 4 (w 0 - w i) (v 0 - v i)) (hetam : EtaOK 4 (w 0 + w i) (v 0 + v i)) :
    v i = v 0 ∨ v i = - v 0 := by
  have hε : IsRefl p a := FFourCoord.isRefl_of_toMatrix hp f (zs4h_e0_mat h) (zs4h_pairing_diag 0)
  have hεG : a ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  refine zs4h_sign_core hp h hπG hεG hxG hπ hε hxr hπV hεV hxnot hπε hπε4 i hd
    heta hetam ?_ ?_
  · intro hb1
    refine zs4h_orderOf_mul_eq_three_of_toMatrix (hp := hp) (f := f) (x := π) (y := x)
      (v := ρ) (w := κ) (ρ := v) (κ := w) hπm hκρ hxm hwv hneπx ?_
    rw [ht, hs, mul_comm]
    exact hb1
  · intro hb2
    refine zs4h_orderOf_mul_eq_three_of_toMatrix (hp := hp) (f := f) (x := a) (y := x)
      (v := Pi.single 0 1) (w := Pi.single 0 2) (ρ := v) (κ := w) (zs4h_e0_mat h)
      (zs4h_pairing_diag 0) hxm hwv hneεx ?_
    rw [zs4h_sum_single_two v 0, zs4h_sum_single w 0]
    linear_combination hd 0

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_not_moved_le_span {x : U ≃ₗ[ZMod p] U} {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ l, w l * v l = 2) (hxr : IsRefl p x) (hv : ∀ l, v l ≠ 0)
    {i : Fin 4} {j : Fin 4} (hj0 : j ≠ 0) (hji : j ≠ i) :
    ¬ HardMathSupport.Kantor79.movedSpace x ≤ Submodule.span (ZMod p) ({f 0, f i} : Set U) := by
  have haxne : (∑ l, v l • f l) ≠ 0 := by
    intro h0
    exact hv 0 ((Fintype.linearIndependent_iff.mp f.linearIndependent) v h0 0)
  have hspan : HardMathSupport.Kantor79.movedSpace x =
      Submodule.span (ZMod p) {∑ l, v l • f l} :=
    Submodule.eq_of_le_of_finrank_eq (zs4h_movedSpace_le_span_of_vec hxm hwv)
      (by rw [finrank_span_singleton haxne]; exact hxr.2)
  intro hle
  exact zs4h_sum_smul_not_mem_span hv hj0 hji
    (hle (by rw [hspan]; exact Submodule.mem_span_singleton_self _))

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_ne_a_of_vec (h : FFourData f a b c g H G) {π : U ≃ₗ[ZMod p] U}
    {ρ κ : Fin 4 → ZMod p} (hπm : LinearMap.toMatrix f f π.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hρ0 : ρ 0 = 1) (hκ0 : κ 0 = 1) : π ≠ a := by
  intro heq
  have hm := congrArg (fun z : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f z.toLinearMap) heq
  rw [hπm, h.toMatrix_a] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h0 : (0 : ZMod p) = -1 := by
    simp [Matrix.sub_apply, Matrix.vecMulVec_apply, hρ0, hκ0, diagSignMat] at h00
  exact one_ne_zero (neg_eq_zero.mp h0.symm)

private lemma zs4h_moved_ne_a (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {π : U ≃ₗ[ZMod p] U} (hπG : π ∈ G) (hπ : IsRefl p π) (hπa : π ≠ a) :
    HardMathSupport.Kantor79.movedSpace π ≠ HardMathSupport.Kantor79.movedSpace a := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hε : IsRefl p a := FFourCoord.isRefl_of_toMatrix hp f (zs4h_e0_mat h) (zs4h_pairing_diag 0)
  exact fun heq => hπa (eq_of_movedSpace_eq hp h.transvectionFree hπG (h.H_le haH) hπ hε heq)

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_span_sub_le (i : Fin 4) :
    Submodule.span (ZMod p)
        {∑ l, ((Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) -
          (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p)) l • f l} ≤
      Submodule.span (ZMod p) ({f 0, f i} : Set U) := by
  rw [zs4h_sum_sub_smul i]
  refine Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
  exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

private lemma zs4h_bond_pi_a (i : Fin 4) (hi : i ≠ 0) :
    (∑ l, ((Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) -
        (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p)) l *
        (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) l) *
      (∑ l, (Pi.single 0 (2 : ZMod p) : Fin 4 → ZMod p) l *
        ((Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) -
          (Pi.single i (1 : ZMod p) : Fin 4 → ZMod p)) l) = 2 := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases i <;> simp_all

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_moved_a_le_span (h : FFourData f a b c g H G) (i : Fin 4) :
    HardMathSupport.Kantor79.movedSpace a ≤
      Submodule.span (ZMod p) ({f 0, f i} : Set U) := by
  refine (zs4h_movedSpace_le_span_of_vec (zs4h_e0_mat h) (zs4h_pairing_diag 0)).trans ?_
  rw [zs4h_sum_single_smul 0]
  refine Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
  exact Submodule.subset_span (by simp)

private lemma zs4h_sign_one (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) (hxrefl : IsRefl p x) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i, 2 * (w i * v i) = 1) :
    v 1 = v 0 ∨ v 1 = - v 0 := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbG : b ∈ G := h.H_le hbH
  have hεM : IsMonomialIn f a := hHmono a haH
  have hxneε : a ≠ x := fun heq => hxnonmono (by rw [← heq]; exact hεM)
  have hπ : IsRefl p b :=
    FFourCoord.isRefl_of_toMatrix hp f (zs4h_p1_mat h) (zs4h_pairing_sub 0 1 (by decide))
  have hπV : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({f 0, f 1} : Set U) :=
    (zs4h_movedSpace_le_span_of_vec (zs4h_p1_mat h) (zs4h_pairing_sub 0 1 (by decide))).trans
      (zs4h_span_sub_le 1)
  have hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) ({f 0, f 1} : Set U) :=
    zs4h_not_moved_le_span (i := 1) (j := 2) hxm hwv hxrefl hv
      (by decide) (by decide)
  have hπε : HardMathSupport.Kantor79.movedSpace b ≠
      HardMathSupport.Kantor79.movedSpace a :=
    zs4h_moved_ne_a hp h hbG hπ
      (zs4h_ne_a_of_vec (h := h)
        (ρ := (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) - Pi.single 1 1)
        (κ := (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) - Pi.single 1 1)
        (zs4h_p1_mat h) (by simp) (by simp))
  have hπε4 : orderOf (b * a) = 4 :=
    FFourCoord.orderOf_mul_eq_four_of_toMatrix hp f (zs4h_p1_mat h)
      (zs4h_pairing_sub 0 1 (by decide)) (zs4h_e0_mat h) (zs4h_pairing_diag 0)
      (zs4h_bond_pi_a 1 (by decide))
  exact zs4h_sign_case hp h (zs4h_p1_mat h) (zs4h_pairing_sub 0 1 (by decide)) hxm hwv
    hbG hxG (fun heq => hxnonmono (by rw [← heq]; exact hHmono b hbH)) hxneε hπ hxrefl
    hπV (zs4h_moved_a_le_span h 1) hxnot hπε hπε4 1 hd
    (zs4h_sum_sub w 0 1) (zs4h_sum_sub' v 0 1)
    (zs4h_etaOK_p hp h hr hrm hxG hxm hwv hxnonmono hHmono 1 (by decide))
    (zs4h_etaOK_pm hp h hr hrm hxG hxm hwv hxnonmono hHmono 1 (by decide))

private lemma zs4h_swap_two (hp : p ≠ 2) (h : FFourData f a b c g H G) :
    IsRefl p (b * c * b) ∧
      HardMathSupport.Kantor79.movedSpace (b * c * b) ≤
        Submodule.span (ZMod p) ({f 0, f 2} : Set U) ∧
      HardMathSupport.Kantor79.movedSpace (b * c * b) ≠
        HardMathSupport.Kantor79.movedSpace a ∧
      orderOf ((b * c * b) * a) = 4 := by
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbG : b ∈ G := h.H_le hbH
  have hcG : c ∈ G := h.H_le hcH
  have hbcbG : b * c * b ∈ G := G.mul_mem (G.mul_mem hbG hcG) hbG
  have hπ : IsRefl p (b * c * b) :=
    FFourCoord.isRefl_of_toMatrix hp f (zs4h_p2_mat h) (zs4h_pairing_sub 0 2 (by decide))
  have hπV : HardMathSupport.Kantor79.movedSpace (b * c * b) ≤
      Submodule.span (ZMod p) ({f 0, f 2} : Set U) :=
    (zs4h_movedSpace_le_span_of_vec (zs4h_p2_mat h) (zs4h_pairing_sub 0 2 (by decide))).trans
      (zs4h_span_sub_le 2)
  have hπε : HardMathSupport.Kantor79.movedSpace (b * c * b) ≠
      HardMathSupport.Kantor79.movedSpace a :=
    zs4h_moved_ne_a hp h hbcbG hπ
      (zs4h_ne_a_of_vec (h := h)
        (ρ := (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) - Pi.single 2 1)
        (κ := (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) - Pi.single 2 1)
        (zs4h_p2_mat h) (by simp) (by simp))
  have hπε4 : orderOf ((b * c * b) * a) = 4 :=
    FFourCoord.orderOf_mul_eq_four_of_toMatrix hp f (zs4h_p2_mat h)
      (zs4h_pairing_sub 0 2 (by decide)) (zs4h_e0_mat h) (zs4h_pairing_diag 0)
      (zs4h_bond_pi_a 2 (by decide))
  exact ⟨hπ, hπV, hπε, hπε4⟩

private lemma zs4h_sign_two (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) (hxrefl : IsRefl p x) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i, 2 * (w i * v i) = 1) :
    v 2 = v 0 ∨ v 2 = - v 0 := by
  obtain ⟨hπ, hπV, hπε, hπε4⟩ := zs4h_swap_two hp h
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbG : b ∈ G := h.H_le hbH
  have hcG : c ∈ G := h.H_le hcH
  have hεM : IsMonomialIn f a := hHmono a haH
  have hbM : IsMonomialIn f b := hHmono b hbH
  have hcM : IsMonomialIn f c := hHmono c hcH
  have hbcbG : b * c * b ∈ G := G.mul_mem (G.mul_mem hbG hcG) hbG
  have hbcbM : IsMonomialIn f (b * c * b) := IsMonomialIn.mul (IsMonomialIn.mul hbM hcM) hbM
  have hxneε : a ≠ x := fun heq => hxnonmono (by rw [← heq]; exact hεM)
  have hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) ({f 0, f 2} : Set U) :=
    zs4h_not_moved_le_span (i := 2) (j := 1) hxm hwv hxrefl hv
      (by decide) (by decide)
  exact zs4h_sign_case hp h (zs4h_p2_mat h) (zs4h_pairing_sub 0 2 (by decide)) hxm hwv
    hbcbG hxG (fun heq => hxnonmono (by rw [← heq]; exact hbcbM)) hxneε hπ hxrefl
    hπV (zs4h_moved_a_le_span h 2) hxnot hπε hπε4 2 hd
    (zs4h_sum_sub w 0 2) (zs4h_sum_sub' v 0 2)
    (zs4h_etaOK_p hp h hr hrm hxG hxm hwv hxnonmono hHmono 2 (by decide))
    (zs4h_etaOK_pm hp h hr hrm hxG hxm hwv hxnonmono hHmono 2 (by decide))

private lemma zs4h_swap_three (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    IsRefl p (r * (b * c * b) * r) ∧
      HardMathSupport.Kantor79.movedSpace (r * (b * c * b) * r) ≤
        Submodule.span (ZMod p) ({f 0, f 3} : Set U) ∧
      HardMathSupport.Kantor79.movedSpace (r * (b * c * b) * r) ≠
        HardMathSupport.Kantor79.movedSpace a ∧
      orderOf ((r * (b * c * b) * r) * a) = 4 := by
  have hbG : b ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hcG : c ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hbcbG : b * c * b ∈ G := G.mul_mem (G.mul_mem hbG hcG) hbG
  have hq3G : r * (b * c * b) * r ∈ G := G.mul_mem (G.mul_mem hr hbcbG) hr
  have hπ : IsRefl p (r * (b * c * b) * r) :=
    FFourCoord.isRefl_of_toMatrix hp f (zs4h_p3_mat h hrm) (zs4h_pairing_sub 0 3 (by decide))
  have hπV : HardMathSupport.Kantor79.movedSpace (r * (b * c * b) * r) ≤
      Submodule.span (ZMod p) ({f 0, f 3} : Set U) :=
    (zs4h_movedSpace_le_span_of_vec (zs4h_p3_mat h hrm)
      (zs4h_pairing_sub 0 3 (by decide))).trans (zs4h_span_sub_le 3)
  have hπε : HardMathSupport.Kantor79.movedSpace (r * (b * c * b) * r) ≠
      HardMathSupport.Kantor79.movedSpace a :=
    zs4h_moved_ne_a hp h hq3G hπ
      (zs4h_ne_a_of_vec (h := h)
        (ρ := (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) - Pi.single 3 1)
        (κ := (Pi.single 0 (1 : ZMod p) : Fin 4 → ZMod p) - Pi.single 3 1)
        (zs4h_p3_mat h hrm) (by simp) (by simp))
  have hπε4 : orderOf ((r * (b * c * b) * r) * a) = 4 :=
    FFourCoord.orderOf_mul_eq_four_of_toMatrix hp f (zs4h_p3_mat h hrm)
      (zs4h_pairing_sub 0 3 (by decide)) (zs4h_e0_mat h) (zs4h_pairing_diag 0)
      (zs4h_bond_pi_a 3 (by decide))
  exact ⟨hπ, hπV, hπε, hπε4⟩

private lemma zs4h_sign_three (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) (hxrefl : IsRefl p x) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i, 2 * (w i * v i) = 1) :
    v 3 = v 0 ∨ v 3 = - v 0 := by
  obtain ⟨hπ, hπV, hπε, hπε4⟩ := zs4h_swap_three hp h hr hrm
  have hbG : b ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hcG : c ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hbM : IsMonomialIn f b := zs4h_monomial_b h
  have hcM : IsMonomialIn f c := zs4h_monomial_c h
  have hrM : IsMonomialIn f r := zs4h_monomial_r hrm
  have hxneε : a ≠ x := fun heq => hxnonmono (by rw [← heq]; exact zs4h_monomial_a h)
  have hbcbG : b * c * b ∈ G := G.mul_mem (G.mul_mem hbG hcG) hbG
  have hbcbM : IsMonomialIn f (b * c * b) := IsMonomialIn.mul (IsMonomialIn.mul hbM hcM) hbM
  have hq3G : r * (b * c * b) * r ∈ G := G.mul_mem (G.mul_mem hr hbcbG) hr
  have hq3M : IsMonomialIn f (r * (b * c * b) * r) :=
    IsMonomialIn.mul (IsMonomialIn.mul hrM hbcbM) hrM
  have hxnot : ¬ HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) ({f 0, f 3} : Set U) :=
    zs4h_not_moved_le_span (i := 3) (j := 1) hxm hwv hxrefl hv
      (by decide) (by decide)
  exact zs4h_sign_case hp h (zs4h_p3_mat h hrm) (zs4h_pairing_sub 0 3 (by decide)) hxm hwv
    hq3G hxG (fun heq => hxnonmono (by rw [← heq]; exact hq3M)) hxneε hπ hxrefl
    hπV (zs4h_moved_a_le_span h 3) hxnot hπε hπε4 3 hd
    (zs4h_sum_sub w 0 3) (zs4h_sum_sub' v 0 3)
    (zs4h_etaOK_p hp h hr hrm hxG hxm hwv hxnonmono hHmono 3 (by decide))
    (zs4h_etaOK_pm hp h hr hrm hxG hxm hwv hxnonmono hHmono 3 (by decide))

private lemma zs4h_sign_of_pair (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G) (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) (hxrefl : IsRefl p x) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) (hxnonmono : ¬ IsMonomialIn f x)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i, 2 * (w i * v i) = 1) :
    ∀ i, i ≠ 0 → v i = v 0 ∨ v i = - v 0 := by
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · exact zs4h_sign_one hp h hr hrm hxG hxrefl hxm hwv hxnonmono hHmono hv hd
  · exact zs4h_sign_two hp h hr hrm hxG hxrefl hxm hwv hxnonmono hHmono hv hd
  · exact zs4h_sign_three hp h hr hrm hxG hxrefl hxm hwv hxnonmono hHmono hv hd

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_v_ne_zero (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U}
    (hr : r ∈ G) (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G) (hxrefl : IsRefl p x) {v w : Fin 4 → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hHmono : ∀ k ∈ H, IsMonomialIn f k) (hxnonmono : ¬ IsMonomialIn f x) :
    ∀ i, v i ≠ 0 := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbG : b ∈ G := h.H_le hbH
  have hcG : c ∈ G := h.H_le hcH
  have hbMono : IsMonomialIn f b := zs4h_monomial_b h
  have hcMono : IsMonomialIn f c := zs4h_monomial_c h
  have hrMono : IsMonomialIn f r := zs4h_monomial_r hrm
  have hbcbG : b * c * b ∈ G := G.mul_mem (G.mul_mem hbG hcG) hbG
  have hbcbMono : IsMonomialIn f (b * c * b) :=
    IsMonomialIn.mul (IsMonomialIn.mul hbMono hcMono) hbMono
  intro i hi
  fin_cases i
  · have hkG : r * (b * c * b) * r ∈ G := G.mul_mem (G.mul_mem hr hbcbG) hr
    have hkMono : IsMonomialIn f (r * (b * c * b) * r) :=
      IsMonomialIn.mul (IsMonomialIn.mul hrMono hbcbMono) hrMono
    refine hxnonmono (zs4h_mono_of_conj_swap h hxG hxrefl hxm hHmono hkG hkMono
      (zs4h_p3_mat h hrm) (zs4h_pairing_sub 0 3 (by decide)) ?_)
    rw [Fin.sum_univ_four]
    simpa [Pi.sub_apply, Pi.smul_apply, Pi.single_apply] using hi
  · have hrcrG : r * c * r ∈ G := G.mul_mem (G.mul_mem hr hcG) hr
    have hrcrMono : IsMonomialIn f (r * c * r) :=
      IsMonomialIn.mul (IsMonomialIn.mul hrMono hcMono) hrMono
    refine hxnonmono (zs4h_mono_of_conj_swap h hxG hxrefl hxm hHmono hrcrG hrcrMono
      (zs4h_p13_mat h hrm) (zs4h_pairing_sub 1 3 (by decide)) ?_)
    rw [Fin.sum_univ_four]
    simpa [Pi.sub_apply, Pi.smul_apply, Pi.single_apply] using hi
  · refine hxnonmono (zs4h_mono_of_conj_swap h hxG hxrefl hxm hHmono hr hrMono
      (zs4h_r_mat hrm) (zs4h_pairing_sub 2 3 (by decide)) ?_)
    rw [Fin.sum_univ_four]
    simpa [Pi.sub_apply, Pi.smul_apply, Pi.single_apply] using hi
  · have hxVH : HardMathSupport.Kantor79.movedSpace x ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) :=
      FFourCoord.movedSpace_le_span_of_toMatrix f hxm (by simpa using hi)
    exact hxnonmono (hHmono x (h.inH x hxG hxrefl hxVH))

private lemma zs4h_conj_half {σ v w : Fin 4 → ZMod p}
    (hσsq : ∀ i, σ i ^ 2 = 1) (hv : ∀ i, v i = v 0 * σ i)
    (hd : ∀ i, 2 * (w i * v i) = 1) (hv0 : v 0 ≠ 0) (htwo : (2 : ZMod p) ≠ 0) :
    Matrix.diagonal σ * (1 - Matrix.vecMulVec v w) * Matrix.diagonal σ = halfOnesMat 4 := by
  have hσv : ∀ i, σ i * v i = v 0 := by
    intro i
    rw [hv i, ← mul_assoc, mul_comm (σ i) (v 0), mul_assoc, ← pow_two, hσsq i, mul_one]
  have hσw : ∀ j, w j * σ j = (2 * v 0)⁻¹ := by
    intro j
    have h := hd j
    rw [hv j] at h
    exact eq_inv_of_mul_eq_one_right (by rw [← h]; ring)
  have hJ : Matrix.diagonal σ * Matrix.vecMulVec v w * Matrix.diagonal σ =
      (2 : ZMod p)⁻¹ • Matrix.vecMulVec (fun _ : Fin 4 => 1) (fun _ : Fin 4 => 1) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
    calc (σ i * (v i * w j)) * σ j
        = ((σ i * v i) * w j) * σ j := by ring
      _ = (v 0 * w j) * σ j := by rw [hσv i]
      _ = v 0 * (w j * σ j) := by ring
      _ = v 0 * (2 * v 0)⁻¹ := by rw [hσw j]
      _ = (2 : ZMod p)⁻¹ := by field_simp
  have hσdiag : Matrix.diagonal σ * Matrix.diagonal σ = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => σ i * σ i) = (fun _ : Fin 4 => (1 : ZMod p)) by
      funext i; rw [← pow_two, hσsq i]]
    exact Matrix.diagonal_one
  rw [mul_sub, sub_mul, mul_one, hσdiag, hJ, halfOnesMat]
  congr 1
  ext i j
  simp [Matrix.vecMulVec_apply]

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_signMat_eps (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    ∃ d1 ∈ G, ∃ d2 ∈ G, ∃ d3 ∈ G,
      LinearMap.toMatrix f f d1.toLinearMap = diagSignMat 1 ∧
      LinearMap.toMatrix f f d2.toLinearMap = diagSignMat 2 ∧
      LinearMap.toMatrix f f d3.toLinearMap = diagSignMat 3 := by
  have haG : a ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hbG : b ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  have hcG : c ∈ G := h.H_le (by rw [h.H_eq]; exact Subgroup.subset_closure (by simp))
  let d1 : U ≃ₗ[ZMod p] U := b * a * b
  let d2 : U ≃ₗ[ZMod p] U := c * d1 * c
  let d3 : U ≃ₗ[ZMod p] U := r * d2 * r
  have hd1G : d1 ∈ G := G.mul_mem (G.mul_mem hbG haG) hbG
  have hd2G : d2 ∈ G := G.mul_mem (G.mul_mem hcG hd1G) hcG
  have hd3G : d3 ∈ G := G.mul_mem (G.mul_mem hr hd2G) hr
  have hd1m : LinearMap.toMatrix f f d1.toLinearMap = diagSignMat 1 := by
    dsimp only [d1]
    rw [zs4h_e1_mat h, diagSignMat_eq_one_sub_vecMulVec]
  have hd2m : LinearMap.toMatrix f f d2.toLinearMap = diagSignMat 2 := by
    dsimp only [d2, d1]
    rw [zs4h_e2_mat h, diagSignMat_eq_one_sub_vecMulVec]
  have hd3m : LinearMap.toMatrix f f d3.toLinearMap = diagSignMat 3 := by
    dsimp only [d3, d2, d1]
    rw [zs4h_e3_mat h hrm, diagSignMat_eq_one_sub_vecMulVec]
  exact ⟨d1, hd1G, d2, hd2G, d3, hd3G, hd1m, hd2m, hd3m⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4h_signMat_mem (h : FFourData f a b c g H G) {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1)
    {s1 s2 s3 : ZMod p} (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (hs3 : s3 = 1 ∨ s3 = -1) :
    ∃ D ∈ G, LinearMap.toMatrix f f D.toLinearMap = Matrix.diagonal ![1, s1, s2, s3] := by
  obtain ⟨d1, hd1G, d2, hd2G, d3, hd3G, hd1m, hd2m, hd3m⟩ :=
    zs4h_signMat_eps h hr hrm
  rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> rcases hs3 with rfl | rfl
  · exact ⟨1, G.one_mem, by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]⟩
  · exact ⟨d3, hd3G, by
      rw [hd3m]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagSignMat]⟩
  · exact ⟨d2, hd2G, by
      rw [hd2m]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagSignMat]⟩
  · exact ⟨d2 * d3, G.mul_mem hd2G hd3G, by
      rw [toMatrix_coe_mul, hd2m, hd3m]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagSignMat]⟩
  · exact ⟨d1, hd1G, by
      rw [hd1m]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagSignMat]⟩
  · exact ⟨d1 * d3, G.mul_mem hd1G hd3G, by
      rw [toMatrix_coe_mul, hd1m, hd3m]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagSignMat]⟩
  · exact ⟨d1 * d2, G.mul_mem hd1G hd2G, by
      rw [toMatrix_coe_mul, hd1m, hd2m]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [diagSignMat]⟩
  · exact ⟨d1 * d2 * d3, G.mul_mem (G.mul_mem hd1G hd2G) hd3G, by
      rw [toMatrix_coe_mul, toMatrix_coe_mul, hd1m, hd2m, hd3m]; ext i j;
      fin_cases i <;> fin_cases j <;> simp [diagSignMat]⟩

theorem exists_halfOnes_of_pi34 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ G)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = pijMat 2 3 1) :
    ∃ x ∈ G, LinearMap.toMatrix f f x.toLinearMap = halfOnesMat 4 := by
  have hHmono : ∀ k ∈ H, IsMonomialIn f k := zs4h_H_monomial h
  obtain ⟨x, hxG, hxrefl, hxnonmono⟩ :=
    exists_isRefl_not_isMonomialIn (n := 4) (by norm_num) f h.reflGen h.primitive
  obtain ⟨v, w, hxm, hwv⟩ := FFourCoord.exists_toMatrix_of_isRefl hp f hxrefl
  have hv : ∀ i, v i ≠ 0 :=
    zs4h_v_ne_zero h hr hrm hxG hxrefl hxm hHmono hxnonmono
  have hd : ∀ i, 2 * (w i * v i) = 1 :=
    zs4h_d_eq_one hp h hr hrm hxG hxm hwv hxnonmono hHmono hv
  have hsign : ∀ i, i ≠ 0 → v i = v 0 ∨ v i = -v 0 :=
    zs4h_sign_of_pair hp h hr hrm hxG hxrefl hxm hwv hxnonmono hHmono hv hd
  let σ : Fin 4 → ZMod p := fun i => v i / v 0
  have hσ0 : σ 0 = 1 := by simp [σ, hv 0]
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := by
    intro i
    by_cases hi : i = 0
    · left; rw [hi]; exact hσ0
    · rcases hsign i hi with hi' | hi'
      · left; dsimp only [σ]; rw [hi']; exact div_self (hv 0)
      · right; dsimp only [σ]; rw [hi', neg_div, div_self (hv 0)]
  have hσsq : ∀ i, σ i ^ 2 = 1 := by
    intro i
    rcases hσ i with hi | hi <;> rw [hi] <;> norm_num
  have hvσ : ∀ i, v i = v 0 * σ i := by
    intro i
    dsimp only [σ]
    field_simp [hv 0]
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨D, hDG, hDm⟩ :=
    zs4h_signMat_mem h hr hrm (s1 := σ 1) (s2 := σ 2) (s3 := σ 3) (hσ 1) (hσ 2) (hσ 3)
  have hDm' : LinearMap.toMatrix f f D.toLinearMap = Matrix.diagonal σ := by
    rw [hDm]
    congr 1
    funext i
    fin_cases i <;> simp [hσ0]
  refine ⟨D * x * D, G.mul_mem (G.mul_mem hDG hxG) hDG, ?_⟩
  rw [toMatrix_coe_mul, toMatrix_coe_mul, hDm', hxm]
  exact zs4h_conj_half hσsq hvσ hd (hv 0) htwo

theorem weylF4_le (h : FFourData f a b c g H G) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G)
    (hxm : LinearMap.toMatrix f f x.toLinearMap = halfOnesMat 4) :
    basisClosure f weylF4Mats ≤ G := by
  have haH : a ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [h.H_eq]; exact Subgroup.subset_closure (by simp)
  rw [basisClosure, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_setOf_eq, weylF4Mats, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy | hy
  · rw [toMatrix_inj_four (hy.trans h.toMatrix_a.symm)]
    exact h.H_le haH
  · rw [toMatrix_inj_four (hy.trans h.toMatrix_b.symm)]
    exact h.H_le hbH
  · rw [toMatrix_inj_four (hy.trans h.toMatrix_c.symm)]
    exact h.H_le hcH
  · rw [toMatrix_inj_four (hy.trans hxm.symm)]
    exact hx

omit [Module.Finite (ZMod p) U] in
private theorem zs4w_H_le_weylF4 (h : FFourData f a b c g H G) :
    H ≤ basisClosure f weylF4Mats := by
  rw [h.H_eq]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (hy : y ∈ ({a, b, c} : Set (U ≃ₗ[ZMod p] U)))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact Subgroup.subset_closure (by simp [weylF4Mats, h.toMatrix_a])
  · exact Subgroup.subset_closure (by simp [weylF4Mats, h.toMatrix_b])
  · exact Subgroup.subset_closure (by simp [weylF4Mats, h.toMatrix_c])

omit [Module.Finite (ZMod p) U] in
theorem le_weylF4 (hp : p ≠ 2) (h : FFourData f a b c g H G)
    (hF : basisClosure f weylF4Mats ≤ G) : G ≤ basisClosure f weylF4Mats := by
  exact CFSG.StandardType.ZS.FFourCoord.le_weylF4_of_inH hp h.reflGen h.dmax hF
    (zs4w_H_le_weylF4 h) h.inH

omit [Module.Finite (ZMod p) U] in
private lemma zs4k_unitsSMul_pijMat (β : (ZMod p)ˣ) :
    (fun r c : Fin 4 => (((![1, 1, 1, β⁻¹] : Fin 4 → (ZMod p)ˣ) r)⁻¹ : ZMod p) *
        pijMat 2 3 (β : ZMod p) r c *
        (((![1, 1, 1, β⁻¹] : Fin 4 → (ZMod p)ˣ) c) : ZMod p)) = pijMat 2 3 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp +decide only [pijMat, ↓reduceIte, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Units.val_one, Units.val_inv_eq_inv_val]
  all_goals (try ring_nf)
  all_goals (try exact mul_inv_cancel₀ (Units.ne_zero β))
  all_goals (try (rw [inv_inv]; exact inv_mul_cancel₀ (Units.ne_zero β)))

theorem eq_weylF4_or_eq_isIsom (hp : p ≠ 2) (h : FFourData f a b c g H G) (hT : TFSmallThree p) :
    (∃ f' : Module.Basis (Fin 4) (ZMod p) U, G = basisClosure f' weylF4Mats) ∨
      (p = 3 ∧ ∃ f' : Module.Basis (Fin 4) (ZMod p) U, ∀ x, x ∈ G ↔ IsIsom p (phiForm f') x) := by
  obtain ⟨k, hk, hkg⟩ := h.exists_conj_ne_comm_aba hp
  have h' : FFourData f a b c (k * g * k⁻¹) H G := h.conj hk
  rcases h'.pi34_or_oPhi hp hT hkg with ⟨hp3, ε, hO⟩ | ⟨β, r, hr, hrm⟩
  · have h'' : FFourData (f.unitsSMul ![1, 1, 1, ε]) a b c (k * g * k⁻¹) H G :=
      h'.rescale ε
    exact Or.inr ⟨hp3, f.unitsSMul ![1, 1, 1, ε],
      fun x => h''.eq_isIsom_of_oPhi_le hp3 hO x⟩
  · have h'' : FFourData (f.unitsSMul ![1, 1, 1, β⁻¹]) a b c (k * g * k⁻¹) H G :=
      h'.rescale β⁻¹
    have hrm' : LinearMap.toMatrix (f.unitsSMul ![1, 1, 1, β⁻¹])
        (f.unitsSMul ![1, 1, 1, β⁻¹]) r.toLinearMap = pijMat 2 3 1 := by
      ext i j
      rw [zs4k_toMatrix_unitsSMul_apply, hrm]
      simpa only [Units.val_inv_eq_inv_val] using
        congrFun (congrFun (zs4k_unitsSMul_pijMat β) i) j
    obtain ⟨x, hx, hxm⟩ := h''.exists_halfOnes_of_pi34 hp hr hrm'
    have hF : basisClosure (f.unitsSMul ![1, 1, 1, β⁻¹]) weylF4Mats ≤ G := h''.weylF4_le hx hxm
    exact Or.inl ⟨f.unitsSMul ![1, 1, 1, β⁻¹],
      le_antisymm (h''.le_weylF4 hp hF) hF⟩

end FFourData

private theorem zs4q_reflB3_pair_pow :
    ∀ i j : Fin 9, (FFourCoord.reflB3 i * FFourCoord.reflB3 j) ^ 4 = 1 ∨
      (FFourCoord.reflB3 i * FFourCoord.reflB3 j) ^ 3 = 1 := by
  decide +kernel

private theorem zs4q_orderOf_mul_le_four_of_mem_g2mmn_zero_one
    (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Module.Basis (Fin 3) (ZMod p) V) {x y : V ≃ₗ[ZMod p] V}
    (hx : x ∈ g2mmn p e 0 1 1) (hy : y ∈ g2mmn p e 0 1 1)
    (hxr : IsRefl p x) (hyr : IsRefl p y) : orderOf (x * y) ≤ 4 := by
  obtain ⟨i, hi⟩ := FFourCoord.exists_reflB3_of_isRefl hp e hx hxr
  obtain ⟨j, hj⟩ := FFourCoord.exists_reflB3_of_isRefl hp e hy hyr
  let τ : (V ≃ₗ[ZMod p] V) →* Matrix (Fin 3) (Fin 3) (ZMod p) :=
    { toFun := fun x => LinearMap.toMatrix e e (x : V →ₗ[ZMod p] V)
      map_one' := by rw [LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
      map_mul' := fun x y => by rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] }
  have hτ : Function.Injective τ := by
    intro x y hxy
    exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix e e).injective hxy)
  have hτxy : τ (x * y) = (Int.castRingHom (ZMod p)).mapMatrix
      (FFourCoord.reflB3 i * FFourCoord.reflB3 j) := by
    change LinearMap.toMatrix e e (x * y).toLinearMap = _
    rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hi, hj, ← map_mul]
  have hpow : ∀ m : ℕ, (FFourCoord.reflB3 i * FFourCoord.reflB3 j) ^ m = 1 →
      (x * y) ^ m = 1 := by
    intro m hm
    apply hτ
    rw [map_pow, hτxy, ← map_pow, hm, map_one]
    exact (map_one τ).symm
  rcases zs4q_reflB3_pair_pow i j with h | h
  · exact orderOf_le_of_pow_eq_one (by norm_num) (hpow 4 h)
  · exact le_trans (orderOf_le_of_pow_eq_one (by norm_num) (hpow 3 h)) (by norm_num)

private theorem zs4q_signChange_mem_g2mmn_zero_one
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Module.Basis (Fin 3) (ZMod p) V) (k : Fin 3) :
    diagMap p e (fun i => if i = k then (-1 : (ZMod p)ˣ) else 1) ∈ g2mmn p e 0 1 1 := by
  by_cases hk : k = 0
  · subst hk
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · have hτ : permMap p e (Equiv.swap 0 k) ∈ g2mmn p e 0 1 1 :=
      Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
    have hs : diagMap p e (fun i => if i = 0 then (-1 : (ZMod p)ˣ) else 1) ∈
        g2mmn p e 0 1 1 :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hmem : permMap p e (Equiv.swap 0 k) *
        diagMap p e (fun i => if i = 0 then (-1 : (ZMod p)ˣ) else 1) *
        (permMap p e (Equiv.swap 0 k))⁻¹ ∈ g2mmn p e 0 1 1 :=
      (g2mmn p e 0 1 1).mul_mem
        ((g2mmn p e 0 1 1).mul_mem hτ hs) ((g2mmn p e 0 1 1).inv_mem hτ)
    convert hmem using 1
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext i
    rw [Function.comp_apply, Equiv.symm_swap]
    by_cases hi : i = k
    · subst hi
      rw [Equiv.swap_apply_right]
      simp
    · have hne : Equiv.swap (0 : Fin 3) k i ≠ 0 := by
        intro h
        have h' : i = k := by
          have := congrArg (Equiv.swap (0 : Fin 3) k) h
          rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
        exact hi h'
      simp [hi, hne]

private theorem zs4q_unit_eq_one_or_neg_one {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1) :
    ζ = 1 ∨ ζ = -1 := by
  have h : (ζ : ZMod p) ^ 2 = 1 := by
    have h' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hζ
    simpa [pow_two] using h'
  rcases sq_eq_one_iff.mp h with h1 | h1
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext h1)

private theorem zs4q_g2mmn_le_zero_one_of_sq_one
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Module.Basis (Fin 3) (ZMod p) V) {j₀ j₁ : Fin 3} (hj : j₀ ≠ j₁)
    {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1) :
    g2mmn p e j₀ j₁ ζ ≤ g2mmn p e 0 1 1 := by
  rw [g2mmn, Subgroup.closure_le]
  rintro x (hx | hx)
  · obtain ⟨τ, rfl⟩ := hx
    exact Subgroup.subset_closure (Or.inl (Set.mem_range_self τ))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact zs4q_signChange_mem_g2mmn_zero_one e j₀
    · rcases zs4q_unit_eq_one_or_neg_one hζ with h | h
      · rw [h, pairUnit_one, diagMap_one]
        exact Subgroup.one_mem _
      · rw [h]
        have hpair : diagMap p e (pairUnit p j₀ j₁ (-1)) =
            diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1) *
              diagMap p e (fun i => if i = j₁ then (-1 : (ZMod p)ˣ) else 1) := by
          rw [diagMap_mul]
          congr 1
          funext i
          simp only [Pi.mul_apply, pairUnit]
          by_cases h0 : i = j₀
          · subst h0; simp [hj]
          · by_cases h1 : i = j₁
            · subst h1; simp [h0]
            · simp [h0, h1]
        rw [hpair]
        exact (g2mmn p e 0 1 1).mul_mem
          (zs4q_signChange_mem_g2mmn_zero_one e j₀)
          (zs4q_signChange_mem_g2mmn_zero_one e j₁)

private theorem zs4q_orderOf_mul_le_four_of_mem_g2mmn_sq_one
    (hp : p ≠ 2) {n : ℕ} (hn : n = 3) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Module.Basis (Fin n) (ZMod p) V) {j₀ j₁ : Fin n} (hj : j₀ ≠ j₁)
    {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1) {x y : V ≃ₗ[ZMod p] V}
    (hx : x ∈ g2mmn p e j₀ j₁ ζ) (hy : y ∈ g2mmn p e j₀ j₁ ζ)
    (hxr : IsRefl p x) (hyr : IsRefl p y) : orderOf (x * y) ≤ 4 := by
  subst hn
  exact zs4q_orderOf_mul_le_four_of_mem_g2mmn_zero_one hp e
    (zs4q_g2mmn_le_zero_one_of_sq_one e hj hζ hx)
    (zs4q_g2mmn_le_zero_one_of_sq_one e hj hζ hy) hxr hyr

namespace ImpExtStd

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
  {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace H)}
  {j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)} {ζ : (ZMod p)ˣ}

private theorem zs4q_permMap_one {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Module.Basis (Fin n) (ZMod p) V) : permMap p e 1 = 1 := by
  show e.equiv e 1 = 1
  rw [show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl, Module.Basis.equiv_refl]
  rfl

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_exists_lift {f : Module.Basis (Fin 4) (ZMod p) U}
    (hf₃ : f 3 ∈ centralizerSpace H)
    {x : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      (HardMathSupport.Kantor79.commutatorSpace H)} (hx : x ∈ movedGroup H) :
    ∃ h ∈ H, h (f 3) = f 3 ∧
      ∀ v : HardMathSupport.Kantor79.commutatorSpace H, h (v : U) = (x v : U) := by
  obtain ⟨⟨h, hh⟩, heq⟩ := MonoidHom.mem_range.mp hx
  refine ⟨h, hh, (mem_centralizerSpace.mp hf₃) h hh, fun v => ?_⟩
  rw [← heq]
  exact (restrictHom_apply H _ _ ⟨h, hh⟩ v).symm

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_exists_a (hH : movedGroup H = g2mmn p e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ a ∈ H, (∀ v : HardMathSupport.Kantor79.commutatorSpace H,
        a (v : U) = ((diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1)) v : U)) ∧
      LinearMap.toMatrix f f a.toLinearMap = diagSignMat 0 := by
  have hx : diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1) ∈ movedGroup H := by
    rw [hH]
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  obtain ⟨a, haH, ha3, haact⟩ := zs4q_exists_lift (H := H) hf₃ hx
  have hact : ∀ i : Fin 3,
      a (f i.castSucc) = (if σ i = j₀ then (-1 : ZMod p) else 1) • f i.castSucc := by
    intro i
    rw [hf i, haact (e (σ i)), diagMap_apply_basis, Submodule.coe_smul, ← hf i]
    by_cases h : σ i = j₀ <;> simp [h]
  have ha0 : a (f 0) = -f 0 := by
    have h : a (f (0 : Fin 3).castSucc) = -f (0 : Fin 3).castSucc := by
      rw [hact 0, hσ₀]
      simp
    simpa using h
  have ha1 : a (f 1) = f 1 := by
    have hne : σ 1 ≠ j₀ := by rw [← hσ₀]; exact σ.injective.ne (by decide)
    have h : a (f (1 : Fin 3).castSucc) = f (1 : Fin 3).castSucc := by
      rw [hact 1, if_neg hne, one_smul]
    simpa using h
  have ha2 : a (f 2) = f 2 := by
    have hne : σ 2 ≠ j₀ := by rw [← hσ₀]; exact σ.injective.ne (by decide)
    have h : a (f (2 : Fin 3).castSucc) = f (2 : Fin 3).castSucc := by
      rw [hact 2, if_neg hne, one_smul]
    simpa using h
  refine ⟨a, haH, haact, ?_⟩
  ext r col
  fin_cases r <;> fin_cases col <;>
    simp [LinearMap.toMatrix_apply, ha0, ha1, ha2, ha3, diagSignMat]

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_exists_b (hH : movedGroup H = g2mmn p e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ b ∈ H, (∀ v : HardMathSupport.Kantor79.commutatorSpace H,
        b (v : U) = ((permMap p e (Equiv.swap j₀ j₁)) v : U)) ∧
      LinearMap.toMatrix f f b.toLinearMap = pijMat 0 1 1 := by
  have hx : permMap p e (Equiv.swap j₀ j₁) ∈ movedGroup H := by
    rw [hH]
    exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  obtain ⟨b, hbH, hb3, hbact⟩ := zs4q_exists_lift (H := H) hf₃ hx
  have hb0 : b (f 0) = f 1 := by
    have h : b (f (0 : Fin 3).castSucc) = f (1 : Fin 3).castSucc := by
      rw [hf 0, hbact (e (σ 0)), permMap_apply_basis, hσ₀, Equiv.swap_apply_left, ← hσ₁]
      exact (hf 1).symm
    simpa using h
  have hb1 : b (f 1) = f 0 := by
    have h : b (f (1 : Fin 3).castSucc) = f (0 : Fin 3).castSucc := by
      rw [hf 1, hbact (e (σ 1)), permMap_apply_basis, hσ₁, Equiv.swap_apply_right, ← hσ₀]
      exact (hf 0).symm
    simpa using h
  have hb2 : b (f 2) = f 2 := by
    have hne0 : σ 2 ≠ j₀ := by rw [← hσ₀]; exact σ.injective.ne (by decide)
    have hne1 : σ 2 ≠ j₁ := by rw [← hσ₁]; exact σ.injective.ne (by decide)
    have h : b (f (2 : Fin 3).castSucc) = f (2 : Fin 3).castSucc := by
      rw [hf 2, hbact (e (σ 2)), permMap_apply_basis,
        Equiv.swap_apply_of_ne_of_ne hne0 hne1]
    simpa using h
  refine ⟨b, hbH, hbact, ?_⟩
  ext r col
  fin_cases r <;> fin_cases col <;>
    simp [LinearMap.toMatrix_apply, hb0, hb1, hb2, hb3, pijMat]

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_exists_c (hH : movedGroup H = g2mmn p e j₀ j₁ ζ)
    {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₁ : σ 1 = j₁) (hf : ∀ i : Fin 3, f i.castSucc = e (σ i))
    (hf₃ : f 3 ∈ centralizerSpace H) :
    ∃ c ∈ H, (∀ v : HardMathSupport.Kantor79.commutatorSpace H,
        c (v : U) = ((permMap p e (Equiv.swap j₁ (σ 2))) v : U)) ∧
      LinearMap.toMatrix f f c.toLinearMap = pijMat 1 2 1 := by
  have hx : permMap p e (Equiv.swap j₁ (σ 2)) ∈ movedGroup H := by
    rw [hH]
    exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  obtain ⟨c, hcH, hc3, hcact⟩ := zs4q_exists_lift (H := H) hf₃ hx
  have hc0 : c (f 0) = f 0 := by
    have hne1 : σ 0 ≠ j₁ := by rw [← hσ₁]; exact σ.injective.ne (by decide)
    have hne2 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
    have h : c (f (0 : Fin 3).castSucc) = f (0 : Fin 3).castSucc := by
      rw [hf 0, hcact (e (σ 0)), permMap_apply_basis,
        Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    simpa using h
  have hc1 : c (f 1) = f 2 := by
    have h : c (f (1 : Fin 3).castSucc) = f (2 : Fin 3).castSucc := by
      rw [hf 1, hcact (e (σ 1)), permMap_apply_basis, hσ₁, Equiv.swap_apply_left]
      exact (hf 2).symm
    simpa using h
  have hc2 : c (f 2) = f 1 := by
    have h : c (f (2 : Fin 3).castSucc) = f (1 : Fin 3).castSucc := by
      rw [hf 2, hcact (e (σ 2)), permMap_apply_basis, Equiv.swap_apply_right, ← hσ₁]
      exact (hf 1).symm
    simpa using h
  refine ⟨c, hcH, hcact, ?_⟩
  ext r col
  fin_cases r <;> fin_cases col <;>
    simp [LinearMap.toMatrix_apply, hc0, hc1, hc2, hc3, pijMat]

private theorem zs4q_map_injective_of_injective {G K : Type*} [Group G] [Group K]
    (f : G →* K) (hf : Function.Injective f) : Function.Injective (Subgroup.map f) := by
  intro A B h
  ext x
  constructor
  · intro hx
    have hmem : f x ∈ Subgroup.map f B := by rw [← h]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [hf hyx] at hy
    exact hy
  · intro hx
    have hmem : f x ∈ Subgroup.map f A := by rw [h]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [hf hyx] at hy
    exact hy

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_span_eq {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hf : ∀ i : Fin 3, f i.castSucc = e (σ i)) :
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hrange : Set.range (fun i : Fin 3 => f i.castSucc) =
      Set.range (fun j : Fin (Module.finrank (ZMod p) U - 1) => (e j : U)) := by
    ext w; constructor
    · rintro ⟨i, rfl⟩; exact ⟨σ i, (hf i).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨σ.symm j, by
        change f (σ.symm j).castSucc = (e j : U)
        rw [hf (σ.symm j), Equiv.apply_symm_apply]⟩
  have hrangeE : Set.range (fun j : Fin (Module.finrank (ZMod p) U - 1) => (e j : U)) =
      (HardMathSupport.Kantor79.commutatorSpace H).subtype '' Set.range e := by
    ext w; constructor
    · rintro ⟨j, rfl⟩; exact ⟨e j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
  rw [hrange, hrangeE, ← Submodule.map_span, e.span_eq, Submodule.map_top,
    Submodule.range_subtype]

private noncomputable def zs4q_permMapHom {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (e : Module.Basis (Fin n) (ZMod p) V) :
    Equiv.Perm (Fin n) →* (V ≃ₗ[ZMod p] V) where
  toFun := permMap p e
  map_one' := zs4q_permMap_one e
  map_mul' σ τ := (permMap_mul e σ τ).symm

private theorem zs4q_closure_swap_eq_top {L : ℕ} (σ : Fin 3 ≃ Fin L) {j₀ j₁ : Fin L}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) :
    Subgroup.closure ({Equiv.swap j₀ j₁, Equiv.swap j₁ (σ 2)} : Set (Equiv.Perm (Fin L))) =
      ⊤ := by
  have h01 : σ.permCongrHom (Equiv.swap (0 : Fin 3) 1) = Equiv.swap j₀ j₁ := by
    change σ.permCongr (Equiv.swap (0 : Fin 3) 1) = Equiv.swap j₀ j₁
    rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans, hσ₀, hσ₁]
  have h12 : σ.permCongrHom (Equiv.swap (1 : Fin 3) 2) = Equiv.swap j₁ (σ 2) := by
    change σ.permCongr (Equiv.swap (1 : Fin 3) 2) = Equiv.swap j₁ (σ 2)
    rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans, hσ₁]
  have hrange : ({(Equiv.swap (0 : Fin 3) 1), (Equiv.swap 1 2)} : Set (Equiv.Perm (Fin 3))) =
      Set.range (fun i : Fin 2 => Equiv.swap i.castSucc i.succ) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by decide⟩
      · exact ⟨1, by decide⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
  have htop3 : Subgroup.closure ({(Equiv.swap (0 : Fin 3) 1), (Equiv.swap 1 2)} :
      Set (Equiv.Perm (Fin 3))) = ⊤ := by
    rw [hrange]
    exact Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 2)
  have himg : σ.permCongrHom '' ({(Equiv.swap (0 : Fin 3) 1), (Equiv.swap 1 2)} :
      Set (Equiv.Perm (Fin 3))) =
      ({Equiv.swap j₀ j₁, Equiv.swap j₁ (σ 2)} : Set (Equiv.Perm (Fin L))) := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl | rfl, rfl⟩
      · exact Or.inl h01
      · exact Or.inr h12
    · rintro (rfl | rfl)
      · exact ⟨Equiv.swap (0 : Fin 3) 1, Or.inl rfl, h01⟩
      · exact ⟨Equiv.swap (1 : Fin 3) 2, Or.inr rfl, h12⟩
  rw [← himg]
  change Subgroup.closure ((σ.permCongrHom : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin L)) ''
    ({(Equiv.swap (0 : Fin 3) 1), (Equiv.swap 1 2)} : Set (Equiv.Perm (Fin 3)))) = ⊤
  rw [← MonoidHom.map_closure (σ.permCongrHom : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin L))
    ({(Equiv.swap (0 : Fin 3) 1), (Equiv.swap 1 2)} : Set (Equiv.Perm (Fin 3))), htop3]
  exact Subgroup.map_top_of_surjective _ (EquivLike.surjective _)

private theorem zs4q_sign_conj {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (e : Module.Basis (Fin n) (ZMod p) V) {a b : Fin n} (hab : a ≠ b) :
    permMap p e (Equiv.swap a b) *
      diagMap p e (fun i => if i = a then (-1 : (ZMod p)ˣ) else 1) *
      (permMap p e (Equiv.swap a b))⁻¹ =
      diagMap p e (fun i => if i = b then (-1 : (ZMod p)ˣ) else 1) := by
  rw [permMap_mul_diagMap_mul_inv]
  congr 1
  funext i
  rw [Function.comp_apply, Equiv.symm_swap]
  by_cases hi : i = b
  · subst hi
    rw [Equiv.swap_apply_right]
    simp
  · have hne : Equiv.swap a b i ≠ a := by
      intro h
      have h' : i = b := by
        have := congrArg (Equiv.swap a b) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact hi h'
    simp [hi, hne]

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_diagMap_pairUnit_neg (hj : j₀ ≠ j₁) :
    diagMap p e (pairUnit p j₀ j₁ (-1)) =
      diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1) *
        diagMap p e (fun i => if i = j₁ then (-1 : (ZMod p)ˣ) else 1) := by
  rw [diagMap_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, pairUnit]
  by_cases h0 : i = j₀
  · subst h0; simp [hj]
  · by_cases h1 : i = j₁
    · subst h1; simp [h0]
    · simp [h0, h1]

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_permMap_mem_closure
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁)
    (K : Subgroup (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H))
    (hKsub : Subgroup.closure ({permMap p e (Equiv.swap j₀ j₁),
      permMap p e (Equiv.swap j₁ (σ 2))} : Set
        (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H)) ≤ K) :
    ∀ τ : Equiv.Perm (Fin (Module.finrank (ZMod p) U - 1)), permMap p e τ ∈ K := by
  intro τ
  have hτ : τ ∈ Subgroup.closure ({Equiv.swap j₀ j₁, Equiv.swap j₁ (σ 2)} : Set _) := by
    rw [zs4q_closure_swap_eq_top σ hσ₀ hσ₁]; exact Subgroup.mem_top τ
  have hmem : permMap p e τ ∈ Subgroup.map (zs4q_permMapHom e)
      (Subgroup.closure ({Equiv.swap j₀ j₁, Equiv.swap j₁ (σ 2)} : Set _)) :=
    ⟨τ, hτ, rfl⟩
  rw [MonoidHom.map_closure] at hmem
  exact hKsub (by simpa [zs4q_permMapHom] using hmem)

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_g2mmn_le_closure (hj : j₀ ≠ j₁) (hζ : ζ * ζ = 1)
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) :
    g2mmn p e j₀ j₁ ζ ≤ Subgroup.closure
      ({diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1),
        permMap p e (Equiv.swap j₀ j₁),
        permMap p e (Equiv.swap j₁ (σ 2))} :
        Set (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H)) := by
  let K : Subgroup (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H) := Subgroup.closure
    ({diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1),
      permMap p e (Equiv.swap j₀ j₁),
      permMap p e (Equiv.swap j₁ (σ 2))} :
      Set (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H))
  have hsign0 : diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1) ∈ K :=
    Subgroup.subset_closure (by simp)
  have hswap01 : permMap p e (Equiv.swap j₀ j₁) ∈ K :=
    Subgroup.subset_closure (by simp)
  have hsign1 : diagMap p e (fun i => if i = j₁ then (-1 : (ZMod p)ˣ) else 1) ∈ K := by
    rw [← zs4q_sign_conj e hj]
    exact K.mul_mem (K.mul_mem hswap01 hsign0) (K.inv_mem hswap01)
  have hKsub : Subgroup.closure ({permMap p e (Equiv.swap j₀ j₁),
      permMap p e (Equiv.swap j₁ (σ 2))} : Set
        (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H)) ≤ K := by
    refine (Subgroup.closure_le K).mpr ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hswap01
    · exact Subgroup.subset_closure (by simp)
  have hgen := zs4q_permMap_mem_closure hσ₀ hσ₁ K hKsub
  rw [g2mmn, Subgroup.closure_le]
  rintro x (hx | hx)
  · obtain ⟨τ, rfl⟩ := hx
    exact hgen τ
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hsign0
    · rcases zs4q_unit_eq_one_or_neg_one hζ with h | h
      · rw [h, pairUnit_one, diagMap_one]
        exact K.one_mem
      · rw [h, zs4q_diagMap_pairUnit_neg hj]
        exact K.mul_mem hsign0 hsign1

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_closure_le_g2mmn
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} :
    Subgroup.closure
      ({diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1),
        permMap p e (Equiv.swap j₀ j₁),
        permMap p e (Equiv.swap j₁ (σ 2))} :
        Set (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H)) ≤ g2mmn p e j₀ j₁ ζ := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_g2mmn_eq_closure (hj : j₀ ≠ j₁) (hζ : ζ * ζ = 1)
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁) :
    g2mmn p e j₀ j₁ ζ = Subgroup.closure
      ({diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1),
        permMap p e (Equiv.swap j₀ j₁),
        permMap p e (Equiv.swap j₁ (σ 2))} :
        Set (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H)) :=
  le_antisymm (zs4q_g2mmn_le_closure hj hζ hσ₀ hσ₁) zs4q_closure_le_g2mmn

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_map_subtype_closure {a b c : U ≃ₗ[ZMod p] U}
    (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H) :
    Subgroup.map H.subtype (Subgroup.closure {⟨a, haH⟩, ⟨b, hbH⟩, ⟨c, hcH⟩}) =
      Subgroup.closure {a, b, c} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_map_restrictHom_eq_movedGroup (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) (hζ : ζ * ζ = 1)
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)} (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁)
    {a b c : U ≃ₗ[ZMod p] U} (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    {ρ : H →* (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H)}
    (hρa : (ρ ⟨a, haH⟩ : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H) =
      diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1))
    (hρb : (ρ ⟨b, hbH⟩ : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H) = permMap p e (Equiv.swap j₀ j₁))
    (hρc : (ρ ⟨c, hcH⟩ : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace H) = permMap p e (Equiv.swap j₁ (σ 2))) :
    Subgroup.map ρ (Subgroup.closure {⟨a, haH⟩, ⟨b, hbH⟩, ⟨c, hcH⟩}) = movedGroup H := by
  have h1 : Subgroup.map ρ (Subgroup.closure {⟨a, haH⟩, ⟨b, hbH⟩, ⟨c, hcH⟩}) =
      Subgroup.closure ({ρ ⟨a, haH⟩, ρ ⟨b, hbH⟩, ρ ⟨c, hcH⟩} : Set
        (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace H)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  rw [h1, hρa, hρb, hρc, ← zs4q_g2mmn_eq_closure S.ne hζ hσ₀ hσ₁, hH]

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_H_le_closure (ρ : H →* (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H)) (hρinj : Function.Injective ρ)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {XH : Subgroup H}
    (hrange : ρ.range = movedGroup H)
    (hmap : Subgroup.map ρ XH = movedGroup H) (hmap_sub : Subgroup.map H.subtype XH = X) :
    H ≤ X := by
  have hXH : XH = ⊤ := by
    apply zs4q_map_injective_of_injective ρ hρinj
    rw [hmap, ← hrange]
    exact MonoidHom.range_eq_map ρ
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈ XH := by rw [hXH]; trivial
  rw [← hmap_sub]
  exact ⟨⟨h, hh⟩, hmem, rfl⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4q_H_eq (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) (hζ : ζ * ζ = 1)
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hσ₀ : σ 0 = j₀) (hσ₁ : σ 1 = j₁)
    {a b c : U ≃ₗ[ZMod p] U} (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (hacta : ∀ v : HardMathSupport.Kantor79.commutatorSpace H,
      a (v : U) = ((diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1)) v : U))
    (hactb : ∀ v : HardMathSupport.Kantor79.commutatorSpace H,
      b (v : U) = ((permMap p e (Equiv.swap j₀ j₁)) v : U))
    (hactc : ∀ v : HardMathSupport.Kantor79.commutatorSpace H,
      c (v : U) = ((permMap p e (Equiv.swap j₁ (σ 2))) v : U)) :
    H = Subgroup.closure {a, b, c} := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let ρ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hρinj : Function.Injective ρ := restrictHom_injective_of_splitSupport S.splitSupport
  let X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure {a, b, c}
  let XH : Subgroup H := Subgroup.closure {⟨a, haH⟩, ⟨b, hbH⟩, ⟨c, hcH⟩}
  have hXH_le : X ≤ H := by
    change Subgroup.closure {a, b, c} ≤ H
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  have hmap_sub : Subgroup.map H.subtype XH = X := zs4q_map_subtype_closure haH hbH hcH
  have hρa : (ρ ⟨a, haH⟩ : V ≃ₗ[ZMod p] V) =
      diagMap p e (fun i => if i = j₀ then (-1 : (ZMod p)ˣ) else 1) := by
    ext v
    rw [restrictHom_apply]
    exact hacta v
  have hρb : (ρ ⟨b, hbH⟩ : V ≃ₗ[ZMod p] V) = permMap p e (Equiv.swap j₀ j₁) := by
    ext v
    rw [restrictHom_apply]
    exact hactb v
  have hρc : (ρ ⟨c, hcH⟩ : V ≃ₗ[ZMod p] V) = permMap p e (Equiv.swap j₁ (σ 2)) := by
    ext v
    rw [restrictHom_apply]
    exact hactc v
  have hmap : Subgroup.map ρ XH = movedGroup H :=
    zs4q_map_restrictHom_eq_movedGroup S hH hζ hσ₀ hσ₁ haH hbH hcH hρa hρb hρc
  have hrange : ρ.range = movedGroup H := rfl
  exact le_antisymm (zs4q_H_le_closure ρ hρinj hrange hmap hmap_sub) hXH_le

omit [Module.Finite (ZMod p) U] in
theorem dmax_eq_four_of_orderOf_dvd_two (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ ∣ 2)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) : d = 4 := by
  have hζ' : ζ * ζ = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp hζ
  have hD : DMax p (movedGroup H) d := (dmax_movedGroup_iff S.splitSupport d).2 S.dmax_H
  rw [hH] at hD
  have hle : d ≤ 4 := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hD.2
    rw [← hxy]
    exact zs4q_orderOf_mul_le_four_of_mem_g2mmn_sq_one hp (by rw [hn]) e S.ne hζ'
      hx hy hxr hyr
  exact le_antisymm hle (Nat.succ_le_of_lt S.three_lt)

private theorem zs4i_inH_map {x : U ≃ₗ[ZMod p] U}
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ HardMathSupport.Kantor79.commutatorSpace H) :
    (HardMathSupport.Kantor79.commutatorSpace H).map x.toLinearMap =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hle : (HardMathSupport.Kantor79.commutatorSpace H).map x.toLinearMap ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    intro w hw
    rw [Submodule.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hmem : x v - v ∈ HardMathSupport.Kantor79.movedSpace x := by
      exact ⟨v, by simp [LinearMap.sub_apply]⟩
    have h : x v = v + (x v - v) := by abel
    change x v ∈ HardMathSupport.Kantor79.commutatorSpace H
    rw [h]
    exact Submodule.add_mem _ hv (hxV hmem)
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq x _)

omit [Module.Finite (ZMod p) U] in
private theorem zs4i_inH_fix {x : U ≃ₗ[ZMod p] U}
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ HardMathSupport.Kantor79.commutatorSpace H)
    {h c : U ≃ₗ[ZMod p] U} (hh : h ∈ H)
    (hc : c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hx : x = h * c) (hcomp : IsCompl (HardMathSupport.Kantor79.commutatorSpace H)
      (centralizerSpace H)) :
    ∀ v ∈ centralizerSpace H, x v = v := by
  intro v hv
  have hc_mem : c v ∈ centralizerSpace H := by
    rw [mem_centralizerSpace]
    intro h' hh'
    have hcomm : c * h' = h' * c := ((Subgroup.mem_centralizer_iff.mp hc) h' hh').symm
    have hcv : c (h' v) = h' (c v) := by
      have := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hcomm
      simpa [LinearEquiv.mul_apply] using this
    rw [← hcv, (mem_centralizerSpace.mp hv) h' hh']
  have hxv : x v = c v := by
    rw [hx, LinearEquiv.mul_apply, (mem_centralizerSpace.mp hc_mem) h hh]
  have hmem : c v - v ∈ centralizerSpace H := Submodule.sub_mem _ hc_mem hv
  have hmemV : c v - v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    have h : x v - v ∈ HardMathSupport.Kantor79.movedSpace x := by
      exact ⟨v, by simp [LinearMap.sub_apply]⟩
    have hxv' : x v - v = c v - v := by rw [hxv]
    rw [← hxv']
    exact hxV h
  have hzero : c v - v = 0 := by
    have h : c v - v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      Submodule.mem_inf.mpr ⟨hmemV, hmem⟩
    rw [hcomp.inf_eq_bot] at h
    simpa [Submodule.mem_bot] using h
  rw [sub_eq_zero.mp hzero] at hxv
  exact hxv

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_card_H_eq_48 (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ ∣ 2)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) : Nat.card H = 48 := by
  rw [← card_movedGroup_of_splitSupport S.splitSupport, hH]
  rw [card_g2mmn hp (by omega) e S.ne ζ]
  have hlcm : Nat.lcm 2 (orderOf ζ) = 2 := by
    have h : orderOf ζ = 1 ∨ orderOf ζ = 2 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hζ
    rcases h with h | h <;> rw [h] <;> norm_num
  rw [hlcm, hn]; norm_num

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_maximal_card_le (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (h4 : d = 4) (hcardH : Nat.card H = 48) :
    ∀ X ≤ G, ReflGen p X → SplitSupport X 3 → DMax p X 4 → Nat.card X ≤ 48 := by
  intro X hXG hXr hXs hXd
  have hdX : DMax p X d := by rwa [← h4] at hXd
  have hsX : SplitSupport X (Module.finrank (ZMod p) U - 1) := by
    have h : Module.finrank (ZMod p) U - 1 = 3 := by omega
    rwa [h]
  have h := S.maximal X hXG hXr hsX hdX
  rwa [hcardH] at h

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_dmax_closure_insert (S : ImpExtStd G H d e j₀ j₁ ζ) {x : U ≃ₗ[ZMod p] U}
    (hXG : Subgroup.closure (insert x (H : Set (U ≃ₗ[ZMod p] U))) ≤ G) :
    DMax p (Subgroup.closure (insert x (H : Set (U ≃ₗ[ZMod p] U)))) d := by
  refine ⟨?_, ?_⟩
  · intro y hy z hz hyr hzr
    exact S.dmax.1 y (hXG hy) z (hXG hz) hyr hzr
  · obtain ⟨y, hy, z, hz, hyr, hzr, hord⟩ := S.dmax_H.2
    exact ⟨y, Subgroup.subset_closure (Or.inr hy), z, Subgroup.subset_closure (Or.inr hz),
      hyr, hzr, hord⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4q_closure_insert_eq {x : U ≃ₗ[ZMod p] U} {f : Module.Basis (Fin 4) (ZMod p) U}
    (hXcard : Nat.card (Subgroup.closure (insert x (H : Set (U ≃ₗ[ZMod p] U)))) ≤ Nat.card H) :
    Subgroup.closure (insert x (H : Set (U ≃ₗ[ZMod p] U))) = H := by
  let X := Subgroup.closure (insert x (H : Set (U ≃ₗ[ZMod p] U)))
  change X = H
  have hHX : H ≤ X := fun y hy => Subgroup.subset_closure (Or.inr hy)
  have : Finite U := Finite.of_injective f.equivFun.toFun f.equivFun.injective
  have : Finite (U → U) := by infer_instance
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun f : U ≃ₗ[ZMod p] U => (f : U → U))
      (fun f g h => LinearEquiv.ext (congrFun h))
  have : Finite ↥X := Subtype.finite
  have : Finite ↥H := Subtype.finite
  have hcard_le : Nat.card H ≤ Nat.card X :=
    Nat.card_le_card_of_injective (fun y : H => (⟨y.val, hHX y.2⟩ : X))
      (fun a b h => Subtype.ext (congrArg (fun z : X => (z : U ≃ₗ[ZMod p] U)) h))
  have hcard_eq : Nat.card X = Nat.card H := le_antisymm hXcard hcard_le
  exact Subgroup.ext (Set.ext_iff.mp (Set.eq_of_subset_of_ncard_le hHX (by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact le_of_eq hcard_eq)).symm)

private lemma zs4q_inH_of_movedSpace_le (S : ImpExtStd G H d e j₀ j₁ ζ) (I : ImpExtInputs G H)
    (hn : Module.finrank (ZMod p) U = 4) {f : Module.Basis (Fin 4) (ZMod p) U}
    (hV_eq : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      HardMathSupport.Kantor79.commutatorSpace H) :
    ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H := by
  intro x hxG hxr hxV
  have hxV' : HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.commutatorSpace H := by rwa [hV_eq] at hxV
  have hmap : (HardMathSupport.Kantor79.commutatorSpace H).map x.toLinearMap =
      HardMathSupport.Kantor79.commutatorSpace H := zs4i_inH_map hxV'
  obtain ⟨h, hh, c, hc, hxc⟩ :=
    ImpExtSetting.mem_mul_centralizer_of_map_eq S.toImpExtSetting I.lemmaOneSeven hxG hxr
      (Or.inl hmap)
  have hxfix : ∀ v ∈ centralizerSpace H, x v = v :=
    zs4i_inH_fix hxV' hh hc hxc S.splitSupport.1
  let X := Subgroup.closure (insert x (H : Set (U ≃ₗ[ZMod p] U)))
  have hXG : X ≤ G := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact hxG
    · exact S.H_le hy
  have hXr : ReflGen p X := by
    have h := CFSG.StandardType.ZS.ReflGen.closure_insert S.reflGen_H hxr
    simpa [X] using h
  have hXs : SplitSupport X 3 := by
    have h : Module.finrank (ZMod p) U - 1 = 3 := by omega
    rw [← h]
    simpa [X] using splitSupport_closure_insert_of_fix S.splitSupport hxV' hxfix
  have hXd : DMax p X d := zs4q_dmax_closure_insert S hXG
  have hXcard : Nat.card X ≤ Nat.card H := by
    have h : Module.finrank (ZMod p) U - 1 = 3 := by omega
    have hXs' : SplitSupport X (Module.finrank (ZMod p) U - 1) := by rwa [h]
    exact S.maximal X hXG hXr hXs' hXd
  have hXH : X = H := zs4q_closure_insert_eq (x := x) (f := f) hXcard
  have hxX : x ∈ X := Subgroup.subset_closure (Or.inl rfl)
  rwa [hXH] at hxX

private lemma zs4q_map_ne_of_not_mem (S : ImpExtStd G H d e j₀ j₁ ζ) (I : ImpExtInputs G H)
    {f : Module.Basis (Fin 4) (ZMod p) U} {g : U ≃ₗ[ZMod p] U}
    (hV_eq : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      HardMathSupport.Kantor79.commutatorSpace H)
    (hgG : g ∈ G) (hgr : IsRefl p g)
    (hg_not_mem : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)),
      g = h * c) :
    (Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)).map g.toLinearMap ≠
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  intro hmap
  rw [hV_eq] at hmap
  exact hg_not_mem (ImpExtSetting.mem_mul_centralizer_of_map_eq S.toImpExtSetting I.lemmaOneSeven
    hgG hgr (Or.inl hmap))

private lemma zs4q_apply_not_mem_of_not_mem (S : ImpExtStd G H d e j₀ j₁ ζ)
    (I : ImpExtInputs G H) {f : Module.Basis (Fin 4) (ZMod p) U} {g : U ≃ₗ[ZMod p] U}
    (hf₃ : f 3 ∈ centralizerSpace H) (hgG : g ∈ G) (hgr : IsRefl p g)
    (hg_not_mem : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)),
      g = h * c) :
    g (f 3) ∉ Submodule.span (ZMod p) {f 3} := by
  intro hmem
  have hline : Submodule.span (ZMod p) {f 3} = centralizerSpace H := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; exact Set.singleton_subset_iff.mpr hf₃
    · rw [finrank_span_singleton (f.ne_zero 3),
        ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting]
  have hmap : (centralizerSpace H).map g.toLinearMap = centralizerSpace H := by
    rw [← hline]
    have hle : (Submodule.span (ZMod p) {f 3}).map g.toLinearMap ≤
        Submodule.span (ZMod p) {f 3} := by
      rw [Submodule.map_span]
      simpa using Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g _)
  exact hg_not_mem (ImpExtSetting.mem_mul_centralizer_of_map_eq S.toImpExtSetting I.lemmaOneSeven
    hgG hgr (Or.inr hmap))

theorem exists_fFourData (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) (I : ImpExtInputs G H)
    (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ ∣ 2)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (a b c g : U ≃ₗ[ZMod p] U),
      FFourData f a b c g H G := by
  obtain ⟨f, σ, hσ₀, hσ₁, hf, hf₃⟩ := exists_basis_castSucc S hn
  obtain ⟨a, haH, hacta, ha_mat⟩ := zs4q_exists_a hH hσ₀ hf hf₃
  obtain ⟨b, hbH, hactb, hb_mat⟩ := zs4q_exists_b hH hσ₀ hσ₁ hf hf₃
  obtain ⟨c, hcH, hactc, hc_mat⟩ := zs4q_exists_c hH hσ₁ hf hf₃
  obtain ⟨g, hgG, hgr, hg_not_mem⟩ := S.exists_isRefl_not_mem_mul hp
  have hζ' : ζ * ζ = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hζ
  have hH_eq : H = Subgroup.closure {a, b, c} :=
    zs4q_H_eq S hH hζ' hσ₀ hσ₁ haH hbH hcH hacta hactb hactc
  have hV_eq : Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      HardMathSupport.Kantor79.commutatorSpace H := zs4q_span_eq hf
  have hd4 : d = 4 := dmax_eq_four_of_orderOf_dvd_two hp S hn hζ hH
  have hsplit : SplitOfIrred p G 3 := by
    have h : Module.finrank (ZMod p) U - 1 = 3 := by omega
    rw [← h]; exact I.splitOfIrred
  have hcardH : Nat.card H = 48 := zs4q_card_H_eq_48 hp S hn hζ hH
  have hmax : ∀ X ≤ G, ReflGen p X → SplitSupport X 3 → DMax p X 4 → Nat.card X ≤ 48 :=
    zs4q_maximal_card_le S hn hd4 hcardH
  have hInH : ∀ x ∈ G, IsRefl p x → HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) → x ∈ H :=
    zs4q_inH_of_movedSpace_le S I hn hV_eq
  refine ⟨f, a, b, c, g, ?_⟩
  refine {
    toMatrix_a := ha_mat
    toMatrix_b := hb_mat
    toMatrix_c := hc_mat
    H_eq := hH_eq
    H_le := S.H_le
    g_mem := hgG
    isRefl_g := hgr
    map_ne := zs4q_map_ne_of_not_mem S I hV_eq hgG hgr hg_not_mem
    apply_not_mem := zs4q_apply_not_mem_of_not_mem S I hf₃ hgG hgr hg_not_mem
    irred := I.lemmaOneSeven g hgG hgr hg_not_mem
    reflGen := S.reflGen
    primitive := S.primitive
    transvectionFree := S.transvectionFree
    dmax := by rw [← hd4]; exact S.dmax
    splitOfIrred := hsplit
    maximal := hmax
    inH := hInH }

theorem eq_weylF4_or_eq_isIsom (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (I : ImpExtInputs G H) (hn : Module.finrank (ZMod p) U = 4) (hζ : orderOf ζ ∣ 2)
    (hH : movedGroup H = g2mmn p e j₀ j₁ ζ) :
    (∃ f : Module.Basis (Fin 4) (ZMod p) U, G = basisClosure f weylF4Mats) ∨
      (p = 3 ∧ ∃ f : Module.Basis (Fin 4) (ZMod p) U, ∀ x, x ∈ G ↔ IsIsom p (phiForm f) x) := by
  obtain ⟨f, a, b, c, g, h⟩ := exists_fFourData hp S I hn hζ hH
  exact h.eq_weylF4_or_eq_isIsom hp I.smallThree

end ImpExtStd

end CFSG.StandardType.ZS

end
