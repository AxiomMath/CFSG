module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalfKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionCount
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalBase
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLang

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExcTwoFusion CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace TableBExcTwoTB

section Aux

variable
  {τ : Tag}

@[expose] def pairChar (τ : Tag) (X : Set (Fin τ.rank → ZMod 3)) :
    Multiplicative (Fin τ.rank → ℤ) →* Multiplicative (X → ZMod 3) where
  toFun α := Multiplicative.ofAdd fun x => rootPairing τ (Multiplicative.toAdd α) x.1
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext x
    simp [rootPairing]
  map_mul' α β := by
    apply Multiplicative.toAdd.injective
    funext x
    simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply, rootPairing, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_mul, ← Int.cast_add, ← Finset.sum_add_distrib]
    congr 3
    ext j
    ring

theorem mem_kernelRoots_pairChar {X : Set (Fin τ.rank → ZMod 3)} {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots (pairChar τ X) ↔ IsRoot τ α ∧ ∀ x ∈ X, rootPairing τ α x = 0 := by
  change IsRoot τ α ∧ pairChar τ X (Multiplicative.ofAdd α) = 1 ↔
    IsRoot τ α ∧ ∀ x ∈ X, rootPairing τ α x = 0
  constructor
  · rintro ⟨hroot, hker⟩
    have hzero : (fun x : X => rootPairing τ α x.1) = 0 :=
      ofAdd_eq_one.mp hker
    exact ⟨hroot, fun x hx => congr_fun hzero ⟨x, hx⟩⟩
  · rintro ⟨hroot, h⟩
    exact ⟨hroot, ofAdd_eq_one.mpr (funext fun x => h x.1 x.2)⟩

theorem mem_kernelWeylGroup_pairChar {X C : Set (Fin τ.rank → ZMod 3)} (hXC : X ⊆ C)
    {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {r : WeylGroup τ | ∃ (u : WeylGroup τ) (j : Fin τ.rank),
      (∀ x ∈ C, rootPairing τ (u • (Pi.single j 1 : Fin τ.rank → ℤ)) x = 0) ∧
        r = u * simple τ j * u⁻¹}) :
    w ∈ kernelWeylGroup (pairChar τ X) := by
  show w ∈ Subgroup.closure {r : WeylGroup τ | ∃ (u : WeylGroup τ) (j : Fin τ.rank),
    u • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ kernelRoots (pairChar τ X) ∧
      r = u * simple τ j * u⁻¹}
  refine Subgroup.closure_mono ?_ hw
  rintro r ⟨u, j, hu, rfl⟩
  exact ⟨u, j, (mem_kernelRoots_pairChar.2
    ⟨IsRoot.smul (isRoot_single τ j) u, fun x hx => hu x (hXC hx)⟩), rfl⟩

private theorem three_dvd_sum_cartan_mul_val {α : Fin τ.rank → ℤ} {x : Fin τ.rank → ZMod 3}
    (h : rootPairing τ α x = 0) :
    (3 : ℤ) ∣ ∑ i, (∑ j, τ.cartan i j * α j) * ((x i).val : ℤ) := by
  have hcast : rootPairing τ α x =
      (((∑ i, (∑ j, τ.cartan i j * α j) * ((x i).val : ℤ)) : ℤ) : ZMod 3) := by
    rw [rootPairing, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [h] at hcast
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hcast.symm

private theorem torusRootChar_chevTorus {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin τ.rank → ZMod 3) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar ((chevTorus τ ζ hζ (Multiplicative.ofAdd x) : adjointGroup τ K) :
      ModGL τ K) α =
      ((ζ ^ (∑ i, (∑ j, τ.cartan i j * α j) * ((x i).val : ℤ)) : Kˣ) : K) := by
  rw [coe_chevTorus]
  simp only [toAdd_ofAdd]
  have h1 : torusRootChar ((List.ofFn fun i => torusElt τ K i
      (zmodPowHom ζ hζ (Multiplicative.ofAdd (x i)))).prod) α =
      ((∏ i, (zmodPowHom ζ hζ (Multiplicative.ofAdd (x i))) ^
        (∑ j, τ.cartan i j * α j) : Kˣ) : K) := by
    apply torusRootChar_eq_of_apply hα
    have h := list_prod_torusElt_rootVec (R := K) (α := α) hα
      (List.ofFn fun i => (i, zmodPowHom ζ hζ (Multiplicative.ofAdd (x i))))
    rw [List.map_ofFn] at h
    have hfun : ((fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∘
        fun i => (i, zmodPowHom ζ hζ (Multiplicative.ofAdd (x i)))) =
        (fun i => torusElt τ K i (zmodPowHom ζ hζ (Multiplicative.ofAdd (x i)))) := by
      funext i; rfl
    rw [hfun] at h
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply] at h
    simpa only [List.prod_ofFn, Function.comp_apply] using h
  rw [h1]
  congr 1
  trans ∏ i, (ζ : Kˣ) ^ ((∑ j, τ.cartan i j * α j) * ((x i).val : ℤ))
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [zmodPowHom_apply, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  · rw [Finset.prod_zpow_eq_zpow_sum]

theorem rootSpan_le_centralizer_baseChange_chevTorus {K₂ L : Type} [Field K₂] [Field L]
    (ψ : K₂ →+* L) {ζ : K₂ˣ} (hζ : ζ ^ 3 = 1) (x : Fin τ.rank → ZMod 3)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α ∧ rootPairing τ α x = 0) :
    rootSpan τ L S ≤ Subgroup.centralizer
      {baseChangeGL ψ ((chevTorus τ ζ hζ (Multiplicative.ofAdd x) : adjointGroup τ K₂) :
        ModGL τ K₂)} := by
  have hd : ((chevTorus τ ζ hζ (Multiplicative.ofAdd x) : adjointGroup τ K₂) :
      ModGL τ K₂) ∈ torusGroup τ K₂ := coe_chevTorus_mem_torusGroup hζ _
  have hdL : baseChangeGL ψ ((chevTorus τ ζ hζ (Multiplicative.ofAdd x) :
      adjointGroup τ K₂) : ModGL τ K₂) ∈ torusGroup τ L :=
    CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup ψ hd
  refine iSup₂_le fun α hαS => ?_
  rw [rootSubgroup]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  refine ((commute_pinnedX_iff hdL (hS α hαS).1).2 ?_ c).symm
  rw [CFSG.ComponentClassification.Burgoyne.E2.torusRootChar_baseChangeGL ψ _
    (hS α hαS).1]
  have hchar : torusRootChar ((chevTorus τ ζ hζ (Multiplicative.ofAdd x) :
      adjointGroup τ K₂) : ModGL τ K₂) α = 1 := by
    rw [torusRootChar_chevTorus hζ x (hS α hαS).1]
    obtain ⟨k, hk⟩ := three_dvd_sum_cartan_mul_val (hS α hαS).2
    have hz : (ζ : K₂ˣ) ^ (∑ i, (∑ j, τ.cartan i j * α j) * ((x i).val : ℤ)) = 1 := by
      rw [hk, zpow_mul]
      rw [show (ζ : K₂ˣ) ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; exact hζ]
      exact one_zpow k
    rw [hz]
    exact Units.val_one
  rw [hchar, map_one]

theorem mul_comm_baseChangeGL_of_mem_rootSpan {K₂ L : Type} [Field K₂] [Field L]
    (ψ : K₂ →+* L) {ζ : K₂ˣ} (hζ : ζ ^ 3 = 1) {E : Subgroup (adjointGroup τ K₂)}
    {g : ModGL τ L}
    (hg : g ∈ rootSpan τ L
      (kernelRoots (pairChar τ ((torusSet hζ E : AddSubgroup (Fin τ.rank → ZMod 3)) :
        Set (Fin τ.rank → ZMod 3)))))
    {e : adjointGroup τ K₂} (he : e ∈ E) (heV : e ∈ (chevTorus τ ζ hζ).range) :
    g * baseChangeGL ψ (e : ModGL τ K₂) = baseChangeGL ψ (e : ModGL τ K₂) * g := by
  obtain ⟨y, hy⟩ := heV
  set x : Fin τ.rank → ZMod 3 := Multiplicative.toAdd y with hx
  have heq : e = chevTorus τ ζ hζ (Multiplicative.ofAdd x) := by
    rw [← hy]
    exact congrArg (chevTorus τ ζ hζ) (ofAdd_toAdd y).symm
  have hxE : x ∈ torusSet hζ E := by
    rw [mem_torusSet, ← heq]
    exact he
  have hS : ∀ α ∈ kernelRoots (pairChar τ
      ((torusSet hζ E : AddSubgroup (Fin τ.rank → ZMod 3)) :
        Set (Fin τ.rank → ZMod 3))), IsRoot τ α ∧ rootPairing τ α x = 0 := by
    intro α hα
    obtain ⟨hr, hz⟩ := (mem_kernelRoots_pairChar).1 hα
    exact ⟨hr, hz x hxE⟩
  have hmem := rootSpan_le_centralizer_baseChange_chevTorus ψ hζ x hS hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  have heq' : (e : ModGL τ K₂) =
      ((chevTorus τ ζ hζ (Multiplicative.ofAdd x) : adjointGroup τ K₂) : ModGL τ K₂) :=
    congrArg (fun z : adjointGroup τ K₂ => (z : ModGL τ K₂)) heq
  rw [heq']
  exact hmem

theorem weylQuotientHom_baseChangeGL {K₂ L : Type} [Field K₂] [Field L] (ψ : K₂ →+* L)
    {m : ModGL τ K₂} (hm : m ∈ monomialSubgroup τ K₂) :
    weylQuotientHom τ L ⟨baseChangeGL ψ m, baseChangeGL_mem_monomialSubgroup ψ hm⟩ =
      weylQuotientHom τ K₂ ⟨m, hm⟩ := by
  refine weylQuotientHom_eq ?_
  exact CFSG.LieType.AlgebraicGroups.MapsRootLines.baseChangeGL ψ
    (mapsRootLines_weylQuotientHom ⟨m, hm⟩)

end Aux

end TableBExcTwoTB

end CFSG.StandardType

end
