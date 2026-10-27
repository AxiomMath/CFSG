module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGResIICell
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGTWReflConj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJTwoNodeParabolic {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    {M : CoxeterMatrix (Fin n)} (hM : M = CoxeterMatrix.A n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.A n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V}
    {φ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range (φ ∘ Fin.castLE (by omega : n - 2 ≤ n)))) :
    GGResTwoNodeSideDatum p Bs X J := by
  let b₁ : Fin n := ⟨n - 2, by omega⟩
  let b₂ : Fin n := ⟨n - 1, by omega⟩
  have hb : b₁ ≠ b₂ := by
    intro h
    have : (n - 2) = (n - 1) := congrArg Fin.val h
    omega
  let Jset : Set (Fin n) := {j | j ≠ b₁ ∧ j ≠ b₂}
  let eJ : Jset ≃ Fin (n - 2) :=
    { toFun := fun j => ⟨j.val.val, by
        have h1 : j.val.val ≠ n - 2 := by
          intro h
          exact j.property.1 (Fin.ext h)
        have h2 : j.val.val ≠ n - 1 := by
          intro h
          exact j.property.2 (Fin.ext h)
        have hj : j.val.val < n := j.val.isLt
        omega⟩
      invFun := fun i => ⟨⟨i.val, by omega⟩, by
        constructor
        · intro h
          have : i.val = n - 2 := congrArg Fin.val h
          omega
        · intro h
          have : i.val = n - 1 := congrArg Fin.val h
          omega⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by ext; rfl }
  let MJ : CoxeterMatrix Jset := CFSG.Monster.B.Geometry.parMatrix M Jset
  let CJ : Matrix Jset Jset ℤ := fun j j' => (CartanMatrix.A (n - 2)) (eJ j) (eJ j')
  have hMJ_eq : MJ = (CoxeterMatrix.A (n - 2)).reindex eJ.symm := by
    ext j j'
    change M.M j.val j'.val = ((CoxeterMatrix.A (n - 2)).reindex eJ.symm).M j j'
    rw [hM]
    simp [CoxeterMatrix.reindex_apply, CoxeterMatrix.A, eJ, Fin.ext_iff]
  have hWM : GGIsWeylMatrix M := by
    rw [hM]
    exact ggResII_isWeyl_A (by omega)
  have hMC : GGIntCartan M C := by
    rw [hM, hC]
    exact ggIntCartan_A n
  have hWMJ : GGIsWeylMatrix MJ := by
    rw [hMJ_eq]
    exact l05nBL_weyl_reindex (ggResII_isWeyl_A (by omega)) eJ.symm
  have hMCJ : GGIntCartan MJ CJ := by
    rw [hMJ_eq]
    exact l05nBL_intCartan_reindex (ggIntCartan_A (n - 2)) eJ
  have hMJ_sub : ∀ j j' : Jset, MJ.M j j' = M.M j j' := by
    intro j j'
    rfl
  have hCJ_sub : ∀ j j' : Jset, CJ j j' = C j j' := by
    intro j j'
    dsimp [CJ, eJ, b₁, b₂]
    rw [hC]
    simp [CartanMatrix.A, Fin.ext_iff]
  let cs := M.toCoxeterSystem
  let gSub : MJ.Group →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp (parToGroup cs Jset)
  let g : MJ.Group →* MulAut ↥Bs := (Subgroup.subtype (ggAutomizer X Bs)).comp gSub
  have hg_simple : ∀ j : Jset, g (MJ.simple j) = φ j := by
    intro j
    change (f (parToGroup cs Jset (MJ.simple j)) : MulAut Bs) = _
    rw [parToGroup_simple]
    exact hf j
  have hg_inj : Function.Injective g := by
    intro x y h
    exact f.injective.comp (parToGroup_injective cs Jset) (Subtype.ext h)
  have hg_mem : ∀ x : MJ.Group, g x ∈ ggAutomizer J Bs := by
    have hle : Subgroup.closure (Set.range (MJ.simple)) ≤
        Subgroup.comap g (ggAutomizer J Bs) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      change g (MJ.simple j) ∈ ggAutomizer J Bs
      rw [hg_simple, hJ]
      have hj : j.val.val < n - 2 := by
        have h1 : j.val.val ≠ n - 2 := by
          intro h
          exact j.property.1 (Fin.ext h)
        have h2 : j.val.val ≠ n - 1 := by
          intro h
          exact j.property.2 (Fin.ext h)
        have hjlt : j.val.val < n := j.val.isLt
        omega
      let i : Fin (n - 2) := ⟨j.val.val, hj⟩
      have hi : Fin.castLE (by omega : n - 2 ≤ n) i = j.val := by
        ext
        rfl
      rw [← hi]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    intro x
    have hx : x ∈ Subgroup.closure (Set.range (MJ.simple)) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple,
        (MJ.toCoxeterSystem).subgroup_closure_range_simple]
      exact Subgroup.mem_top x
    exact hle hx
  let g' : MJ.Group →* ↥(ggAutomizer J Bs) :=
    { toFun := fun x => ⟨g x, hg_mem x⟩
      map_one' := by ext; simp [g]
      map_mul' := by intro x y; ext; simp [g] }
  have hg'_inj : Function.Injective g' := by
    intro x y hxy
    apply hg_inj
    exact congrArg (fun z : ggAutomizer J Bs => (z : MulAut Bs)) hxy
  have hg'_surj : Function.Surjective g' := by
    intro y
    have hy : (y : MulAut ↥Bs) ∈ Subgroup.closure (Set.range (φ ∘ Fin.castLE (by omega : n - 2 ≤ n))) := by
      rw [← hJ]
      exact y.property
    have h : ∃ a : MJ.Group, (g' a : MulAut ↥Bs) = (y : MulAut ↥Bs) := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro x hx
        rcases hx with ⟨i, rfl⟩
        refine ⟨MJ.simple (eJ.symm i), ?_⟩
        change g (MJ.simple (eJ.symm i)) = φ (Fin.castLE _ i)
        rw [hg_simple]
        congr 1
      · exact ⟨1, by change g 1 = 1; exact g.map_one⟩
      · intro x z hx hz ihx ihz
        rcases ihx with ⟨a, ha⟩
        rcases ihz with ⟨b, hb'⟩
        refine ⟨a * b, ?_⟩
        change g (a * b) = x * z
        rw [map_mul]
        exact congrArg₂ (· * ·) ha hb'
      · intro x hx ih
        rcases ih with ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        change g a⁻¹ = x⁻¹
        rw [map_inv]
        exact congrArg Inv.inv ha
    rcases h with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  let fJ : MJ.Group ≃* ↥(ggAutomizer J Bs) :=
    MulEquiv.ofBijective g' ⟨hg'_inj, hg'_surj⟩
  have hfJ : ∀ j : Jset, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j := by
    intro j
    exact hg_simple j
  have hALJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j) := by
    rw [hJ]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨eJ.symm i, ?_⟩
      exact congrArg φ (Fin.ext rfl)
    · rintro ⟨j, rfl⟩
      refine ⟨eJ j, ?_⟩
      exact congrArg φ (Fin.ext rfl)
  let φJ : Jset → MulAut ↥Bs := fun j => φ j.val
  let hJfun : Jset → V := fun j => h j.val
  let αJ : Jset → Module.Dual (ZMod p) V := fun j => α j.val
  have hpairJ : ∀ j j', αJ j (hJfun j') = (CJ j j' : ZMod p) := by
    intro j j'
    change α j (h j') = (CJ j j' : ZMod p)
    rw [hCJ_sub]
    exact hpair j j'
  have hlinJ : ∀ j w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJfun j := by
    intro j w
    exact hlin j.val w
  have hreflJ : ∀ j, GGIsReflection p (φJ j) := by
    intro j
    exact hrefl j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j) := by
    have hcomm : ∀ a b : Bs, a * b = b * a := by
      intro a b
      apply Additive.ofMul.injective
      apply ι.injective
      change ι (Additive.ofMul a + Additive.ofMul b) =
        ι (Additive.ofMul b + Additive.ofMul a)
      rw [map_add, map_add, add_comm]
    have hpow : ∀ b : Bs, b ^ p = 1 := by
      intro b
      apply Additive.ofMul.injective
      apply ι.injective
      rw [ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p),
        ZMod.natCast_self, zero_smul, ofMul_one, map_zero]
    have hBs : IsElemAbelian p Bs := by
      have h := isElemAbelian_range hcomm hpow Bs.subtype
      rwa [Subgroup.range_subtype] at h
    intro s hs hr
    exact ggTW_refl_conj_of_typeA hp (by omega : 2 ≤ n - 2) hBs eJ.symm hMJ_eq
      (ggAutomizer J Bs) fJ (fun j : Jset => φ j) hfJ hreflJ s hs hr
  refine ⟨Fin n, inferInstance, inferInstance, b₁, b₂, M, C, MJ, V, inferInstance, inferInstance,
    ι, φ, h, α, hb, hWM, hMC, hWMJ, hMJ_sub, hlin, hrefl, hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩,
    hALJ, hconjJ⟩

end CFSG.StandardType

end
