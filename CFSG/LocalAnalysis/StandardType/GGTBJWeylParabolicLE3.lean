module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tbP_parabolicRestricted
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Λ : Type}
    {M : CoxeterMatrix Λ} {φ : Λ → MulAut ↥Bs}
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (Jset : Set Λ) [Fintype Jset] [DecidableEq Jset]
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j.1))
    (hRC : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j.1)) :
    (∃ fJ : (parMatrix M Jset).Group ≃* ↥(ggAutomizer J Bs),
        ∀ j : Jset, (fJ ((parMatrix M Jset).simple j) : MulAut ↥Bs) = φ j.1) ∧
      (ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j.1)) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j.1) := by
  classical
  let MJ : CoxeterMatrix Jset := parMatrix M Jset
  let cs := M.toCoxeterSystem
  let gSub : MJ.Group →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp (parToGroup cs Jset)
  let g : MJ.Group →* MulAut ↥Bs := (Subgroup.subtype (ggAutomizer X Bs)).comp gSub
  have hg_simple : ∀ j : Jset, g (MJ.simple j) = φ j := by
    intro j
    change (f (parToGroup cs Jset (MJ.simple j)) : MulAut ↥Bs) = _
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
      exact Subgroup.subset_closure ⟨j, rfl⟩
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
    exact congrArg (fun z : ggAutomizer J Bs => (z : MulAut ↥Bs)) hxy
  have hg'_surj : Function.Surjective g' := by
    intro y
    have hy : (y : MulAut ↥Bs) ∈ Subgroup.closure (Set.range fun j : Jset => φ j.1) := by
      rw [← hJ]
      exact y.property
    have h : ∃ a : MJ.Group, (g' a : MulAut ↥Bs) = (y : MulAut ↥Bs) := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro x hx
        rcases hx with ⟨i, rfl⟩
        refine ⟨MJ.simple i, ?_⟩
        change g (MJ.simple i) = φ i.1
        exact hg_simple i
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
  exact ⟨⟨fJ, hfJ⟩, hJ, hRC⟩

theorem ggTBJWeylParabolicLE3 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M) (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)} (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (T : Finset Λ) (hT1 : 1 ≤ T.card) (hT3 : T.card ≤ 3)
    (hJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Λ // j ∉ T} => φ j.1))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Λ | j ∉ T}))
    (hRC : GGReflConjSimple p (ggAutomizer J Bs) fun j : {j : Λ // j ∉ T} => φ j.1) :
    (∀ b : Λ, T = {b} → GGResSideDatum p Bs X J) ∧
      (2 ≤ T.card → GGResLeviSideDatumLE3 p Bs X J) := by
  constructor
  · intro b hT
    obtain ⟨⟨fJ0, hfJ0⟩, hALJ0, hconj0⟩ :=
      tbP_parabolicRestricted (p := p) (X := X) (J := J) (f := f)
        (Jset := {j : Λ | j ∉ T}) hf hJ hRC
    let e : {j : Λ // j ≠ b} ≃ {j : Λ // j ∉ T} :=
      { toFun := fun j => ⟨j.1, by rw [hT]; simpa using j.2⟩
        invFun := fun j => ⟨j.1, by
          obtain ⟨x, hx⟩ := j
          rw [hT] at hx
          simpa using hx⟩
        left_inv := fun j => by ext; rfl
        right_inv := fun j => by ext; rfl }
    let P := parMatrix M {j : Λ | j ∉ T}
    let MJ : CoxeterMatrix {j : Λ // j ≠ b} := P.reindex e.symm
    have hWMJ' : GGIsWeylMatrix MJ := l05nBL_weyl_reindex hWMJ e.symm
    have hMJ_sub : ∀ j j' : {j : Λ // j ≠ b}, MJ.M j j' = M.M j j' := by
      intro j j'
      rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm]
      rfl
    let fJ' : MJ.Group ≃* ↥(ggAutomizer J Bs) := (P.reindexGroupEquiv e.symm).trans fJ0
    have hfJ' : ∀ j : {j : Λ // j ≠ b}, (fJ' (MJ.simple j) : MulAut ↥Bs) = φ j := by
      intro j
      change fJ0 ((P.reindexGroupEquiv e.symm) ((P.reindex e.symm).simple j)) = φ j
      rw [CoxeterMatrix.reindexGroupEquiv_apply_simple, Equiv.symm_symm]
      exact hfJ0 (e j)
    have hALJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b} => φ j) := by
      rw [hALJ0]
      congr 1
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
    have hconjJ' : GGReflConjSimple p (ggAutomizer J Bs)
        (fun j : {j : Λ // j ≠ b} => φ j) := by
      intro t ht hr
      obtain ⟨w, hw, i, hi⟩ := hconj0 t ht hr
      exact ⟨w, hw, e.symm i, hi⟩
    exact ⟨Λ, inferInstance, inferInstance, b, M, C, MJ, V, inferInstance, inferInstance,
      ι, φ, h, α, hWM, hMC, hWMJ', hMJ_sub, hlin, hrefl, hpair, ⟨f, hf⟩, hclos,
      ⟨fJ', hfJ'⟩, hALJ', hconjJ'⟩
  · intro h2
    obtain ⟨⟨fJ, hfJ⟩, hALJ, hconjJ⟩ :=
      tbP_parabolicRestricted (p := p) (X := X) (J := J) (f := f)
        (Jset := {j : Λ | j ∉ T}) hf hJ hRC
    have hMJ_sub : ∀ j j' : {j : Λ // j ∉ T},
        (parMatrix M {j : Λ | j ∉ T}).M j j' = M.M j j' := fun _ _ => rfl
    exact ⟨Λ, inferInstance, inferInstance, T, M, C, parMatrix M {j : Λ | j ∉ T}, V,
      inferInstance, inferInstance, ι, φ, h, α, h2, hT3, hWM, hMC, hWMJ, hMJ_sub, hlin, hrefl,
      hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hALJ, hconjJ⟩

end CFSG.StandardType

end
