module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGReflShape
public import CFSG.LocalAnalysis.StandardType.GGReflModule
public import CFSG.LocalAnalysis.StandardType.GGWeylReflection
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem

theorem ggNoTransvection_of_le_automizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : A ≤ ggAutomizer ⊤ Bs) : ∀ φ ∈ A, ¬ GGIsTransvection p φ := by
  intro φ hφA
  have hφ : φ ∈ ggInduced ⊤ Bs := by
    refine Subgroup.closure_induction (p := fun ψ _ => ψ ∈ ggInduced ⊤ Bs) ?_ ?_ ?_ ?_
      (hA hφA)
    · rintro ψ ⟨g, -, hgN, hg⟩
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
    · exact one_mem_ggInduced ⊤ Bs
    · intro ψ χ _ _ h1 h2
      exact mul_mem_ggInduced h1 h2
    · intro ψ _ h
      exact inv_mem_ggInduced h
  exact hNT φ hφ

private theorem ggCoxRefl_of_isReflection_aux {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hodd : p ≠ 2) {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hM : GGIsWeylMatrix (coxeterMatrix hC))
    (h3 : ∀ i j : ι, i ≠ j → (coxeterMatrix hC).M i j ≤ 3)
    (hInt : GGIntCartan (coxeterMatrix hC) C) {e : (coxeterMatrix hC).Group ≃* ↥A}
    (hrefl : ∀ i : ι, GGIsReflection p ((e ((coxeterMatrix hC).simple i) : ↥A) : MulAut ↥Bs))
    (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (ι' : Additive ↥Bs ≃+ V) {r : MulAut ↥Bs} (hrA : r ∈ A)
    (hr : GGIsReflection p r) : r ∈ ggCoxRefl (coxeterMatrix hC) e := by
  obtain ⟨h, f, hfh, hshape⟩ := ggRefl_shape (p := p) (hp2 := hodd) hM h3 hrefl hnt hInt ι'
  let ρ : (coxeterMatrix hC).Group →* (V ≃ₗ[ZMod p] V) :=
    (ggLin (p := p) ι').comp
      ((A.subtype : ↥A →* MulAut ↥Bs).comp e.toMonoidHom)
  have hρ : ∀ i v, ρ ((coxeterMatrix hC).toCoxeterSystem.simple i) v =
      v - f i v • h i := by
    intro i v
    rw [CoxeterMatrix.toCoxeterSystem_simple]
    change ggLin (p := p) ι' (A.subtype (e ((coxeterMatrix hC).simple i))) v =
      v - f i v • h i
    exact hshape i v
  let t : (coxeterMatrix hC).Group := e.symm ⟨r, hrA⟩
  have het : e t = ⟨r, hrA⟩ := by
    change e (e.symm ⟨r, hrA⟩) = ⟨r, hrA⟩
    exact e.apply_symm_apply _
  have hrr : r * r = 1 := by
    rw [← pow_two]
    exact hr.1
  have ht2 : t * t = 1 := by
    apply e.injective
    rw [map_mul, map_one, het]
    exact Subtype.ext hrr
  have htρ : ρ t = ggLin (p := p) ι' r := by
    change ggLin (p := p) ι' (A.subtype (e (e.symm ⟨r, hrA⟩))) = ggLin (p := p) ι' r
    rw [e.apply_symm_apply]
    rfl
  have hr' := (ggIsReflection_iff (p := p) ι' r).mp hr
  have hT : (ρ t) ^ 2 = 1 := by
    rw [htρ, ← map_pow, hr.1, map_one]
  have hfix : Nat.card {v : V // (ρ t) v = v} * p = Nat.card V := by
    rw [htρ]
    exact hr'.2
  have hdim1 : Module.finrank (ZMod p)
      (LinearMap.ker ((ρ t).toLinearMap + 1)) = 1 :=
    ggFinrank_minus_eq_one hodd (ρ t) hT hfix
  have hle : LinearMap.ker ((ρ t).toLinearMap + 1) ≤
      Submodule.span (ZMod p) (Set.range h) := by
    intro v hv
    have hv' : ρ t v = -v := by
      have h0 : ρ t v + v = 0 := by
        simpa using (LinearMap.mem_ker.mp hv)
      exact eq_neg_of_add_eq_zero_left h0
    have hmem : ρ t v - v ∈ Submodule.span (ZMod p) (Set.range h) :=
      ggRefl_sub_mem hC h f ρ hρ t v
    have h2mem : (2 : ZMod p) • v ∈ Submodule.span (ZMod p) (Set.range h) := by
      have hEq : (2 : ZMod p) • v = -(ρ t v - v) := by
        rw [hv', two_smul]
        abel
      rw [hEq]
      exact Submodule.neg_mem _ hmem
    have h2ne : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (p := p) hodd
    have hv_eq : v = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • v) := by
      rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul]
    rw [hv_eq]
    exact Submodule.smul_mem _ _ h2mem
  have hfr : Module.finrank (ZMod p)
      ↥(LinearMap.ker ((ρ t).toLinearMap + 1) ⊓
        Submodule.span (ZMod p) (Set.range h)) = 1 := by
    rw [inf_eq_left.mpr hle]
    exact hdim1
  have hrat : Module.finrank ℚ
      (LinearMap.ker (Matrix.toLin' ((ggWeylMat hC t).map (Int.castRingHom ℚ) + 1))) = 1 := by
    rw [← ggRefl_minus_finrank hC hodd h f hfh ρ hρ t ht2]
    exact hfr
  obtain ⟨g, i, htg⟩ := ggWeyl_isReflection_of_finrank hC t ht2 hrat
  rw [CoxeterMatrix.toCoxeterSystem_simple] at htg
  refine ⟨g, i, ?_⟩
  have hee : (⟨r, hrA⟩ : ↥A) = e (g * (coxeterMatrix hC).simple i * g⁻¹) := by
    have h1 : e t = e (g * (coxeterMatrix hC).simple i * g⁻¹) := congrArg e htg
    rwa [het] at h1
  have hval := congrArg (fun x : ↥A => ((x : MulAut ↥Bs))) hee
  simpa using hval

theorem ggCoxRefl_of_isReflection {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {A : Subgroup (MulAut ↥Bs)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (hpres : GGCoxeterPres p A M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ)
    {r : MulAut ↥Bs} (hrA : r ∈ A) (hr : GGIsReflection p r) : r ∈ ggCoxRefl M e := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfin : Finite ι := ggIsWeylMatrix_finite hpres.1
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨C, hC, hInt, hcox⟩ := ggWeylCartan hpres.1 h3
  subst hcox
  letI : AddCommGroup (Additive ↥Bs) :=
    { (inferInstance : AddGroup (Additive ↥Bs)) with
      add_comm := fun a b => by
        have h := hBs.1.is_comm.comm (Additive.toMul a) (Additive.toMul b)
        exact congrArg Additive.ofMul h }
  letI : Module (ZMod p) (Additive ↥Bs) :=
    AddCommGroup.zmodModule (n := p) fun a => by
      have h : (Additive.toMul a) ^ p = 1 := Subtype.ext (hBs.2 _ (Additive.toMul a).2)
      rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  haveI : Finite (Additive ↥Bs) := inferInstanceAs (Finite ↥Bs)
  exact ggCoxRefl_of_isReflection_aux (p := p) (Bs := Bs) (A := A) (ι := ι) (C := C) hodd hC
    hpres.1 h3 hInt hpres.2 hnt (AddEquiv.refl _) hrA hr

end CFSG.StandardType
