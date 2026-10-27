module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis
public import CFSG.Open.MatrixModelCore
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.Group
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

open scoped Matrix

section Matrices

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem toGL_mulVec_basis (b : Module.Basis ι K V) (f : V ≃ₗ[K] V) (w : V) :
    (b.toGL f : Matrix ι ι K) *ᵥ b.equivFun w = b.equivFun (f w) := by
  have h1 : (Matrix.GeneralLinearGroup.toLin' b (b.toGL f)).toLinearEquiv w = f w := by
    rw [Module.Basis.toLin'_toGL]
    rfl
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at h1
  apply b.equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply, ← h1,
    Fintype.linearCombination_apply]
  rfl

theorem matrix_eq_of_mulVec_eq (A B : Matrix ι ι K) (h : ∀ x : ι → K, A *ᵥ x = B *ᵥ x) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem vecMulVec_mulVec_basis (u v x : ι → K) :
    Matrix.vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dotProduct_eq_form (b : Module.Basis ι K V) (φ : V →ₗ[K] K) (x : ι → K) :
    (fun i => φ (b i)) ⬝ᵥ x = φ (b.equivFun.symm x) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem toGL_eq_one_add_of_transv (b : Module.Basis ι K V) (φ : V →ₗ[K] K) (e : V)
    (g : V ≃ₗ[K] V) (hg : ∀ w, g w = w + φ w • e) :
    (b.toGL g : Matrix ι ι K) = 1 + Matrix.vecMulVec (b.equivFun e) (fun i => φ (b i)) := by
  apply matrix_eq_of_mulVec_eq
  intro x
  obtain ⟨w, rfl⟩ : ∃ w, x = b.equivFun w :=
    ⟨b.equivFun.symm x, (b.equivFun.apply_symm_apply x).symm⟩
  have hL : (b.toGL g : Matrix ι ι K) *ᵥ b.equivFun w = b.equivFun w + φ w • b.equivFun e := by
    rw [toGL_mulVec_basis, hg w, map_add, map_smul]
  rw [hL, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec_basis,
    dotProduct_eq_form b φ (b.equivFun w), b.equivFun.symm_apply_apply]

theorem form_eq_zero_of_basis (b : Module.Basis ι K V) {φ : V →ₗ[K] K}
    (h : ∀ i, φ (b i) = 0) : φ = 0 :=
  b.ext fun i => by rw [h i, LinearMap.zero_apply]

theorem det_one_add_vecMulVec_basis (u v : ι → K) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  have h : Matrix.vecMulVec u v = Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]

end Matrices

section Transport

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : LinearMap.BilinForm K V}

theorem natIrred_map (b : Module.Basis ι K V) (X : Subgroup (V ≃ₗ[K] V))
    (hirr : ∀ U : Submodule K V, (∀ g ∈ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    NatIrred (X.map b.toGL.toMonoidHom) := by
  intro S hS
  have hU : ∀ g ∈ X, ∀ u ∈ S.comap (b.equivFun : V →ₗ[K] (ι → K)),
      g u ∈ S.comap (b.equivFun : V →ₗ[K] (ι → K)) := by
    intro g hg u hu
    have hu' : b.equivFun u ∈ S := hu
    have hmem : b.toGL g ∈ X.map b.toGL.toMonoidHom := Subgroup.mem_map_of_mem _ hg
    have h1 := hS _ hmem _ hu'
    rw [toGL_mulVec_basis] at h1
    exact h1
  rcases hirr _ hU with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : b.equivFun.symm x ∈ S.comap (b.equivFun : V →ₗ[K] (ι → K)) := by
      show b.equivFun (b.equivFun.symm x) ∈ S
      rw [LinearEquiv.apply_symm_apply]
      exact hx
    rw [h, Submodule.mem_bot] at hx'
    have hx0 : x = 0 := by
      have := congrArg b.equivFun hx'
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    exact (Submodule.mem_bot K).mpr hx0
  · right
    rw [eq_top_iff]
    intro x _
    have hx : b.equivFun.symm x ∈ S.comap (b.equivFun : V →ₗ[K] (ι → K)) := by
      rw [h]
      exact Submodule.mem_top
    have hx2 : b.equivFun (b.equivFun.symm x) ∈ S := hx
    rwa [LinearEquiv.apply_symm_apply] at hx2

theorem genByTransvLines_map (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (b : Module.Basis ι K V) (X : Subgroup (V ≃ₗ[K] V)) (Y : Set V) (hY0 : ∀ y ∈ Y, y ≠ 0)
    (htr : ∀ y ∈ Y, ∀ c : K, ∃ g ∈ X, ∀ v, g v = v + (c * F v y) • y)
    (hgen : X = Subgroup.closure
      {g : V ≃ₗ[K] V | ∃ y ∈ Y, ∃ c : K, ∀ v, g v = v + (c * F v y) • y}) :
    GenByTransvLines (X.map b.toGL.toMonoidHom) := by
  have hX' : X.map b.toGL.toMonoidHom = Subgroup.closure (b.toGL.toMonoidHom ''
      {g : V ≃ₗ[K] V | ∃ y ∈ Y, ∃ c : K, ∀ v, g v = v + (c * F v y) • y}) := by
    rw [hgen, MonoidHom.map_closure]
  unfold GenByTransvLines
  apply le_antisymm
  · refine (le_of_eq hX').trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨y, hyY, c, hsc⟩ := hs
    by_cases hc : c = 0
    · have hs1 : s = 1 := by
        apply LinearEquiv.ext
        intro v
        simp [hsc v, hc]
      rw [hs1, map_one]
      exact Subgroup.one_mem _
    · have hyne : y ≠ 0 := hY0 y hyY
      have hFy : (c • F.flip y : V →ₗ[K] K) ≠ 0 := by
        intro h0
        apply hyne
        apply hnd.2 y
        intro m
        have h1 : c • F m y = 0 := by
          have := LinearMap.congr_fun h0 m
          simpa using this
        exact (smul_eq_zero.mp h1).resolve_left hc
      have hgs : ∀ w, s w = w + (c • F.flip y) w • y := fun w => by
        rw [hsc w]
        rfl
      apply Subgroup.subset_closure
      refine ⟨b.equivFun y, fun i => (c • F.flip y) (b i), ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h0 => hyne (b.equivFun.map_eq_zero_iff.mp h0)
      · intro h0
        exact hFy (form_eq_zero_of_basis b (φ := c • F.flip y) (fun i => congrFun h0 i))
      · rw [dotProduct_eq_form b (c • F.flip y) (b.equivFun y), b.equivFun.symm_apply_apply]
        show c • F y y = 0
        rw [form_self halt, smul_zero]
      · exact toGL_eq_one_add_of_transv b (c • F.flip y) y s hgs
      · intro c'
        obtain ⟨g', hg'X, hg'⟩ := htr y hyY (c' * c)
        refine ⟨b.toGL.toMonoidHom g', Subgroup.mem_map_of_mem _ hg'X, ?_⟩
        have hgs' : ∀ w, g' w = w + ((c' * c) • F.flip y) w • y := fun w => by
          rw [hg' w]
          rfl
        have hmat := toGL_eq_one_add_of_transv b ((c' * c) • F.flip y) y g' hgs'
        show (b.toGL g' : Matrix ι ι K) = _
        rw [hmat]
        congr 1
        ext i j
        show (b.equivFun y) i * ((c' * c) * F (b j) y) = c' * ((b.equivFun y) i * (c * F (b j) y))
        ring
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨v, ψ, hv, hψ, hdot, hg, hall⟩
    obtain ⟨h, hh, hhm⟩ := hall 1
    have hgh : g = h := Units.ext (by rw [hg, hhm, one_smul])
    rw [hgh]
    exact hh

end Transport

section Nonisom

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem exists_nonisom_transv (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) :
    ∃ (y₀ : V) (φ : V →ₗ[K] K), φ y₀ = 0 ∧ ∃ g : V ≃ₗ[K] V,
      (∀ w, g w = w + φ w • y₀) ∧ ¬ IsIsom F g := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : V)
  have hex : ∃ w, F w y₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy₀ (hnd.2 y₀ hcon)
  obtain ⟨w, hw⟩ := hex
  obtain ⟨w₀, hFw₀⟩ : ∃ w₀ : V, F w₀ y₀ = 1 :=
    ⟨(F w y₀)⁻¹ • w, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  have hp : Submodule.span K ({y₀, w₀} : Set V) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 : Module.finrank K V = Module.finrank K (Submodule.span K ({y₀, w₀} : Set V)) := by
      rw [htop, finrank_top]
    have h2 : Module.finrank K (Submodule.span K ({y₀, w₀} : Set V)) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := K) ({y₀, w₀} : Finset V)
      have h3 : ({y₀, w₀} : Finset V).card ≤ 2 := Finset.card_le_two
      simp only [Finset.coe_insert, Finset.coe_singleton] at h
      exact h.trans h3
    omega
  obtain ⟨φ, hφne, hφle⟩ := Submodule.exists_le_ker_of_lt_top _ hp
  have hφy₀ : φ y₀ = 0 :=
    LinearMap.mem_ker.mp (hφle (Submodule.subset_span (Set.mem_insert y₀ {w₀})))
  have hφw₀ : φ w₀ = 0 :=
    LinearMap.mem_ker.mp
      (hφle (Submodule.subset_span (Set.mem_insert_of_mem y₀ (Set.mem_singleton w₀))))
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, φ v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφne (LinearMap.ext hcon)
  have hinv : Function.Involutive (LinearMap.id + φ.smulRight y₀ : V →ₗ[K] V) := by
    intro w
    have h1 : φ (w + φ w • y₀) = φ w := by
      rw [map_add, map_smul, hφy₀, smul_zero, add_zero]
    show w + φ w • y₀ + φ (w + φ w • y₀) • y₀ = w
    rw [h1, add_assoc, vec_add_self K, add_zero]
  obtain ⟨g₀, hg₀⟩ : ∃ g : V ≃ₗ[K] V, ∀ w, g w = w + φ w • y₀ :=
    ⟨LinearEquiv.ofInvolutive _ hinv, fun w => rfl⟩
  refine ⟨y₀, φ, hφy₀, g₀, hg₀, fun hiso => ?_⟩
  have key : F (g₀ w₀) (g₀ v₀) = F w₀ v₀ + φ v₀ := by
    rw [hg₀, hg₀]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hφw₀, hFw₀, zero_smul, add_zero, mul_one]
  have h1 := hiso w₀ v₀
  rw [key] at h1
  exact hv₀ (by linear_combination h1)

theorem isIsom_conj_iff {F' : LinearMap.BilinForm K V} (φ : V ≃ₗ[K] V)
    (hφ : ∀ x y, F (φ x) (φ y) = F' x y) (h : V ≃ₗ[K] V) :
    IsIsom F' h ↔ IsIsom F (φ * h * φ⁻¹) := by
  have hφφ : ∀ z, φ (φ⁻¹ z) = z := fun z => by simp
  have hφφ' : ∀ z, φ⁻¹ (φ z) = z := fun z => by simp
  constructor
  · intro hh x y
    simp only [LinearEquiv.mul_apply]
    rw [hφ, hh (φ⁻¹ x) (φ⁻¹ y), ← hφ (φ⁻¹ x) (φ⁻¹ y), hφφ, hφφ]
  · intro hh x y
    rw [← hφ (h x) (h y), ← hφ x y]
    have := hh (φ x) (φ y)
    simp only [LinearEquiv.mul_apply, hφφ'] at this
    exact this

end Nonisom

section Main

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem eq_symp_of_transvections (hMcL : McLaughlinStatement) (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (hq : 4 ≤ Nat.card K) (hdim : 4 ≤ Module.finrank K V)
    (X : Subgroup (V ≃ₗ[K] V)) (hX : X ≤ sympSubgroup F) (Y : Set V) (hY0 : ∀ y ∈ Y, y ≠ 0)
    (htr : ∀ y ∈ Y, ∀ c : K, ∃ g ∈ X, ∀ v, g v = v + (c * F v y) • y)
    (hgen : X = Subgroup.closure
      {g : V ≃ₗ[K] V | ∃ y ∈ Y, ∃ c : K, ∀ v, g v = v + (c * F v y) • y})
    (hirr : ∀ U : Submodule K V, (∀ g ∈ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    X = sympSubgroup F := by
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank K V)) K V) :=
    ⟨Module.finBasis K V⟩
  have hn2 : 2 ≤ Fintype.card (Fin (Module.finrank K V)) := by
    rw [Fintype.card_fin]
    omega
  have hL1 : NatIrred (X.map b.toGL.toMonoidHom) := natIrred_map b X hirr
  have hL2 : GenByTransvLines (X.map b.toGL.toMonoidHom) :=
    genByTransvLines_map hnd halt b X Y hY0 htr hgen
  rcases hMcL K (Fin (Module.finrank K V)) (X.map b.toGL.toMonoidHom) hn2 hq hL1 hL2 with
    hsl | ⟨β, hβn, hβalt, hβX⟩
  · exfalso
    obtain ⟨y₀, φ, hφy₀, g₀, hg₀, hnot⟩ := exists_nonisom_transv hnd halt (by omega)
    apply hnot
    have hmem : b.toGL g₀ ∈ X.map b.toGL.toMonoidHom := by
      rw [hsl]
      show Matrix.GeneralLinearGroup.det (b.toGL g₀) = 1
      apply Units.ext
      show (b.toGL g₀ : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K).det = 1
      rw [toGL_eq_one_add_of_transv b φ y₀ g₀ hg₀, det_one_add_vecMulVec_basis,
        dotProduct_eq_form b φ (b.equivFun y₀), b.equivFun.symm_apply_apply, hφy₀, add_zero]
    have hgX : g₀ ∈ X :=
      (Subgroup.mem_map_iff_mem (f := b.toGL.toMonoidHom) b.toGL.injective).mp hmem
    exact hX hgX
  · obtain ⟨F', hF'⟩ : ∃ F' : LinearMap.BilinForm K V,
        ∀ x y, F' x y = β (b.equivFun x) (b.equivFun y) :=
      ⟨β.compl₁₂ b.equivFun b.equivFun, fun x y => rfl⟩
    have hF'alt : F'.IsAlt := fun x => by
      rw [hF']
      exact hβalt _
    have hF'nd : F'.Nondegenerate := by
      show LinearMap.SeparatingLeft F' ∧ LinearMap.SeparatingRight F'
      refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · have h0 : b.equivFun x = 0 := hβn.1 _ fun z => by
          obtain ⟨w, rfl⟩ := b.equivFun.surjective z
          rw [← hF']
          exact hx w
        exact b.equivFun.map_eq_zero_iff.mp h0
      · have h0 : b.equivFun y = 0 := hβn.2 _ fun z => by
          obtain ⟨w, rfl⟩ := b.equivFun.surjective z
          rw [← hF']
          exact hy w
        exact b.equivFun.map_eq_zero_iff.mp h0
    have hXeq : X = sympSubgroup F' := by
      ext g
      have hg : g ∈ X ↔ b.toGL g ∈ X.map b.toGL.toMonoidHom :=
        (Subgroup.mem_map_iff_mem (f := b.toGL.toMonoidHom) b.toGL.injective).symm
      rw [hg, hβX (b.toGL g)]
      constructor
      · intro h
        show IsIsom F' g
        intro x y
        rw [hF', hF', ← toGL_mulVec_basis b g x, ← toGL_mulVec_basis b g y]
        exact h _ _
      · intro h x' y'
        have h' : IsIsom F' g := h
        obtain ⟨x, rfl⟩ := b.equivFun.surjective x'
        obtain ⟨y, rfl⟩ := b.equivFun.surjective y'
        rw [toGL_mulVec_basis, toGL_mulVec_basis, ← hF', ← hF']
        exact h' x y
    obtain ⟨φ, hφ⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isometry_of_finrank_eq
      hF'alt hF'nd halt hnd rfl
    have hconj : (sympSubgroup F').map (MulAut.conj φ).toMonoidHom = sympSubgroup F := by
      ext g
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact (isIsom_conj_iff φ hφ h).mp hh
      · intro hg
        refine ⟨φ⁻¹ * g * φ, (isIsom_conj_iff φ hφ _).mpr ?_, ?_⟩
        · rw [show φ * (φ⁻¹ * g * φ) * φ⁻¹ = g by group]
          exact hg
        · show φ * (φ⁻¹ * g * φ) * φ⁻¹ = g
          group
    have hcard : Nat.card (sympSubgroup F') = Nat.card (sympSubgroup F) := by
      rw [← hconj]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective (sympSubgroup F') (MulAut.conj φ).toMonoidHom
          (MulAut.conj φ).injective).toEquiv
    haveI : Finite V := Module.finite_of_finite K
    haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
      (fun g h hgh => LinearEquiv.ext fun x => congrFun hgh x)
    have hc2 : Nat.card (sympSubgroup F) ≤ Nat.card X :=
      le_of_eq (by rw [hXeq, hcard])
    exact Subgroup.eq_of_le_of_card_ge hX hc2

end Main

end CFSG.RankThree.GF2n.Stroth80.Classify
