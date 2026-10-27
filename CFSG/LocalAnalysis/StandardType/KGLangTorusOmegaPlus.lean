module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpanH90
import CFSG.LocalAnalysis.StandardType.KGLangTorusInnerModel
import CFSG.LocalAnalysis.StandardType.KGLangTorusClassicalInner
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
import CFSG.LocalAnalysis.StandardType.KGLangTorusNorm
import CFSG.LocalAnalysis.StandardType.KGLangTorusOrth
import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitForm
import Mathlib.LinearAlgebra.Matrix.CharP
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitC
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

private theorem kgLangCOmPAux_adjoin_toSubmodule_eq_span {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι]
    [Field 𝕂] (P : Subgroup (GL ι 𝕂)) :
    Subalgebra.toSubmodule (Algebra.adjoin 𝕂
        ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂)))) =
      Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))) := by
  rw [Algebra.adjoin_eq_span]
  congr 1
  let S : Submonoid (Matrix ι ι 𝕂) :=
    { carrier := (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))
      one_mem' := ⟨1, P.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
        exact ⟨g * h, P.mul_mem hg hh, by simp [Matrix.GeneralLinearGroup.coe_mul]⟩ }
  have hS : Submonoid.closure
      ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))) = S :=
    Submonoid.closure_eq S
  rw [hS]
  rfl

private theorem kgLangCOmPAux_span_comm {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∀ x ∈ Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))),
      ∀ y ∈ Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))),
        x * y = y * x := by
  set s : Set (Matrix ι ι 𝕂) := (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))
  have hs_pair : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro a ⟨g, hg, rfl⟩ b ⟨h, hh, rfl⟩
    show (g : Matrix ι ι 𝕂) * (h : Matrix ι ι 𝕂) = (h : Matrix ι ι 𝕂) * (g : Matrix ι ι 𝕂)
    rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul, hab g hg h hh]
  have h1 : ∀ x ∈ Submodule.span 𝕂 s, ∀ b ∈ s, x * b = b * x := by
    intro x hx
    refine Submodule.span_induction (s := s) (p := fun x _ => ∀ b ∈ s, x * b = b * x)
      ?_ ?_ ?_ ?_ hx
    · intro a ha b hb; exact hs_pair a ha b hb
    · intro b _; rw [zero_mul, mul_zero]
    · intro a c _ _ ha hc b hb; rw [add_mul, mul_add, ha b hb, hc b hb]
    · intro r a _ ha b hb; rw [Matrix.smul_mul, Matrix.mul_smul, ha b hb]
  intro x hx y hy
  refine Submodule.span_induction (s := s) (p := fun y _ => x * y = y * x) ?_ ?_ ?_ ?_ hy
  · intro b hb; exact h1 x hx b hb
  · rw [mul_zero, zero_mul]
  · intro a c _ _ ha hc; rw [mul_add, add_mul, ha, hc]
  · intro r a _ ha; rw [Matrix.mul_smul, Matrix.smul_mul, ha]

private theorem kgLangCOmPAux_spForm_mul_self {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] (m : ℕ) :
    LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m = 1 := by
  rw [largeEvenSpForm_def, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, CharTwo.neg_eq]

private theorem kgLangCOmPAux_polar_preserved {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] {m : ℕ}
    {x : GL (Fin m ⊕ Fin m) 𝕂}
    (hx : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
        (LargeEvenSpForm 𝕂 m *
          Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
          LargeEvenSpForm 𝕂 m) = 1) :
    ∀ u v, QuadraticMap.polar (TableBOrth.qPlusForm 𝕂 m)
        (Matrix.mulVec (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) u)
        (Matrix.mulVec (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) v)
      = QuadraticMap.polar (TableBOrth.qPlusForm 𝕂 m) u v := by
  have hJJ := kgLangCOmPAux_spForm_mul_self (𝕂 := 𝕂) m
  have hxinv : LargeEvenSpForm 𝕂 m *
        Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
        LargeEvenSpForm 𝕂 m =
      ((x⁻¹ : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
    have h1 := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 =>
      ((x⁻¹ : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) * M) hx
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at h1
    exact h1
  have h2 : Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
        LargeEvenSpForm 𝕂 m =
      LargeEvenSpForm 𝕂 m *
        ((x⁻¹ : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
    have h := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 =>
      LargeEvenSpForm 𝕂 m * M) hxinv
    have hL : LargeEvenSpForm 𝕂 m *
        (LargeEvenSpForm 𝕂 m *
          Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
          LargeEvenSpForm 𝕂 m) =
        Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
          LargeEvenSpForm 𝕂 m := by
      rw [show LargeEvenSpForm 𝕂 m *
          (LargeEvenSpForm 𝕂 m *
            Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            LargeEvenSpForm 𝕂 m) =
          (LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m) *
            Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
            LargeEvenSpForm 𝕂 m from by noncomm_ring, hJJ, one_mul]
    rw [hL] at h
    exact h
  have hxTJx : Matrix.transpose (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
        LargeEvenSpForm 𝕂 m * (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      LargeEvenSpForm 𝕂 m := by
    rw [h2, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hxSp : x ∈ LargeEvenSpGroup 𝕂 m := by
    rw [largeEvenSpGroup_def]
    exact Subgroup.subset_closure (by simpa using hxTJx)
  intro u v
  have h := CFSG.ComponentClassification.RankTwoClassical.polarBilin_mulVec_of_mem_statedSp
    (K := 𝕂) (n := m) hxSp u v
  simpa only [TableBOrth.qPlusForm, QuadraticMap.polarBilin_apply_apply] using h

private theorem kgLangCOmPAux_exists_noncomm_omegaPlus {𝕂 : Type} [Field 𝕂] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)), a * b ≠ b * a := by
  haveI : Group.IsPerfect (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :=
    Group.isPerfect_def.mpr (LayerCyc.commutator_largeEvenOmegaPlus (K := 𝕂) hm3)
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    Group.IsPerfect.ofSurjective
      (f := LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))
      (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := 𝕂) hm3
  haveI : Nontrivial (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    (inferInstance : IsSimpleGroup _).toNontrivial
  by_contra h
  push Not at h
  haveI : IsMulCommutative (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    IsMulCommutative.of_comm h
  exact Group.IsPerfect.not_isMulCommutative
    (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) inferInstance

private theorem kgLangCOmPAux_center_eq_bot {𝕂 : Type} [Field 𝕂] {m : ℕ} (hm3 : 3 ≤ m) :
    Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) = ⊥ := by
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := 𝕂) hm3
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) := by
    haveI : Group.IsPerfect (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :=
      Group.isPerfect_def.mpr (LayerCyc.commutator_largeEvenOmegaPlus (K := 𝕂) hm3)
    exact Group.IsPerfect.ofSurjective
      (f := LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))
      (QuotientGroup.mk'_surjective _)
  haveI : Nontrivial (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    (inferInstance : IsSimpleGroup _).toNontrivial
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
      IsMulCommutative.of_comm (fun a b =>
        Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    exact Group.IsPerfect.not_isMulCommutative
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) inferInstance

private noncomputable def kgLangCOmPAux_cHom (𝕂 : Type) [Field 𝕂] (m : ℕ) :
    LargeEvenOmega (LargeEvenQPlus 𝕂 m) →*
      MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
  (MulAut.conj).comp (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))

private theorem kgLangCOmPAux_cHom_range (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] {m : ℕ}
    (hm1 : 1 ≤ m) :
    ((kgLangCOmPAux_cHom 𝕂 m).range :
        Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))))) =
      LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) := by
  ext φ
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) A, rfl⟩
  · rintro ⟨r, rfl⟩
    refine ⟨(TableBOrth.projMkEquiv
      (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := 𝕂) hm1)).symm r, ?_⟩
    show MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m))
      ((TableBOrth.projMkEquiv
        (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := 𝕂) hm1)).symm r)) = MulAut.conj r
    congr 1
    exact (TableBOrth.projMkEquiv
      (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := 𝕂) hm1)).apply_symm_apply r

private theorem kgLangCOmPAux_odd_card_of_isElemAbelian {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Odd (Nat.card E) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2 : 2 ∣ Nat.card E := even_iff_two_dvd.mp heven
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 (g : G) g.2)
  have hdivp : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
  have hdiv2 : orderOf g ∣ 2 := by rw [hg]
  have hcop : Nat.Coprime 2 p := by
    have hnotdvd : ¬ p ∣ 2 := by
      intro h
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have hpge : 2 ≤ p := hp.two_le
      omega
    exact (hp.coprime_iff_not_dvd.mpr hnotdvd).symm
  have h1 : orderOf g = 1 := by
    have hgcd := Nat.dvd_gcd hdiv2 hdivp
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  rw [h1] at hg
  omega

private noncomputable def kgLangCOmPAux_fieldOm {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] {m : ℕ}
    (hm : 1 ≤ m) (σ : 𝕂 ≃+* 𝕂) :
    LargeEvenOmega (LargeEvenQPlus 𝕂 m) →* LargeEvenOmega (LargeEvenQPlus 𝕂 m) where
  toFun A := Classical.choose (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm σ A)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [Classical.choose_spec (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm σ 1)]
    simp
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Classical.choose_spec (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm σ (A * B)),
      Classical.choose_spec (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm σ A),
      Classical.choose_spec (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm σ B)]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

private theorem kgLangCOmPAux_fieldOm_val {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] {m : ℕ}
    (hm : 1 ≤ m) (σ : 𝕂 ≃+* 𝕂) (A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
    (((kgLangCOmPAux_fieldOm hm σ A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
        GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      (((A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
        GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map σ :=
  Classical.choose_spec (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm σ A)

private theorem kgLangCOmPAux_fieldOm_iter_val {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] {m : ℕ}
    (hm : 1 ≤ m) (σ : 𝕂 ≃+* 𝕂) (i : ℕ) (A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
    (((endPow (kgLangCOmPAux_fieldOm hm σ) i A :
        LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      (((A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
        GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map (σ ^ i) := by
  induction i with
  | zero => rw [endPow_apply]; simp [Matrix.map_id]
  | succ i ih =>
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
      rw [kgLangCOmPAux_fieldOm_val, ih, Matrix.map_map, pow_succ']
      rfl

private theorem kgLangCOmPAux_spForm_transpose {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] (m : ℕ) :
    Matrix.transpose (LargeEvenSpForm 𝕂 m) = LargeEvenSpForm 𝕂 m := by
  rw [largeEvenSpForm_def]
  ext i j
  rw [Matrix.transpose_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, eq_comm, CharTwo.neg_eq]

private theorem kgLangCOmPAux_spForm_map {𝕂 : Type} [Field 𝕂] (m : ℕ) (σ : 𝕂 ≃+* 𝕂) :
    (LargeEvenSpForm 𝕂 m).map σ = LargeEvenSpForm 𝕂 m := by
  rw [largeEvenSpForm_def]
  ext i j
  rw [Matrix.map_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, apply_ite σ, map_neg, map_one, map_zero]

private noncomputable def kgLangCOmPAux_tau (m : ℕ) (𝕂 : Type) [Field 𝕂] :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
  fun x => LargeEvenSpForm 𝕂 m * Matrix.transpose x * LargeEvenSpForm 𝕂 m

private theorem kgLangCOmPAux_tau_add (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCOmPAux_tau m 𝕂 (a + b) = kgLangCOmPAux_tau m 𝕂 a + kgLangCOmPAux_tau m 𝕂 b := by
  simp only [kgLangCOmPAux_tau, Matrix.transpose_add, mul_add, add_mul]

private theorem kgLangCOmPAux_tau_mul (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCOmPAux_tau m 𝕂 (a * b) = kgLangCOmPAux_tau m 𝕂 b * kgLangCOmPAux_tau m 𝕂 a := by
  have hJJ : LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m = 1 := kgLangCOmPAux_spForm_mul_self m
  simp only [kgLangCOmPAux_tau, Matrix.transpose_mul]
  calc LargeEvenSpForm 𝕂 m * (Matrix.transpose b * Matrix.transpose a) * LargeEvenSpForm 𝕂 m
      = LargeEvenSpForm 𝕂 m * Matrix.transpose b *
          (LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m) * Matrix.transpose a *
          LargeEvenSpForm 𝕂 m := by
          rw [hJJ, mul_one]; simp only [Matrix.mul_assoc]
    _ = (LargeEvenSpForm 𝕂 m * Matrix.transpose b * LargeEvenSpForm 𝕂 m) *
          (LargeEvenSpForm 𝕂 m * Matrix.transpose a * LargeEvenSpForm 𝕂 m) := by
          simp only [Matrix.mul_assoc]

private theorem kgLangCOmPAux_tau_one (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2] :
    kgLangCOmPAux_tau m 𝕂 1 = 1 := by
  simp only [kgLangCOmPAux_tau, Matrix.transpose_one, Matrix.mul_one]
  exact kgLangCOmPAux_spForm_mul_self m

private theorem kgLangCOmPAux_tau_tau (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCOmPAux_tau m 𝕂 (kgLangCOmPAux_tau m 𝕂 a) = a := by
  have hJJ : LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m = 1 := kgLangCOmPAux_spForm_mul_self m
  have ht : Matrix.transpose (LargeEvenSpForm 𝕂 m) = LargeEvenSpForm 𝕂 m :=
    kgLangCOmPAux_spForm_transpose m
  simp only [kgLangCOmPAux_tau, Matrix.transpose_mul, Matrix.transpose_transpose, ht]
  have h1 : LargeEvenSpForm 𝕂 m *
        (LargeEvenSpForm 𝕂 m * (a * LargeEvenSpForm 𝕂 m)) * LargeEvenSpForm 𝕂 m =
      LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m * a *
        (LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m) := by
    simp only [Matrix.mul_assoc]
  rw [h1]
  simp only [hJJ, one_mul, mul_one]

private theorem kgLangCOmPAux_tau_map (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (σ : 𝕂 ≃+* 𝕂) (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    kgLangCOmPAux_tau m 𝕂 (a.map σ) = (kgLangCOmPAux_tau m 𝕂 a).map σ := by
  have hJm : (LargeEvenSpForm 𝕂 m).map σ = LargeEvenSpForm 𝕂 m := kgLangCOmPAux_spForm_map m σ
  calc LargeEvenSpForm 𝕂 m * Matrix.transpose (a.map σ) * LargeEvenSpForm 𝕂 m
      = (LargeEvenSpForm 𝕂 m).map σ * (Matrix.transpose a).map σ *
          (LargeEvenSpForm 𝕂 m).map σ := by rw [hJm, Matrix.transpose_map]
    _ = (LargeEvenSpForm 𝕂 m * Matrix.transpose a * LargeEvenSpForm 𝕂 m).map σ := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]

private theorem kgLangCOmPAux_tau_scalar (m : ℕ) (𝕂 : Type) [Field 𝕂] [CharP 𝕂 2]
    (r : 𝕂) : kgLangCOmPAux_tau m 𝕂 (Matrix.scalar (Fin m ⊕ Fin m) r) =
      Matrix.scalar (Fin m ⊕ Fin m) r := by
  have htrans : Matrix.transpose (Matrix.scalar (Fin m ⊕ Fin m) r) =
      Matrix.scalar (Fin m ⊕ Fin m) r := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]
  have hcomm : Commute (Matrix.scalar (Fin m ⊕ Fin m) r) (LargeEvenSpForm 𝕂 m) :=
    Matrix.scalar_commute r (fun r' => Commute.all r r') (LargeEvenSpForm 𝕂 m)
  have hJJ : LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m = 1 := kgLangCOmPAux_spForm_mul_self m
  rw [kgLangCOmPAux_tau, htrans]
  calc LargeEvenSpForm 𝕂 m * Matrix.scalar (Fin m ⊕ Fin m) r * LargeEvenSpForm 𝕂 m
      = LargeEvenSpForm 𝕂 m *
          (Matrix.scalar (Fin m ⊕ Fin m) r * LargeEvenSpForm 𝕂 m) := by
          rw [Matrix.mul_assoc]
    _ = LargeEvenSpForm 𝕂 m *
          (LargeEvenSpForm 𝕂 m * Matrix.scalar (Fin m ⊕ Fin m) r) := by rw [hcomm.eq]
    _ = (LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m) *
          Matrix.scalar (Fin m ⊕ Fin m) r := by rw [Matrix.mul_assoc]
    _ = Matrix.scalar (Fin m ⊕ Fin m) r := by rw [hJJ, one_mul]

private theorem kgLangCOmPAux_map_scalar (m : ℕ) (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) (r : 𝕂) :
    (Matrix.scalar (Fin m ⊕ Fin m) r).map σ = Matrix.scalar (Fin m ⊕ Fin m) (σ r) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite σ, map_zero]

private theorem kgLangCOmPAux_mapMatrix_iterate (m : ℕ) (𝕂 : Type) [Field 𝕂]
    (σ : 𝕂 ≃+* 𝕂) (n : ℕ) (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :
    (⇑(RingHom.mapMatrix σ.toRingHom))^[n] a = a.map (σ ^ n) := by
  induction n with
  | zero => simp [Matrix.map_id]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, RingHom.mapMatrix_apply, Matrix.map_map, pow_succ']
      rfl

private theorem kgLangCOmPAux_tau_eq_inv {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] {m : ℕ}
    (A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
    kgLangCOmPAux_tau m 𝕂 (((A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
        GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      (((A⁻¹ : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
  have hJJ : LargeEvenSpForm 𝕂 m * LargeEvenSpForm 𝕂 m = 1 := kgLangCOmPAux_spForm_mul_self m
  set Am : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
    (((A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) with hAm
  have hiso : ∀ v, LargeEvenQPlus 𝕂 m (Matrix.mulVec Am v) = LargeEvenQPlus 𝕂 m v := by
    intro v
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ A.2) v
  have hiso' : ∀ v, (CFSG.LieType.Universal.Spin.quadPlus m 𝕂) (Matrix.mulVec Am v) = (CFSG.LieType.Universal.Spin.quadPlus m 𝕂) v := by
    intro v
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact hiso v
  have hcomp : (CFSG.LieType.Universal.Spin.quadPlus m 𝕂).comp (Matrix.mulVecLin Am) = CFSG.LieType.Universal.Spin.quadPlus m 𝕂 := by
    ext v
    simpa [QuadraticMap.comp_apply, Matrix.mulVecLin_apply] using hiso' v
  have hpolar : ∀ u v, (CFSG.LieType.Universal.Spin.quadPlus m 𝕂).polarBilin (Matrix.mulVec Am u) (Matrix.mulVec Am v) =
      (CFSG.LieType.Universal.Spin.quadPlus m 𝕂).polarBilin u v := by
    intro u v
    have h := QuadraticMap.polarBilin_comp (CFSG.LieType.Universal.Spin.quadPlus m 𝕂) (Matrix.mulVecLin Am)
    rw [hcomp] at h
    have h2 := LinearMap.congr_fun (LinearMap.congr_fun h u) v
    rw [LinearMap.compl₁₂_apply] at h2
    simpa only [Matrix.mulVecLin_apply] using h2.symm
  have hsp : (A : GL (Fin m ⊕ Fin m) 𝕂) ∈ LargeEvenSpGroup 𝕂 m :=
    CFSG.ComponentClassification.RankTwoClassical.mem_statedSp_of_polarBilin
      (X := (A : GL (Fin m ⊕ Fin m) 𝕂)) hpolar
  have hmat : Matrix.transpose Am * LargeEvenSpForm 𝕂 m * Am = LargeEvenSpForm 𝕂 m := by
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff).mp hsp
    simpa [hAm, largeEvenSpForm_def] using h
  have hleft : (LargeEvenSpForm 𝕂 m * Matrix.transpose Am * LargeEvenSpForm 𝕂 m) * Am = 1 := by
    have h := congrArg (fun M => LargeEvenSpForm 𝕂 m * M) hmat
    rw [hJJ] at h
    simpa only [Matrix.mul_assoc] using h
  have hinv : LargeEvenSpForm 𝕂 m * Matrix.transpose Am * LargeEvenSpForm 𝕂 m = Am⁻¹ :=
    (Matrix.inv_eq_left_inv hleft).symm
  change kgLangCOmPAux_tau m 𝕂 Am =
    (((A⁻¹ : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
  rw [kgLangCOmPAux_tau, hinv, Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv, hAm]

private theorem kgLangCOmPAux_adjoin_comm_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    {𝕂 : Type} [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2]
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (Nat.card P)) :
    (∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
      ∀ y ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
        x * y = y * x) ∧
    ∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
      IsNilpotent x → x = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    exact ⟨fun x _ y _ => Subsingleton.elim _ _, fun x _ _ => Subsingleton.elim _ _⟩
  · set s : Set (Matrix ι ι 𝕂) :=
      (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _) with hs
    let S : Subalgebra 𝕂 (Matrix ι ι 𝕂) := Algebra.adjoin 𝕂 s
    have hs_pair : s.Pairwise Commute := by
      intro a ha b hb _
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨h, hh, rfl⟩ := hb
      show Commute (↑g : Matrix ι ι 𝕂) (↑h : Matrix ι ι 𝕂)
      rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
        hab g hg h hh]
    have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      haveI : IsMulCommutative S := Algebra.isMulCommutative_adjoin 𝕂 hs_pair
      intro x hx y hy
      have hcommS : ∀ a b : S, a * b = b * a :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative S)
      simpa using congrArg Subtype.val (hcommS ⟨x, hx⟩ ⟨y, hy⟩)
    refine ⟨hcomm, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Algebra (ZMod 2) 𝕂 := ZMod.algebra 𝕂 2
    letI : Fintype 𝕂 := Fintype.ofFinite 𝕂
    let f := Module.finrank (ZMod 2) 𝕂
    let m := Nat.card P
    let k := f * Nat.totient m
    have hcard : 2 ^ f = Nat.card 𝕂 := FiniteField.pow_finrank_eq_natCard 2 𝕂
    have hm_pos : 0 < m := by
      haveI : Nonempty P := ⟨⟨1, one_mem P⟩⟩
      change 0 < Nat.card P
      exact Nat.card_pos
    have hf_pos : 0 < f := by
      change 0 < Module.finrank (ZMod 2) 𝕂
      exact Module.finrank_pos
    have hk_pos : 0 < k := by
      change 0 < f * Nat.totient m
      exact Nat.mul_pos hf_pos (Nat.totient_pos.mpr hm_pos)
    have hcop : Nat.Coprime 2 m := hodd.coprime_two_left
    have hk_mod : 2 ^ k ≡ 1 [MOD m] := by
      have h1 : (2 ^ Nat.totient m) ^ f ≡ 1 ^ f [MOD m] :=
        (Nat.ModEq.pow_totient hcop).pow f
      rw [one_pow] at h1
      have h2 : (2 ^ Nat.totient m) ^ f = 2 ^ k := by
        change (2 ^ Nat.totient m) ^ f = 2 ^ (f * Nat.totient m)
        rw [Nat.mul_comm, pow_mul]
      rwa [← h2]
    have hfixK : ∀ c : 𝕂, c ^ (2 ^ k) = c := by
      intro c
      have hq : 2 ^ k = (Nat.card 𝕂) ^ Nat.totient m := by
        change 2 ^ (f * Nat.totient m) = (Nat.card 𝕂) ^ Nat.totient m
        rw [← hcard, pow_mul]
      rw [hq, ← Fintype.card_eq_nat_card]
      exact FiniteField.pow_card_pow (Nat.totient m) c
    have hfixS : ∀ x ∈ S, x ^ (2 ^ k) = x := by
      intro x hxS
      refine Algebra.adjoin_induction (p := fun x _ => x ^ (2 ^ k) = x) ?_ ?_ ?_ ?_ hxS
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hy
        have hgm : (↑g : Matrix ι ι 𝕂) ^ m = 1 := by
          have h : g ^ m = 1 := by
            have h' := congrArg Subtype.val (pow_card_eq_one' (G := P) (x := ⟨g, hg⟩))
            simp only [Subgroup.coe_pow] at h'
            simpa [m] using h'
          have h2 := congrArg (fun u : GL ι 𝕂 => (u : Matrix ι ι 𝕂)) h
          simpa using h2
        have h := pow_eq_pow_of_modEq (x := (↑g : Matrix ι ι 𝕂)) hk_mod hgm
        rwa [pow_one] at h
      · intro r
        have hr : algebraMap 𝕂 (Matrix ι ι 𝕂) r = Matrix.scalar ι r := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr, ← map_pow, hfixK r]
      · intro a b ha hb ha' hb'
        rw [add_pow_char_pow_of_commute (p := 2) (n := k) (hcomm a ha b hb), ha', hb']
      · intro a b ha hb ha' hb'
        rw [Commute.mul_pow (hcomm a ha b hb) (2 ^ k), ha', hb']
    intro x hxS hnil
    obtain ⟨n, hn⟩ := hnil
    have hiter : ∀ t : ℕ, x ^ ((2 ^ k) ^ t) = x := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, pow_mul, ih]; exact hfixS x hxS
    have h2k_ge_two : 2 ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_pos
    have hle : n ≤ (2 ^ k) ^ n :=
      (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left h2k_ge_two n)
    have hzero : x ^ ((2 ^ k) ^ n) = 0 := by
      rw [show (2 ^ k) ^ n = n + ((2 ^ k) ^ n - n) from (Nat.add_sub_cancel' hle).symm]
      rw [pow_add, hn, zero_mul]
    rw [hiter n] at hzero
    exact hzero

private theorem kgLangCOmPAux_conj_conj {R : Type*} [Group R] (f : MulAut R) (x : R) :
    (MulAut.conj f) (MulAut.conj x) = MulAut.conj (f x) := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem kgLangCOmPAux_mulAut_conj_injective {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff (MulAut.conj : G →* MulAut G)]
  rw [eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  rw [← hZ]
  rw [Subgroup.mem_center_iff]
  intro b
  have h : a * b * a⁻¹ = b := by
    have := congrArg (fun φ : MulAut G => φ b) ha
    simpa [MulAut.conj_apply] using this
  have hab : a * b = b * a := by
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h]
  exact hab.symm

theorem kgLangC_torusInput_omegaPlus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 4 ≤ m)
    (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n)
    (J : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))))
    (hJ : (J : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))))) = LargeEvenInnSet _)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m))))
    (hfp : orderOf f = p) :
    KGLangTorusInput p J (MulAut.conj f).toMonoidHom := by
  classical
  haveI : CharP 𝕂 2 := LayerCC.charP_two_of_natCard h𝕂
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  let c : LargeEvenOmega (LargeEvenQPlus 𝕂 m) →*
      MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) := kgLangCOmPAux_cHom 𝕂 m
  have hc_range : c.range =
      LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    kgLangCOmPAux_cHom_range 𝕂 hm1
  have hc_inj : Function.Injective c := by
    intro A B hAB
    have h1 : MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) A) =
        MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) B) := hAB
    have h2 : LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) A =
        LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) B :=
      kgLangCOmPAux_mulAut_conj_injective
        (kgLangCOmPAux_center_eq_bot (𝕂 := 𝕂) hm3) h1
    exact (TableBOrth.projMkEquiv
      (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := 𝕂) hm1)).injective h2
  obtain ⟨σ, hσgraph⟩ := hf
  have hf_eq : f = (MulAut.congr (RecipeFieldOmega.plusEquiv (K := 𝕂) hm1)).symm
      (AutOm.fieldAutP m σ) :=
    CFSG.StandardType.eq_of_graphAut RecipeFieldOmega.proj_surjective_plus hσgraph
      (RecipeFieldOmega.graphAut_fieldAutP (K := 𝕂) hm1 σ)
      (RecipeFieldOmega.exists_map_mem_plus (K := 𝕂) hm1 σ)
  have hcongr : MulAut.congr (RecipeFieldOmega.plusEquiv (K := 𝕂) hm1) f =
      AutOm.fieldAutP m σ := by
    rw [hf_eq, MulEquiv.apply_symm_apply]
  have hfieldAutP_inj : Function.Injective (AutOm.fieldAutP (K := 𝕂) m) := by
    intro σ τ h
    have h1 : AutOm.fieldAutP (K := 𝕂) m (σ * τ⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : σ * τ⁻¹ = 1 := AutOm.eq_one_of_fieldAutP_eq_one hm3 h1
    exact mul_inv_eq_one.mp h2
  have hσo : orderOf σ = p := by
    rw [← orderOf_injective (AutOm.fieldAutP (K := 𝕂) m) hfieldAutP_inj σ]
    rw [← hcongr]
    exact (orderOf_injective
      ((MulAut.congr (RecipeFieldOmega.plusEquiv (K := 𝕂) hm1)).toMonoidHom)
      (MulAut.congr (RecipeFieldOmega.plusEquiv (K := 𝕂) hm1)).injective f).trans hfp
  let S : LargeEvenOmega (LargeEvenQPlus 𝕂 m) →*
      LargeEvenOmega (LargeEvenQPlus 𝕂 m) := kgLangCOmPAux_fieldOm hm1 σ
  have hS_val : ∀ A : LargeEvenOmega (LargeEvenQPlus 𝕂 m),
      (((S A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
      (((A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂).map σ :=
    fun A => kgLangCOmPAux_fieldOm_val hm1 σ A
  have hF0c : ∀ a : LargeEvenOmega (LargeEvenQPlus 𝕂 m),
      (MulAut.conj f) (c a) = c (S a) := by
    intro a
    have hgraph := hσgraph a (S a) (kgLangCOmPAux_fieldOm_val hm1 σ a)
    have hcc := kgLangCOmPAux_conj_conj (R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))
      f (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) a)
    change (MulAut.conj f)
        (MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) a)) =
      MulAut.conj (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) (S a))
    rw [hcc, hgraph]
  intro E hE hEfix
  have hEcr : E ≤ c.range := by
    intro x hx
    have hxJ : x ∈ LargeEvenInnSet _ := by
      have h := (hEfix x hx).1
      change x ∈ (J : Set _) at h
      rwa [hJ] at h
    change x ∈ (c.range : Set _)
    rwa [hc_range]
  set Phat : Subgroup (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) := E.comap c with hPhat
  have hcP : Phat.map c = E := by
    rw [hPhat, Subgroup.map_comap_eq, inf_eq_right.mpr hEcr]
  have hPhat_ab : ∀ a ∈ Phat, ∀ b ∈ Phat, a * b = b * a := by
    intro a ha b hb
    apply hc_inj
    rw [map_mul, map_mul]
    have hcomm : c a * c b = c b * c a := by
      letI : IsMulCommutative E := hE.1
      exact congrArg Subtype.val (mul_comm' (⟨c a, ha⟩ : E) (⟨c b, hb⟩ : E))
    exact hcomm
  have hcardPhat : Nat.card Phat = Nat.card E := by
    rw [← hcP]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Phat c hc_inj).toEquiv
  have hEodd : Odd (Nat.card E) := kgLangCOmPAux_odd_card_of_isElemAbelian hp hp2 hE
  set P : Subgroup (GL (Fin m ⊕ Fin m) 𝕂) :=
    Phat.map (LargeEvenOmega (LargeEvenQPlus 𝕂 m)).subtype with hP
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    rw [hP] at ha hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg (fun x : LargeEvenOmega (LargeEvenQPlus 𝕂 m) => (x : GL (Fin m ⊕ Fin m) 𝕂))
      (hPhat_ab a' ha' b' hb')
  have hcardP : Nat.card P = Nat.card E := by
    rw [hP, Subgroup.card_map_of_injective (LargeEvenOmega (LargeEvenQPlus 𝕂 m)).subtype_injective,
      hcardPhat]
  have hPodd : Odd (Nat.card P) := by rw [hcardP]; exact hEodd
  set B : Subalgebra 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) :=
    Algebra.adjoin 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)) with hB
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)) := by
      have h := (Subalgebra.mem_toSubmodule B).mpr hx
      rwa [kgLangCOmPAux_adjoin_toSubmodule_eq_span P] at h
    have hy' : y ∈ Submodule.span 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)) := by
      have h := (Subalgebra.mem_toSubmodule B).mpr hy
      rwa [kgLangCOmPAux_adjoin_toSubmodule_eq_span P] at h
    exact kgLangCOmPAux_span_comm P hPab x hx' y hy'
  let β : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 →+*
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 := RingHom.mapMatrix σ.toRingHom
  have hβsc : ∀ r : 𝕂, β (Matrix.scalar (Fin m ⊕ Fin m) r) =
      Matrix.scalar (Fin m ⊕ Fin m) (σ r) :=
    fun r => kgLangCOmPAux_map_scalar m 𝕂 σ r
  have hβP : ∀ g ∈ P, β (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈
      (fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _) := by
    intro g hg
    rw [hP] at hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    have hcA : c A ∈ E := by rw [hPhat] at hA; exact hA
    have hfixA : (MulAut.conj f) (c A) = c A := (hEfix (c A) hcA).2
    have hconjA : (MulAut.conj f) (c A) = c (S A) := hF0c A
    have hmem : S A ∈ Phat := by
      rw [hPhat, Subgroup.mem_comap]
      rw [← hconjA, hfixA]
      exact hcA
    refine ⟨((S A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂),
      Subgroup.mem_map.mpr ⟨S A, hmem, rfl⟩, ?_⟩
    exact kgLangCOmPAux_fieldOm_val hm1 σ A
  have hβB : ∀ a ∈ B, β a ∈ B := by
    intro a ha
    rw [hB] at ha ⊢
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      exact Algebra.subset_adjoin (hβP g₀ hg₀)
    · intro r
      change β (algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r) ∈ _
      rw [show algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r =
          Matrix.scalar (Fin m ⊕ Fin m) r from rfl, hβsc]
      exact Subalgebra.algebraMap_mem _ (σ r)
    · intro x y hx hy hx' hy'
      rw [map_add]
      exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      rw [map_mul]
      exact mul_mem hx' hy'
  have hβp : ∀ a ∈ B, (⇑β)^[p] a = a := by
    intro a _
    rw [show ⇑β = ⇑(RingHom.mapMatrix σ.toRingHom) from rfl,
      kgLangCOmPAux_mapMatrix_iterate m 𝕂 σ p a]
    have hσp : σ ^ p = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
    rw [hσp]
    exact Matrix.map_id a
  have hτB : ∀ a ∈ B, kgLangCOmPAux_tau m 𝕂 a ∈ B := by
    intro a ha
    rw [hB] at ha ⊢
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      rw [hP] at hg₀
      obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg₀
      change kgLangCOmPAux_tau m 𝕂
        (((A : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈ _
      rw [kgLangCOmPAux_tau_eq_inv A]
      exact Algebra.subset_adjoin
        ⟨((A⁻¹ : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂),
          Subgroup.mem_map.mpr ⟨A⁻¹, Phat.inv_mem hA, rfl⟩, rfl⟩
    · intro r
      change kgLangCOmPAux_tau m 𝕂
        (algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r) ∈ _
      rw [show algebraMap 𝕂 (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) r =
          Matrix.scalar (Fin m ⊕ Fin m) r from rfl, kgLangCOmPAux_tau_scalar]
      exact Subalgebra.algebraMap_mem _ r
    · intro x y hx hy hx' hy'
      change kgLangCOmPAux_tau m 𝕂 (x + y) ∈ _
      rw [kgLangCOmPAux_tau_add]
      exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      change kgLangCOmPAux_tau m 𝕂 (x * y) ∈ _
      rw [kgLangCOmPAux_tau_mul]
      exact mul_mem hy' hx'
  have hτadd : ∀ a ∈ B, ∀ b ∈ B, kgLangCOmPAux_tau m 𝕂 (a + b) =
      kgLangCOmPAux_tau m 𝕂 a + kgLangCOmPAux_tau m 𝕂 b :=
    fun a _ b _ => kgLangCOmPAux_tau_add m 𝕂 a b
  have hτone : kgLangCOmPAux_tau m 𝕂 1 = 1 := kgLangCOmPAux_tau_one m 𝕂
  have hττ : ∀ a ∈ B, kgLangCOmPAux_tau m 𝕂 (kgLangCOmPAux_tau m 𝕂 a) = a :=
    fun a _ => kgLangCOmPAux_tau_tau m 𝕂 a
  have hτmul : ∀ a ∈ B, ∀ b ∈ B, kgLangCOmPAux_tau m 𝕂 (a * b) =
      kgLangCOmPAux_tau m 𝕂 a * kgLangCOmPAux_tau m 𝕂 b := by
    intro a ha b hb
    rw [show kgLangCOmPAux_tau m 𝕂 (a * b) =
        kgLangCOmPAux_tau m 𝕂 b * kgLangCOmPAux_tau m 𝕂 a from
      kgLangCOmPAux_tau_mul m 𝕂 a b]
    exact hBcomm _ (hτB b hb) _ (hτB a ha)
  have hτβ : ∀ a ∈ B, kgLangCOmPAux_tau m 𝕂 (β a) = β (kgLangCOmPAux_tau m 𝕂 a) := by
    intro a _
    change kgLangCOmPAux_tau m 𝕂 (a.map σ) = (kgLangCOmPAux_tau m 𝕂 a).map σ
    exact kgLangCOmPAux_tau_map m 𝕂 σ a
  have hH90 := kgLangC_span_h90_unitary (hp := hp) (hσ := hσo) P hPab hPodd B hB β hβP hβsc hβp
    (kgLangCOmPAux_tau m 𝕂) hτB hτadd hτmul hτone hττ hτβ
  let Ugl : Subgroup (GL (Fin m ⊕ Fin m) 𝕂) :=
    { carrier := {x | (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈ B ∧
        (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
          kgLangCOmPAux_tau m 𝕂 (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1}
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul]
          exact mul_mem hx.1 hy.1
        · rw [Units.val_mul, kgLangCOmPAux_tau_mul]
          calc (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
                (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
                (kgLangCOmPAux_tau m 𝕂 (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
                  kgLangCOmPAux_tau m 𝕂 (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂))
              = (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
                  ((y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
                    kgLangCOmPAux_tau m 𝕂 (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) *
                  kgLangCOmPAux_tau m 𝕂 (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
                  simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hy.2, Matrix.mul_one, hx.2]
      one_mem' := by
        refine ⟨B.one_mem, ?_⟩
        rw [Units.val_one, kgLangCOmPAux_tau_one, Matrix.mul_one]
      inv_mem' := by
        intro x hx
        have hinv : ((x⁻¹ : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
            kgLangCOmPAux_tau m 𝕂 ((x : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
          rw [Matrix.GeneralLinearGroup.coe_inv]
          exact Matrix.inv_eq_right_inv hx.2
        refine ⟨?_, ?_⟩
        · rw [hinv]; exact hτB _ hx.1
        · rw [hinv, kgLangCOmPAux_tau_tau]
          rw [show kgLangCOmPAux_tau m 𝕂 (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
              (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)⁻¹ from
            (Matrix.inv_eq_right_inv hx.2).symm]
          exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp ⟨x, rfl⟩) }
  have hUodd : Odd (Nat.card Ugl) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hdvd : 2 ∣ Nat.card Ugl := even_iff_two_dvd.mp heven
    letI : Fintype Ugl := Fintype.ofFinite Ugl
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hdvd
    have hx2U : (x : Ugl) ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx2 : (x : GL (Fin m ⊕ Fin m) 𝕂) ^ 2 = 1 := by
      have := congrArg (fun y : Ugl => (y : GL (Fin m ⊕ Fin m) 𝕂)) hx2U
      simpa using this
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx
      omega
    apply hxne
    set M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
      ((x : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) with hM
    have hval2 : M * M = 1 := by
      have := congrArg (fun y : GL (Fin m ⊕ Fin m) 𝕂 =>
        (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) hx2
      simpa [hM, pow_two] using this
    have hnil : IsNilpotent (M + 1) := by
      refine ⟨2, ?_⟩
      rw [pow_two]
      rw [show (M + 1) * (M + 1) = M * M + (M + M) + 1 from by noncomm_ring]
      rw [hval2, CharTwo.add_self_eq_zero, add_zero]
      exact CharTwo.add_self_eq_zero 1
    have hmem : M + 1 ∈ B := by
      rw [hM]
      exact add_mem (x.2).1 (Subalgebra.one_mem B)
    have hzero := (kgLangCOmPAux_adjoin_comm_reduced P hPab hPodd).2 _ hmem hnil
    have hx1mat : ((x : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1 := by
      have h : M = -1 := eq_neg_of_add_eq_zero_left hzero
      rw [CharTwo.neg_eq] at h
      rwa [hM] at h
    apply Subtype.ext
    apply Units.ext
    exact hx1mat
  have hUΩ : Ugl ≤ LargeEvenOmega (LargeEvenQPlus 𝕂 m) := by
    intro x hx
    have hxB : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈ B := hx.1
    have hxτ : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
        kgLangCOmPAux_tau m 𝕂 (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1 := hx.2
    have hpolar := kgLangCOmPAux_polar_preserved (𝕂 := 𝕂) (m := m) (x := x) hxτ
    have hPQ : ∀ g ∈ P, ∀ v,
        TableBOrth.qPlusForm 𝕂 m (Matrix.mulVec
          (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) v) =
        TableBOrth.qPlusForm 𝕂 m v := by
      intro g hg v
      rw [hP] at hg
      obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
      rw [TableBOrth.coe_qPlusForm]
      exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ A.2) v
    have hxspan : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈
        Submodule.span 𝕂 ((fun g : GL (Fin m ⊕ Fin m) 𝕂 =>
          (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) '' (P : Set _)) := by
      have h := (Subalgebra.mem_toSubmodule B).mpr hxB
      rwa [kgLangCOmPAux_adjoin_toSubmodule_eq_span P] at h
    have hQpres := kgLangC_quadratic_preserved (TableBOrth.qPlusForm 𝕂 m)
      (TableBOrth.nondegenerate_qPlusForm m) P hPab hPodd hPQ hxspan (by
        intro u v
        exact hpolar u v)
    have hT : ∃ T : Submodule 𝕂 (Fin m ⊕ Fin m → 𝕂),
        Module.finrank 𝕂 T = 3 ∧ ∀ y ∈ T, TableBOrth.qPlusForm 𝕂 m y = 0 := by
      let e : Fin 3 → Fin m ⊕ Fin m := fun i => Sum.inl ⟨i, by omega⟩
      have he : Function.Injective e := by
        intro i j h
        have := Sum.inl.inj h
        exact Fin.ext (by simpa using congrArg Fin.val this)
      have hli : LinearIndependent 𝕂 (fun i : Fin 3 =>
          (Pi.single (e i) (1 : 𝕂) : Fin m ⊕ Fin m → 𝕂)) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have h := congrFun hg (e i)
        simp only [Finset.sum_apply, Pi.smul_apply] at h
        rw [Finset.sum_eq_single i] at h
        · simpa [Pi.single_apply] using h
        · intro j _ hji
          have hne : e i ≠ e j := fun hc => hji (he hc.symm)
          simp [Pi.single_apply, hne]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      refine ⟨Submodule.span 𝕂 (Set.range (fun i : Fin 3 =>
        (Pi.single (e i) (1 : 𝕂) : Fin m ⊕ Fin m → 𝕂))), ?_, ?_⟩
      · rw [finrank_span_eq_card hli, Fintype.card_fin]
      · intro y hy
        have hy0 : ∀ i, y (Sum.inr i) = 0 := by
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
          · intro z hz
            obtain ⟨j, rfl⟩ := hz
            exact fun i => by simp [Pi.single_apply]
          · intro i; simp
          · intro a b _ _ ha hb i
            simp [Pi.add_apply, ha i, hb i]
          · intro cc a _ ha i
            simp [Pi.smul_apply, ha i]
        rw [TableBOrth.coe_qPlusForm]
        show (∑ i, y (Sum.inl i) * y (Sum.inr i)) = 0
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hy0 i, mul_zero]
    have hgm : x ^ Nat.card Ugl = 1 := by
      have h' := congrArg Subtype.val (pow_card_eq_one' (G := Ugl) (x := ⟨x, hx⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have hQmem := kgLangC_mem_omega_of_odd (TableBOrth.qPlusForm 𝕂 m)
      (TableBOrth.nondegenerate_qPlusForm m) hT (by
        intro v
        exact hQpres v) hUodd hgm
    rwa [TableBOrth.coe_qPlusForm] at hQmem
  let U : Subgroup (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :=
    Ugl.comap (LargeEvenOmega (LargeEvenQPlus 𝕂 m)).subtype
  have hUm : ∀ u : LargeEvenOmega (LargeEvenQPlus 𝕂 m),
      u ∈ U ↔ ((u : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈ B ∧
        ((u : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
          kgLangCOmPAux_tau m 𝕂 ((u : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1 :=
    fun u => Iff.rfl
  let N : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))) := U.map c
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · rintro n ⟨u, -, rfl⟩
    change c u ∈ (J : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))))
    rw [hJ]
    exact ⟨LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)) u, rfl⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    have hxy : x * y = y * x := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      exact hBcomm _ ((hUm x).mp hx).1 _ ((hUm y).mp hy).1
    rw [← map_mul, hxy, map_mul]
  · rintro n ⟨u, hu, rfl⟩
    refine ⟨S u, ?_, ?_⟩
    · have hSuB : ((((S u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂)) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) ∈ B := by
        rw [hS_val]
        exact hβB _ ((hUm u).mp hu).1
      refine (hUm (S u)).mpr ⟨hSuB, ?_⟩
      have hSu : (((S u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
          β (((u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
        rw [hS_val]; rfl
      rw [hSu, hτβ _ ((hUm u).mp hu).1, ← map_mul, ((hUm u).mp hu).2, map_one]
    · exact (hF0c u).symm
  · intro n hn hnorm
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hn
    have hiter : ∀ i, endPow ((MulAut.conj f).toMonoidHom) i (c u) = c (endPow S i u) := by
      intro i
      induction i with
      | zero => rw [endPow_apply]; rfl
      | succ i ih =>
          rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply, ih]
          rw [show endPow S (i + 1) u = S (endPow S i u) from by
            rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]]
          exact hF0c (endPow S i u)
    have hnormU : ((List.range p).map fun i => endPow S i u).prod = 1 := by
      apply hc_inj
      rw [map_one, MonoidHom.map_list_prod, List.map_map, ← hnorm]
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      exact (hiter i).symm
    set Mu : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
      (((u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) with hMu
    have hnormMat : ((List.range p).map fun i => (⇑β)^[i] Mu).prod = 1 := by
      have hiter_mat : ∀ i : ℕ, (⇑β)^[i] Mu =
          (((endPow S i u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) := by
        intro i
        rw [show (⇑β)^[i] Mu = Mu.map (σ ^ i) from
          kgLangCOmPAux_mapMatrix_iterate m 𝕂 σ i Mu, hMu]
        exact (kgLangCOmPAux_fieldOm_iter_val hm1 σ i u).symm
      have hlist : (List.range p).map (fun i : ℕ => (⇑β)^[i] Mu) =
          (List.range p).map (fun i : ℕ =>
            (((endPow S i u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) :=
        List.map_congr_left (fun i _ => hiter_mat i)
      rw [hlist]
      have hcoe : (List.range p).map (fun i : ℕ =>
            (((endPow S i u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)) =
          ((List.range p).map (fun i : ℕ => endPow S i u)).map
            ((Units.coeHom (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)).comp
              (LargeEvenOmega (LargeEvenQPlus 𝕂 m)).subtype) := by
        rw [List.map_map]; rfl
      rw [hcoe, ← MonoidHom.map_list_prod, hnormU, map_one]
    obtain ⟨s, hsB, hsτ, hsu⟩ := hH90 ((u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) :
      GL (Fin m ⊕ Fin m) 𝕂) ((hUm u).mp hu).1 ((hUm u).mp hu).2 hnormMat
    let sΩ : LargeEvenOmega (LargeEvenQPlus 𝕂 m) := ⟨s, hUΩ ⟨hsB, hsτ⟩⟩
    have hsU : sΩ ∈ U := by
      rw [hUm]
      exact ⟨hsB, hsτ⟩
    have hsu' : (((u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) =
        (((s : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂))⁻¹ *
          (((s : GL (Fin m ⊕ Fin m) 𝕂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)).map σ := by
      rw [hsu, Matrix.GeneralLinearGroup.coe_inv]
      rfl
    have hsuΩ : u = sΩ⁻¹ * (S sΩ) := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv,
        hS_val]
      exact hsu'
    refine ⟨c sΩ, Subgroup.mem_map.mpr ⟨sΩ, hsU, rfl⟩, ?_⟩
    rw [hsuΩ, map_mul, map_inv, ← hF0c]
    rfl
  · intro n hn
    have hncr : n ∈ c.range := by
      change n ∈ (c.range : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))))
      rw [hc_range]
      have h := (hEfix n hn).1
      change n ∈ (J : Set _) at h
      rwa [hJ] at h
    obtain ⟨u, rfl⟩ := hncr
    have huP : u ∈ Phat := by
      rw [hPhat, Subgroup.mem_comap]
      exact hn
    have huU : u ∈ U := by
      rw [hUm]
      refine ⟨?_, ?_⟩
      · rw [hB]
        exact Algebra.subset_adjoin ⟨(u : GL (Fin m ⊕ Fin m) 𝕂),
          Subgroup.mem_map.mpr ⟨u, huP, rfl⟩, rfl⟩
      · rw [kgLangCOmPAux_tau_eq_inv u]
        rw [show (((u : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) *
              ((((u⁻¹ : LargeEvenOmega (LargeEvenQPlus 𝕂 m)) : GL (Fin m ⊕ Fin m) 𝕂)) :
                Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂) = 1 from by
          rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
            Units.val_one]]
    exact Subgroup.mem_map.mpr ⟨u, huU, rfl⟩

theorem kgLangTorusDatumCont_omegaPlus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 4 ≤ m)
    (hpn : p ∣ n) (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n)
    (hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))
      (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))))
    (hZ : ∀ [Finite (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))))]
      (θ : HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) ⧸
        Subgroup.center (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))) ≃*
          LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))),
      commutator (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))) = ⊤ →
      Nat.Coprime
        (Nat.card (Subgroup.center (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))))) p) :
    KGLangTorusDatumCont p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))) := by
  haveI : CharP 𝕂 2 := LayerCC.charP_two_of_natCard h𝕂
  have hm3 : 3 ≤ m := by omega
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := 𝕂) hm3
  have hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)), a * b ≠ b * a :=
    kgLangCOmPAux_exists_noncomm_omegaPlus (𝕂 := 𝕂) hm3
  apply kgLangTorusDatumCont_of_models (R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))
    (I := LargeEvenInnSet _)
    (F := LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))) hp
  · exact hcyc hs hna
  · refine kgLangTorusMPart_of_inner (R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus 𝕂 m)))
      hp hs hna hcyc ?_ ?_ ?_ ?_ ?_
    · exact RecipeFieldOmega.ggRawFieldConj_omegaPlus (K := 𝕂) (m := m) (by omega) hp hp2
    · intro r
      exact ⟨r, rfl⟩
    · intro u hu _
      obtain ⟨r, hr⟩ := hu
      exact ⟨r, hr.symm⟩
    · intro J hJ f hf hfp
      exact kgLangC_torusInput_omegaPlus hp hp2 hm 𝕂 h𝕂 J hJ hf hfp
    · exact hZ

end CFSG.StandardType
