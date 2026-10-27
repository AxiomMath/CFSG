module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bOriginalActorLift
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public noncomputable section


namespace CFSG.StandardType.E4bOriginalField

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType.E4bLift CFSG.StandardType.E4bOriginalLift
open CFSG.StandardType.SCFourCover CFSG.StandardType.GGFinModel
open scoped MatrixGroups

theorem four_lt_card_of_ninth_root {F : Type} [Field F] [Finite F]
    {ζ ω : Fˣ} (hζ : ζ ^ 3 = ω) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    4 < Nat.card F := by
  have hζ9 : ζ ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hζ, hω3]
  have hζ3ne : ζ ^ 3 ≠ 1 := by
    rw [hζ]
    exact hω1
  have hζne1 : ζ ≠ 1 := by
    intro h
    apply hζ3ne
    rw [h, one_pow]
  have hordvd : orderOf ζ ∣ 9 := orderOf_dvd_iff_pow_eq_one.mpr hζ9
  have hdvd : orderOf ζ ∣ 3 ^ 2 := by
    simpa using hordvd
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hord : orderOf ζ = 9 := by
    interval_cases k
    · exfalso
      apply hζne1
      simpa [hk] using pow_orderOf_eq_one ζ
    · exfalso
      apply hζ3ne
      simpa [hk] using pow_orderOf_eq_one ζ
    · simpa using hk
  have h9 : 9 ∣ Nat.card Fˣ := by
    rw [← hord]
    exact orderOf_dvd_natCard ζ
  rw [Nat.card_units] at h9
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  have h9le : 9 ≤ Nat.card F - 1 := Nat.le_of_dvd (by omega) h9
  omega

theorem exists_common_field_original_actor_model
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : ↥J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center ↥J)
    (hperf : commutator ↥J = ⊤)
    (hAI : ∀ a ∈ actualRecipeActorGroup hN,
      ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : ↥J, φ (ψ l) = ψ (a l))
    {y0 : ModGL Tag.E6 GGL} (hy0 : y0 ∈ adjointGroup Tag.E6 GGL)
    {ωΩ : GGLˣ} (hω3 : ωΩ ^ 3 = 1) (hω1 : ωΩ ≠ 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (ιK : K →+* F) (κ : F →+* GGL)
      (ζF ωF : Fˣ) (y0F : adjointGroup Tag.E6 F)
      (eF : actualRecipeActorGroup hN →* adjointGroup Tag.E6 F)
      (t : ↥(e6Data_valid.minGroup F))
      (σF : GGL →+* GGL),
      κ.comp ιK = algebraMap K GGL ∧
      Units.map κ ωF = ωΩ ∧
      (Units.map κ ζF) ^ 3 = ωΩ ∧
      ζF ^ 3 = ωF ∧ ωF ^ 3 = 1 ∧ ωF ≠ 1 ∧
      4 < Nat.card F ∧
      (∀ b, σF b = b ^ Nat.card F) ∧
      baseChangeGL κ (y0F : ModGL Tag.E6 F) = y0 ∧
      e6Isogeny F t = y0F ∧
      baseChangeGL κ ((e6Isogeny F t : adjointGroup Tag.E6 F) : ModGL Tag.E6 F) = y0 ∧
      (∀ j : ↥J, baseChangeGL κ
        (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j) =
          y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) j * y0⁻¹) ∧
      (∀ a : actualRecipeActorGroup hN, baseChangeGL κ ((eF a : ModGL Tag.E6 F)) =
        y0 * (recipeActorModelEquiv (A := actualRecipeActorGroup hN)
          hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL Tag.E6 GGL) * y0⁻¹) ∧
      (∀ (a : actualRecipeActorGroup hN) (j : ↥J),
        originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t (a.1 j) =
          (eF a : ModGL Tag.E6 F) *
            originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j *
            (eF a : ModGL Tag.E6 F)⁻¹) := by
  classical
  haveI : IsAlgClosed GGL := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K GGL := IsAlgClosure.isAlgebraic
  obtain ⟨ζΩ0, hζΩ0⟩ := IsAlgClosed.exists_pow_nat_eq (ωΩ : GGL) (by norm_num : 0 < 3)
  have hζΩ0ne : ζΩ0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hζΩ0
    exact Units.ne_zero ωΩ hζΩ0.symm
  let ζΩ : GGLˣ := Units.mk0 ζΩ0 hζΩ0ne
  have hζΩ : ζΩ ^ 3 = ωΩ := by
    apply Units.ext
    change ζΩ0 ^ 3 = (ωΩ : GGL)
    exact hζΩ0
  obtain ⟨E, hEfin, hζE, hKE⟩ :=
    exists_finite_subfield_of_finset (K := K) (L := GGL) ({(ζΩ : GGL)} : Finset GGL)
  letI : Field E := inferInstance
  letI : Finite E := hEfin
  have hζE_mem : (ζΩ : GGL) ∈ E := hζE (by simp)
  have hωE_mem : (ωΩ : GGL) ∈ E := by
    have hωeq : (ωΩ : GGL) = (ζΩ : GGL) ^ 3 := by
      rw [← hζΩ]
      rfl
    rw [hωeq]
    simpa [pow_succ, pow_two, mul_assoc] using
      E.mul_mem (E.mul_mem hζE_mem hζE_mem) hζE_mem
  let ζE : Eˣ := Units.mk0 ⟨ζΩ, hζE_mem⟩ (by
    intro h
    exact Units.ne_zero ζΩ (congrArg Subtype.val h))
  let ωE : Eˣ := Units.mk0 ⟨ωΩ, hωE_mem⟩ (by
    intro h
    exact Units.ne_zero ωΩ (congrArg Subtype.val h))
  let ιKE : K →+* E :=
    { toFun := fun x => ⟨algebraMap K GGL x, hKE ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  obtain ⟨F1, hF1field, hF1fin, κ1, ι1, hcomp1, hy0desc⟩ :=
    CFSG.StandardType.LieCore.M6c.exists_finite_subfield_lift_adjoint
      (S := ({y0} : Finset (ModGL Tag.E6 GGL)))
      (hS := by
        intro s hs
        have hs' : s = y0 := by simpa using hs
        subst s
        exact hy0)
      E E.subtype
  letI : Field F1 := hF1field
  letI : Finite F1 := hF1fin
  obtain ⟨y0F1, hy0F1mem, hy0F1base⟩ := hy0desc y0 (by simp)
  obtain ⟨F, hFfield, hFfin, hFchar, κ2, ι, hcomp2, e_k, j_k, hek, hjk, hconj, hinj⟩ :=
    CFSG.StandardType.SCFourCover.exists_actual_recipe_action_finite_descent
      (G := G) hN hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI F1 ι1
  letI : Field F := hFfield
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  let ιK : K →+* F := κ2.comp (κ1.comp ιKE)
  have hιK : ι.comp ιK = algebraMap K GGL := by
    ext x
    change ι (κ2 (κ1 (ιKE x))) = (algebraMap K GGL) x
    rw [← RingHom.comp_apply, hcomp2, ← RingHom.comp_apply, hcomp1]
    rfl
  let y0F : adjointGroup Tag.E6 F :=
    ⟨baseChangeGL κ2 (y0F1 : ModGL Tag.E6 F1),
      baseChangeGL_mem_adjointGroup κ2 hy0F1mem⟩
  have hy0F : baseChangeGL ι (y0F : ModGL Tag.E6 F) = y0 := by
    change baseChangeGL ι (baseChangeGL κ2 (y0F1 : ModGL Tag.E6 F1)) = y0
    rw [baseChangeGL_baseChangeGL, hcomp2, hy0F1base]
  let ζF1 : F1ˣ := Units.map κ1 ζE
  let ωF1 : F1ˣ := Units.map κ1 ωE
  let ζF : Fˣ := Units.map κ2 ζF1
  let ωF : Fˣ := Units.map κ2 ωF1
  have hζF : Units.map ι ζF = ζΩ := by
    apply Units.ext
    change ι (κ2 (κ1 (ζE : E))) = (ζΩ : GGL)
    rw [← RingHom.comp_apply, hcomp2, ← RingHom.comp_apply, hcomp1]
    rfl
  have hωF : Units.map ι ωF = ωΩ := by
    apply Units.ext
    change ι (κ2 (κ1 (ωE : E))) = (ωΩ : GGL)
    rw [← RingHom.comp_apply, hcomp2, ← RingHom.comp_apply, hcomp1]
    rfl
  have hζFval : ι (ζF : F) = (ζΩ : GGL) := congrArg Units.val hζF
  have hωFval : ι (ωF : F) = (ωΩ : GGL) := congrArg Units.val hωF
  have hζF3 : ζF ^ 3 = ωF := by
    apply Units.ext
    apply ι.injective
    calc
      ι ((ζF ^ 3 : Fˣ) : F) = (ι (ζF : F)) ^ 3 := by simp
      _ = (ζΩ : GGL) ^ 3 := by rw [hζFval]
      _ = (ωΩ : GGL) := by simpa using congrArg Units.val hζΩ
      _ = ι (ωF : F) := by rw [hωFval]
  have hωF3 : ωF ^ 3 = 1 := by
    apply Units.ext
    apply ι.injective
    calc
      ι ((ωF ^ 3 : Fˣ) : F) = (ι (ωF : F)) ^ 3 := by simp
      _ = (ωΩ : GGL) ^ 3 := by rw [hωFval]
      _ = 1 := by simpa using congrArg Units.val hω3
      _ = ι (1 : F) := by simp
  have hωF1 : ωF ≠ 1 := by
    intro h
    apply hω1
    rw [← hωF, h]
    simp
  have hcard4 : 4 < Nat.card F :=
    four_lt_card_of_ninth_root hζF3 hωF3 hωF1
  obtain ⟨t, ht⟩ := e6Isogeny_surjective F y0F
  let eF : actualRecipeActorGroup hN →* adjointGroup Tag.E6 F :=
    (MulAut.conj y0F).toMonoidHom.comp e_k
  have heF : ∀ a : actualRecipeActorGroup hN,
      baseChangeGL ι ((eF a : ModGL Tag.E6 F)) =
        y0 * (recipeActorModelEquiv (A := actualRecipeActorGroup hN)
          hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL Tag.E6 GGL) * y0⁻¹ := by
    intro a
    have heka : baseChangeGL ι (e_k a : ModGL Tag.E6 F) =
        (recipeActorModelEquiv (A := actualRecipeActorGroup hN)
          hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL Tag.E6 GGL) := by
      simpa using hek a
    change baseChangeGL ι ((y0F : ModGL Tag.E6 F) * (e_k a : ModGL Tag.E6 F) *
      (y0F : ModGL Tag.E6 F)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hy0F, heka]
  have hmodelJ : ∀ j : ↥J, baseChangeGL ι
      (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j) =
        y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) j * y0⁻¹ := by
    intro j
    have hM := originalM_apply (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ)
      (ι := ιK) (t := t) j
    rw [ht, MulAut.conj_apply] at hM
    have hmid : baseChangeGL (τ := Tag.E6) ι
        (baseChangeGL (τ := Tag.E6) ιK ((ε.symm (ψ j)).1)) =
        recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) j := by
      rw [baseChangeGL_baseChangeGL (f := ιK) (f' := ι)
        (g := (show ModGL Tag.E6 K from ((ε.symm (ψ j)).1))), hιK]
      exact (recipeMatrixHom_apply (Ω := GGL) σ ε (ψ := ψ) j).symm
    rw [hM, map_mul, map_mul, map_inv, hy0F, hmid]
  have hmodel : ∀ (a : actualRecipeActorGroup hN) (j : ↥J),
      originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t (a.1 j) =
        (eF a : ModGL Tag.E6 F) *
          originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) ιK t j *
          (eF a : ModGL Tag.E6 F)⁻¹ := by
    intro a j
    apply baseChangeGL_injective ι
    rw [hmodelJ (a.1 j), map_mul, map_mul, map_inv, heF a, hmodelJ j]
    have hseed := E4bActorSeed.recipeActorModelEquiv_conj_recipeMatrix
      (A := actualRecipeActorGroup hN) (Ω := GGL)
      hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a j
    rw [← hseed]
    group
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hfprime, hFcard⟩ := FiniteField.card F 2
  have hFcard' : Nat.card F = 2 ^ (f : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  let σF : GGL →+* GGL := ggFrobT (f : ℕ)
  have hσF : ∀ b, σF b = b ^ Nat.card F := by
    intro b
    change ggFrobT (f : ℕ) b = b ^ Nat.card F
    rw [ggFrobT_apply, hFcard']
  have hζFmap3 : (Units.map ι ζF) ^ 3 = ωΩ := by
    rw [← map_pow, hζF3, hωF]
  have hπt : baseChangeGL ι ((e6Isogeny F t : adjointGroup Tag.E6 F) : ModGL Tag.E6 F) = y0 := by
    rw [ht, hy0F]
  exact ⟨F, hFfield, hFfin, hFchar, ιK, ι, ζF, ωF, y0F, eF, t, σF,
    hιK, hωF, hζFmap3, hζF3, hωF3, hωF1, hcard4, hσF, hy0F, ht, hπt, hmodelJ, heF, hmodel⟩

end CFSG.StandardType.E4bOriginalField
