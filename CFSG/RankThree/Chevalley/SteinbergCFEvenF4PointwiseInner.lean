module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4RootSL2Traces
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.RankThree.Classical.SL2SemilinearRoots
public import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial

theorem dualRoot_neg_F4 {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : IsRoot ReeTag.F4.tag α) :
    ReeTag.F4.dualRoot (-α) = -ReeTag.F4.dualRoot α := by
  have h1 := ReeTag.duality_eq_dualRoot (t := .F4) (IsRoot.neg hα)
  have h2 := ReeTag.duality_eq_dualRoot (t := .F4) hα
  have h3 : ReeTag.F4.duality (-α) = -ReeTag.F4.duality α := by
    unfold ReeTag.duality ReeTag.lengthParam
    rw [ReeTag.quadForm_neg, ← smul_neg, ← map_neg]
    congr 2
  funext j
  have h4 := congrFun (h1.symm.trans (h3.trans (congrArg Neg.neg h2))) j
  simp only [Pi.neg_apply] at h4
  exact_mod_cast h4

theorem neg_mem_longRoots_F4 {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ ReeTag.F4.longRoots) :
    -α ∈ ReeTag.F4.longRoots :=
  ⟨IsRoot.neg hα.1, by rw [ReeTag.lengthParam, ReeTag.quadForm_neg]; exact hα.2⟩

variable {M : Type} [Field M] [Finite M] [CharP M ReeTag.F4.prime]

omit [Finite M] in
theorem rootSL2_uSL_F4 {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) (c : M) :
    rootSL2 ReeTag.F4.tag M β (uSL c) = pinnedX ReeTag.F4.tag M β c :=
  @rootSL2_uSL_of_charTwo _ M _ ‹CharP M ReeTag.F4.prime› _ hβ c

omit [Finite M] in
theorem rootSL2_vSL_F4 {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) (c : M) :
    rootSL2 ReeTag.F4.tag M β (vSL c) = pinnedX ReeTag.F4.tag M (-β) c :=
  @rootSL2_vSL_of_charTwo _ M _ ‹CharP M ReeTag.F4.prime› _ hβ c

theorem finiteExceptionalAut_rootSL2_long {β : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : β ∈ ReeTag.F4.longRoots) (B : SL2 M) :
    (ReeTag.F4.finiteExceptionalAut M ⟨rootSL2 ReeTag.F4.tag M β B, rootSL2_mem_adjointGroup β B⟩ :
      ModGL ReeTag.F4.tag M) = rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β) B := by
  have hΨ := ReeTag.isRoot_dualRoot hβ.1
  have h : (adjointGroup ReeTag.F4.tag M).subtype.comp
      ((ReeTag.F4.finiteExceptionalAut M).toMonoidHom.comp
        ((rootSL2 ReeTag.F4.tag M β).codRestrict _ fun B => rootSL2_mem_adjointGroup β B)) =
      rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change (ReeTag.F4.finiteExceptionalAut M ⟨rootSL2 ReeTag.F4.tag M β (uSL c), _⟩ :
          ModGL ReeTag.F4.tag M) = rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β) (uSL c)
        simp only [rootSL2_uSL_F4 hβ.1, rootSL2_uSL_F4 hΨ]
        rw [finiteExceptionalAut_pinnedX_long hβ]
      · change (ReeTag.F4.finiteExceptionalAut M ⟨rootSL2 ReeTag.F4.tag M β (vSL c), _⟩ :
          ModGL ReeTag.F4.tag M) = rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β) (vSL c)
        simp only [rootSL2_vSL_F4 hβ.1, rootSL2_vSL_F4 hΨ]
        rw [finiteExceptionalAut_pinnedX_long (neg_mem_longRoots_F4 hβ), dualRoot_neg_F4 hβ.1]
  exact DFunLike.congr_fun h B

theorem finiteExceptionalAut_rootSL2_short {β : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : β ∈ ReeTag.F4.shortRoots) {σ : M ≃+* M} (hσ : ∀ c, σ c = c ^ 2) (B : SL2 M) :
    (ReeTag.F4.finiteExceptionalAut M ⟨rootSL2 ReeTag.F4.tag M β B, rootSL2_mem_adjointGroup β B⟩ :
      ModGL ReeTag.F4.tag M) =
        rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β)
          (Matrix.SpecialLinearGroup.map σ.toRingHom B) := by
  have hΨ := ReeTag.isRoot_dualRoot hβ.1
  have h : (adjointGroup ReeTag.F4.tag M).subtype.comp
      ((ReeTag.F4.finiteExceptionalAut M).toMonoidHom.comp
        ((rootSL2 ReeTag.F4.tag M β).codRestrict _ fun B => rootSL2_mem_adjointGroup β B)) =
      (rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β)).comp
        (Matrix.SpecialLinearGroup.map σ.toRingHom) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change (ReeTag.F4.finiteExceptionalAut M ⟨rootSL2 ReeTag.F4.tag M β (uSL c), _⟩ :
          ModGL ReeTag.F4.tag M) = rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β)
            (Matrix.SpecialLinearGroup.map σ.toRingHom (uSL c))
        rw [map_uSL]
        simp only [rootSL2_uSL_F4 hβ.1, rootSL2_uSL_F4 hΨ]
        rw [finiteExceptionalAut_pinnedX_short hβ]
        show pinnedX ReeTag.F4.tag M _ (c ^ 2) = pinnedX ReeTag.F4.tag M _ (σ c)
        rw [hσ]
      · change (ReeTag.F4.finiteExceptionalAut M ⟨rootSL2 ReeTag.F4.tag M β (vSL c), _⟩ :
          ModGL ReeTag.F4.tag M) = rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot β)
            (Matrix.SpecialLinearGroup.map σ.toRingHom (vSL c))
        rw [map_vSL]
        simp only [rootSL2_vSL_F4 hβ.1, rootSL2_vSL_F4 hΨ]
        rw [finiteExceptionalAut_pinnedX_short (ReeTag.neg_mem_shortRoots hβ),
          dualRoot_neg_F4 hβ.1]
        show pinnedX ReeTag.F4.tag M _ (c ^ 2) = pinnedX ReeTag.F4.tag M _ (σ c)
        rw [hσ]
  exact DFunLike.congr_fun h B

theorem finiteFrobeniusAut_pow_rootSL2 {σ : M ≃+* M} (hσ : ∀ c, σ c = c ^ 2) (j : ℕ)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) (B : SL2 M) :
    ((ReeTag.F4.finiteFrobeniusAut M ^ j) ⟨rootSL2 ReeTag.F4.tag M β B,
      rootSL2_mem_adjointGroup β B⟩ : ModGL ReeTag.F4.tag M) =
        rootSL2 ReeTag.F4.tag M β (Matrix.SpecialLinearGroup.map (σ ^ j).toRingHom B) := by
  rw [ReeTag.coe_finiteFrobeniusAut_pow hσ j, units_map_entrywiseHom_eq_baseChangeGL_self]
  exact @baseChangeGL_rootSL2_of_charTwo _ M _ ‹CharP M ReeTag.F4.prime› M _ _ _ hβ B

theorem exists_ringEquiv_sq (M : Type) [Field M] [Finite M] [CharP M ReeTag.F4.prime] :
    ∃ σ : M ≃+* M, ∀ c, σ c = c ^ 2 := by
  have : CharP M 2 := ‹CharP M ReeTag.F4.prime›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (frobenius M 2) := frobenius_inj M 2
  exact ⟨RingEquiv.ofBijective (frobenius M 2) ⟨hinj, Finite.surjective_of_injective hinj⟩,
    fun c => frobenius_def 2 c⟩

theorem ringEquiv_pow_apply_sq {R : Type*} [CommRing R] {σ : R ≃+* R} (hσ : ∀ c, σ c = c ^ 2)
    (j : ℕ) (c : R) : (σ ^ j) c = c ^ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    change σ ((σ ^ j) c) = _
    rw [ih, hσ, ← pow_mul, ← pow_succ]

theorem trace_map_SL2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (B : Matrix.SpecialLinearGroup (Fin 2) R) :
    ((Matrix.SpecialLinearGroup.map f B : Matrix.SpecialLinearGroup (Fin 2) S) :
      Matrix (Fin 2) (Fin 2) S).trace = f (B : Matrix (Fin 2) (Fin 2) R).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
  rfl

theorem trace_conjSL {R : Type*} [Field R] (P : GL (Fin 2) R) (B : SL2 R) :
    ((CFSG.RankThree.Classical.conjSL P B : SL2 R) : Matrix (Fin 2) (Fin 2) R).trace =
      (B : Matrix (Fin 2) (Fin 2) R).trace := by
  change ((P : Matrix (Fin 2) (Fin 2) R) * B * (↑P⁻¹ : Matrix (Fin 2) (Fin 2) R)).trace = _
  rw [Matrix.trace_mul_cycle, show (↑P⁻¹ : Matrix (Fin 2) (Fin 2) R) *
    (P : Matrix (Fin 2) (Fin 2) R) = 1 from P.inv_mul, Matrix.one_mul]

variable {K : Type} [Field K]

@[expose] def entrywiseInclusionF4 (ι : K →+* M) :
    adjointGroup ReeTag.F4.tag K →* adjointGroup ReeTag.F4.tag M :=
  ((baseChangeGL ι).comp (adjointGroup ReeTag.F4.tag K).subtype).codRestrict _ fun g =>
    baseChangeGL_mem_adjointGroup ι g.2

theorem finiteExceptionalAut_comp_entrywiseInclusionF4 [Finite K] [CharP K ReeTag.F4.prime]
    (ι : K →+* M) :
    (ReeTag.F4.finiteExceptionalAut M).toMonoidHom.comp (entrywiseInclusionF4 ι) =
      (entrywiseInclusionF4 ι).comp (ReeTag.F4.finiteExceptionalAut K).toMonoidHom := by
  refine adjointGroup_hom_ext (fun i c => ?_) fun i c => ?_
  · have h1 : entrywiseInclusionF4 ι (xElement i c) = xElement i (ι c) :=
      Subtype.ext (baseChangeGL_xUnit ι i c)
    have h2 : entrywiseInclusionF4 ι (xElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.exponent i)) =
        xElement (ReeTag.F4.perm i) (ι c ^ ReeTag.F4.exponent i) :=
      Subtype.ext ((baseChangeGL_xUnit ι _ _).trans (by rw [map_pow]; rfl))
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1,
      ReeTag.finiteExceptionalAut_xElement, h2]
  · have h1 : entrywiseInclusionF4 ι (yElement i c) = yElement i (ι c) :=
      Subtype.ext (baseChangeGL_yUnit ι i c)
    have h2 : entrywiseInclusionF4 ι (yElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.exponent i)) =
        yElement (ReeTag.F4.perm i) (ι c ^ ReeTag.F4.exponent i) :=
      Subtype.ext ((baseChangeGL_yUnit ι _ _).trans (by rw [map_pow]; rfl))
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1,
      ReeTag.finiteExceptionalAut_yElement, h2]

theorem finiteExceptionalAut_pow_entrywiseInclusionF4 [Finite K] [CharP K ReeTag.F4.prime]
    (ι : K →+* M) (k : ℕ) (h : adjointGroup ReeTag.F4.tag K) :
    (ReeTag.F4.finiteExceptionalAut M ^ k) (entrywiseInclusionF4 ι h) =
      entrywiseInclusionF4 ι ((ReeTag.F4.finiteExceptionalAut K ^ k) h) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
    have h1 := DFunLike.congr_fun (finiteExceptionalAut_comp_entrywiseInclusionF4 (M := M) ι) h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    rw [h1, ih]

omit [Finite M] in
theorem neg_one_eq_one_F4 {R : Type*} [Ring R] [CharP R ReeTag.F4.prime] : (-1 : R) = 1 :=
  @CharTwo.neg_eq R _ ‹CharP R ReeTag.F4.prime› 1

omit [Finite M] in
theorem sq_injective_F4 {a b : M} (h : a ^ 2 = b ^ 2) : a = b :=
  @CharTwo.sq_injective M _ ‹CharP M ReeTag.F4.prime› _ a b h

omit [Finite M] [CharP M ReeTag.F4.prime] in
theorem trace_restrict_congr {V : Type*} [AddCommGroup V] [Module M V] (p : Submodule M V)
    {g g' : V →ₗ[M] V} (e : g = g') (h : ∀ v ∈ p, g v ∈ p) (h' : ∀ v ∈ p, g' v ∈ p) :
    LinearMap.trace M p (g.restrict h) = LinearMap.trace M p (g'.restrict h') := by
  subst e
  rfl

omit [Finite M] in
theorem trace_rootSL2_F4 {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β)
    (B : SL2 M) :
    LinearMap.trace M (RootModule ReeTag.F4.tag M)
        (rootSL2 ReeTag.F4.tag M β B : Module.End M (RootModule ReeTag.F4.tag M)) =
      (B : Matrix (Fin 2) (Fin 2) M).trace ^ 2 ∧
    ∀ h : ∀ v ∈ ReeTag.F4.shortModule M, (rootSL2 ReeTag.F4.tag M β B :
        Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M,
      (β ∈ ReeTag.F4.longRoots → LinearMap.trace M (ReeTag.F4.shortModule M)
          ((rootSL2 ReeTag.F4.tag M β B :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h) = 0) ∧
      (β ∈ ReeTag.F4.shortRoots → LinearMap.trace M (ReeTag.F4.shortModule M)
          ((rootSL2 ReeTag.F4.tag M β B :
            Module.End M (RootModule ReeTag.F4.tag M)).restrict h) =
        (B : Matrix (Fin 2) (Fin 2) M).trace ^ 2) := by
  obtain ⟨h1, -, h3⟩ :=
    @even_F4_root_SL2_adjoint_and_short_module_traces M _ ‹CharP M ReeTag.F4.prime› β hβ B
  exact ⟨h1, h3⟩

omit [Finite M] in
theorem mapsTo_shortModule_F4' {X : ModGL ReeTag.F4.tag M}
    (hX : X ∈ adjointGroup ReeTag.F4.tag M) :
    ∀ v ∈ ReeTag.F4.shortModule M,
      (X : Module.End M (RootModule ReeTag.F4.tag M)) v ∈ ReeTag.F4.shortModule M :=
  @mapsTo_shortModule_F4 M _ ‹CharP M ReeTag.F4.prime› X hX

omit [Finite M] in
theorem traces_eq_of_conj_eq {v X Y : adjointGroup ReeTag.F4.tag M} (e : v * Y * v⁻¹ = X) :
    LinearMap.trace M (RootModule ReeTag.F4.tag M)
        ((X : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) =
      LinearMap.trace M (RootModule ReeTag.F4.tag M)
        ((Y : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) ∧
    LinearMap.trace M (ReeTag.F4.shortModule M)
        (((X : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)).restrict
          (mapsTo_shortModule_F4' X.2)) =
      LinearMap.trace M (ReeTag.F4.shortModule M)
        (((Y : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)).restrict
          (mapsTo_shortModule_F4' Y.2)) := by
  have hE : ((X : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) =
      ((v : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) *
        ((Y : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) *
        (((v : ModGL ReeTag.F4.tag M)⁻¹ : ModGL ReeTag.F4.tag M) :
          Module.End M (RootModule ReeTag.F4.tag M)) := by
    rw [← e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
  refine ⟨by rw [hE, LinearMap.trace_conj], ?_⟩
  have hv := mapsTo_shortModule_F4' v.2
  have hv' := mapsTo_shortModule_F4' (inv_mem v.2)
  rw [trace_restrict_congr _ hE _ (hE ▸ mapsTo_shortModule_F4' X.2)]
  exact trace_restrict_conj _ _ _ hv hv' _ _


theorem even_F4_descended_root_SL2_pointwise_automorphisms_inner {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (M : Type) [Field M] [Finite M]
    (ι : K →+* M) (R₀ : Subgroup (adjointGroup ReeTag.F4.tag K)) {g : ModGL ReeTag.F4.tag M}
    (hg : g ∈ adjointGroup ReeTag.F4.tag M) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) (P : GL (Fin 2) M)
    (hR : (R₀.map ((baseChangeGL ι).comp (adjointGroup ReeTag.F4.tag K).subtype)).map
        (MulAut.conj g).toMonoidHom =
      ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
        (rootSL2 ReeTag.F4.tag M α)) :
    (∀ η : MulAut (adjointGroup ReeTag.F4.tag K), (∀ r ∈ R₀, η r = r) →
      η ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range) ∧
    ∀ η : MulAut (adjointGroup ReeTag.F4.tag K), (∀ r ∈ R₀, η r = r) ↔
      ∃ y ∈ Subgroup.centralizer (R₀ : Set (adjointGroup ReeTag.F4.tag K)),
        η = MulAut.conj y := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K ReeTag.F4.prime := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP M ReeTag.F4.prime := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact charP_of_injective_ringHom ι.injective 2
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_sq M
  let x : SL2 K → adjointGroup ReeTag.F4.tag M := fun A =>
    ⟨rootSL2 ReeTag.F4.tag M α (CFSG.RankThree.Classical.conjSL P
      (Matrix.SpecialLinearGroup.map ι A)), rootSL2_mem_adjointGroup α _⟩
  have hmemR : ∀ A : SL2 K, ∃ r ∈ R₀,
      (⟨g, hg⟩ : adjointGroup ReeTag.F4.tag M) * entrywiseInclusionF4 ι r *
        (⟨g, hg⟩ : adjointGroup ReeTag.F4.tag M)⁻¹ = x A := by
    intro A
    have hx : (x A : ModGL ReeTag.F4.tag M) ∈
        ((Matrix.SpecialLinearGroup.map ι).range.map (CFSG.RankThree.Classical.conjSL P)).map
          (rootSL2 ReeTag.F4.tag M α) := ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    rw [← hR] at hx
    obtain ⟨_, ⟨r, hr, rfl⟩, hrx⟩ := hx
    exact ⟨r, hr, Subtype.ext hrx⟩
  have htrx : ∀ A : SL2 K, ((CFSG.RankThree.Classical.conjSL P
      (Matrix.SpecialLinearGroup.map ι A) : SL2 M) : Matrix (Fin 2) (Fin 2) M).trace =
        ι (A : Matrix (Fin 2) (Fin 2) K).trace := fun A => by
    rw [trace_conjSL, trace_map_SL2]
  have hmain : ∀ η : MulAut (adjointGroup ReeTag.F4.tag K), (∀ r ∈ R₀, η r = r) →
      η ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range := by
    intro η hη
    obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF η
    simp only at hyk
    set φ := ReeTag.F4.finiteExceptionalAut M ^ (k : ℕ) with hφ
    set g' : adjointGroup ReeTag.F4.tag M := ⟨g, hg⟩ with hg'
    set v : adjointGroup ReeTag.F4.tag M := g' * entrywiseInclusionF4 ι y * (φ g')⁻¹ with hv
    have hkey : ∀ A : SL2 K, v * φ (x A) * v⁻¹ = x A := by
      intro A
      obtain ⟨r, hr, hrx⟩ := hmemR A
      have hηr : y * (ReeTag.F4.finiteExceptionalAut K ^ (k : ℕ)) r * y⁻¹ = r := by
        have h1 := hη r hr
        rw [hyk, MulAut.mul_apply, MulAut.conj_apply] at h1
        exact h1
      have hincl : entrywiseInclusionF4 ι y * φ (entrywiseInclusionF4 ι r) *
          (entrywiseInclusionF4 ι y)⁻¹ = entrywiseInclusionF4 ι r := by
        rw [hφ, finiteExceptionalAut_pow_entrywiseInclusionF4, ← map_inv, ← map_mul, ← map_mul,
          hηr]
      rw [← hrx, map_mul, map_mul, map_inv, hv]
      calc g' * entrywiseInclusionF4 ι y * (φ g')⁻¹ *
            (φ g' * φ (entrywiseInclusionF4 ι r) * (φ g')⁻¹) *
            (g' * entrywiseInclusionF4 ι y * (φ g')⁻¹)⁻¹ =
          g' * (entrywiseInclusionF4 ι y * φ (entrywiseInclusionF4 ι r) *
            (entrywiseInclusionF4 ι y)⁻¹) * g'⁻¹ := by group
        _ = g' * entrywiseInclusionF4 ι r * g'⁻¹ := by rw [hincl]
    have hkeven : Even (k : ℕ) := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨j, hj⟩ := hodd
      let A₁ : SL2 K := ⟨!![1, 1; 1, 0], by
        rw [Matrix.det_fin_two_of, mul_zero, mul_one, zero_sub, neg_one_eq_one_F4]⟩
      have htr1 : ((CFSG.RankThree.Classical.conjSL P (Matrix.SpecialLinearGroup.map ι A₁) :
          SL2 M) : Matrix (Fin 2) (Fin 2) M).trace = 1 := by
        rw [htrx, show (A₁ : Matrix (Fin 2) (Fin 2) K).trace = 1 by
          rw [show (A₁ : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, 0] from rfl,
            Matrix.trace_fin_two_of, add_zero], map_one]
      set B₁ := CFSG.RankThree.Classical.conjSL P (Matrix.SpecialLinearGroup.map ι A₁) with hB₁
      have hFr : (ReeTag.F4.finiteFrobeniusAut M ^ j) (x A₁) =
          ⟨rootSL2 ReeTag.F4.tag M α (Matrix.SpecialLinearGroup.map (σ ^ j).toRingHom B₁),
            rootSL2_mem_adjointGroup α _⟩ :=
        Subtype.ext (finiteFrobeniusAut_pow_rootSL2 hσ j hα B₁)
      have hφx : φ (x A₁) = ReeTag.F4.finiteExceptionalAut M
          ((ReeTag.F4.finiteFrobeniusAut M ^ j) (x A₁)) := by
        rw [hφ, hj, pow_succ', MulAut.mul_apply, finiteExceptionalAut_pow_two_mul]
      have htrj : ((Matrix.SpecialLinearGroup.map (σ ^ j).toRingHom B₁ : SL2 M) :
          Matrix (Fin 2) (Fin 2) M).trace = 1 := by
        rw [trace_map_SL2, htr1, map_one]
      have hI := (traces_eq_of_conj_eq (hkey A₁)).2
      rcases (show α ∈ ReeTag.F4.shortRoots ∪ ReeTag.F4.longRoots from
        (ReeTag.shortRoots_union_longRoots _).symm ▸ hα) with hs | hl
      ·
        have hΨ : ReeTag.F4.dualRoot α ∈ ReeTag.F4.longRoots := by
          obtain ⟨γ, hγ, hγα⟩ := (ReeTag.bijOn_dualRoot ReeTag.F4).2.2 hs
          rw [← hγα, ReeTag.dualRoot_dualRoot hγ.1]
          exact hγ
        have e1 : ((φ (x A₁) : ModGL ReeTag.F4.tag M) :
            Module.End M (RootModule ReeTag.F4.tag M)) =
            (rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot α) (Matrix.SpecialLinearGroup.map
              σ.toRingHom (Matrix.SpecialLinearGroup.map (σ ^ j).toRingHom B₁)) :
                Module.End M (RootModule ReeTag.F4.tag M)) := by
          rw [hφx, hFr, finiteExceptionalAut_rootSL2_short hs hσ]
        rw [trace_restrict_congr _ e1 _ (e1 ▸ mapsTo_shortModule_F4' (φ (x A₁)).2),
          ((trace_rootSL2_F4 (ReeTag.isRoot_dualRoot hα) _).2 _).1 hΨ] at hI
        rw [((trace_rootSL2_F4 hα B₁).2 _).2 hs, htr1, one_pow] at hI
        exact one_ne_zero hI
      ·
        have hΨ : ReeTag.F4.dualRoot α ∈ ReeTag.F4.shortRoots := (ReeTag.bijOn_dualRoot _).1 hl
        have e1 : ((φ (x A₁) : ModGL ReeTag.F4.tag M) :
            Module.End M (RootModule ReeTag.F4.tag M)) =
            (rootSL2 ReeTag.F4.tag M (ReeTag.F4.dualRoot α)
              (Matrix.SpecialLinearGroup.map (σ ^ j).toRingHom B₁) :
                Module.End M (RootModule ReeTag.F4.tag M)) := by
          rw [hφx, hFr, finiteExceptionalAut_rootSL2_long hl]
        rw [trace_restrict_congr _ e1 _ (e1 ▸ mapsTo_shortModule_F4' (φ (x A₁)).2),
          ((trace_rootSL2_F4 (ReeTag.isRoot_dualRoot hα) _).2 _).2 hΨ, htrj, one_pow] at hI
        rw [((trace_rootSL2_F4 hα B₁).2 _).1 hl] at hI
        exact zero_ne_one hI
    obtain ⟨j, hj⟩ := hkeven
    have hφFr : φ = ReeTag.F4.finiteFrobeniusAut M ^ j := by
      rw [hφ, hj, ← two_mul, finiteExceptionalAut_pow_two_mul]
    have hfix : ∀ t : K, t ^ 2 ^ j = t := by
      intro t
      let A : SL2 K := ⟨!![t, 1; 1, 0], by
        rw [Matrix.det_fin_two_of, mul_zero, mul_one, zero_sub, neg_one_eq_one_F4]⟩
      have htrA : ((CFSG.RankThree.Classical.conjSL P (Matrix.SpecialLinearGroup.map ι A) :
          SL2 M) : Matrix (Fin 2) (Fin 2) M).trace = ι t := by
        rw [htrx, show (A : Matrix (Fin 2) (Fin 2) K) = !![t, 1; 1, 0] from rfl,
          Matrix.trace_fin_two_of, add_zero]
      have hV := (traces_eq_of_conj_eq (hkey A)).1
      have e1 : ((φ (x A) : ModGL ReeTag.F4.tag M) :
          Module.End M (RootModule ReeTag.F4.tag M)) =
          (rootSL2 ReeTag.F4.tag M α (Matrix.SpecialLinearGroup.map (σ ^ j).toRingHom
            (CFSG.RankThree.Classical.conjSL P (Matrix.SpecialLinearGroup.map ι A))) :
              Module.End M (RootModule ReeTag.F4.tag M)) := by
        rw [hφFr]
        exact congrArg Units.val (finiteFrobeniusAut_pow_rootSL2 hσ j hα _)
      have hL : LinearMap.trace M (RootModule ReeTag.F4.tag M) ((x A : ModGL ReeTag.F4.tag M) :
          Module.End M (RootModule ReeTag.F4.tag M)) = ι t ^ 2 := by
        change LinearMap.trace M (RootModule ReeTag.F4.tag M) (rootSL2 ReeTag.F4.tag M α
          (CFSG.RankThree.Classical.conjSL P (Matrix.SpecialLinearGroup.map ι A)) :
            Module.End M (RootModule ReeTag.F4.tag M)) = _
        rw [(trace_rootSL2_F4 hα _).1, htrA]
      have hRt : LinearMap.trace M (RootModule ReeTag.F4.tag M)
          ((φ (x A) : ModGL ReeTag.F4.tag M) : Module.End M (RootModule ReeTag.F4.tag M)) =
            (ι t ^ 2 ^ j) ^ 2 := by
        rw [e1, (trace_rootSL2_F4 hα _).1, trace_map_SL2, htrA]
        change ((σ ^ j) (ι t)) ^ 2 = _
        rw [ringEquiv_pow_apply_sq hσ]
      rw [hL, hRt] at hV
      have h1 := sq_injective_F4 hV
      apply ι.injective
      rw [map_pow, ← h1]
    obtain ⟨φK, hφK, hφKord, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
    have hφKj : φK ^ j = 1 := RingEquiv.ext fun t => by
      rw [ringEquiv_pow_apply_sq hφK, hfix]
      rfl
    have hfj : f ∣ j := hφKord ▸ orderOf_dvd_of_pow_eq_one hφKj
    have hjf : j < f := by
      have := k.2
      omega
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hfj hjf
    refine ⟨y, ?_⟩
    rw [hyk, show (k : ℕ) = 0 by omega, pow_zero, mul_one]
  refine ⟨hmain, fun η => ⟨fun hη => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hmain η hη
    refine ⟨y, Subgroup.mem_centralizer_iff.2 fun r hr => ?_, rfl⟩
    have h1 := hη r hr
    rw [MulAut.conj_apply] at h1
    calc r * y = y * r * y⁻¹ * y := by rw [h1]
      _ = y * r := by group
  · rintro ⟨y, hy, rfl⟩ r hr
    rw [MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.1 hy r hr, mul_inv_cancel_right]

end CFSG.RankThree.Chevalley
