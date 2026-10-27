module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModSp4OuterFlip

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer

open Matrix CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Semidihedral.Principal Representation

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

private theorem three_mul_le_four_pow_sub_one (k : ℕ) : 3 * k ≤ 4 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem sum_weight_le_finrank (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F (antiSp F) V) (O : Finset (Finset ℕ))
    (hO : ∀ C ∈ O, C ⊆ Finset.range (2 * f)) :
    ∑ C ∈ O, 3 * C.card * repMultiplicity ρ (matRep (tensorRepS (F := F) F C)) ≤
      Module.finrank F V := by
  classical
  have key := sum_repMultiplicity_mul_fixedCodim_le (k := F) ρ
    ((upperUniSp F : Subgroup (antiSp F)) : Set (antiSp F)) (ι := ↥O)
    (fun t => (↥(t : Finset ℕ) → Fin 4) → F) (fun t => matRep (tensorRepS (F := F) F t))
    (fun t t' h => Subtype.ext
      ((tensorRepS_absolutely_irreducible_and_distinct (k := F) hF hf).2 t (hO t t.2) t'
        (hO t' t'.2) h))
  have hc : ∀ t : ↥O, 3 * (t : Finset ℕ).card ≤
      Module.finrank F ((↥(t : Finset ℕ) → Fin 4) → F) -
        Module.finrank F (repFixedSpace (matRep (tensorRepS (F := F) F t))
          ((upperUniSp F : Subgroup (antiSp F)) : Set (antiSp F))) := by
    intro t
    obtain ⟨hdim, -, hfix, -⟩ :=
      squarefree_tensor_fixed_line_and_character (F := F) F hF (hO t t.2)
    have h1 : repFixedSpace (matRep (tensorRepS (F := F) F t))
        ((upperUniSp F : Subgroup (antiSp F)) : Set (antiSp F)) =
        fixedSub (matRep (tensorRepS (F := F) F t)) (upperUniSp F) := rfl
    rw [h1, hfix, finrank_span_singleton (hwS_ne_zero F _), hdim]
    exact three_mul_le_four_pow_sub_one _
  calc ∑ C ∈ O, 3 * C.card * repMultiplicity ρ (matRep (tensorRepS (F := F) F C))
      = ∑ t : ↥O, 3 * (t : Finset ℕ).card *
          repMultiplicity ρ (matRep (tensorRepS (F := F) F t)) :=
        (Finset.sum_coe_sort O (fun C => 3 * C.card *
          repMultiplicity ρ (matRep (tensorRepS (F := F) F C)))).symm
    _ ≤ ∑ t : ↥O, repMultiplicity ρ (matRep (tensorRepS (F := F) F t)) *
          (Module.finrank F ((↥(t : Finset ℕ) → Fin 4) → F) -
            Module.finrank F (repFixedSpace (matRep (tensorRepS (F := F) F t))
              ((upperUniSp F : Subgroup (antiSp F)) : Set (antiSp F)))) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (hc t)
    _ ≤ _ := key
    _ ≤ Module.finrank F V := Nat.sub_le _ _

theorem sum_weight_le_codim_of_gsIrreducible (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {W : Type} [AddCommGroup W] [Module F W] [Module.Finite F W]
    (ρ' : Representation F (antiSp F) W) (s' : W ≃ₗ[F] W) (hss : ∀ w, s' (s' w) = w)
    (hs : ∀ g w, s' (ρ' g w) = ρ' ((minorAut F ^ f) g) (s' w)) (hirr : GSIrreducible ρ' s')
    (O : Finset (Finset ℕ)) (hO : ∀ C ∈ O, C ⊆ Finset.range (2 * f)) :
    ∑ C ∈ O, 3 * C.card * repMultiplicity ρ' (matRep (tensorRepS (F := F) F C)) ≤
      2 * (Module.finrank F W - Module.finrank F (LinearMap.ker (s'.toLinearMap - 1))) := by
  classical
  have hdimsum := sum_weight_le_finrank hF hf ρ' O hO
  have hrn : ∀ D : W →ₗ[F] W, Module.finrank F (LinearMap.range D) +
      Module.finrank F (LinearMap.ker D) = Module.finrank F W :=
    fun D => LinearMap.finrank_range_add_finrank_ker D
  by_cases hW : Nontrivial W
  swap
  · have : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
    have h0 : Module.finrank F W = 0 := Module.finrank_zero_of_subsingleton
    omega
  set τ : MulAut (antiSp F) := minorAut F ^ f with hτdef
  have hττ : ∀ g, τ (τ g) = g := by
    intro g
    have h := minorAut_pow_two_mul hF hf
    show (minorAut F ^ f) ((minorAut F ^ f) g) = g
    rw [← MulAut.mul_apply, ← pow_add, ← two_mul, h]
    rfl
  have hs2 : ∀ g w, ρ' g (s' w) = s' (ρ' (τ g) w) := fun g w => by
    have := hs (τ g) w
    rw [hττ] at this
    exact this.symm
  obtain ⟨Ur, hUr⟩ := exists_isAtom_subrep ρ'
  set U : Submodule F W := Ur.toSubmodule with hUdef
  have hUne : U ≠ ⊥ := fun h => hUr.1 (Subrepresentation.toSubmodule_injective h)
  have hUG : ∀ g, ∀ u ∈ U, ρ' g u ∈ U := fun g u hu => Ur.apply_mem_toSubmodule g hu
  set sU : Submodule F W := U.map s'.toLinearMap with hsUdef
  have hsU : ∀ u ∈ U, s' u ∈ sU := fun u hu => ⟨u, hu, rfl⟩
  have hsUG : ∀ g, ∀ y ∈ sU, ρ' g y ∈ sU := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨ρ' (τ g) u, hUG _ u hu, (hs2 g u).symm⟩
  have hsUs : ∀ y ∈ sU, s' y ∈ U := by
    rintro _ ⟨u, hu, rfl⟩
    show s' (s' u) ∈ U
    rw [hss]
    exact hu
  have hsupG : ∀ g, ∀ w ∈ U ⊔ sU, ρ' g w ∈ U ⊔ sU := by
    intro g w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    exact Submodule.add_mem_sup (hUG g y hy) (hsUG g z hz)
  have hsups : ∀ w ∈ U ⊔ sU, s' w ∈ U ⊔ sU := by
    intro w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, add_comm]
    exact Submodule.add_mem_sup (hsUs z hz) (hsU y hy)
  have htop : U ⊔ sU = ⊤ := by
    rcases hirr (U ⊔ sU) hsupG hsups with h | h
    · exfalso
      apply hUne
      rw [_root_.eq_bot_iff, ← h]
      exact le_sup_left
    · exact h
  by_cases hcase : sU = U
  ·
    have hUtop : U = ⊤ := by rw [← htop, hcase, sup_idem]
    have hUr_top : Ur = ⊤ := Subrepresentation.toSubmodule_injective hUtop
    have hρirr : ρ'.IsIrreducible := by
      have : IsAtom (⊤ : Subrepresentation ρ') := hUr_top ▸ hUr
      exact isSimpleOrder_iff_isAtom_top.mpr this
    obtain ⟨⟨A, ⟨hA, ⟨e⟩⟩, -⟩, -⟩ :=
      split_simple_module_production (F := F) (k := F) hF hf ρ' hρirr
    let eL : ((↥A → Fin 4) → F) ≃ₗ[F] W := e.toLinearEquiv
    have heint : ∀ g v, eL (matRep (tensorRepS (F := F) F A) g v) = ρ' g (eL v) :=
      fun g v => IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
    have heint' : ∀ g w, eL.symm (ρ' g w) = matRep (tensorRepS (F := F) F A) g (eL.symm w) :=
      fun g w => by
        apply eL.injective
        rw [heint, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    let S₀ : ((↥A → Fin 4) → F) →ₗ[F] ((↥A → Fin 4) → F) :=
      eL.symm.toLinearMap ∘ₗ s'.toLinearMap ∘ₗ eL.toLinearMap
    have hS₀apply : ∀ v, S₀ v = eL.symm (s' (eL v)) := fun v => rfl
    have hS₀S₀ : ∀ v, S₀ (S₀ v) = v := fun v => by
      rw [hS₀apply, hS₀apply, LinearEquiv.apply_symm_apply, hss, LinearEquiv.symm_apply_apply]
    have hS₀T : ∀ g v, S₀ (matRep (tensorRepS (F := F) F A) g v) =
        matRep (tensorRepS (F := F) F A) (τ g) (S₀ v) := fun g v => by
      rw [hS₀apply, hS₀apply, heint, hs, heint']
    let S : Matrix (↥A → Fin 4) (↥A → Fin 4) F := LinearMap.toMatrix' S₀
    have hSS : S * S = 1 := by
      rw [← LinearMap.toMatrix'_comp, show S₀ ∘ₗ S₀ = LinearMap.id from LinearMap.ext hS₀S₀,
        LinearMap.toMatrix'_id]
    have hST : ∀ g, S * tensorRepS (F := F) F A g = tensorRepS (F := F) F A (τ g) * S := by
      intro g
      have h1 : S₀ ∘ₗ Matrix.mulVecLin (tensorRepS (F := F) F A g) =
          Matrix.mulVecLin (tensorRepS (F := F) F A (τ g)) ∘ₗ S₀ :=
        LinearMap.ext fun v => hS₀T g v
      have hT : ∀ M : Matrix (↥A → Fin 4) (↥A → Fin 4) F,
          LinearMap.toMatrix' (Matrix.mulVecLin M) = M := fun M => by
        rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      have h2 := congrArg LinearMap.toMatrix' h1
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, hT] at h2
      exact h2
    have h6 := three_mul_card_le_two_mul_rank_of_flip hF hf hA S hSS hST
    have hrank : (S - 1).rank = Module.finrank F (LinearMap.range (s'.toLinearMap - 1)) := by
      have h1 : Matrix.mulVecLin (S - 1) =
          eL.symm.toLinearMap ∘ₗ (s'.toLinearMap - 1) ∘ₗ eL.toLinearMap := by
        have : Matrix.mulVecLin (S - 1) = S₀ - LinearMap.id := by
          rw [← Matrix.toLin'_apply', map_sub, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
        rw [this]
        refine LinearMap.ext fun v => ?_
        simp [hS₀apply]
      unfold Matrix.rank
      rw [h1, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range eL)]
      exact LinearEquiv.finrank_map_eq eL.symm _
    have hmult : ∀ C ∈ O, 3 * C.card * repMultiplicity ρ' (matRep (tensorRepS (F := F) F C)) ≤
        if C = A then 3 * A.card else 0 := by
      intro C hC
      rw [repMultiplicity_of_isIrreducible hρirr]
      by_cases hne : Nonempty (ρ'.Equiv (matRep (tensorRepS (F := F) F C)))
      · obtain ⟨e'⟩ := hne
        have hCA : A = C :=
          (tensorRepS_absolutely_irreducible_and_distinct (k := F) hF hf).2 A hA C (hO C hC)
            ⟨e.trans e'⟩
        subst hCA
        rw [if_pos ⟨e'⟩, if_pos rfl, mul_one]
      · simp [hne]
    have hsum : ∑ C ∈ O, 3 * C.card * repMultiplicity ρ' (matRep (tensorRepS (F := F) F C)) ≤
        3 * A.card := by
      calc _ ≤ ∑ C ∈ O, (if C = A then 3 * A.card else 0) := Finset.sum_le_sum hmult
        _ ≤ 3 * A.card := by
          rw [Finset.sum_ite_eq']
          split_ifs <;> omega
    have := hrn (s'.toLinearMap - 1)
    omega
  ·
    have hinter : U ⊓ sU = ⊥ := by
      let Ui : Subrepresentation ρ' := ⟨U ⊓ sU, fun g v hv => ⟨hUG g v hv.1, hsUG g v hv.2⟩⟩
      have hle : Ui ≤ Ur := fun v hv => hv.1
      rcases hUr.le_iff.mp hle with h | h
      · exact congrArg Subrepresentation.toSubmodule h
      · exfalso
        have h1 : U ≤ sU := fun u hu => by
          have : u ∈ Ui.toSubmodule := by rw [h]; exact hu
          exact this.2
        have hfin : Module.finrank F sU = Module.finrank F U := LinearEquiv.finrank_map_eq s' U
        exact hcase (Submodule.eq_of_le_of_finrank_eq h1 hfin.symm).symm
    set D : W →ₗ[F] W := s'.toLinearMap - 1 with hD
    have hDinj : ∀ u ∈ U, D u = 0 → u = 0 := by
      intro u hu hDu
      have h1 : s' u = u := by
        have : s' u - u = 0 := hDu
        exact sub_eq_zero.mp this
      have hu' : u ∈ sU := ⟨u, hu, h1⟩
      have : u ∈ U ⊓ sU := ⟨hu, hu'⟩
      rw [hinter] at this
      exact (Submodule.mem_bot F).mp this
    have hrank : Module.finrank F U ≤ Module.finrank F (LinearMap.range D) := by
      have hinj : Function.Injective (D.domRestrict U) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro a ha
        have ha' : D a = 0 := ha
        exact Subtype.ext (hDinj a a.2 ha')
      have h1 := LinearMap.finrank_range_of_inj hinj
      have h2 : LinearMap.range (D.domRestrict U) ≤ LinearMap.range D := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      rw [← h1]
      exact Submodule.finrank_mono h2
    have hdimW : Module.finrank F W ≤ 2 * Module.finrank F U := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq U sU
      have hfin : Module.finrank F sU = Module.finrank F U := LinearEquiv.finrank_map_eq s' U
      rw [htop, hinter, finrank_top, finrank_bot] at h1
      omega
    have := hrn D
    omega

theorem sum_weight_le_codim (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F (antiSp F) V) (s : V ≃ₗ[F] V) (hss : ∀ v, s (s v) = v)
    (hs : ∀ g v, s (ρ g v) = ρ ((minorAut F ^ f) g) (s v))
    (O : Finset (Finset ℕ)) (hO : ∀ C ∈ O, C ⊆ Finset.range (2 * f)) :
    ∑ C ∈ O, 3 * C.card * repMultiplicity ρ (matRep (tensorRepS (F := F) F C)) ≤
      2 * (Module.finrank F V - Module.finrank F (LinearMap.ker (s.toLinearMap - 1))) := by
  set τ : antiSp F ≃* antiSp F := minorAut F ^ f with hτ
  have hss' : s * s = 1 := LinearEquiv.ext hss
  have hs' : ∀ g, s * repLinEquiv ρ g = repLinEquiv ρ (τ g) * s := fun g =>
    LinearEquiv.ext fun v => hs g v
  let Γ := gammaGroup ρ s τ hss' hs'
  let ι : antiSp F →* ↥Γ :=
    { toFun := fun g => ⟨repLinEquiv ρ g, g, false, by simp [sPow]⟩
      map_one' := Subtype.ext (repLinEquiv_one ρ)
      map_mul' := fun g h => Subtype.ext (repLinEquiv_mul ρ g h) }
  let t : ↥Γ := ⟨s, 1, true, by simp [sPow, repLinEquiv_one]⟩
  have htt : t * t = 1 := Subtype.ext hss'
  have htι : ∀ g, t * ι g = ι (τ g) * t := fun g => Subtype.ext (hs' g)
  have hdec : ∀ γ : ↥Γ, (∃ g, γ = ι g) ∨ (∃ g, γ = ι g * t) := by
    rintro ⟨γ, g, e, hγ⟩
    cases e
    · left
      refine ⟨g, Subtype.ext ?_⟩
      show γ = repLinEquiv ρ g
      rw [hγ]
      simp [sPow]
    · right
      refine ⟨g, Subtype.ext ?_⟩
      show γ = repLinEquiv ρ g * s
      rw [hγ]
      rfl
  let ρΓ : Representation F ↥Γ V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)).comp Γ.subtype
  have hρΓι : ρΓ.comp ι = ρ := MonoidHom.ext fun g => LinearMap.ext fun v => rfl
  have hfixker : ∀ {W : Type} [AddCommGroup W] [Module F W] (ρ' : Representation F ↥Γ W),
      repFixedSpace ρ' {t} = LinearMap.ker ((repLinEquiv ρ' t).toLinearMap - 1) := by
    intro W _ _ ρ'
    ext v
    simp only [mem_repFixedSpace, Set.mem_singleton_iff, forall_eq, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, repLinEquiv_apply,
      sub_eq_zero]
  have key := rep_induction (k := F) (G := ↥Γ)
    (fun {W} _ _ _ ρ' => ∑ C ∈ O, 3 * C.card *
        repMultiplicity (ρ'.comp ι) (matRep (tensorRepS (F := F) F C)) ≤
      2 * (Module.finrank F W - Module.finrank F (repFixedSpace ρ' {t})))
    (fun {W} _ _ _ ρ' hsub => by
      have h := sum_weight_le_finrank hF hf (ρ'.comp ι) O hO
      have h0 : Module.finrank F W = 0 := Module.finrank_zero_of_subsingleton
      omega)
    (fun {W} _ _ _ ρ' hirrΓ => by
      let s' : W ≃ₗ[F] W := repLinEquiv ρ' t
      have hs's' : ∀ w, s' (s' w) = w := fun w => by
        show ρ' t (ρ' t w) = w
        rw [← Module.End.mul_apply, ← map_mul, htt, map_one]
        rfl
      have hs'G : ∀ g w, s' ((ρ'.comp ι) g w) = (ρ'.comp ι) (τ g) (s' w) := fun g w => by
        show ρ' t (ρ' (ι g) w) = ρ' (ι (τ g)) (ρ' t w)
        rw [← Module.End.mul_apply, ← map_mul, htι, map_mul]
        rfl
      have hGS : GSIrreducible (ρ'.comp ι) s' := by
        intro U hUG hUs
        let Ux : Subrepresentation ρ' := ⟨U, fun γ w hw => by
          rcases hdec γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
          · exact hUG g w hw
          · show ρ' (ι g * t) w ∈ U
            rw [map_mul]
            exact hUG g _ (hUs w hw)⟩
        rcases hirrΓ.eq_bot_or_eq_top Ux with h | h
        · left
          exact congrArg Subrepresentation.toSubmodule h
        · right
          exact congrArg Subrepresentation.toSubmodule h
      have := sum_weight_le_codim_of_gsIrreducible hF hf (ρ'.comp ι) s' hs's' hs'G hGS O hO
      rwa [hfixker ρ'])
    (fun {W} _ _ _ ρ' U hU1 hU2 => by
      let UG : Subrepresentation (ρ'.comp ι) :=
        ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (ι g) hv⟩
      have hm : ∀ C, repMultiplicity (ρ'.comp ι) (matRep (tensorRepS (F := F) F C)) =
          repMultiplicity (U.toRepresentation.comp ι) (matRep (tensorRepS (F := F) F C)) +
            repMultiplicity (U.quotient.comp ι) (matRep (tensorRepS (F := F) F C)) :=
        fun C => repMultiplicity_sub_quot (ρ'.comp ι) UG _
      have hcod := codim_sub_quot ρ' U {t}
      simp only [hm, mul_add, Finset.sum_add_distrib]
      omega)
    (Module.finrank F V) ρΓ rfl
  have hker : repFixedSpace ρΓ {t} = LinearMap.ker (s.toLinearMap - 1) := by
    rw [hfixker]
    rfl
  rw [hρΓι, hker] at key
  exact key

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer
