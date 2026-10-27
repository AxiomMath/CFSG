module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem eq_one_of_mul_self_eq_one_of_charTwo [CharP K 2] {ε : K} (h : ε * ε = 1) : ε = 1 :=
  CharTwo.sq_injective (show ε ^ 2 = 1 ^ 2 by rw [one_pow, sq, h])

theorem simpleRootSL2_injective_of_charTwo [CharP K 2] (i : Fin τ.rank) :
    Function.Injective (simpleRootSL2 τ K i) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  obtain ⟨l, hl, hBl⟩ :=
    (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.2.2.1 B
      (MonoidHom.mem_ker.2 hB)
  have hl1 : (l : K) = 1 :=
    CharTwo.sq_injective (show (l : K) ^ 2 = 1 ^ 2 by rw [hl, one_pow])
  refine Subtype.ext ?_
  rw [hBl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem list_prod_weylElt_conj_pinnedX_of_charTwo [CharP K 2] (ω : List (Fin τ.rank))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : K) :
    (ω.map fun i => weylElt τ K i 1).prod * pinnedX τ K β c *
        ((ω.map fun i => weylElt τ K i 1).prod)⁻¹ =
      pinnedX τ K ((coxeterSystem τ).wordProd ω • β) c := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ :=
      weylElt_mul_pinnedX_mul_inv K i (IsRoot.smul hβ ((coxeterSystem τ).wordProd ω))
    rw [List.map_cons, List.prod_cons, mul_inv_rev, (coxeterSystem τ).wordProd_cons, mul_smul,
      simple_smul]
    calc weylElt τ K i 1 * (ω.map fun i => weylElt τ K i 1).prod * pinnedX τ K β c *
          (((ω.map fun i => weylElt τ K i 1).prod)⁻¹ * (weylElt τ K i 1)⁻¹)
        = weylElt τ K i 1 * ((ω.map fun i => weylElt τ K i 1).prod * pinnedX τ K β c *
          ((ω.map fun i => weylElt τ K i 1).prod)⁻¹) * (weylElt τ K i 1)⁻¹ := by
          simp only [mul_assoc]
      _ = _ := by rw [ih, h, eq_one_of_mul_self_eq_one_of_charTwo hε, one_mul]

theorem rootSL2_uSL_of_charTwo [CharP K 2] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    rootSL2 τ K α (uSL c) = pinnedX τ K α c := by
  rw [rootSL2_apply, simpleRootSL2_uSL, ← pinnedX_single, pinnedWeyl_eq_list_prod,
    list_prod_weylElt_conj_pinnedX_of_charTwo _ (isRoot_single τ _), wordProd_pinnedWord_smul hα]

theorem rootSL2_vSL_of_charTwo [CharP K 2] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    rootSL2 τ K α (vSL c) = pinnedX τ K (-α) c := by
  rw [rootSL2_apply, simpleRootSL2_vSL, ← pinnedX_neg_single, pinnedWeyl_eq_list_prod,
    list_prod_weylElt_conj_pinnedX_of_charTwo _ (isRoot_neg_single τ _), smul_neg,
    wordProd_pinnedWord_smul hα]

theorem baseChangeGL_rootSL2_of_charTwo [CharP K 2] {L : Type} [Field L] (f : K →+* L)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (A : SL2 K) :
    baseChangeGL f (rootSL2 τ K α A) = rootSL2 τ L α (Matrix.SpecialLinearGroup.map f A) := by
  have : CharP L 2 := charP_of_injective_ringHom f.injective 2
  have h : (baseChangeGL f).comp (rootSL2 τ K α) =
      (rootSL2 τ L α).comp (Matrix.SpecialLinearGroup.map f) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change baseChangeGL f (rootSL2 τ K α (uSL c)) =
          rootSL2 τ L α (Matrix.SpecialLinearGroup.map f (uSL c))
        rw [rootSL2_uSL_of_charTwo hα, baseChangeGL_pinnedX, map_uSL, rootSL2_uSL_of_charTwo hα]
      · change baseChangeGL f (rootSL2 τ K α (vSL c)) =
          rootSL2 τ L α (Matrix.SpecialLinearGroup.map f (vSL c))
        rw [rootSL2_vSL_of_charTwo hα, baseChangeGL_pinnedX, map_vSL, rootSL2_vSL_of_charTwo hα]
  exact DFunLike.congr_fun h A

theorem units_map_entrywiseHom_eq_baseChangeGL_self (σ : K →+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ) g = baseChangeGL σ g :=
  Units.ext rfl

theorem uSL_mul_vSL_ne : (uSL 1 : SL2 K) * vSL 1 ≠ vSL 1 * uSL 1 := by
  intro h
  have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change ((uSL 1 : SL2 K) * (vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
    ((vSL 1 : SL2 K) * (uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 at h00
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem exists_finset_card_four {F : Type*} [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have := Fintype.ofFinite F
  have hle : 4 ≤ (Finset.univ : Finset F).card := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  exact ⟨s, hs⟩

theorem even_Chevalley_pinned_root_SL2_maps (τ : Tag) (K : Type) [Field K] [CharP K 2]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    Function.Injective (rootSL2 τ K α) ∧
    (rootSL2 τ K α).range = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ∧
    (∃ e : SL2 K ≃* (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)),
      ∀ A, (e A : ModGL τ K) = rootSL2 τ K α A) ∧
    (∀ c : K, rootSL2 τ K α (uSL c) = pinnedX τ K α c ∧
      rootSL2 τ K α (vSL c) = pinnedX τ K (-α) c) ∧
    (∀ c : Kˣ, ((nSL c : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
        !![0, (c : K); ((c⁻¹ : Kˣ) : K), 0] ∧
      rootTorusSL2 τ K α c ∈ torusGroup τ K ∧
      ∃ h : rootWeylSL2 τ K α c ∈ monomialSubgroup τ K,
        weylQuotientHom τ K ⟨_, h⟩ = rootReflection α) ∧
    (∀ v : Fin τ.rank → ℤ, rootReflection α • v = v - (2 * iform α v / iform α α) • α ∧
      2 * iform α v / iform α α * iform α α = 2 * iform α v) ∧
    (∀ c : Kˣ, (∀ i, (rootTorusSL2 τ K α c : Module.End K (RootModule τ K)) (hVec τ K i) =
        hVec τ K i) ∧
      ∀ β, IsRoot τ β → (rootTorusSL2 τ K α c : Module.End K (RootModule τ K)) (rootVec τ K β) =
        ((c ^ (2 * iform α β / iform α α) : Kˣ) : K) • rootVec τ K β) ∧
    (∀ (L : Type) [Field L] (f : K →+* L) (A : SL2 K),
      baseChangeGL f (rootSL2 τ K α A) = rootSL2 τ L α (Matrix.SpecialLinearGroup.map f A)) ∧
    (∀ (σ : K →+* K) (A : SL2 K), Units.map (entrywiseHom σ) (rootSL2 τ K α A) =
      rootSL2 τ K α (Matrix.SpecialLinearGroup.map σ A)) ∧
    (∀ t ∈ torusGroup τ K, ∃! a : Fin τ.rank → Kˣ, t = rootDiagUnit τ a) ∧
    (∀ (a : Fin τ.rank → Kˣ) (c : K),
      rootDiagUnit τ a * pinnedX τ K α c * (rootDiagUnit τ a)⁻¹ =
          pinnedX τ K α ((rootChar a α : K) * c) ∧
      rootDiagUnit τ a * pinnedX τ K (-α) c * (rootDiagUnit τ a)⁻¹ =
          pinnedX τ K (-α) (((rootChar a α)⁻¹ : Kˣ) * c)) ∧
    (Finite K → 4 ≤ Nat.card K →
      IsSimpleGroup (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) ∧
      Group.IsPerfect (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) ∧
      ∃ x y : (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)),
        x * y ≠ y * x) := by
  obtain ⟨hL, hdH, hnN, hrefl, hv, hH, hconj, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport τ K hα
  have hinj : Function.Injective (rootSL2 τ K α) := fun A B h => by
    rw [rootSL2_apply, rootSL2_apply] at h
    exact simpleRootSL2_injective_of_charTwo _ (by simpa using h)
  have hrange : (rootSL2 τ K α).range = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := hL
  let e : SL2 K ≃* (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ A, (e A : ModGL τ K) = rootSL2 τ K α A := fun A => rfl
  refine ⟨hinj, hrange, ⟨e, he⟩, fun c => ⟨rootSL2_uSL_of_charTwo hα c,
    rootSL2_vSL_of_charTwo hα c⟩, fun c => ⟨?_, hdH c, hnN c⟩, hrefl, hv,
    fun L _ f A => baseChangeGL_rootSL2_of_charTwo f hα A, fun σ A => ?_, hH,
    fun a c => ⟨hconj a α hα c, ?_⟩, fun _ hK => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [nSL, CharTwo.neg_eq]
  · rw [units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_rootSL2_of_charTwo σ hα]
  · rw [hconj a (-α) (IsRoot.neg hα) c]
    congr 2
    simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  · have h4 := exists_finset_card_four hK
    obtain ⟨-, hsimple, -⟩ :=
      CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr h4)
    have : IsSimpleGroup (SL2 K) :=
      (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup
    have : Group.IsPerfect (SL2 K) := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    refine ⟨e.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective,
      e (uSL 1), e (vSL 1), fun h => uSL_mul_vSL_ne (K := K) ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact e.injective h

end CFSG.RankThree.Chevalley
