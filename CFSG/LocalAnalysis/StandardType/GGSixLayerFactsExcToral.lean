module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcComp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaDefs
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

namespace LayerExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

variable {τ : Tag} {K : Type} [Field K]

@[expose] def famChar (F : Set (Fin τ.rank → Kˣ)) :
    Multiplicative (Fin τ.rank → ℤ) →* (F → Kˣ) where
  toFun v := fun a => rootChar a.1 (Multiplicative.toAdd v)
  map_one' := funext fun a => rootChar_zero a.1
  map_mul' _ _ := funext fun a => rootChar_add a.1 _ _

theorem kernelRoots_famChar (F : Set (Fin τ.rank → Kˣ)) :
    kernelRoots (famChar F) = famKernel F := by
  ext α
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha => congrFun h2 ⟨a, ha⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun a => h2 a.1 a.2⟩

theorem neg_mem_famKernel {F : Set (Fin τ.rank → Kˣ)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ famKernel F) : -α ∈ famKernel F := by
  refine ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, fun a ha => ?_⟩
  have h := rootChar_add a α (-α)
  rw [add_neg_cancel, rootChar_zero, hα.2 a ha, one_mul] at h
  exact h.symm

theorem commute_of_mem_torusGroup
    {x y : ModGL τ K} (hx : x ∈ torusGroup τ K) (hy : y ∈ torusGroup τ K) : x * y = y * x := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l hy

theorem commutator_torus_sup_rootSpan_le
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    ⁅torusGroup τ K ⊔ rootSpan τ K S, torusGroup τ K ⊔ rootSpan τ K S⁆ ≤ rootSpan τ K S := by
  have hN := torusGroup_le_normalizer_rootSpan (K := K) hS
  have hconj : ∀ t ∈ torusGroup τ K, ∀ q ∈ rootSpan τ K S, t * q * t⁻¹ ∈ rootSpan τ K S :=
    fun t ht q hq => (Subgroup.mem_normalizer_iff.1 (hN ht) q).1 hq
  have hdec : ∀ x ∈ torusGroup τ K ⊔ rootSpan τ K S,
      ∃ a ∈ rootSpan τ K S, ∃ t ∈ torusGroup τ K, x = a * t := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx
    obtain ⟨t, ht, q, hq, rfl⟩ := hx
    exact ⟨t * q * t⁻¹, hconj t ht q hq, t, ht, by group⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, t, ht, rfl⟩ := hdec x hx
  obtain ⟨b, hb, t', ht', rfl⟩ := hdec y hy
  have htt : t' * t⁻¹ = t⁻¹ * t' := by
    have h := commute_of_mem_torusGroup ht' (inv_mem ht)
    exact h
  have e : a * t * (b * t') * (a * t)⁻¹ * (b * t')⁻¹ =
      a * (t * b * t⁻¹) * (t' * a⁻¹ * t'⁻¹) * b⁻¹ := by
    calc a * t * (b * t') * (a * t)⁻¹ * (b * t')⁻¹ =
          a * t * b * (t' * t⁻¹) * a⁻¹ * t'⁻¹ * b⁻¹ := by group
      _ = a * (t * b * t⁻¹) * (t' * a⁻¹ * t'⁻¹) * b⁻¹ := by rw [htt]; group
  rw [commutatorElement_def, e]
  exact mul_mem (mul_mem (mul_mem ha (hconj t ht b hb)) (hconj t' ht' _ (inv_mem ha)))
    (inv_mem hb)

theorem odd_card_units [Finite K] [CharP K 2] : Odd (Nat.card Kˣ) := by
  refine LayerFacts.odd_card_of_forall_sq_eq_one fun x hx => ?_
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hx' : ((x : K)) ^ 2 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hx
    simpa using this
  have h : ((x : K) - 1) ^ 2 = 0 := by linear_combination hx' + (1 - (x : K)) * h2
  exact Units.ext (by simpa [sub_eq_zero] using h)

section Family


theorem isSubCoreFamily_torus_sup_rootSpan [Finite K] [CharP K 2] (F : Set (Fin τ.rank → Kˣ))
    {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) :
    LayerCores.IsSubCoreFamily (torusGroup τ K ⊔ rootSpan τ K (famKernel F))
      (componentRootSpan K (famChar F)) := by
  have hker := kernelRoots_famChar F
  have hsup : ⨆ i, componentRootSpan K (famChar F) i = rootSpan τ K (famKernel F) := by
    rw [iSup_componentRootSpan, hker]
  have hleQ : ∀ i, componentRootSpan K (famChar F) i ≤ rootSpan τ K (famKernel F) := fun i =>
    hsup ▸ le_iSup (componentRootSpan K (famChar F)) i
  refine ⟨fun i => (hleQ i).trans le_sup_right, fun i => ?_,
    fun i => isQuasisimple_componentRootSpan_of_sq_ne_one ht, ⟨1, ?_⟩, ?_⟩
  · have hN : torusGroup τ K ⊔ rootSpan τ K (famKernel F) ≤
        Subgroup.normalizer (componentRootSpan K (famChar F) i : Set (ModGL τ K)) := by
      refine sup_le (torusGroup_le_normalizer_rootSpan (S := componentRoots (famChar F) i)
        fun α hα => isRoot_of_mem_componentRoots hα) ?_
      rw [← hker]
      exact rootSpan_le_normalizer K i
    exact LayerCores.ggSubnormal_of_normal ((hleQ i).trans le_sup_right) fun u hu s hs =>
      (Subgroup.mem_normalizer_iff.1 (hN hu) s).1 hs
  · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, hsup]
    exact commutator_torus_sup_rootSpan_le fun α hα => hα.1
  · intro z hz hzc hz2
    rw [hsup] at hz hzc
    exact eq_one_of_commute_componentRootSpan (χ := famChar F) odd_card_units
      (fun x hx => pow_eq_one_of_mem_torusGroup hx) (by rw [hker]; exact hz)
      (fun i s hs => hzc s (hleQ i hs)) hz2

theorem centralizer_map_subtype_eq (F : Set (Fin τ.rank → Kˣ))
    (hstab : famStabilizer F ⊆ (Subgroup.closure
      {s | ∃ α ∈ famKernel F, s = rootReflection α} : Set (WeylGroup τ)))
    (A : Subgroup ↥(adjointGroup τ K)) (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K)
    (hF : ∀ a, a ∈ F ↔ ∃ x ∈ A, (x : ModGL τ K) = rootDiagUnit τ a) :
    (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))).map (adjointGroup τ K).subtype =
      torusGroup τ K ⊔ rootSpan τ K (famKernel F) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have hcomm : ∀ a ∈ F, (g : ModGL τ K) * rootDiagUnit τ a = rootDiagUnit τ a * g := by
      intro a ha
      obtain ⟨x, hx, hxa⟩ := (hF a).1 ha
      rw [← hxa]
      exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg x hx)).symm
    obtain ⟨t, ht, q, hq, htq⟩ := mem_torus_mul_rootSpan_of_commute_fam F hstab
      (S := famKernel F) (fun α hα => hα.1) (fun α hα => neg_mem_famKernel hα) subset_rfl g.2
      hcomm
    change (g : ModGL τ K) ∈ _
    rw [← htq]
    exact Subgroup.mul_mem_sup ht hq
  · intro x hx
    have hxL : x ∈ adjointGroup τ K :=
      (sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
        (rootSpan_le_adjointGroup K _)) hx
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA y hy)
    have hlF : l ∈ F := (hF l).2 ⟨y, hy, hl⟩
    have hle : torusGroup τ K ⊔ rootSpan τ K (famKernel F) ≤
        Subgroup.centralizer ({rootDiagUnit τ l} : Set (ModGL τ K)) := by
      refine sup_le (fun h hh => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (rootDiagUnit_mul_comm_of_mem_torusGroup l hh).symm
      · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
        rintro _ ⟨c, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have h1 := rootDiagUnit_conj_pinnedX l hα.1 c
        rw [hα.2 l hlF, Units.val_one, one_mul] at h1
        calc pinnedX τ K α c * rootDiagUnit τ l =
              rootDiagUnit τ l * pinnedX τ K α c * (rootDiagUnit τ l)⁻¹ * rootDiagUnit τ l := by
              rw [h1]
          _ = rootDiagUnit τ l * pinnedX τ K α c := by group
    have hc := hle hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hl]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm

theorem exists_subCoreFamily_centralizer_toral [Finite K] [CharP K 2]
    (F : Set (Fin τ.rank → Kˣ))
    (hstab : famStabilizer F ⊆ (Subgroup.closure
      {s | ∃ α ∈ famKernel F, s = rootReflection α} : Set (WeylGroup τ)))
    {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) (A : Subgroup ↥(adjointGroup τ K))
    (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K)
    (hF : ∀ a, a ∈ F ↔ ∃ x ∈ A, (x : ModGL τ K) = rootDiagUnit τ a) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S := by
  have h := (isSubCoreFamily_torus_sup_rootSpan F ht).comap (adjointGroup τ K).subtype
    (adjointGroup τ K).subtype_injective (by
      rw [Subgroup.range_subtype]
      exact sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
        (rootSpan_le_adjointGroup K _))
  rw [← centralizer_map_subtype_eq F hstab A hA hF,
    Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective] at h
  exact ⟨_, _, h⟩

theorem exists_subCoreFamily_centralizer_of_le_torusGroup [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hord : ¬ p ∣ Nat.card (WeylGroup τ)) (A : Subgroup ↥(adjointGroup τ K))
    (hA : ∀ x ∈ A, (x : ModGL τ K) ∈ torusGroup τ K) (hexp : ∀ x ∈ A, x ^ p = 1)
    (hA1 : A ≠ ⊥) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set F : Set (Fin τ.rank → Kˣ) := {a | ∃ x ∈ A, (x : ModGL τ K) = rootDiagUnit τ a} with hFdef
  have hFp : ∀ a ∈ F, ∀ i, a i ^ p = 1 := by
    rintro a ⟨y, hy, hya⟩ i
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_one]
      change rootDiagUnitHom τ K (a ^ p) = 1
      rw [map_pow]
      change rootDiagUnit τ a ^ p = 1
      rw [← hya]
      have h2 := congrArg (fun z : ↥(adjointGroup τ K) => (z : ModGL τ K)) (hexp y hy)
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
    exact congrFun (rootDiagUnit_injective h1) i
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA _ x.2)
  have hlF : l ∈ F := ⟨x, x.2, hl⟩
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 1 := by
    by_contra h
    push Not at h
    apply hx1
    have hl1 : l = 1 := funext h
    rw [hl1, rootDiagUnit_one] at hl
    exact Subtype.ext (Subtype.ext hl)
  have hζ : orderOf (l j) = p := orderOf_eq_prime (hFp l hlF j) hj
  have ht : ((l j : Kˣ) : K) ^ 2 ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h3 : ((l j : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (l j : K)) * h2
    exact hj (Units.ext (by simpa [sub_eq_zero] using h3))
  exact exists_subCoreFamily_centralizer_toral F
    (famStabilizer_subset_closure hp hord hζ F hFp) ht A hA fun a => Iff.rfl

end Family

end LayerExc

end CFSG.StandardType
