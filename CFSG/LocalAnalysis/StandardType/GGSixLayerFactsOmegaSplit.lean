module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaReduce
public import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

namespace CFSG.StandardType

namespace LayerCores

namespace OrthSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

section Avg

variable (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]

@[expose] noncomputable def avg : V →ₗ[K] V :=
  (Fintype.card A : K)⁻¹ • ∑ a : A, ((a : V ≃ₗ[K] V) : V →ₗ[K] V)

theorem avg_apply (v : V) :
    avg A v = (Fintype.card A : K)⁻¹ • ∑ a : A, (a : V ≃ₗ[K] V) v := by
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, LinearEquiv.coe_coe]

variable {A}

theorem apply_avg {a : V ≃ₗ[K] V} (ha : a ∈ A) (v : V) : a (avg A v) = avg A v := by
  rw [avg_apply, LinearEquiv.map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : A)) _ _ fun b => rfl

theorem avg_apply_apply {a : V ≃ₗ[K] V} (ha : a ∈ A) (v : V) : avg A (a v) = avg A v := by
  rw [avg_apply, avg_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : A)) _ _ fun b => rfl

theorem avg_of_fixed (hA : (Fintype.card A : K) ≠ 0) {v : V} (hv : ∀ a ∈ A, a v = v) :
    avg A v = v := by
  rw [avg_apply, Finset.sum_congr rfl fun (a : A) _ => hv a a.2, Finset.sum_const,
    Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hA, one_smul]

theorem avg_avg (hA : (Fintype.card A : K) ≠ 0) (v : V) : avg A (avg A v) = avg A v :=
  avg_of_fixed hA fun _ ha => apply_avg ha v

theorem isIdempotentElem_avg (hA : (Fintype.card A : K) ≠ 0) : IsIdempotentElem (avg A) :=
  LinearMap.ext fun v => avg_avg hA v

theorem commute_avg {g : V ≃ₗ[K] V} (hg : g ∈ Subgroup.centralizer (A : Set (V ≃ₗ[K] V)))
    (v : V) : g (avg A v) = avg A (g v) := by
  rw [avg_apply, avg_apply, LinearEquiv.map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := Subgroup.mem_centralizer_iff.mp hg a a.2
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, h]

variable {Q : QuadraticForm K V}

theorem polar_avg (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (v w : V) :
    polar Q (avg A v) w = polar Q v (avg A w) := by
  have h1 : ∀ x y : V, polar Q x y = polarBilin Q x y := fun _ _ => rfl
  rw [h1, h1, avg_apply, avg_apply, map_smul, LinearMap.smul_apply, map_smul, map_sum, map_sum,
    LinearMap.sum_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv A) _ _ fun a => ?_
  rw [← h1, ← h1]
  have ha := hAO a.2
  calc polar Q ((a : V ≃ₗ[K] V) v) w
      = polar Q ((a : V ≃ₗ[K] V) v) ((a : V ≃ₗ[K] V) (((a⁻¹ : A) : V ≃ₗ[K] V) w)) := by
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
        rfl
    _ = polar Q v (((Equiv.inv A a : A) : V ≃ₗ[K] V) w) := polar_map_of_mem ha _ _

end Avg

section Spaces

variable (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]

noncomputable abbrev fixSp : Submodule K V := LinearMap.range (avg A)

noncomputable abbrev freeSp : Submodule K V := LinearMap.ker (avg A)

variable {A}

theorem avg_mem_fixSp (v : V) : avg A v ∈ fixSp A := LinearMap.mem_range_self _ v

theorem mem_fixSp_iff (hA : (Fintype.card A : K) ≠ 0) {v : V} :
    v ∈ fixSp A ↔ ∀ a ∈ A, a v = v := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_avg hA)]
  constructor
  · intro h a ha
    rw [← h, apply_avg ha]
  · exact avg_of_fixed hA

theorem sub_avg_mem_freeSp (hA : (Fintype.card A : K) ≠ 0) (v : V) : v - avg A v ∈ freeSp A := by
  rw [LinearMap.mem_ker, map_sub, avg_avg hA, sub_self]

theorem isCompl_fixSp_freeSp (hA : (Fintype.card A : K) ≠ 0) : IsCompl (fixSp A) (freeSp A) :=
  LinearMap.IsIdempotentElem.isCompl (isIdempotentElem_avg hA)

variable {Q : QuadraticForm K V}

theorem polar_fixSp_freeSp (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {v w : V}
    (hv : v ∈ fixSp A) (hw : w ∈ freeSp A) : polar Q v w = 0 := by
  obtain ⟨u, rfl⟩ := hv
  rw [polar_avg hAO, LinearMap.mem_ker.mp hw, polar_zero_right]

theorem polar_eq_add_of_avg (x v : V) :
    polar Q x v = polar Q x (avg A v) + polar Q x (v - avg A v) := by
  rw [← polar_add_right, add_sub_cancel]

theorem polarNondegOn_fixSp (hQ : (polarBilin Q).Nondegenerate) (hA : (Fintype.card A : K) ≠ 0)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) : PolarNondegOn Q (fixSp A) := by
  intro x hx hxW
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  rw [polar_eq_add_of_avg (A := A), hxW _ (avg_mem_fixSp v),
    polar_fixSp_freeSp hAO hx (sub_avg_mem_freeSp hA v), add_zero]

theorem polarNondegOn_freeSp (hQ : (polarBilin Q).Nondegenerate) (hA : (Fintype.card A : K) ≠ 0)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) : PolarNondegOn Q (freeSp A) := by
  intro x hx hxW
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  rw [polar_eq_add_of_avg (A := A), polar_comm, polar_fixSp_freeSp hAO (avg_mem_fixSp v) hx,
    hxW _ (sub_avg_mem_freeSp hA v), add_zero]

end Spaces

section Restrict

variable (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]

@[expose] def stab : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v, avg A (g v) = g (avg A v)}
  one_mem' _ := rfl
  mul_mem' {g h} hg hh v := by
    simp only [Set.mem_ofPred_eq, LinearEquiv.mul_apply] at hg hh ⊢
    rw [hg, hh]
  inv_mem' {g} hg v := by
    simp only [Set.mem_ofPred_eq, LinearEquiv.coe_inv] at hg ⊢
    apply g.injective
    rw [← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

variable {A}

theorem mem_stab {g : V ≃ₗ[K] V} : g ∈ stab A ↔ ∀ v, avg A (g v) = g (avg A v) := Iff.rfl

theorem le_stab : A ≤ stab A := fun a ha v => by rw [avg_apply_apply ha, apply_avg ha]

theorem centralizer_le_stab : Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ≤ stab A :=
  fun _ hg v => (commute_avg hg v).symm

theorem map_fixSp_eq {g : V ≃ₗ[K] V} (hg : g ∈ stab A) :
    (fixSp A).map (g : V →ₗ[K] V) = fixSp A := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨g u, hg u⟩
  · obtain ⟨u, rfl⟩ := hw
    refine ⟨avg A (g⁻¹ u), avg_mem_fixSp _, ?_⟩
    show g (avg A (g⁻¹ u)) = avg A u
    rw [← hg, ← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq]

theorem map_freeSp_eq {g : V ≃ₗ[K] V} (hg : g ∈ stab A) :
    (freeSp A).map (g : V →ₗ[K] V) = freeSp A := by
  have hmem : ∀ {h : V ≃ₗ[K] V}, h ∈ stab A → ∀ w ∈ freeSp A, h w ∈ freeSp A :=
    fun {h} hh w hw => by rw [LinearMap.mem_ker, hh, LinearMap.mem_ker.mp hw, map_zero]
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hmem hg w hw
  · refine ⟨g⁻¹ w, hmem ((stab A).inv_mem hg) w hw, ?_⟩
    show g (g⁻¹ w) = w
    rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq]

variable (A)

@[expose] noncomputable def restrFix : stab A →* (fixSp A ≃ₗ[K] fixSp A) where
  toFun g := (g : V ≃ₗ[K] V).ofSubmodules _ _ (map_fixSp_eq g.2)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[expose] noncomputable def restrFree : stab A →* (freeSp A ≃ₗ[K] freeSp A) where
  toFun g := (g : V ≃ₗ[K] V).ofSubmodules _ _ (map_freeSp_eq g.2)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

variable {A}

theorem coe_restrFix_apply (g : stab A) (x : fixSp A) :
    (restrFix A g x : V) = (g : V ≃ₗ[K] V) x := rfl

theorem coe_restrFree_apply (g : stab A) (x : freeSp A) :
    (restrFree A g x : V) = (g : V ≃ₗ[K] V) x := rfl

variable (A)

@[expose] noncomputable def freeGroup : Subgroup (freeSp A ≃ₗ[K] freeSp A) :=
  (A.subgroupOf (stab A)).map (restrFree A)

end Restrict

section Split

variable {A : Subgroup (V ≃ₗ[K] V)} [Fintype A] (hA : (Fintype.card A : K) ≠ 0)

@[expose] noncomputable def split :
    (fixSp A ≃ₗ[K] fixSp A) × (freeSp A ≃ₗ[K] freeSp A) →* (V ≃ₗ[K] V) where
  toFun g := (Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)).symm.trans
    ((g.1.prodCongr g.2).trans (Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)))
  map_one' := by
    ext v
    show (Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA))
      (((1 : fixSp A ≃ₗ[K] fixSp A).prodCongr (1 : freeSp A ≃ₗ[K] freeSp A))
        ((Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)).symm v)) = v
    rw [LinearEquiv.prodCongr_apply]
    exact (Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)).apply_symm_apply v
  map_mul' g h := by
    ext v
    simp

theorem split_apply_fix (g : (fixSp A ≃ₗ[K] fixSp A) × (freeSp A ≃ₗ[K] freeSp A))
    (x : fixSp A) : split hA g x = g.1 x := by
  show (Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)) ((g.1.prodCongr g.2)
    ((Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)).symm x)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, add_zero]

theorem split_apply_free (g : (fixSp A ≃ₗ[K] fixSp A) × (freeSp A ≃ₗ[K] freeSp A))
    (y : freeSp A) : split hA g y = g.2 y := by
  show (Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)) ((g.1.prodCongr g.2)
    ((Submodule.prodEquivOfIsCompl _ _ (isCompl_fixSp_freeSp hA)).symm y)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, zero_add]

theorem split_apply (g : (fixSp A ≃ₗ[K] fixSp A) × (freeSp A ≃ₗ[K] freeSp A)) (v : V) :
    split hA g v = (g.1 ⟨avg A v, avg_mem_fixSp v⟩ : V) +
      (g.2 ⟨v - avg A v, sub_avg_mem_freeSp hA v⟩ : V) := by
  have h := congrArg (split hA g) (add_sub_cancel (avg A v) v)
  rw [← h, map_add]
  exact congrArg₂ (· + ·) (split_apply_fix hA g ⟨avg A v, avg_mem_fixSp v⟩)
    (split_apply_free hA g ⟨v - avg A v, sub_avg_mem_freeSp hA v⟩)

theorem split_injective : Function.Injective (split hA) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Prod.ext (LinearEquiv.ext fun x => Subtype.ext ?_)
    (LinearEquiv.ext fun y => Subtype.ext ?_)
  · rw [← split_apply_fix hA g x, hg]
    rfl
  · rw [← split_apply_free hA g y, hg]
    rfl

variable {Q : QuadraticForm K V}

noncomputable abbrev freeCent (A : Subgroup (V ≃ₗ[K] V)) [Fintype A] (Q : QuadraticForm K V) :
    Subgroup (freeSp A ≃ₗ[K] freeSp A) :=
  Subgroup.centralizer (freeGroup A : Set (freeSp A ≃ₗ[K] freeSp A)) ⊓
    TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A))

theorem centralizer_eq_map_split (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q =
      ((TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp A))).prod
        (freeCent A Q)).map (split hA) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgc, hgO⟩ := Subgroup.mem_inf.mp hg
    have hgs := centralizer_le_stab hgc
    refine ⟨(restrFix A ⟨g, hgs⟩, restrFree A ⟨g, hgs⟩), Subgroup.mem_prod.mpr ⟨?_, ?_⟩, ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => map_of_mem hgO (x : V)
    · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_,
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => map_of_mem hgO (x : V)⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc _ (Subgroup.mem_subgroupOf.mp ha))
    · refine LinearEquiv.ext fun v => ?_
      rw [split_apply]
      show g (avg A v) + g (v - avg A v) = g v
      rw [← map_add, add_sub_cancel]
  · rintro _ ⟨⟨g₀, g₁⟩, hg, rfl⟩
    obtain ⟨hg₀, hg₁⟩ := Subgroup.mem_prod.mp hg
    obtain ⟨hg₁c, hg₁O⟩ := Subgroup.mem_inf.mp hg₁
    have hQ0 : ∀ x : fixSp A, Q (g₀ x) = Q x := fun x =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg₀ x
    have hQ1 : ∀ y : freeSp A, Q (g₁ y) = Q y := fun y =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg₁O y
    have key : ∀ (x : fixSp A) (y : freeSp A), Q ((x : V) + y) = Q x + Q y := fun x y => by
      rw [QuadraticMap.map_add Q, polar_fixSp_freeSp hAO x.2 y.2, add_zero]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun a ha => ?_,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_⟩
    · refine LinearEquiv.ext fun v => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, split_apply, split_apply, map_add]
      have e0 : (⟨avg A (a v), avg_mem_fixSp (a v)⟩ : fixSp A) = ⟨avg A v, avg_mem_fixSp v⟩ :=
        Subtype.ext (avg_apply_apply ha v)
      have e1 : (⟨a v - avg A (a v), sub_avg_mem_freeSp hA (a v)⟩ : freeSp A) =
          restrFree A ⟨a, le_stab ha⟩ ⟨v - avg A v, sub_avg_mem_freeSp hA v⟩ := by
        refine Subtype.ext ?_
        rw [coe_restrFree_apply]
        show a v - avg A (a v) = a (v - avg A v)
        rw [map_sub, avg_apply_apply ha, apply_avg ha]
      have hc := Subgroup.mem_centralizer_iff.mp hg₁c (restrFree A ⟨a, le_stab ha⟩)
        ⟨⟨a, le_stab ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [e0, e1, ← LinearEquiv.mul_apply g₁, ← hc, LinearEquiv.mul_apply,
        coe_restrFree_apply, (mem_fixSp_iff hA).mp (g₀ _).2 a ha]
    · rw [split_apply, key, hQ0, hQ1, ← key]
      congr 1
      exact add_sub_cancel (avg A v) v

end Split

end OrthSplit

end LayerCores

open QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores LayerCores.OrthSplit

@[expose] def GGOrthRegularCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (W : Type) [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (Q : QuadraticForm K W), (polarBilin Q).Nondegenerate →
      ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
        IsSubCoreFamily (TauCeti.QuadraticMap.orthogonalGroup Q) S

@[expose] def GGOrthFreeCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (W : Type) [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (Q : QuadraticForm K W), (polarBilin Q).Nondegenerate →
    ∀ A : Subgroup (W ≃ₗ[K] W), A ≤ TauCeti.QuadraticMap.orthogonalGroup Q → Odd (Nat.card A) →
      (∀ w : W, (∀ a ∈ A, a w = w) → w = 0) →
      ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
        IsCoreFamily (Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓
          TauCeti.QuadraticMap.orthogonalGroup Q) S

theorem natCast_card_ne_zero_of_odd {K : Type} [Field K] [CharP K 2] {m : ℕ} (hm : Odd m) :
    (m : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K 2]
  exact fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)

theorem ggOrthCentralizerCoreInput_of (hreg : GGOrthRegularCoreInput)
    (hfree : GGOrthFreeCoreInput) : GGOrthCentralizerCoreInput := by
  intro K _ _ _ V _ _ _ Q hQ A hAO hodd
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨β₀, S₀, hS₀⟩ := hreg K (fixSp A) (Q.restrict (fixSp A))
    (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO))
  have hA₁O : freeGroup A ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y =>
      map_of_mem (hAO (Subgroup.mem_subgroupOf.mp ha)) (y : V)
  have hA₁odd : Odd (Nat.card (freeGroup A)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_stab).toEquiv]
    exact hodd
  have hA₁free : ∀ w : freeSp A, (∀ a ∈ freeGroup A, a w = w) → w = 0 := by
    intro w hw
    have h1 : (w : V) ∈ fixSp A := (mem_fixSp_iff hA).mpr fun a ha =>
      congrArg Subtype.val (hw (restrFree A ⟨a, le_stab ha⟩)
        ⟨⟨a, le_stab ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
    exact Subtype.ext ((Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA).disjoint) _ h1 w.2)
  obtain ⟨β₁, S₁, hS₁⟩ := hfree K (freeSp A) (Q.restrict (freeSp A))
    (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) (freeGroup A) hA₁O
    hA₁odd hA₁free
  refine ⟨β₀ ⊕ β₁, fun c => (prodFamily S₀ S₁ c).map (split hA), ?_⟩
  rw [centralizer_eq_map_split hA hAO]
  exact (hS₀.prod hS₁.toSub).map _ (split_injective hA)

end CFSG.StandardType
