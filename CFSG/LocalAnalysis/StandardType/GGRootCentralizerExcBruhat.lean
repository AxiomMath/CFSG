module

public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.OppositeBorel
public import CFSG.LieType.Chevalley.LongestElement
public import CFSG.LieType.Chevalley.PositiveRootCollection
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.SimpleWeylComplement
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.HeightSeries

public section

namespace CFSG.StandardType

namespace RootCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise


variable {τ : Tag} {K : Type} [Field K] {θ : Fin τ.rank → ℤ}

@[expose] def IsMaxHeight (τ : Tag) (θ : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ θ ∧ ∀ α, IsRoot τ α → height α ≤ height θ

theorem IsMaxHeight.height_pos (hθ : IsMaxHeight τ θ) : 0 < height θ := by
  have h := hθ.2 _ (isRoot_single τ ⟨0, by cases τ <;> decide⟩)
  rw [height_single] at h
  omega

theorem commute_pinnedX_of_isMaxHeight (hθ : IsMaxHeight τ θ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβp : 0 < height β) (a b : K) :
    Commute (pinnedX τ K β a) (pinnedX τ K θ b) := by
  by_cases hβθ : β = θ
  · subst hβθ
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hc := commutator_rootSubgroup_le K hβ hθ.1 hβp hθ.height_pos hβθ
    have hbot : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • β + b • θ), rootSubgroup τ K γ) = ⊥ := by
      refine iSup₂_eq_bot.2 ?_
      rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
      have h1 := hθ.2 _ hγ
      rw [height_nsmul_add_nsmul] at h1
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      have hθp := hθ.height_pos
      exfalso
      nlinarith
    rw [hbot] at hc
    have hmem := hc (Subgroup.commutator_mem_commutator (mem_rootSubgroup.2 ⟨a, rfl⟩)
      (mem_rootSubgroup.2 ⟨b, rfl⟩))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem commute_of_mem_posUnipotent (hθ : IsMaxHeight τ θ) {g : ModGL τ K}
    (hg : g ∈ posUnipotent τ K) (b : K) : Commute g (pinnedX τ K θ b) := by
  have hle : posUnipotent τ K ≤ Subgroup.centralizer {pinnedX τ K θ b} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_pinnedX_of_isMaxHeight hθ hβ.1 hβ.2 a b).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem torusGroup_le_normalizer_rootSubgroup {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusGroup τ K ≤ Subgroup.normalizer (rootSubgroup τ K α : Set (ModGL τ K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro g
  have h := map_conj_torusElt_rootSubgroup i s hα (R := K)
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', he⟩ := hg
    have : g' = g := by
      simpa [MulAut.conj_apply] using he
    rwa [← this]

theorem borelGroup_le_normalizer_rootSubgroup (hθ : IsMaxHeight τ θ) :
    borelGroup τ K ≤ Subgroup.normalizer (rootSubgroup τ K θ : Set (ModGL τ K)) := by
  refine sup_le (torusGroup_le_normalizer_rootSubgroup hθ.1) fun u hu => ?_
  have hc : ∀ g ∈ rootSubgroup τ K θ, u * g * u⁻¹ = g := by
    intro g hg
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rw [(commute_of_mem_posUnipotent hθ hu c).eq, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [hc g hg]
    exact hg
  · intro hg
    have e := hc _ hg
    have : g = u * g * u⁻¹ := by
      calc g = u⁻¹ * (u * (u * g * u⁻¹) * u⁻¹) * u := by rw [e]; group
        _ = u * g * u⁻¹ := by group
    rw [this]
    exact hg

theorem pinnedX_mem_posUnipotent {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβp : 0 < height β)
    (c : K) : pinnedX τ K β c ∈ posUnipotent τ K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) ⟨hβ, hβp⟩ c

theorem eq_of_pinnedX_eq (hθ : IsRoot τ θ) (hθp : 0 < height θ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) {d e : K} (hd : d ≠ 0)
    (h : pinnedX τ K β d = pinnedX τ K θ e) : β = θ := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hβ with hpos | hneg
  · have hinj : Function.Injective ![β, θ] := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
    have hposα : ∀ i, IsRoot τ (![β, θ] i) ∧ 0 < height (![β, θ] i) := by
      intro i
      fin_cases i
      · exact ⟨hβ, hpos⟩
      · exact ⟨hθ, hθp⟩
    have hprod := (positive_root_product_injectivity τ K _ hinj hposα).2
      (a₁ := ![d, 0]) (a₂ := ![0, e]) (by simp [List.ofFn_succ, pinnedX_zero, h])
    have := congrFun hprod 0
    exact hd (by simpa using this)
  · obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
    have hbot := (opposite_Borel_intersection τ K w₀ hw₀).2.2.2
    have hmem : pinnedX τ K β d ∈ borelGroup τ K ⊓ negUnipotent τ K := by
      refine Subgroup.mem_inf.2 ⟨?_, pinnedX_mem_rootSpan
        (S := {α | IsRoot τ α ∧ height α < 0}) ⟨hβ, hneg⟩ d⟩
      rw [h]
      exact Subgroup.mem_sup_right (pinnedX_mem_posUnipotent hθ hθp e)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd (pinnedX_injective τ K β (hmem.trans (pinnedX_zero _ _ _).symm))

theorem canonicalRep_mul_pinnedX_mul_inv_of_two (h2 : (2 : K) = 0) (w : WeylGroup τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K α c *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ = pinnedX τ K (w • α) c := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hα
  have hε1 : ε = 1 := by
    have h' : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
  rw [h, hε1, one_mul]

theorem mem_parabolicWeylGroup_of_smul_eq {i₀ : Fin τ.rank} {c : ℤ} (hc : c ≠ 0)
    (hform : ∀ v, CFSG.LieType.Steinberg.Adjoint.iform θ v = c * v i₀) {w : WeylGroup τ}
    (hw : w • θ = θ) : w ∈ parabolicWeylGroup τ {i | i ≠ i₀} := by
  have hset := (parabolic_Weyl_coordinate_stabilizer τ {i | i ≠ i₀}).1
  have hmem : w ∈ (parabolicWeylGroup τ {i | i ≠ i₀} : Set (WeylGroup τ)) := by
    rw [hset]
    intro v i hi
    have hi' : i = i₀ := by
      by_contra h'
      exact hi h'
    subst hi'
    have h1 := iform_smul w θ v
    rw [hw, hform, hform] at h1
    exact mul_left_cancel₀ hc h1
  exact hmem

theorem mem_parabolicSubgroup_of_conj (h2 : (2 : K) = 0) (hθ : IsMaxHeight τ θ)
    {A : Set (Fin τ.rank)} (hW : ∀ w : WeylGroup τ, w • θ = θ → w ∈ parabolicWeylGroup τ A)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) {c : K}
    (hc : g * pinnedX τ K θ 1 * g⁻¹ = pinnedX τ K θ c) :
    g ∈ parabolicSubgroup τ K A := by
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  have hB := borelGroup_le_normalizer_rootSubgroup (K := K) hθ
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB hb') _).1
    (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have h1 : pinnedX τ K θ (1 : K) = 1 := by
      calc pinnedX τ K θ (1 : K) = b'⁻¹ * (b' * pinnedX τ K θ 1 * b'⁻¹) * b' := by group
        _ = 1 := by rw [← hd]; group
    exact one_ne_zero (pinnedX_injective τ K θ (h1.trans (pinnedX_zero _ _ _).symm))
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB (inv_mem hb)) _).1
    (mem_rootSubgroup.2 ⟨c, rfl⟩))
  have hn := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hθ.1 d
  have hkey : pinnedX τ K (w • θ) d = pinnedX τ K θ e := by
    rw [← hn, he, hd, ← hc]
    group
  have hwθ := eq_of_pinnedX_eq hθ.1 hθ.height_pos (IsRoot.smul hθ.1 w) hd0 hkey
  have hP := (standard_parabolic_cells τ K).1 A
  have hmem : b * canonicalRep (coxeterSystem τ) K w * b' ∈
      (parabolicSubgroup τ K A : Set (ModGL τ K)) := by
    rw [hP]
    exact Set.mem_biUnion (hW w hwθ) hw
  exact hmem

@[expose] def leviGens (τ : Tag) (K : Type) [Field K] (A : Set (Fin τ.rank)) : Set (ModGL τ K) :=
  {g | ∃ j ∈ A, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}

theorem mem_normalizer_closure_of {G : Type*} [Group G] {X : Set G} {t : G}
    (h1 : ∀ x ∈ X, t * x * t⁻¹ ∈ Subgroup.closure X)
    (h2 : ∀ x ∈ X, t⁻¹ * x * t ∈ Subgroup.closure X) :
    t ∈ Subgroup.normalizer (Subgroup.closure X : Set G) := by
  have key : ∀ s : G, (∀ x ∈ X, s * x * s⁻¹ ∈ Subgroup.closure X) →
      ∀ g ∈ Subgroup.closure X, s * g * s⁻¹ ∈ Subgroup.closure X := by
    intro s hs g hg
    have hle : (Subgroup.closure X).map (MulAut.conj s).toMonoidHom ≤ Subgroup.closure X := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact hs x hx
    exact hle ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key t h1 g, fun hg => ?_⟩
  have h := key t⁻¹ (by simpa using h2) _ hg
  rwa [show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at h

theorem torusElt_conj_xUnit (i j : Fin τ.rank) (s : Kˣ) (c : K) :
    torusElt τ K i s * xUnit τ K j c * (torusElt τ K i s)⁻¹ =
      xUnit τ K j (((s ^ τ.cartan i j : Kˣ) : K) * c) := by
  rw [← pinnedX_single, root_torus_conjugation i (isRoot_single τ j) s c, pinnedX_single]
  congr 4
  rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]

theorem torusElt_conj_yUnit (i j : Fin τ.rank) (s : Kˣ) (c : K) :
    torusElt τ K i s * yUnit τ K j c * (torusElt τ K i s)⁻¹ =
      yUnit τ K j (((s ^ (-τ.cartan i j) : Kˣ) : K) * c) := by
  rw [← pinnedX_neg_single, root_torus_conjugation i (isRoot_neg_single τ j) s c,
    pinnedX_neg_single]
  congr 4
  rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [Pi.neg_apply, Pi.single_eq_of_ne hk, neg_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.neg_apply, Pi.single_eq_same, mul_neg, mul_one]

theorem torusGroup_le_normalizer_leviGens (A : Set (Fin τ.rank)) :
    torusGroup τ K ≤
      Subgroup.normalizer (Subgroup.closure (leviGens τ K A) : Set (ModGL τ K)) := by
  have hgen : ∀ (i : Fin τ.rank) (s : Kˣ), ∀ x ∈ leviGens τ K A,
      torusElt τ K i s * x * (torusElt τ K i s)⁻¹ ∈ Subgroup.closure (leviGens τ K A) := by
    rintro i s _ ⟨j, hj, c, rfl | rfl⟩
    · rw [torusElt_conj_xUnit]
      exact Subgroup.subset_closure ⟨j, hj, _, Or.inl rfl⟩
    · rw [torusElt_conj_yUnit]
      exact Subgroup.subset_closure ⟨j, hj, _, Or.inr rfl⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  refine mem_normalizer_closure_of (hgen i s) fun x hx => ?_
  have h := hgen i s⁻¹ x hx
  have e : (torusElt τ K i s⁻¹)⁻¹ = torusElt τ K i s := by
    rw [inv_eq_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
  have e' : torusElt τ K i s⁻¹ = (torusElt τ K i s)⁻¹ := by rw [← e, inv_inv]
  rw [e] at h
  rw [e'] at h
  exact h

theorem torusElt_mem_closure_leviGens {A : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ A)
    (s : Kˣ) : torusElt τ K i s ∈ Subgroup.closure (leviGens τ K A) := by
  have hx : ∀ c : K, xUnit τ K i c ∈ Subgroup.closure (leviGens τ K A) := fun c =>
    Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩
  have hy : ∀ c : K, yUnit τ K i c ∈ Subgroup.closure (leviGens τ K A) := fun c =>
    Subgroup.subset_closure ⟨i, hi, c, Or.inr rfl⟩
  have hw : ∀ t : Kˣ, weylElt τ K i t ∈ Subgroup.closure (leviGens τ K A) := fun t => by
    rw [weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  exact mul_mem (hw s) (hw (-1))

theorem prod_zpow_eq_zpow_finsetSum {M : Type*} [CommGroup M] {ι : Type*} (s : Finset ι) (a : M)
    (f : ι → ℤ) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

variable (τ K) in
@[expose] noncomputable def cartanCharHom : (Fin τ.rank → Kˣ) →* (Fin τ.rank → Kˣ) where
  toFun := cartanChar
  map_one' := by
    funext l
    simp [cartanChar]
  map_mul' u v := by
    funext l
    simp [cartanChar, mul_zpow, Finset.prod_mul_distrib]

variable (τ K) in
@[expose] noncomputable def torusHom : (Fin τ.rank → Kˣ) →* ModGL τ K :=
  (rootDiagUnitHom τ K).comp (cartanCharHom τ K)

theorem torusHom_mulSingle (i : Fin τ.rank) (s : Kˣ) :
    torusHom τ K (Pi.mulSingle i s) = torusElt τ K i s := by
  rw [torusElt_eq_rootDiagUnit]
  change rootDiagUnit τ (cartanChar (Pi.mulSingle i s)) = _
  congr 1
  funext l
  rw [cartanChar, Finset.prod_eq_single i
    (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
    (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]

theorem torusGroup_le_range_torusHom : torusGroup τ K ≤ (torusHom τ K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  exact ⟨Pi.mulSingle i s, torusHom_mulSingle i s⟩

theorem torusHom_conj_pinnedX (hθ : IsRoot τ θ) (u : Fin τ.rank → Kˣ) (c : K) :
    torusHom τ K u * pinnedX τ K θ c * (torusHom τ K u)⁻¹ =
      pinnedX τ K θ (((∏ i, u i ^ (∑ j, τ.cartan i j * θ j) : Kˣ) : K) * c) := by
  change rootDiagUnit τ (cartanChar u) * _ * (rootDiagUnit τ (cartanChar u))⁻¹ = _
  rw [rootDiagUnit_conj_pinnedX _ hθ]
  congr 3
  simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, cartanChar]
  calc ∏ l, (∏ j, u j ^ τ.cartan j l) ^ θ l = ∏ l, ∏ j, u j ^ (τ.cartan j l * θ l) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ l, u j ^ (τ.cartan j l * θ l) := Finset.prod_comm
    _ = ∏ i, u i ^ (∑ j, τ.cartan i j * θ j) :=
        Finset.prod_congr rfl fun i _ => prod_zpow_eq_zpow_finsetSum _ _ _

theorem mem_closure_leviGens_of_mem_torusGroup {i₀ : Fin τ.rank} (hθ : IsRoot τ θ)
    (hco : ∀ i, ∑ j, τ.cartan i j * θ j = if i = i₀ then 1 else 0) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) (hc : h * pinnedX τ K θ 1 = pinnedX τ K θ 1 * h) :
    h ∈ Subgroup.closure (leviGens τ K {i | i ≠ i₀}) := by
  obtain ⟨u, rfl⟩ := torusGroup_le_range_torusHom hh
  have hconj := torusHom_conj_pinnedX (K := K) hθ u 1
  rw [hc, mul_inv_cancel_right] at hconj
  have hprod : ∏ i, u i ^ (∑ j, τ.cartan i j * θ j) = u i₀ := by
    simp only [hco]
    rw [Finset.prod_eq_single i₀ (fun j _ hj => by rw [ite_eq_right_iff.2 (fun h => absurd h hj), zpow_zero])
      (fun h => absurd (Finset.mem_univ i₀) h), ite_eq_left_iff.2 (fun h => absurd rfl h), zpow_one]
  rw [hprod, mul_one] at hconj
  have hu : u i₀ = 1 := Units.ext (pinnedX_injective τ K θ hconj).symm
  have hmem : u ∈ (Subgroup.closure (leviGens τ K {i | i ≠ i₀})).comap (torusHom τ K) := by
    rw [← Finset.univ_prod_mulSingle u]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_comap, torusHom_mulSingle]
    by_cases hi : i = i₀
    · subst hi
      rw [hu, torusElt_one]
      exact one_mem _
    · exact torusElt_mem_closure_leviGens hi _
  exact hmem

@[expose] def radLeviGens (τ : Tag) (K : Type) [Field K] (A : Set (Fin τ.rank)) :
    Set (ModGL τ K) :=
  {x | ∃ γ ∈ parabolicRadicalRoots τ A, ∃ c : K, pinnedX τ K γ c = x} ∪ leviGens τ K A

theorem mem_closure_radLeviGens {i₀ : Fin τ.rank} (hθ : IsMaxHeight τ θ)
    (hco : ∀ i, ∑ j, τ.cartan i j * θ j = if i = i₀ then 1 else 0)
    (hL : ∀ x ∈ leviGens τ K {i | i ≠ i₀}, x * pinnedX τ K θ 1 = pinnedX τ K θ 1 * x)
    {g : ModGL τ K} (hg : g ∈ parabolicSubgroup τ K {i | i ≠ i₀})
    (hgc : g * pinnedX τ K θ 1 = pinnedX τ K θ 1 * g) :
    g ∈ Subgroup.closure (radLeviGens τ K {i | i ≠ i₀}) := by
  set A : Set (Fin τ.rank) := {i | i ≠ i₀} with hA
  set X := pinnedX τ K θ 1 with hX
  obtain ⟨⟨q, m⟩, ⟨hq, hm, hgqm⟩, -⟩ :=
    (parabolic_root_radical_Levi_factors τ K A).2.2.2.2.2.2.1 g hg
  dsimp only at hq hm hgqm
  subst hgqm
  have hqc : q * X = X * q :=
    (commute_of_mem_posUnipotent hθ (parabolicRadical_le_posUnipotent A hq) 1).eq
  have hmc : m * X = X * m := by
    have h1 : q * (m * X) = q * (X * m) := by
      rw [← mul_assoc, hgc, ← mul_assoc, ← hqc, mul_assoc]
    exact mul_left_cancel h1
  have hm' : m ∈ (torusGroup τ K : Set (ModGL τ K)) *
      (Subgroup.closure (leviGens τ K A) : Set (ModGL τ K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_leviGens A)]
    exact hm
  obtain ⟨h, hh, l, hl, rfl⟩ := hm'
  have hlC : Subgroup.closure (leviGens τ K A) ≤ Subgroup.centralizer {X} := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hL x hx
  have hlc : l * X = X * l := Subgroup.mem_centralizer_singleton_iff.1 (hlC hl)
  have hhc : h * X = X * h := by
    have h1 : h * X * l = X * h * l := by
      rw [mul_assoc, ← hlc, ← mul_assoc, hmc, ← mul_assoc]
    exact mul_right_cancel h1
  have hhL := mem_closure_leviGens_of_mem_torusGroup hθ.1 hco hh hhc
  have hQ : q ∈ Subgroup.closure (radLeviGens τ K A) := by
    have hq' : q ∈ Subgroup.closure
        {g | ∃ α ∈ parabolicRadicalRoots τ A, ∃ c : K, pinnedX τ K α c = g} := by
      rw [← rootSpan_eq_closure]
      exact hq
    exact Subgroup.closure_mono Set.subset_union_left hq'
  exact mul_mem hQ (mul_mem (Subgroup.closure_mono Set.subset_union_right hhL)
    (Subgroup.closure_mono Set.subset_union_right hl))

theorem pinnedX_mul_self (h2 : (2 : K) = 0) (γ : Fin τ.rank → ℤ) (c : K) :
    pinnedX τ K γ c * pinnedX τ K γ c = 1 := by
  rw [← pinnedX_add, ← two_mul, h2, zero_mul, pinnedX_zero]

theorem centralizer_le_closure_involutions (h2 : (2 : K) = 0) {i₀ : Fin τ.rank}
    (hθ : IsMaxHeight τ θ) (hco : ∀ i, ∑ j, τ.cartan i j * θ j = if i = i₀ then 1 else 0)
    {c : ℤ} (hc : c ≠ 0) (hform : ∀ v, CFSG.LieType.Steinberg.Adjoint.iform θ v = c * v i₀)
    (hL : ∀ x ∈ leviGens τ K {i | i ≠ i₀}, x * pinnedX τ K θ 1 = pinnedX τ K θ 1 * x) :
    Subgroup.centralizer
        {(⟨pinnedX τ K θ 1, pinnedX_mem_adjointGroup θ 1⟩ : adjointGroup τ K)} ≤
      Subgroup.closure {y | y ∈ Subgroup.centralizer
        {(⟨pinnedX τ K θ 1, pinnedX_mem_adjointGroup θ 1⟩ : adjointGroup τ K)} ∧ y * y = 1} := by
  set x : adjointGroup τ K := ⟨pinnedX τ K θ 1, pinnedX_mem_adjointGroup θ 1⟩ with hx
  set S := {y | y ∈ Subgroup.centralizer {x} ∧ y * y = 1} with hS
  have hgen : ∀ z ∈ radLeviGens τ K {i | i ≠ i₀}, z ∈ (Subgroup.closure S).map
      (adjointGroup τ K).subtype := by
    intro z hz
    have hzA : z ∈ adjointGroup τ K := by
      rcases hz with ⟨γ, -, d, rfl⟩ | ⟨j, -, d, rfl | rfl⟩
      · exact pinnedX_mem_adjointGroup γ d
      · exact xUnit_mem_adjointGroup j d
      · exact yUnit_mem_adjointGroup j d
    have hzc : z * pinnedX τ K θ 1 = pinnedX τ K θ 1 * z := by
      rcases hz with ⟨γ, hγ, d, rfl⟩ | hz
      · exact (commute_pinnedX_of_isMaxHeight hθ hγ.1.1 hγ.1.2 d 1).eq
      · exact hL z hz
    have hz2 : z * z = 1 := by
      rcases hz with ⟨γ, -, d, rfl⟩ | ⟨j, -, d, rfl | rfl⟩
      · exact pinnedX_mul_self h2 γ d
      · rw [← pinnedX_single]
        exact pinnedX_mul_self h2 _ d
      · rw [← pinnedX_neg_single]
        exact pinnedX_mul_self h2 _ d
    refine ⟨⟨z, hzA⟩, Subgroup.subset_closure ⟨?_, Subtype.ext hz2⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hzc
  intro g hg
  have hgc : (g : ModGL τ K) * pinnedX τ K θ 1 = pinnedX τ K θ 1 * g :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hgP : (g : ModGL τ K) ∈ parabolicSubgroup τ K {i | i ≠ i₀} :=
    mem_parabolicSubgroup_of_conj h2 hθ (fun w hw => mem_parabolicWeylGroup_of_smul_eq hc hform hw)
      g.2 (c := 1) (by rw [hgc, mul_inv_cancel_right])
  have hmem := mem_closure_radLeviGens hθ hco hL hgP hgc
  have hle : Subgroup.closure (radLeviGens τ K {i | i ≠ i₀}) ≤
      (Subgroup.closure S).map (adjointGroup τ K).subtype :=
    (Subgroup.closure_le _).2 hgen
  obtain ⟨y, hy, hyg⟩ := hle hmem
  rwa [show y = g from Subtype.ext hyg] at hy

theorem yUnit_mul_pinnedX_comm (h2 : (2 : K) = 0) (hθ : IsMaxHeight τ θ) {j : Fin τ.rank}
    (hj : ∑ k, τ.cartan j k * θ k = 0) (c d : K) :
    yUnit τ K j c * pinnedX τ K θ d = pinnedX τ K θ d * yUnit τ K j c := by
  set n := canonicalRep (coxeterSystem τ) K (simple τ j) with hn
  have e1 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 (simple τ j) (isRoot_neg_single τ j) c
  have e2 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 (simple τ j) hθ.1 d
  rw [simple_smul] at e1 e2
  have r1 : reflect τ j (-Pi.single j 1) = Pi.single j 1 := by
    have hs : ∑ k, τ.cartan j k * (-Pi.single j 1 : Fin τ.rank → ℤ) k = -2 := by
      rw [Finset.sum_eq_single j (fun k _ hk => by
          rw [Pi.neg_apply, Pi.single_eq_of_ne hk, neg_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ j) h), Pi.neg_apply, Pi.single_eq_same, mul_neg,
        mul_one, Tag.cartan_self]
    rw [reflect, hs]
    ext k
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  have r2 : reflect τ j θ = θ := by
    rw [reflect, hj, zero_smul, sub_zero]
  rw [r1] at e1
  rw [r2] at e2
  have hcomm := (commute_pinnedX_of_isMaxHeight hθ (isRoot_single τ j)
    (by rw [height_single]; exact one_pos) c d).eq
  rw [← pinnedX_neg_single]
  apply (MulAut.conj n).injective
  simp only [map_mul, MulAut.conj_apply]
  rw [e1, e2, hcomm]

structure HighRootData (τ : Tag) (θ : Fin τ.rank → ℤ) (i₀ : Fin τ.rank) : Prop where
  maxHeight : IsMaxHeight τ θ
  coPair : ∀ i, ∑ j, τ.cartan i j * θ j = if i = i₀ then 1 else 0
  form : ∃ c : ℤ, c ≠ 0 ∧ ∀ v, CFSG.LieType.Steinberg.Adjoint.iform θ v = c * v i₀

theorem HighRootData.centralizer_le_closure (h2 : (2 : K) = 0) {i₀ : Fin τ.rank}
    (hd : HighRootData τ θ i₀) :
    Subgroup.centralizer
        {(⟨pinnedX τ K θ 1, pinnedX_mem_adjointGroup θ 1⟩ : adjointGroup τ K)} ≤
      Subgroup.closure {y | y ∈ Subgroup.centralizer
        {(⟨pinnedX τ K θ 1, pinnedX_mem_adjointGroup θ 1⟩ : adjointGroup τ K)} ∧ y * y = 1} := by
  obtain ⟨c, hc, hform⟩ := hd.form
  refine centralizer_le_closure_involutions h2 hd.maxHeight hd.coPair hc hform ?_
  rintro _ ⟨j, hj, d, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact (commute_pinnedX_of_isMaxHeight hd.maxHeight (isRoot_single τ j)
      (by rw [height_single]; exact one_pos) d 1).eq
  · have hj0 : ∑ k, τ.cartan j k * θ k = 0 := by
      rw [hd.coPair j, ite_eq_right_iff.2 fun h => absurd h hj]
    exact yUnit_mul_pinnedX_comm h2 hd.maxHeight hj0 d 1

end RootCentExc

end CFSG.StandardType
