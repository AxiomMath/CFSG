module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.RankThree.PartOne.KE6.E6LBruhat

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

@[expose] def e6DList : List (List ℤ) :=
  [[0, -1, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 0], [-1, -2, 2, 0, 0, 0], [-2, -3, 2, 0, 0, 0],
   [-2, -3, 1, -1, 0, 0], [-2, -3, 0, -2, -1, 0], [-2, -3, -1, -3, -2, -1], [0, 0, 0, 0, 0, 0]]

@[expose] def e6D (τ : Tag) (i : Fin τ.rank) (k : Fin Tag.E6.rank) : ℤ :=
  (e6DList.getD i []).getD k 0

theorem e6D_spec_E7 : ∀ j k : Fin Tag.E6.rank,
    ∑ i : Fin Tag.E7.rank, Tag.E7.cartan (e6Idx j) i * e6D Tag.E7 i k = if j = k then 1 else 0 := by
  decide +kernel

theorem e6D_spec_E8 : ∀ j k : Fin Tag.E6.rank,
    ∑ i : Fin Tag.E8.rank, Tag.E8.cartan (e6Idx j) i * e6D Tag.E8 i k = if j = k then 1 else 0 := by
  decide +kernel

theorem e6D_spec {τ : Tag} [M27Ok τ] [E6Sub τ] (j k : Fin Tag.E6.rank) :
    ∑ i : Fin τ.rank, τ.cartan (e6Idx j) i * e6D τ i k = if j = k then 1 else 0 := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact e6D_spec_E7 j k
  · exact e6D_spec_E8 j k

theorem prod_zpow_self {G : Type*} [CommGroup G] {ι : Type*} (a : G) (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, a ^ n i = a ^ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

section Torus

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L]

theorem eq_prod_prod_cartan (a : e6Set τ → Lˣ) (k : Fin Tag.E6.rank) :
    a ⟨e6Idx k, e6Idx_mem_e6Set k⟩ =
      ∏ i : Fin τ.rank, (∏ j : e6Set τ, a j ^ τ.cartan j i) ^ e6D τ i k := by
  classical
  have h1 : ∀ i : Fin τ.rank, (∏ j : e6Set τ, a j ^ τ.cartan j i) ^ e6D τ i k =
      ∏ j : e6Set τ, a j ^ (τ.cartan j i * e6D τ i k) := fun i => by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun j _ => by rw [← zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  have h2 : ∀ j : e6Set τ, ∏ i : Fin τ.rank, a j ^ (τ.cartan j i * e6D τ i k) =
      a j ^ (if j = ⟨e6Idx k, e6Idx_mem_e6Set k⟩ then (1 : ℤ) else 0) := fun j => by
    rw [prod_zpow_self]
    congr 1
    obtain ⟨k', hk'⟩ := exists_e6Id_eq j.2
    have e : j = ⟨e6Idx k', e6Idx_mem_e6Set k'⟩ := Subtype.ext hk'.symm
    rw [e]
    have := e6D_spec (τ := τ) k' k
    simp only [Subtype.mk.injEq, e6Idx_injective.eq_iff]
    exact this
  simp only [h2]
  rw [Finset.prod_eq_single ⟨e6Idx k, e6Idx_mem_e6Set k⟩]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eq_one_of_supportedTorusHom_eq_one (a : e6Set τ → Lˣ)
    (h : supportedTorusHom τ L (e6Set τ) a = 1) : a = 1 := by
  rw [supportedTorusHom_eq_one_iff] at h
  funext j
  obtain ⟨k, hk⟩ := exists_e6Id_eq j.2
  have e : j = ⟨e6Idx k, e6Idx_mem_e6Set k⟩ := Subtype.ext hk.symm
  rw [e, eq_prod_prod_cartan a k]
  simp [h]

theorem supportedTorusHom_injective : Function.Injective (supportedTorusHom τ L (e6Set τ)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  exact eq_one_of_supportedTorusHom_eq_one a ha

end Torus

section Descent

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

@[expose] def frobEquiv (L : Type) [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    (m : ℕ) : L ≃+* L :=
  RingEquiv.ofBijective (iterateFrobenius L ℓ m) ⟨(iterateFrobenius L ℓ m).injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y
      (pow_pos (Fact.out : ℓ.Prime).pos m)
    exact ⟨x, by rw [iterateFrobenius_def, hx]⟩⟩

theorem frobEquiv_toRingHom (m : ℕ) : (frobEquiv L ℓ m).toRingHom = iterateFrobenius L ℓ m :=
  RingHom.ext fun _ => rfl

theorem frobEquiv_apply (m : ℕ) (c : L) : frobEquiv L ℓ m c = c ^ ℓ ^ m :=
  iterateFrobenius_def ℓ m c

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem pinnedX_mem_map {m : ℕ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRoots τ (e6Set τ)) (c : frobeniusFixedField L ℓ m) :
    pinnedX τ L α (c : L) ∈ (subsystemGroup τ (frobeniusFixedField L ℓ m) (e6Set τ)).map
      (baseChangeGL (frobeniusFixedField L ℓ m).subtype) :=
  ⟨pinnedX τ (frobeniusFixedField L ℓ m) α c,
    rootSubgroup_le_subsystemGroup hα (Subgroup.subset_closure ⟨c, rfl⟩),
    baseChangeGL_pinnedX _ α c⟩

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem mem_map_of_fixed_rootSpan {m : ℕ} {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    (hSJ : S ⊆ parabolicRoots τ (e6Set τ))
    (hcoll : ∀ {n : ℕ} (α : Fin n → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin n → L => (List.ofFn fun k => pinnedX τ L (α k) (c k)).prod)
        Set.univ (rootSpan τ L S))
    {u : ModGL τ L} (hu : u ∈ rootSpan τ L S)
    (hfix : Units.map (entrywiseHom (iterateFrobenius L ℓ m)) u = u) :
    u ∈ (subsystemGroup τ (frobeniusFixedField L ℓ m) (e6Set τ)).map
      (baseChangeGL (frobeniusFixedField L ℓ m).subtype) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : Units.map (entrywiseHom (iterateFrobenius L ℓ m))
      ((List.ofFn fun k => pinnedX τ L (α k) (c k)).prod) =
        (List.ofFn fun k => pinnedX τ L (α k) (iterateFrobenius L ℓ m (c k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    refine Units.ext ?_
    rw [Function.comp_apply, Units.coe_map]
    exact entrywise_pinnedX (iterateFrobenius L ℓ m) (α k) (c k)
  rw [hmap] at hfix
  have hc : (fun k => iterateFrobenius L ℓ m (c k)) = c :=
    hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfix
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  have hck : c k ∈ frobeniusFixedField L ℓ m := by
    rw [mem_frobeniusFixedField, ← iterateFrobenius_def ℓ m]
    exact congrFun hc k
  exact pinnedX_mem_map (hSJ (by rw [← hrange]; exact ⟨k, rfl⟩)) ⟨c k, hck⟩

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem baseChangeGL_weylElt_one' {K : Type} [Field K] (f : K →+* L) (i : Fin τ.rank) :
    baseChangeGL f (weylElt τ K i 1) = weylElt τ L i 1 := by
  rw [LieType.Chevalley.weylElt_eq_xUnit_mul, LieType.Chevalley.weylElt_eq_xUnit_mul, map_mul,
    map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit]
  simp

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem baseChangeGL_canonicalRep' {K : Type} [Field K] (f : K →+* L) (w : WeylGroup τ) :
    baseChangeGL f (canonicalRep (coxeterSystem τ) K w) = canonicalRep (coxeterSystem τ) L w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_weylElt_one' f i)

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem baseChangeGL_supportedTorusHom {K : Type} [Field K] (f : K →+* L)
    (a : e6Set τ → Kˣ) :
    baseChangeGL f (supportedTorusHom τ K (e6Set τ) a) =
      supportedTorusHom τ L (e6Set τ) (fun j => Units.map f.toMonoidHom (a j)) := by
  classical
  rw [supportedTorusHom_apply, supportedTorusHom_apply]
  refine (Finset.map_noncommProd _ _ _ (baseChangeGL f)).trans ?_
  exact Finset.noncommProd_congr rfl (fun j _ => baseChangeGL_torusElt f j.1 (a j)) _

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem entrywise_supportedTorusHom (σ : L ≃+* L) (a : e6Set τ → Lˣ) :
    Units.map (entrywiseHom σ.toRingHom) (supportedTorusHom τ L (e6Set τ) a) =
      supportedTorusHom τ L (e6Set τ) (fun j => Units.map σ.toRingHom.toMonoidHom (a j)) := by
  classical
  rw [supportedTorusHom_apply, supportedTorusHom_apply]
  refine (Finset.map_noncommProd _ _ _ (Units.map (entrywiseHom σ.toRingHom))).trans ?_
  exact Finset.noncommProd_congr rfl (fun j _ => entrywise_torusElt σ j.1 (a j)) _

theorem supportedTorusHom_mem_map {m : ℕ} {h : ModGL τ L}
    (hh : h ∈ supportedTorus τ L (e6Set τ))
    (hfix : Units.map (entrywiseHom (iterateFrobenius L ℓ m)) h = h) :
    h ∈ (subsystemGroup τ (frobeniusFixedField L ℓ m) (e6Set τ)).map
      (baseChangeGL (frobeniusFixedField L ℓ m).subtype) := by
  obtain ⟨a, rfl⟩ := mem_supportedTorus.1 hh
  rw [← frobEquiv_toRingHom m, entrywise_supportedTorusHom] at hfix
  have ha := supportedTorusHom_injective (τ := τ) (L := L) hfix
  have hmem : ∀ j, (a j : L) ∈ frobeniusFixedField L ℓ m := fun j => by
    have := congrArg (fun u : e6Set τ → Lˣ => ((u j : Lˣ) : L)) ha
    simp only [Units.coe_map] at this
    rw [mem_frobeniusFixedField, ← frobEquiv_apply m]
    exact this
  refine ⟨supportedTorusHom τ (frobeniusFixedField L ℓ m) (e6Set τ)
    (fun j => Units.mk0 ⟨(a j : L), hmem j⟩ (fun h0 => (a j).ne_zero (congrArg Subtype.val h0))),
    supportedTorus_le_subsystemGroup _ (supportedTorusHom_mem _ _), ?_⟩
  rw [baseChangeGL_supportedTorusHom]
  congr 1
  funext j
  exact Units.ext rfl

theorem exists_mem_map_of_frobenius_fixed (m : ℕ) {g : ModGL τ L}
    (hg : g ∈ subsystemGroup τ L (e6Set τ))
    (hfix : Units.map (entrywiseHom (iterateFrobenius L ℓ m)) g = g) :
    g ∈ (subsystemGroup τ (frobeniusFixedField L ℓ m) (e6Set τ)).map
      (baseChangeGL (frobeniusFixedField L ℓ m).subtype) := by
  set σ : L ≃+* L := frobEquiv L ℓ m with hσ
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom (iterateFrobenius L ℓ m)) with hΦ
  set M := (subsystemGroup τ (frobeniusFixedField L ℓ m) (e6Set τ)).map
    (baseChangeGL (frobeniusFixedField L ℓ m).subtype) with hM
  obtain ⟨⟨v, h, u, u'⟩, ⟨hv, hh, hu, hu', hgeq⟩, huniq⟩ := existsUnique_supportedCell_factors hg
  simp only at hv hh hu hu' hgeq
  have hΦh : Φ h ∈ supportedTorus τ L (e6Set τ) := by
    obtain ⟨a, rfl⟩ := mem_supportedTorus.1 hh
    rw [hΦ, ← frobEquiv_toRingHom m, entrywise_supportedTorusHom]
    exact supportedTorusHom_mem _ _
  have hΦu : Φ u ∈ parabolicLeviUnipotent τ L (e6Set τ) := by
    have := entrywise_mem_rootSpan (σ := σ) (S := parabolicPosRoots τ (e6Set τ)) hu
    rwa [frobEquiv_toRingHom] at this
  have hΦu' : Φ u' ∈ rootSpan τ L (parabolicRoots τ (e6Set τ) ∩ inversionSet v) := by
    have := entrywise_mem_rootSpan (σ := σ) (S := parabolicRoots τ (e6Set τ) ∩ inversionSet v) hu'
    rwa [frobEquiv_toRingHom] at this
  have hΦn : Φ (canonicalRep (coxeterSystem τ) L v) = canonicalRep (coxeterSystem τ) L v := by
    have := entrywise_canonicalRep σ v
    rwa [frobEquiv_toRingHom] at this
  have hcand : Φ h * Φ u * canonicalRep (coxeterSystem τ) L v * Φ u' = g := by
    rw [← hΦn, ← map_mul, ← map_mul, ← map_mul, hgeq]
    exact hfix
  have hp := huniq (v, Φ h, Φ u, Φ u') ⟨hv, hΦh, hΦu, hΦu', hcand⟩
  have hp' : (v, Φ h, Φ u, Φ u') = (v, h, u, u') := hp
  have e1 : Φ h = h := (Prod.mk.inj hp').2 |> fun x => (Prod.mk.inj x).1
  have e2 : Φ u = u := ((Prod.mk.inj ((Prod.mk.inj hp').2)).2 |> fun x => (Prod.mk.inj x).1)
  have e3 : Φ u' = u' := ((Prod.mk.inj ((Prod.mk.inj hp').2)).2 |> fun x => (Prod.mk.inj x).2)
  have hfinPos : (parabolicPosRoots τ (e6Set τ)).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.2.1
  have hfinInv : (parabolicRoots τ (e6Set τ) ∩ inversionSet v).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1.1
  have hhM : h ∈ M := supportedTorusHom_mem_map hh e1
  have huM : u ∈ M :=
    mem_map_of_fixed_rootSpan hfinPos Set.inter_subset_left
      (fun α hα hrange => bijOn_prod_pinnedX_parabolicPosRoots α hα hrange) hu e2
  have hu'M : u' ∈ M :=
    mem_map_of_fixed_rootSpan hfinInv Set.inter_subset_left
      (fun α hα hrange => bijOn_prod_pinnedX_parabolicRoots_inter_inversionSet v α hα hrange)
      hu' e3
  have hnM : canonicalRep (coxeterSystem τ) L v ∈ M :=
    ⟨canonicalRep (coxeterSystem τ) (frobeniusFixedField L ℓ m) v,
      canonicalRep_mem_subsystemGroup hv, baseChangeGL_canonicalRep' _ v⟩
  rw [← hgeq]
  exact mul_mem (mul_mem (mul_mem hhM huM) hnM) hu'M

omit [M27Ok τ] [E6Sub τ] [IsAlgClosed L] in
theorem frobenius_fixed_of_mem_map (m : ℕ) {g : ModGL τ L}
    (hg : g ∈ (subsystemGroup τ (frobeniusFixedField L ℓ m) (e6Set τ)).map
      (baseChangeGL (frobeniusFixedField L ℓ m).subtype)) :
    Units.map (entrywiseHom (iterateFrobenius L ℓ m)) g = g := by
  obtain ⟨q, hq, rfl⟩ := hg
  have hfix : ∀ c : frobeniusFixedField L ℓ m,
      iterateFrobenius L ℓ m ((frobeniusFixedField L ℓ m).subtype c) =
        (frobeniusFixedField L ℓ m).subtype c := fun c => by
    change iterateFrobenius L ℓ m (c : L) = (c : L)
    rw [iterateFrobenius_def]
    exact mem_frobeniusFixedField.1 c.2
  rw [SetLike.mem_coe, subsystemGroup] at hq
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit, units_map_entrywiseHom_xUnit, hfix c]
    · rw [baseChangeGL_yUnit, units_map_entrywiseHom_yUnit, hfix c]
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, map_inv, hx]

end Descent


end CFSG.RankThree.PartOne.KE6
