module

public import CFSG.Timmesfeld.RankTwo.LeviRootSystem
public import CFSG.LieType.Steinberg.Bridge
public import CFSG.LieType.Steinberg.Core

public section

namespace CFSG.Timmesfeld.Levi

open CFSG.LieType CFSG.LieType.Steinberg

section Lists

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Finset ι} {K : Type*} [Group K]

omit [Fintype ι] [DecidableEq ι] in
theorem prod_map_filter {α : Type*} (L : List α) (p : α → Bool) (F : α → K)
    (h : ∀ a ∈ L, p a = false → F a = 1) : (L.map F).prod = ((L.filter p).map F).prod := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    by_cases ha : p a = true
    · simp [ha, ih']
    · simp [ha, ih', h a List.mem_cons_self (by simpa using ha)]

theorem exists_list_sub {X : (ι → ℤ) → Subgroup K} {P : (ι → ℤ) → Prop}
    {R : (ι → ℤ) → (ι → ℤ) → Prop} {L : List (ι → ℤ)} (hnd : L.Nodup)
    (hmem : ∀ γ, γ ∈ L ↔ P γ) (hR : L.Pairwise R) (hinj : ProdInjectiveFor X L) :
    ∃ L' : List (J → ℤ), L'.Nodup ∧ (∀ γ, γ ∈ L' ↔ P (incl J γ)) ∧
      L'.Pairwise (fun γ δ => R (incl J γ) (incl J δ)) ∧
      ProdInjectiveFor (fun γ => X (incl J γ)) L' := by
  set p : (ι → ℤ) → Bool := fun γ => decide (incl J (proj J γ) = γ) with hp
  have hpe : ∀ γ ∈ L.filter p, incl J (proj J γ) = γ := fun γ hγ => by
    simpa [hp] using (List.mem_filter.mp hγ).2
  refine ⟨(L.filter p).map (proj J), ?_, fun γ => ?_, ?_, ?_⟩
  · refine (hnd.filter p).map_on fun x hx y hy hxy => ?_
    rw [← hpe x hx, ← hpe y hy, hxy]
  · simp only [List.mem_map]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      rw [hpe δ hδ]
      exact (hmem δ).mp (List.mem_filter.mp hδ).1
    · intro h
      exact ⟨incl J γ, List.mem_filter.mpr ⟨(hmem _).mpr h, by simp [hp]⟩, proj_incl γ⟩
  · rw [List.pairwise_map]
    refine (hR.filter p).imp_of_mem fun {x y} hx hy h => ?_
    rwa [hpe x hx, hpe y hy]
  · intro f g hf hg hfg γ hγ
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
    have hmemF : ∀ γ ∈ L, ∀ (f : (J → ℤ) → K),
        (∀ γ ∈ (L.filter p).map (proj J), f γ ∈ X (incl J γ)) →
        (if p γ then f (proj J γ) else 1) ∈ X γ := fun γ hγ f hf => by
      by_cases hpγ : p γ = true
      · simp only [hpγ, ↓reduceIte]
        have hγ' : γ ∈ L.filter p := List.mem_filter.mpr ⟨hγ, hpγ⟩
        have := hf _ (List.mem_map_of_mem hγ')
        rwa [hpe γ hγ'] at this
      · simp only [hpγ, Bool.false_eq_true, ↓reduceIte]
        exact one_mem _
    have hprod : ∀ f : (J → ℤ) → K, (L.map fun γ => if p γ then f (proj J γ) else 1).prod =
        (((L.filter p).map (proj J)).map f).prod := fun f => by
      rw [prod_map_filter L p _ fun a _ ha => by simp [ha], List.map_map]
      congr 1
      exact List.map_congr_left fun a ha => by simp [(List.mem_filter.mp ha).2]
    have key := hinj _ _ (fun γ hγ => hmemF γ hγ f hf) (fun γ hγ => hmemF γ hγ g hg)
      (by rw [hprod f, hprod g, hfg]) δ (List.mem_filter.mp hδ).1
    have hpδ : p δ = true := (List.mem_filter.mp hδ).2
    simpa [hpδ] using key

end Lists

section Data

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Steinberg.RootSystem ι} {J : Finset ι}
  (hJ : HasParabolicWords Φ J) {K : Type*} [Group K]

@[expose] def subData (D : RootGroupData Φ K) : RootGroupData (subsystem hJ) K :=
  ⟨fun γ => D.X (incl J γ), fun j => D.n j⟩

variable (D : RootGroupData Φ K)

@[simp] theorem subData_X (γ : J → ℤ) : (subData hJ D).X γ = D.X (incl J γ) := rfl

@[simp] theorem subData_n (j : J) : (subData hJ D).n j = D.n j := rfl

theorem subData_X_single (j : J) :
    (subData hJ D).X (Pi.single j 1) = D.X (Pi.single (j : ι) 1) := by
  rw [subData_X, incl_single]

theorem subData_X_neg_single (j : J) :
    (subData hJ D).X (-Pi.single j 1) = D.X (-Pi.single (j : ι) 1) := by
  rw [subData_X, map_neg, incl_single]

theorem subData_rankOne (j : J) : (subData hJ D).rankOne j = D.rankOne j := by
  rw [RootGroupData.rankOne, RootGroupData.rankOne, subData_X_single, subData_X_neg_single]

theorem subData_torus (j : J) : (subData hJ D).torus j = D.torus j := by
  rw [RootGroupData.torus, RootGroupData.torus, subData_rankOne, subData_X_single,
    subData_X_neg_single]

theorem subData_posPart_le : (subData hJ D).posPart ≤ D.posPart :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le (f := fun γ (_ : γ ∈ Φ.pos) => D.X γ) (incl J γ)
    ((mem_subsystem_pos hJ).mp hγ) le_rfl

theorem subData_negPart_le : (subData hJ D).negPart ≤ D.negPart :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le (f := fun γ (_ : γ ∈ Φ.neg) => D.X γ) (incl J γ)
    ((mem_subsystem_neg hJ).mp hγ) le_rfl

theorem subData_torusPart_le : (subData hJ D).torusPart ≤ D.torusPart :=
  iSup_le fun j => by
    rw [subData_torus]
    exact le_iSup D.torus (j : ι)

variable {hJ D}

theorem isSteinberg_subData (hD : D.IsSteinberg) : (subData hJ D).IsSteinberg where
  ne_bot γ hγ := hD.ne_bot _ hγ
  two_smul_le γ hγ h2 := by
    have h2' : incl J (2 • γ) ∈ Φ.roots := h2
    rw [map_nsmul] at h2'
    rw [subData_X, subData_X, map_nsmul]
    exact hD.two_smul_le _ hγ h2'
  commutator_mem γ hγ δ hδ hli x hx y hy := by
    have h := hD.commutator_mem _ hγ _ hδ (linIndepPair_incl hli) x hx y hy
    refine (iSup₂_le fun ε hε => ?_ : _ ≤ ⨆ ε ∈ openCone (subsystem hJ).roots γ δ,
      (subData hJ D).X ε) h
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    have he : a • incl J γ + b • incl J δ = incl J (a • γ + b • δ) := by
      rw [map_add, map_nsmul, map_nsmul]
    refine le_iSup₂_of_le (f := fun ε (_ : ε ∈ openCone (subsystem hJ).roots γ δ) =>
      (subData hJ D).X ε) (a • γ + b • δ) ⟨by rw [mem_subsystem_roots, ← he]; exact hεr,
        a, b, ha, hb, rfl⟩ ?_
    rw [subData_X, ← he]
  exists_posList := by
    obtain ⟨L, hnd, hmem, hsort, hinj⟩ := hD.exists_posList
    obtain ⟨L', hnd', hmem', hsort', hinj'⟩ := exists_list_sub (J := J) hnd hmem hsort hinj
    refine ⟨L', hnd', fun γ => ?_, hsort'.imp fun h => by rwa [ht_incl, ht_incl] at h, hinj'⟩
    rw [hmem', mem_subsystem_pos, subsystem_isIndiv]
  exists_negList := by
    obtain ⟨L, hnd, hmem, hsort, hinj⟩ := hD.exists_negList
    obtain ⟨L', hnd', hmem', hsort', hinj'⟩ := exists_list_sub (J := J) hnd hmem hsort hinj
    refine ⟨L', hnd', fun γ => ?_, hsort'.imp fun h => by rwa [ht_incl, ht_incl] at h, hinj'⟩
    rw [hmem', mem_subsystem_neg, subsystem_isIndiv]
  posPart_inf_negPart := eq_bot_iff.mpr (le_trans (inf_le_inf (subData_posPart_le hJ D)
    (subData_negPart_le hJ D)) hD.posPart_inf_negPart.le)
  n_mem j := by
    rw [subData_rankOne]
    exact hD.n_mem j
  map_conj_n j γ hγ := by
    rw [subData_X, subData_X, incl_subsystem_refl]
    exact hD.map_conj_n j _ hγ
  torus_le_normalizer j γ hγ := by
    rw [subData_torus, subData_X]
    exact hD.torus_le_normalizer j _ hγ
  rankOne_bruhat j g hg := by
    rw [subData_rankOne] at hg
    rw [subData_torus, subData_X_single, subData_n]
    exact hD.rankOne_bruhat j g hg
  eq_one_of_mem_normalizer j u hu hn := by
    rw [subData_X_single] at hu
    rw [subData_X_neg_single] at hn
    exact hD.eq_one_of_mem_normalizer j u hu hn
  torus_commute i j h hh h' hh' := by
    rw [subData_torus] at hh hh'
    exact hD.torus_commute i j h hh h' hh'
  torus_iSupIndep := by
    have : (subData hJ D).torus = D.torus ∘ Subtype.val := funext (subData_torus hJ D)
    rw [this]
    exact hD.torus_iSupIndep.comp Subtype.val_injective
  torusPart_inf_posPart := eq_bot_iff.mpr (le_trans (inf_le_inf (subData_torusPart_le hJ D)
    (subData_posPart_le hJ D)) hD.torusPart_inf_posPart.le)

end Data

section Transport

variable {I I' : Type*} {K : Type*} [Group K] {X : (I → ℤ) → Subgroup K} {G : Type*} [Group G]
  {ψ : ∀ γ, X γ → G}

theorem relationsHold_mono {S S' : Set (I → ℤ)} (h : CurtisTits.RelationsHold X S ψ)
    (hS : S' ⊆ S) : CurtisTits.RelationsHold X S' ψ :=
  fun l hl h1 => h l (fun p hp => hS (hl p hp)) h1

theorem relationsHold_comap {S : Set (I → ℤ)} (h : CurtisTits.RelationsHold X S ψ)
    (e : (I' → ℤ) → (I → ℤ)) {S' : Set (I' → ℤ)} (hS : ∀ γ ∈ S', e γ ∈ S) :
    CurtisTits.RelationsHold (fun γ => X (e γ)) S' (fun γ x => ψ (e γ) x) := by
  intro l hl h1
  have h2 := h (l.map fun p => (⟨e p.1, p.2⟩ : Σ γ, X γ)) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hS _ (hl q hq))
    (by rw [List.map_map]; exact h1)
  rw [List.map_map] at h2
  exact h2

theorem relationsHold_of_comap (e : (I' → ℤ) → (I → ℤ)) (r : (I → ℤ) → (I' → ℤ))
    {S : Set (I → ℤ)} {S' : Set (I' → ℤ)} (hr : ∀ γ ∈ S, r γ ∈ S' ∧ e (r γ) = γ)
    (h : CurtisTits.RelationsHold (fun γ => X (e γ)) S' (fun γ x => ψ (e γ) x)) :
    CurtisTits.RelationsHold X S ψ := by
  intro l hl h1
  have hcast : ∀ {γ₁ γ₂ : I → ℤ} (_ : γ₁ = γ₂) (x : K) (h₁ : x ∈ X γ₁) (h₂ : x ∈ X γ₂),
      ψ γ₁ ⟨x, h₁⟩ = ψ γ₂ ⟨x, h₂⟩ := by
    rintro _ _ rfl _ _ _
    rfl
  have hmem : ∀ p ∈ l, (p.2 : K) ∈ X (e (r p.1)) := fun p hp => by
    rw [(hr _ (hl p hp)).2]
    exact p.2.2
  let l' : List (Σ γ : I' → ℤ, X (e γ)) :=
    l.attach.map fun p => ⟨r p.1.1, ⟨p.1.2, hmem p.1 p.2⟩⟩
  have h2 := h l' (fun p hp => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      exact (hr _ (hl _ q.2)).1)
    (by
      rw [← h1, List.map_map]
      conv_rhs => rw [← List.attach_map_subtype_val l, List.map_map]
      rfl)
  rw [← h2, List.map_map]
  conv_lhs => rw [← List.attach_map_subtype_val l, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => hcast (hr _ (hl _ p.2)).2.symm _ _ _

end Transport

section Steinberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Steinberg.RootSystem ι} {K : Type*}
  [Group K] {D : RootGroupData Φ K}

theorem relationsHold_of_isSteinberg (hD : D.IsSteinberg) {G : Type*} [Group G]
    {ψ : ∀ γ, D.X γ → G}
    (hψ : ∀ w ∈ rel1 Φ D.X ∪ rel2 Φ D.X, FreeGroup.lift (symbolMap Φ ψ) w = 1) :
    CurtisTits.RelationsHold D.X Φ.roots ψ := by
  refine (relationsHold_iff subset_rfl).mpr fun v _ hv => ?_
  have hN : relN Φ D.X ≤ (FreeGroup.lift (symbolMap Φ ψ)).ker :=
    Subgroup.normalClosure_le_normal fun w hw => hψ w hw
  have h1 : QuotientGroup.mk' (relN Φ D.X) v = 1 :=
    hD.injective_stPi (by rw [D.stPi_mk, hv, map_one])
  exact hN ((QuotientGroup.eq_one_iff v).mp h1)

end Steinberg

section Datum

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem relationsHold_supported
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (J : Finset (Fin D.rank)) {G : Type*} [Group G]
    (ψ : ∀ γ, D.rootGroup γ → G)
    (hcone : ∀ α ∈ D.roots, (∀ k ∉ J, α k = 0) → ∀ β ∈ D.roots, (∀ k ∉ J, β k = 0) →
      ¬ Universal.IsNegMultiple α β → RelationsHold D.rootGroup (D.cone α β) ψ)
    (hrank : ∀ k ∈ J, RelationsHold D.rootGroup {Pi.single k 1, -Pi.single k 1} ψ) :
    RelationsHold D.rootGroup {γ | γ ∈ D.roots ∧ ∀ k ∉ J, γ k = 0} ψ := by
  have hJ : HasParabolicWords (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible) J :=
    hasParabolicWords_ofCartan _ _ J
  have hD := isSteinberg_subData (hJ := hJ) (isSteinberg_of hct hext)
  refine relationsHold_of_comap (incl J) (proj J) (fun γ hγ => ⟨?_, incl_proj hγ.2⟩)
    (relationsHold_of_isSteinberg hD ?_)
  · change incl J (proj J γ) ∈ D.roots
    rw [incl_proj hγ.2]
    exact hγ.1
  rintro w (⟨α, hα, β, hβ, hneg, hw, h1⟩ | ⟨k, hw, h1⟩)
  · have hneg' : ¬ Universal.IsNegMultiple (incl J α) (incl J β) := by
      rintro ⟨a, b, ha, hb, hab⟩
      refine hneg ((Steinberg.isNegMultiple_iff α β).mpr ⟨a, b, ha, hb, incl_injective ?_⟩)
      rw [map_nsmul, map_neg, map_nsmul, hab]
    have hrel := relationsHold_comap
      (hcone _ hα (incl_apply_eq_zero α) _ hβ (incl_apply_eq_zero β) hneg') (incl J)
      (S' := Steinberg.cone (subsystem hJ).roots α β) fun γ ⟨hγ, a, b, hγab⟩ =>
        ⟨hγ, a, b, by rw [hγab, map_add, map_nsmul, map_nsmul]⟩
    exact (relationsHold_iff fun γ hγ => hγ.1).mp hrel w hw h1
  · have hrel := relationsHold_comap (hrank k k.2) (incl J)
      (S' := {Pi.single k 1, -Pi.single k 1}) fun γ hγ => by
        rcases hγ with rfl | rfl
        · exact Or.inl (incl_single k)
        · exact Or.inr (by rw [Set.mem_singleton_iff, map_neg, incl_single])
    refine (relationsHold_iff ?_).mp hrel w hw h1
    rintro γ (rfl | rfl)
    · exact (subsystem hJ).single_mem k
    · exact (subsystem hJ).neg_mem _ ((subsystem hJ).single_mem k)

end Datum

end CFSG.Timmesfeld.Levi
