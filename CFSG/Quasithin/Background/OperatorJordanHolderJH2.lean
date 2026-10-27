module

public import CFSG.Quasithin.Background.OperatorJordanHolderJH1
public import CFSG.Quasithin.Background.OperatorJordanHolder

public section

namespace CFSG.Quasithin.OperatorJH

open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] {Y K : Subgroup G} {x : G} {n : ℕ} {F : Type} [Field F]
  {α₀ : ↥K →* ↥(StatedSL n F)}

theorem IsLabFactor.isYSimple {C S : Subgroup G} {e : Option F}
    (h : IsLabFactor Y K x α₀ C S e) : IsYSimple Y C S :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

open Classical in
@[expose] noncomputable def labelOf (Y K : Subgroup G) (x : G) (α₀ : ↥K →* ↥(StatedSL n F))
    (C S : Subgroup G) : Option (Option F) :=
  if h : ∃ e, IsLabFactor Y K x α₀ C S e then some h.choose else none

theorem labelOf_eq_some {C S : Subgroup G} {e : Option F} (h : IsLabFactor Y K x α₀ C S e)
    (hKY : K ≤ Y) (hxY : x ∈ Y) (hn : 2 ≤ n) (hα : Function.Surjective α₀) :
    labelOf Y K x α₀ C S = some e := by
  unfold labelOf
  split_ifs with hex
  · exact congrArg some (hex.choose_spec.label_unique h hKY hxY hn hα)
  · exact absurd ⟨e, h⟩ hex

theorem isLabFactor_of_labelOf {C S : Subgroup G} {e : Option F}
    (h : labelOf Y K x α₀ C S = some e) : IsLabFactor Y K x α₀ C S e := by
  unfold labelOf at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  exact hex.choose_spec

omit [Group G] in
theorem exists_hom_of_mul {G : Type} [Group G] {M : Type} [Group M] {S S' D : Subgroup G}
    (hDset : (D : Set G) = (S' : Set G) * (S : Set G)) (hS'D : S' ≤ D)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (β' : ↥S' →* M)
    (hβ' : ∀ c : ↥S', (c : G) ∈ S → β' c = 1) :
    ∃ β : ↥D →* M, ∀ (d : ↥D) (s' : ↥S'), (s' : G)⁻¹ * d ∈ S → β d = β' s' := by
  classical
  have hex : ∀ d : ↥D, ∃ s' : ↥S', (s' : G)⁻¹ * d ∈ S := fun d => by
    have hd : (d : G) ∈ (S' : Set G) * (S : Set G) := hDset ▸ d.2
    obtain ⟨s', hs', s, hs, hds⟩ := hd
    refine ⟨⟨s', hs'⟩, ?_⟩
    rw [← hds]
    simpa using hs
  choose f hf using hex
  have hwd : ∀ (d : ↥D) (s₁ s₂ : ↥S'), (s₁ : G)⁻¹ * d ∈ S → (s₂ : G)⁻¹ * d ∈ S →
      β' s₁ = β' s₂ := by
    intro d s₁ s₂ h₁ h₂
    have h3 : ((s₂⁻¹ * s₁ : ↥S') : G) ∈ S := by
      have := S.mul_mem h₂ (S.inv_mem h₁)
      simpa [mul_assoc] using this
    have h4 := hβ' _ h3
    rw [map_mul, map_inv, inv_mul_eq_one] at h4
    exact h4.symm
  refine ⟨{ toFun := fun d => β' (f d), map_one' := ?_, map_mul' := ?_ },
    fun d s' h => hwd d (f d) s' (hf d) h⟩
  · exact (hwd 1 (f 1) 1 (hf 1) (by simp)).trans (map_one β')
  · intro d₁ d₂
    have h : ((f d₁ * f d₂ : ↥S') : G)⁻¹ * ((d₁ * d₂ : ↥D) : G) ∈ S := by
      have e : ((f d₁ * f d₂ : ↥S') : G)⁻¹ * ((d₁ * d₂ : ↥D) : G) =
          ((f d₂ : G)⁻¹ * ((f d₁ : G)⁻¹ * d₁) * ((f d₂ : G)⁻¹)⁻¹) * ((f d₂ : G)⁻¹ * d₂) := by
        simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv]
        group
      rw [e]
      exact S.mul_mem ((Subgroup.mem_normalizer_iff.mp
        (hDS (D.inv_mem (hS'D (f d₂).2))) _).mp (hf d₁)) (hf d₂)
    show β' (f (d₁ * d₂)) = β' (f d₁) * β' (f d₂)
    rw [hwd (d₁ * d₂) (f (d₁ * d₂)) (f d₁ * f d₂) (hf _) h, map_mul]

section Transfer

variable [Finite G] {S S' D : Subgroup G}

omit [Finite G] in
theorem IsYSimple.coe_eq_mul (hS : IsYSimple Y S D) (hS' : IsYSimple Y S' D) (hne : S ≠ S') :
    (D : Set G) = (S' : Set G) * (S : Set G) := by
  rw [← hS.sup_eq hS' hne, sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right S' S (hS'.1.le.trans hS.2.1)

theorem IsLabFactor.inf_right {e : Option F} (hS : IsYSimple Y S D) (hS' : IsYSimple Y S' D)
    (hne : S ≠ S') (hKY : K ≤ Y) (h : IsLabFactor Y K x α₀ S D e) :
    IsLabFactor Y K x α₀ (S ⊓ S') S' e := by
  have hE := hS.inf_right hS' hne
  have hDset := hS.coe_eq_mul hS' hne
  refine ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1, hE.2.2.2.2, ?_⟩
  obtain ⟨-, -, -, -, -, hlab⟩ := h
  cases e with
  | none =>
    intro k hk s' hs'
    exact ⟨hlab k hk s' (hS'.1.le hs'), S'.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hS'.2.2.1 (hKY hk)) s').mp hs') (S'.inv_mem hs')⟩
  | some a =>
    obtain ⟨β, hβs, hβk, hβK, hβx⟩ := hlab
    refine ⟨β.comp (Subgroup.inclusion hS'.1.le), ?_, ?_, ?_, ?_⟩
    · intro v
      obtain ⟨d, rfl⟩ := hβs v
      have hd : (d : G) ∈ (S' : Set G) * (S : Set G) := hDset ▸ d.2
      obtain ⟨s', hs', s, hs, hds⟩ := hd
      refine ⟨⟨s', hs'⟩, ?_⟩
      have h1 : β ⟨s, hS.1.le hs⟩ = 1 := (hβk _).mpr hs
      have h2 : d = ⟨s', hS'.1.le hs'⟩ * ⟨s, hS.1.le hs⟩ := Subtype.ext hds.symm
      rw [h2, map_mul, h1, mul_one]
      rfl
    · intro c
      rw [MonoidHom.comp_apply, hβk]
      exact ⟨fun hc => ⟨hc, c.2⟩, fun hc => hc.1⟩
    · intro k c c' hcc'
      exact hβK k (Subgroup.inclusion _ c) (Subgroup.inclusion _ c') hcc'
    · intro c c' hcc'
      exact hβx (Subgroup.inclusion _ c) (Subgroup.inclusion _ c') hcc'

omit [Finite G] in
theorem IsLabFactor.of_inf_right {e : Option F} (hS : IsYSimple Y S D)
    (hS' : IsYSimple Y S' D) (hne : S ≠ S') (hKY : K ≤ Y) (hxY : x ∈ Y)
    (h : IsLabFactor Y K x α₀ (S ⊓ S') S' e) : IsLabFactor Y K x α₀ S D e := by
  have hDset := hS.coe_eq_mul hS' hne
  refine ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2, ?_⟩
  obtain ⟨-, -, -, -, -, hlab⟩ := h
  cases e with
  | none =>
    intro k hk d hd
    have hd' : d ∈ (S' : Set G) * (S : Set G) := hDset ▸ hd
    obtain ⟨s', hs', s, hs, rfl⟩ := hd'
    have e1 : k * (s' * s) * k⁻¹ * (s' * s)⁻¹ =
        (k * s' * k⁻¹ * s'⁻¹) * (s' * (k * s * k⁻¹ * s⁻¹) * s'⁻¹) := by group
    rw [e1]
    refine S.mul_mem (hlab k hk s' hs').1 ?_
    have hks : k * s * k⁻¹ * s⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.mp (hS.2.2.1 (hKY hk)) s).mp hs) (S.inv_mem hs)
    exact (Subgroup.mem_normalizer_iff.mp (hS.2.1 (hS'.1.le hs')) _).mp hks
  | some a =>
    obtain ⟨β', hβ's, hβ'k, hβ'K, hβ'x⟩ := hlab
    obtain ⟨β, hβ⟩ := exists_hom_of_mul hDset hS'.1.le hS.2.1 β'
      (fun c hc => (hβ'k c).mpr ⟨hc, c.2⟩)
    have hdec : ∀ d : ↥D, ∃ s' : ↥S', (s' : G)⁻¹ * d ∈ S := fun d => by
      have hd : (d : G) ∈ (S' : Set G) * (S : Set G) := hDset ▸ d.2
      obtain ⟨s', hs', s, hs, hds⟩ := hd
      refine ⟨⟨s', hs'⟩, ?_⟩
      rw [← hds]
      simpa using hs
    have hconj : ∀ g ∈ Y, ∀ (d d' : ↥D) (s' : ↥S'), (d' : G) = g * d * g⁻¹ →
        (s' : G)⁻¹ * d ∈ S → ∃ s'' : ↥S', (s'' : G) = g * s' * g⁻¹ ∧ (s'' : G)⁻¹ * d' ∈ S := by
      intro g hg d d' s' hd' hs'
      have h1 : g * (s' : G) * g⁻¹ ∈ S' :=
        (Subgroup.mem_normalizer_iff.mp (hS'.2.2.1 hg) _).mp s'.2
      refine ⟨⟨_, h1⟩, rfl, ?_⟩
      have e : (g * (s' : G) * g⁻¹)⁻¹ * d' = g * ((s' : G)⁻¹ * d) * g⁻¹ := by
        rw [hd']
        group
      show (g * (s' : G) * g⁻¹)⁻¹ * d' ∈ S
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hS.2.2.1 hg) _).mp hs'
    refine ⟨β, ?_, ?_, ?_, ?_⟩
    · intro v
      obtain ⟨c, rfl⟩ := hβ's v
      exact ⟨⟨c, hS'.1.le c.2⟩, hβ _ c (by simp)⟩
    · intro d
      obtain ⟨s', hs'⟩ := hdec d
      rw [hβ d s' hs', hβ'k]
      constructor
      · intro h
        have : (d : G) = s' * ((s' : G)⁻¹ * d) := by group
        rw [this]
        exact S.mul_mem h.1 hs'
      · intro h
        refine ⟨?_, s'.2⟩
        have : (s' : G) = d * ((s' : G)⁻¹ * d)⁻¹ := by group
        rw [this]
        exact S.mul_mem h (S.inv_mem hs')
    · intro k d d' hd'
      obtain ⟨s', hs'⟩ := hdec d
      obtain ⟨s'', hs''e, hs''⟩ := hconj k (hKY k.2) d d' s' hd' hs'
      rw [hβ d s' hs', hβ d' s'' hs'']
      exact hβ'K k s' s'' hs''e
    · intro d d' hd'
      obtain ⟨s', hs'⟩ := hdec d
      obtain ⟨s'', hs''e, hs''⟩ := hconj x hxY d d' s' hd' hs'
      rw [hβ d s' hs', hβ d' s'' hs'']
      exact hβ'x s' s'' hs''e

theorem labelOf_inf (hKY : K ≤ Y) (hxY : x ∈ Y) (hn : 2 ≤ n) (hα : Function.Surjective α₀)
    (hS : IsYSimple Y S D) (hS' : IsYSimple Y S' D) (hne : S ≠ S') :
    labelOf Y K x α₀ S D = labelOf Y K x α₀ (S ⊓ S') S' := by
  by_cases hex : ∃ e, IsLabFactor Y K x α₀ S D e
  · obtain ⟨e, he⟩ := hex
    rw [labelOf_eq_some he hKY hxY hn hα,
      labelOf_eq_some (IsLabFactor.inf_right hS hS' hne hKY he) hKY hxY hn hα]
  · have hex' : ¬ ∃ e, IsLabFactor Y K x α₀ (S ⊓ S') S' e := fun ⟨e, he⟩ =>
      hex ⟨e, IsLabFactor.of_inf_right hS hS' hne hKY hxY he⟩
    have h1 : labelOf Y K x α₀ S D = none := by simp [labelOf, hex]
    have h2 : labelOf Y K x α₀ (S ⊓ S') S' = none := by simp [labelOf, hex']
    rw [h1, h2]

end Transfer

@[expose] def fullLab (l : List (Subgroup G × Option F)) : Multiset (Option (Option F)) :=
  (l.map fun p => some p.2 : List (Option (Option F)))

omit [Field F] in
theorem fullLab_append (l₁ l₂ : List (Subgroup G × Option F)) :
    fullLab (l₁ ++ l₂) = fullLab l₁ + fullLab l₂ := by
  simp [fullLab]

omit [Field F] in
theorem fullLab_singleton (S : Subgroup G) (e : Option F) :
    fullLab [(S, e)] = {some e} := rfl

omit [Field F] in
theorem labMultiset_eq_filterMap (l : List (Subgroup G × Option F)) :
    labMultiset l = (fullLab l).filterMap Option.join := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [labMultiset_cons, ih]
    obtain ⟨S, e⟩ := p
    cases e with
    | none => simp [fullLab]
    | some a => simp [fullLab]

omit [Field F] in
theorem none_not_mem_fullLab (l : List (Subgroup G × Option F)) : none ∉ fullLab l := by
  simp [fullLab]

theorem IsLabSeries.le_normalizer_bot {C D : Subgroup G} {p : Subgroup G × Option F}
    {l : List (Subgroup G × Option F)} (h : IsLabSeries Y K x α₀ C (p :: l) D) :
    Y ≤ Subgroup.normalizer (C : Set G) :=
  h.1.2.2.1

theorem IsLabSeries.le_normalizer_top : ∀ {C D : Subgroup G} {l : List (Subgroup G × Option F)},
    l ≠ [] → IsLabSeries Y K x α₀ C l D → Y ≤ Subgroup.normalizer (D : Set G)
  | _, _, [], hl, _ => absurd rfl hl
  | _, D, p :: l, _, h => by
    by_cases hl : l = []
    · subst hl
      have hpD : p.1 = D := h.2
      rw [← hpD]
      exact h.1.2.2.2.1
    · exact IsLabSeries.le_normalizer_top hl h.2

section Conv

variable [Finite G]

omit [Finite G] in
theorem exists_ySeries_of_isLabSeries (hKY : K ≤ Y) (hxY : x ∈ Y) (hn : 2 ≤ n)
    (hα : Function.Surjective α₀) : ∀ (l : List (Subgroup G × Option F)) (C D : Subgroup G),
    IsLabSeries Y K x α₀ C l D →
      ∃ t, IsYSeries Y C t D ∧ facMultiset (labelOf Y K x α₀) t D = fullLab l := by
  intro l
  induction l with
  | nil => exact fun C D h => ⟨[], h, rfl⟩
  | cons p l ih =>
    intro C D h
    obtain ⟨hf, hl⟩ := h
    obtain ⟨t, ht, htm⟩ := ih p.1 D hl
    refine ⟨t ++ [C], ht.append ⟨IsLabFactor.isYSimple hf, rfl⟩, ?_⟩
    rw [facMultiset_append _ ht, htm]
    simp only [facMultiset, labelOf_eq_some hf hKY hxY hn hα]
    simp [fullLab, add_comm]

omit [Finite G] in
theorem exists_isLabSeries_of_ySeries : ∀ (t : List (Subgroup G)) (C D : Subgroup G),
    IsYSeries Y C t D → none ∉ facMultiset (labelOf Y K x α₀) t D →
      ∃ l : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l D ∧
        fullLab l = facMultiset (labelOf Y K x α₀) t D := by
  intro t
  induction t with
  | nil =>
    intro C D h _
    exact ⟨[], h, rfl⟩
  | cons S t ih =>
    intro C D h hnone
    obtain ⟨hS, ht⟩ := h
    have hnone' : none ∉ labelOf Y K x α₀ S D ::ₘ facMultiset (labelOf Y K x α₀) t S := hnone
    rw [Multiset.mem_cons, not_or] at hnone'
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (Ne.symm hnone'.1)
    obtain ⟨l, hl, hlm⟩ := ih C S ht hnone'.2
    refine ⟨l ++ [(D, e)], hl.append (isLabSeries_singleton (isLabFactor_of_labelOf he)), ?_⟩
    rw [fullLab_append, hlm, fullLab_singleton, ← he]
    show _ = labelOf Y K x α₀ S D ::ₘ facMultiset (labelOf Y K x α₀) t S
    rw [add_comm, Multiset.singleton_add]

end Conv

theorem operatorJHNatEig_holds : OperatorJHNatEig := by
  intro G _ _ Y K x n F _ α₀ hKY hxY hn hα C D l hl
  have hf : ∀ S S' D : Subgroup G, IsYSimple Y S D → IsYSimple Y S' D → S ≠ S' →
      labelOf Y K x α₀ S D = labelOf Y K x α₀ (S ⊓ S') S' :=
    fun S S' D hS hS' hne => labelOf_inf hKY hxY hn hα hS hS' hne
  obtain ⟨t, ht, htm⟩ := exists_ySeries_of_isLabSeries hKY hxY hn hα l C D hl
  refine ⟨fun l' hl' => ?_, fun E hCE hED hEC hDE hYE => ?_⟩
  · obtain ⟨t', ht', htm'⟩ := exists_ySeries_of_isLabSeries hKY hxY hn hα l' C D hl'
    have h1 := facMultiset_eq _ hf _ C D rfl t' t ht' ht
    rw [labMultiset_eq_filterMap, labMultiset_eq_filterMap, ← htm, ← htm', h1]
  · by_cases hl0 : l = []
    · subst hl0
      have hCD : C = D := hl
      subst hCD
      have hEC' : E = C := le_antisymm hED hCE
      subst hEC'
      exact ⟨[], [], rfl, rfl, by simp [labMultiset]⟩
    · have hYC : Y ≤ Subgroup.normalizer (C : Set G) := by
        obtain ⟨p, l₁, rfl⟩ := List.exists_cons_of_ne_nil hl0
        exact IsLabSeries.le_normalizer_bot hl
      have hYD : Y ≤ Subgroup.normalizer (D : Set G) := IsLabSeries.le_normalizer_top hl0 hl
      obtain ⟨t₁, ht₁⟩ := exists_ySeries (Y := Y) _ rfl hCE hEC hYC hYE
      obtain ⟨t₂, ht₂⟩ := exists_ySeries (Y := Y) _ rfl hED hDE hYE hYD
      have hJH := facMultiset_eq _ hf _ C D rfl _ t (ht₂.append ht₁) ht
      rw [facMultiset_append _ ht₂, htm] at hJH
      have hnone := none_not_mem_fullLab (G := G) l
      rw [← hJH] at hnone
      obtain ⟨l₁, hl₁, hl₁m⟩ := exists_isLabSeries_of_ySeries (α₀ := α₀) t₁ C E ht₁
        fun h => hnone (Multiset.mem_add.mpr (Or.inr h))
      obtain ⟨l₂, hl₂, hl₂m⟩ := exists_isLabSeries_of_ySeries (α₀ := α₀) t₂ E D ht₂
        fun h => hnone (Multiset.mem_add.mpr (Or.inl h))
      refine ⟨l₁, l₂, hl₁, hl₂, ?_⟩
      rw [labMultiset_eq_filterMap, labMultiset_eq_filterMap, labMultiset_eq_filterMap,
        ← Multiset.filterMap_add, hl₁m, hl₂m, ← hJH, add_comm]

end CFSG.Quasithin.OperatorJH
