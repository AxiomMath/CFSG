module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.OperatorJH

open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def IsYSimple (Y C S : Subgroup G) : Prop :=
  C < S ∧ S ≤ Subgroup.normalizer (C : Set G) ∧ Y ≤ Subgroup.normalizer (C : Set G) ∧
    Y ≤ Subgroup.normalizer (S : Set G) ∧
    ∀ J : Subgroup G, C ≤ J → J ≤ S → S ≤ Subgroup.normalizer (J : Set G) →
      Y ≤ Subgroup.normalizer (J : Set G) → J = C ∨ J = S

@[expose] def IsYSeries (Y C : Subgroup G) : List (Subgroup G) → Subgroup G → Prop
  | [], D => C = D
  | S :: l, D => IsYSimple Y S D ∧ IsYSeries Y C l S

@[expose] def facMultiset {β : Type} (f : Subgroup G → Subgroup G → β) :
    List (Subgroup G) → Subgroup G → Multiset β
  | [], _ => 0
  | S :: l, D => f S D ::ₘ facMultiset f l S

omit [Group G] in
theorem mem_normalizer_inf_of {G : Type} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hH x, hK x]

variable {Y : Subgroup G}

theorem IsYSeries.le {C D : Subgroup G} {l : List (Subgroup G)} (h : IsYSeries Y C l D) :
    C ≤ D := by
  induction l generalizing D with
  | nil =>
    have hCD : C = D := h
    exact hCD.le
  | cons S l ih => exact (ih h.2).trans h.1.1.le

theorem IsYSeries.append {C D E : Subgroup G} {l₁ l₂ : List (Subgroup G)}
    (h₁ : IsYSeries Y E l₁ D) (h₂ : IsYSeries Y C l₂ E) : IsYSeries Y C (l₁ ++ l₂) D := by
  induction l₁ generalizing D with
  | nil =>
    have hED : E = D := h₁
    subst hED
    exact h₂
  | cons S l ih => exact ⟨h₁.1, ih h₁.2⟩

theorem facMultiset_append {β : Type} (f : Subgroup G → Subgroup G → β) {D E : Subgroup G}
    {l₁ l₂ : List (Subgroup G)} (h₁ : IsYSeries Y E l₁ D) :
    facMultiset f (l₁ ++ l₂) D = facMultiset f l₁ D + facMultiset f l₂ E := by
  induction l₁ generalizing D with
  | nil =>
    have hED : E = D := h₁
    subst hED
    simp [facMultiset]
  | cons S l ih =>
    simp only [List.cons_append, facMultiset]
    rw [ih h₁.2, Multiset.cons_add]

theorem exists_ySeries [Finite G] : ∀ (m : ℕ) {C E : Subgroup G}, Nat.card E = m → C ≤ E →
    E ≤ Subgroup.normalizer (C : Set G) → Y ≤ Subgroup.normalizer (C : Set G) →
    Y ≤ Subgroup.normalizer (E : Set G) → ∃ l, IsYSeries Y C l E := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C E hm hCE hEC hYC hYE
  by_cases hCE' : C = E
  · exact ⟨[], hCE'⟩
  classical
  have hex : ∃ c, ∃ S : Subgroup G, C ≤ S ∧ S < E ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      Y ≤ Subgroup.normalizer (S : Set G) ∧ Nat.card S = c :=
    ⟨_, C, le_rfl, lt_of_le_of_ne hCE hCE', hEC, hYC, rfl⟩
  have hbound : ∀ c, (∃ S : Subgroup G, C ≤ S ∧ S < E ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      Y ≤ Subgroup.normalizer (S : Set G) ∧ Nat.card S = c) → c ≤ Nat.card E := by
    rintro c ⟨S, -, hSE, -, -, rfl⟩
    exact Subgroup.card_le_of_le hSE.le
  obtain ⟨c, hc, hcmax⟩ : ∃ c, (∃ S : Subgroup G, C ≤ S ∧ S < E ∧
      E ≤ Subgroup.normalizer (S : Set G) ∧ Y ≤ Subgroup.normalizer (S : Set G) ∧
      Nat.card S = c) ∧ ∀ c', (∃ S : Subgroup G, C ≤ S ∧ S < E ∧
      E ≤ Subgroup.normalizer (S : Set G) ∧ Y ≤ Subgroup.normalizer (S : Set G) ∧
      Nat.card S = c') → c' ≤ c :=
    ⟨Nat.findGreatest (fun c => ∃ S : Subgroup G, C ≤ S ∧ S < E ∧
        E ≤ Subgroup.normalizer (S : Set G) ∧ Y ≤ Subgroup.normalizer (S : Set G) ∧
        Nat.card S = c) (Nat.card E),
      Nat.findGreatest_spec (P := fun c => ∃ S : Subgroup G, C ≤ S ∧ S < E ∧
        E ≤ Subgroup.normalizer (S : Set G) ∧ Y ≤ Subgroup.normalizer (S : Set G) ∧
        Nat.card S = c) (hbound _ hex.choose_spec) hex.choose_spec,
      fun c' hc' => Nat.le_findGreatest (hbound c' hc') hc'⟩
  obtain ⟨S, hCS, hSE, hES, hYS, hSc⟩ := hc
  have hsimple : IsYSimple Y S E := by
    refine ⟨hSE, hES, hYS, hYE, fun J hSJ hJE hEJ hYJ => ?_⟩
    by_cases hJE' : J = E
    · exact Or.inr hJE'
    left
    have hJlt : J < E := lt_of_le_of_ne hJE hJE'
    have h1 := hcmax _ ⟨J, hCS.trans hSJ, hJlt, hEJ, hYJ, rfl⟩
    rw [← hSc] at h1
    exact (Subgroup.eq_of_le_of_card_ge hSJ h1).symm
  have hSm : Nat.card S < m := hm ▸ Subgroup.card_lt_of_lt hSE
  obtain ⟨l, hl⟩ := ih _ hSm rfl hCS (hSE.le.trans hEC) hYC hYS
  exact ⟨S :: l, hsimple, hl⟩

theorem exists_ySeries_inf [Finite G] {C T : Subgroup G}
    (hYT : Y ≤ Subgroup.normalizer (T : Set G)) :
    ∀ (l : List (Subgroup G)) (S : Subgroup G), IsYSeries Y C l S →
      ∃ l', IsYSeries Y (C ⊓ T) l' (S ⊓ T) := by
  intro l
  induction l with
  | nil =>
    intro S hS
    have hCS : C = S := hS
    subst hCS
    exact ⟨[], rfl⟩
  | cons S₁ l ih =>
    intro S hS
    obtain ⟨l₁, hl₁⟩ := ih S₁ hS.2
    obtain ⟨hlt, hSS₁, hYS₁, hYS, -⟩ := hS.1
    obtain ⟨l₂, hl₂⟩ := exists_ySeries (Y := Y) _ rfl (inf_le_inf_right T hlt.le)
      (fun g hg => mem_normalizer_inf_of (hSS₁ hg.1) (Subgroup.le_normalizer hg.2))
      (fun g hg => mem_normalizer_inf_of (hYS₁ hg) (hYT hg))
      (fun g hg => mem_normalizer_inf_of (hYS hg) (hYT hg))
    exact ⟨l₂ ++ l₁, hl₂.append hl₁⟩

omit [Group G] in
theorem mem_normalizer_sup_of {G : Type} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hH, Subgroup.mem_normalizer_iff_map_conj_eq.mp hK]

omit [Group G] in
theorem mem_normalizer_of_conj_mem_of {G : Type} [Group G] [Finite G] {K : Subgroup G} {m : G}
    (h : ∀ k ∈ K, m * k * m⁻¹ ∈ K) : m ∈ Subgroup.normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj m).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥(K.map (MulAut.conj m).toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj m))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem IsYSimple.sup_eq {S S' D : Subgroup G} (h : IsYSimple Y S D) (h' : IsYSimple Y S' D)
    (hne : S ≠ S') : S ⊔ S' = D := by
  have hSS'D : S ⊔ S' ≤ D := _root_.sup_le h.1.le h'.1.le
  have hDN : D ≤ Subgroup.normalizer ((S ⊔ S' : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_sup_of (h.2.1 hd) (h'.2.1 hd)
  have hYN : Y ≤ Subgroup.normalizer ((S ⊔ S' : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_sup_of (h.2.2.1 hy) (h'.2.2.1 hy)
  rcases h.2.2.2.2 (S ⊔ S') le_sup_left hSS'D hDN hYN with h1 | h1
  · exfalso
    have hS'S : S' ≤ S := by
      rw [← h1]
      exact le_sup_right
    rcases h'.2.2.2.2 S hS'S h.1.le h.2.1 h.2.2.1 with h2 | h2
    · exact hne h2
    · exact h.1.ne h2
  · exact h1

theorem IsYSimple.inf_right [Finite G] {S S' D : Subgroup G} (h : IsYSimple Y S D)
    (h' : IsYSimple Y S' D) (hne : S ≠ S') : IsYSimple Y (S ⊓ S') S' := by
  have hsup := h.sup_eq h' hne
  refine ⟨?_, fun g hg => mem_normalizer_inf_of (h.2.1 (h'.1.le hg)) (Subgroup.le_normalizer hg),
    fun y hy => mem_normalizer_inf_of (h.2.2.1 hy) (h'.2.2.1 hy), h'.2.2.1, ?_⟩
  · refine lt_of_le_of_ne inf_le_right fun heq => ?_
    have hS'S : S' ≤ S := by
      rw [← heq]
      exact inf_le_left
    exact h.1.ne (by rw [← hsup, sup_eq_left.mpr hS'S])
  · intro J hEJ hJS' hS'J hYJ
    have hJS : J ≤ Subgroup.normalizer (S : Set G) := hJS'.trans (h'.1.le.trans h.2.1)
    have hJSD : J ⊔ S ≤ D := _root_.sup_le (hJS'.trans h'.1.le) h.1.le
    have hJSset : ((J ⊔ S : Subgroup G) : Set G) = (J : Set G) * (S : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right J S hJS
    have hSN : S ≤ Subgroup.normalizer ((J ⊔ S : Subgroup G) : Set G) := fun s hs =>
      mem_normalizer_of_conj_mem_of fun k hk => by
        have hk' : k ∈ (J : Set G) * (S : Set G) := by
          rw [← hJSset]
          exact hk
        obtain ⟨j, hj, t, ht, rfl⟩ := hk'
        have hjs : j * s⁻¹ * j⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hJS hj) _).mp (S.inv_mem hs)
        have e : s * (j * t) * s⁻¹ = j * ((j⁻¹ * s * j) * t * s⁻¹) := by group
        rw [e]
        refine Subgroup.mul_mem_sup hj ?_
        have hjs' : j⁻¹ * s * j ∈ S := by
          have := (Subgroup.mem_normalizer_iff.mp (hJS (J.inv_mem hj)) s).mp hs
          simpa using this
        exact S.mul_mem (S.mul_mem hjs' ht) (S.inv_mem hs)
    have hS'N : S' ≤ Subgroup.normalizer ((J ⊔ S : Subgroup G) : Set G) := fun s' hs' =>
      mem_normalizer_sup_of (hS'J hs') (h.2.1 (h'.1.le hs'))
    have hDN : D ≤ Subgroup.normalizer ((J ⊔ S : Subgroup G) : Set G) := by
      rw [← hsup]
      exact _root_.sup_le hSN hS'N
    have hYN : Y ≤ Subgroup.normalizer ((J ⊔ S : Subgroup G) : Set G) := fun y hy =>
      mem_normalizer_sup_of (hYJ hy) (h.2.2.1 hy)
    rcases h.2.2.2.2 (J ⊔ S) le_sup_right hJSD hDN hYN with h1 | h1
    · left
      refine le_antisymm (le_inf ?_ hJS') hEJ
      rw [← h1]
      exact le_sup_left
    · right
      refine le_antisymm hJS' fun s' hs' => ?_
      have hs'D : s' ∈ (J : Set G) * (S : Set G) := by
        rw [← hJSset, h1]
        exact h'.1.le hs'
      obtain ⟨j, hj, t, ht, hjt⟩ := hs'D
      have htS' : t ∈ S' := by
        have : t = j⁻¹ * s' := by rw [← hjt]; group
        rw [this]
        exact S'.mul_mem (S'.inv_mem (hJS' hj)) hs'
      rw [← hjt]
      exact J.mul_mem hj (hEJ ⟨ht, htS'⟩)

theorem IsYSimple.inf_left [Finite G] {S S' D : Subgroup G} (h : IsYSimple Y S D)
    (h' : IsYSimple Y S' D) (hne : S ≠ S') : IsYSimple Y (S ⊓ S') S := by
  have := h'.inf_right h (Ne.symm hne)
  rwa [inf_comm] at this

theorem facMultiset_eq [Finite G] {β : Type} (f : Subgroup G → Subgroup G → β)
    (hf : ∀ S S' D : Subgroup G, IsYSimple Y S D → IsYSimple Y S' D → S ≠ S' →
      f S D = f (S ⊓ S') S') :
    ∀ (m : ℕ) (C D : Subgroup G), Nat.card D = m → ∀ l l' : List (Subgroup G),
      IsYSeries Y C l D → IsYSeries Y C l' D → facMultiset f l D = facMultiset f l' D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C D hm l l' hl hl'
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | cons S' l₀' =>
      exfalso
      have hCD : C = D := hl
      exact absurd (hCD ▸ hl'.2.le) (not_le_of_gt hl'.1.1)
  | cons S l₀ =>
    cases l' with
    | nil =>
      exfalso
      have hCD : C = D := hl'
      exact absurd (hCD ▸ hl.2.le) (not_le_of_gt hl.1.1)
    | cons S' l₀' =>
      have hS := hl.1
      have hS' := hl'.1
      have hSm : Nat.card S < m := hm ▸ Subgroup.card_lt_of_lt hS.1
      have hS'm : Nat.card S' < m := hm ▸ Subgroup.card_lt_of_lt hS'.1
      by_cases hSS' : S = S'
      · subst hSS'
        simp only [facMultiset]
        rw [ih _ hSm C S rfl l₀ l₀' hl.2 hl'.2]
      · have hE := hS.inf_right hS' hSS'
        have hE' := hS.inf_left hS' hSS'
        obtain ⟨lE, hlE⟩ := exists_ySeries_inf (T := S') hS'.2.2.1 l₀ S hl.2
        rw [inf_eq_left.mpr hl'.2.le] at hlE
        have h1 := ih _ hSm C S rfl l₀ ((S ⊓ S') :: lE) hl.2 ⟨hE', hlE⟩
        have h2 := ih _ hS'm C S' rfl l₀' ((S ⊓ S') :: lE) hl'.2 ⟨hE, hlE⟩
        simp only [facMultiset] at h1 h2 ⊢
        have h3 : f S' D = f (S ⊓ S') S := by
          rw [hf S' S D hS' hS (Ne.symm hSS'), inf_comm]
        rw [h1, h2, hf S S' D hS hS' hSS', h3, Multiset.cons_swap]

end CFSG.Quasithin.OperatorJH
