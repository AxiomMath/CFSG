module

public import CFSG.RankThree.GF2n.Smith81.S81UElem
public import CFSG.RankThree.GF2n.Smith81.S81VGeomBasic
public import CFSG.RankThree.GF2n.Smith81.S81VGeomHyp

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

private instance alow_finite_submodule [Finite F] : Finite (Submodule F (Fin 6 → F)) :=
  Finite.of_injective (fun N : Submodule F (Fin 6 → F) => (N : Set (Fin 6 → F)))
    SetLike.coe_injective

private theorem alow_key {a b c : Fin 6 → F} (hind : LinearIndependent F ![a, b, c]) :
    ∀ s t r : F, s • a + t • b + r • c = 0 → s = 0 ∧ t = 0 ∧ r = 0 := by
  intro s t r h
  have h3 := (Fintype.linearIndependent_iff.1 hind) ![s, t, r]
    (by simpa [Fin.sum_univ_three] using h)
  exact ⟨h3 0, h3 1, h3 2⟩

private theorem alow_exists_ne_zero {u : Submodule F (Fin 6 → F)} (hu : finrank F u = 1) :
    ∃ g ∈ u, g ≠ 0 := by
  have hne : u ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hu
    exact zero_ne_one hu
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨g, hg, hg0⟩

private theorem alow_card_option_sigma {V : Type} [Finite V] (T : Set V) {ι : Type} [Fintype ι]
    {E : ι → Set V} {p : V} {m q : ℕ} (hm : Fintype.card ι = m)
    (hE : ∀ i, Nat.card (E i) = q) (hdisj : ∀ i j, i ≠ j → ∀ x ∈ E i, x ∉ E j)
    (hp : ∀ i, p ∉ E i) (hsub : ∀ i, E i ⊆ T) (hpT : p ∈ T) :
    m * q + 1 ≤ Nat.card T := by
  have hX : Nat.card (Σ i : ι, ↥(E i)) = m * q := by
    rw [Nat.card_sigma]
    simp only [hE, Finset.sum_const, Finset.card_univ, smul_eq_mul, hm]
  let f : Option (Σ i : ι, ↥(E i)) → ↥T := fun o =>
    match o with
    | none => ⟨p, hpT⟩
    | some x => ⟨x.2.1, hsub x.1 x.2.2⟩
  have hf : Function.Injective f := by
    rintro (_ | ⟨i, x⟩) (_ | ⟨j, y⟩) h
    · rfl
    · exfalso
      have h1 : p = y.1 := congrArg Subtype.val h
      exact hp j (by rw [h1]; exact y.2)
    · exfalso
      have h1 : x.1 = p := congrArg Subtype.val h
      exact hp i (by rw [← h1]; exact x.2)
    · have h1 : x.1 = y.1 := congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hxy : x = y := Subtype.ext h1
        subst hxy
        rfl
      · exact absurd (by rw [h1]; exact y.2) (hdisj i j hij x.1 x.2)
  calc m * q + 1 = Nat.card (Σ i : ι, ↥(E i)) + 1 := by rw [hX]
    _ = Nat.card (Option (Σ i : ι, ↥(E i))) := (Finite.card_option).symm
    _ ≤ Nat.card T := Nat.card_le_card_of_injective f hf

theorem card_points_ge [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {U : Submodule F (Fin 6 → F)} (h3 : finrank F U = 3)
    (hno : ∀ L ≤ U, finrank F L = 2 → ¬ IsTotIso σ L) {S : Set (Fin 6 → F)} (hS : ClosedPts σ S)
    {a b c : Fin 6 → F} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (haU : a ∈ U) (hbU : b ∈ U)
    (hcU : c ∈ U) (hind : LinearIndependent F ![a, b, c]) :
    Nat.card F + Nat.card (Fσ σ) + 1 ≤
      Nat.card {r : Submodule F (Fin 6 → F) // ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}} := by
  classical
  have key := alow_key hind
  have ha0 : a ≠ 0 := (hS.iso a ha).1
  have hc0 : c ≠ 0 := (hS.iso c hc).1
  have hai : herm σ a a = 0 := (hS.iso a ha).2
  have hbi : herm σ b b = 0 := (hS.iso b hb).2
  have hci : herm σ c c = 0 := (hS.iso c hc).2
  have hbna : b ∉ Submodule.span F {a} := by
    intro hb'
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hb'
    have h := key s (-1) 0 (by rw [hs]; simp)
    exact one_ne_zero (neg_eq_zero.1 h.2.1)
  have hcnab : c ∉ Submodule.span F {a, b} := by
    intro hc'
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 hc'
    have h := key s t (-1) (by rw [hst]; simp)
    exact one_ne_zero (neg_eq_zero.1 h.2.2)
  have hab_le : Submodule.span F {a, b} ≤ U :=
    Submodule.span_le.mpr (Set.insert_subset_iff.mpr ⟨haU, Set.singleton_subset_iff.mpr hbU⟩)
  have hab : herm σ a b ≠ 0 := herm_ne_zero_of_noTI hσ.invol hno haU hbU ha0 hbna hai hbi
  have hgS : ∀ g ∈ Submodule.span F {a, b}, g ≠ 0 → herm σ g g = 0 → g ∈ S :=
    fun g hg hg0 hgi => hS.secant a ha b hb hab g hg0 hgi hg
  have hcg : ∀ g ∈ Submodule.span F {a, b}, g ≠ 0 → herm σ g g = 0 → herm σ c g ≠ 0 := by
    intro g hg hg0 hgi hcg0
    have hcg' : c ∉ Submodule.span F {g} := fun h =>
      hcnab (((Submodule.span_singleton_le_iff_mem g _).2 hg) h)
    have hgc : herm σ g c ≠ 0 :=
      herm_ne_zero_of_noTI hσ.invol hno (hab_le hg) hcU hg0 hcg' hgi hci
    exact hgc (herm_eq_zero_comm σ hσ.invol hcg0)
  have hblk_card : ∀ u ∈ IsoPtsOn σ (Submodule.span F {a, b}),
      Nat.card (IsoPtsOn σ (u ⊔ Submodule.span F {c})) = Nat.card (Fσ σ) + 1 := by
    intro u hu
    obtain ⟨g, hg, hg0⟩ := alow_exists_ne_zero hu.2.1
    have hu_eq : u = Submodule.span F {g} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hu.2.1 hg hg0
    have hsup : u ⊔ Submodule.span F {c} = Submodule.span F {c, g} := by
      rw [hu_eq, Submodule.span_insert, sup_comm]
    rw [hsup]
    exact card_isoPtsOn_pair hσ hci (hu.2.2 g hg) (hcg g (hu.1 hg) hg0 (hu.2.2 g hg))
  have hct : ∀ u : Submodule F (Fin 6 → F),
      Submodule.span F {c} ∈ IsoPtsOn σ (u ⊔ Submodule.span F {c}) := by
    intro u
    refine ⟨le_sup_right, finrank_span_singleton hc0, ?_⟩
    intro v hv
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 hv
    simp [herm_smul_left, herm_smul_right, hci]
  have hcont : ∀ u ∈ IsoPtsOn σ (Submodule.span F {a, b}),
      ∀ r ∈ IsoPtsOn σ (u ⊔ Submodule.span F {c}), ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x} := by
    intro u hu r hr
    obtain ⟨g, hg, hg0⟩ := alow_exists_ne_zero hu.2.1
    have hu_eq : u = Submodule.span F {g} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hu.2.1 hg hg0
    have hgab : g ∈ Submodule.span F {a, b} := hu.1 hg
    have hgi : herm σ g g = 0 := hu.2.2 g hg
    have hsup : u ⊔ Submodule.span F {c} = Submodule.span F {c, g} := by
      rw [hu_eq, Submodule.span_insert, sup_comm]
    rw [hsup] at hr
    obtain ⟨w, hwr, hw0⟩ := alow_exists_ne_zero hr.2.1
    have hwi : herm σ w w = 0 := hr.2.2 w hwr
    have hwS : w ∈ S := hS.secant c hc g (hgS g hgab hg0 hgi) (hcg g hgab hg0 hgi) w hw0 hwi
      (hr.1 hwr)
    have hcgU : Submodule.span F {c, g} ≤ U :=
      Submodule.span_le.mpr
        (Set.insert_subset_iff.mpr ⟨hcU, Set.singleton_subset_iff.mpr (hab_le hgab)⟩)
    exact ⟨w, hwS, hcgU (hr.1 hwr), eq_span_singleton_of_mem_of_finrank_eq_one hr.2.1 hwr hw0⟩
  have hdisj : ∀ u ∈ IsoPtsOn σ (Submodule.span F {a, b}),
      ∀ u' ∈ IsoPtsOn σ (Submodule.span F {a, b}), u ≠ u' →
      ∀ r ∈ IsoPtsOn σ (u ⊔ Submodule.span F {c}),
      r ∈ IsoPtsOn σ (u' ⊔ Submodule.span F {c}) → r = Submodule.span F {c} := by
    intro u hu u' hu' hne r hr hr'
    obtain ⟨w, hwr, hw0⟩ := alow_exists_ne_zero hr.2.1
    obtain ⟨y, hyu, z, hzc, hw⟩ := Submodule.mem_sup.1 (hr.1 hwr)
    obtain ⟨y', hyu', z', hzc', hw'⟩ := Submodule.mem_sup.1 (hr'.1 hwr)
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.1 hzc
    obtain ⟨l', rfl⟩ := Submodule.mem_span_singleton.1 hzc'
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 (hu.1 hyu)
    obtain ⟨s', t', hst'⟩ := Submodule.mem_span_pair.1 (hu'.1 hyu')
    have e1 : s • a + t • b + l • c = w := by rw [hst]; exact hw
    have e2 : s' • a + t' • b + l' • c = w := by rw [hst']; exact hw'
    have hll : l = l' := by
      have h0 := key (s - s') (t - t') (l - l') (by
        calc (s - s') • a + (t - t') • b + (l - l') • c
            = (s • a + t • b + l • c) - (s' • a + t' • b + l' • c) := by module
          _ = 0 := by rw [e1, e2, sub_self])
      exact sub_eq_zero.1 h0.2.2
    rw [← hll] at hw'
    have hyy : y = y' := add_right_cancel (hw.trans hw'.symm)
    by_cases hy0 : y = 0
    · have hwl : w = l • c := by rw [← hw, hy0, zero_add]
      have hl0 : l ≠ 0 := by
        rintro rfl
        apply hw0
        rw [hwl, zero_smul]
      rw [eq_span_singleton_of_mem_of_finrank_eq_one hr.2.1 hwr hw0, hwl,
        Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hl0)]
    · exfalso
      have huy : u = Submodule.span F {y} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hu.2.1 hyu hy0
      have hu'y : u' = Submodule.span F {y} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hu'.2.1 (by rw [hyy]; exact hyu') hy0
      exact hne (huy.trans hu'y.symm)
  haveI : Fintype ↥(IsoPtsOn σ (Submodule.span F {a, b})) := Fintype.ofFinite _
  have hm : Fintype.card ↥(IsoPtsOn σ (Submodule.span F {a, b})) = Nat.card (Fσ σ) + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_isoPtsOn_pair hσ hai hbi hab
  have hE : ∀ u : ↥(IsoPtsOn σ (Submodule.span F {a, b})),
      Nat.card ↥(IsoPtsOn σ (u.1 ⊔ Submodule.span F {c}) \ {Submodule.span F {c}}) =
        Nat.card (Fσ σ) := by
    intro u
    have h := hblk_card u.1 u.2
    rw [Nat.card_coe_set_eq] at h
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (hct u.1), h, Nat.add_sub_cancel]
  have hdisj' : ∀ i j : ↥(IsoPtsOn σ (Submodule.span F {a, b})), i ≠ j →
      ∀ x ∈ IsoPtsOn σ (i.1 ⊔ Submodule.span F {c}) \ {Submodule.span F {c}},
        x ∉ IsoPtsOn σ (j.1 ⊔ Submodule.span F {c}) \ {Submodule.span F {c}} := by
    intro i j hij x hx hxj
    apply hx.2
    exact hdisj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx.1 hxj.1
  have hp : ∀ i : ↥(IsoPtsOn σ (Submodule.span F {a, b})),
      Submodule.span F {c} ∉ IsoPtsOn σ (i.1 ⊔ Submodule.span F {c}) \ {Submodule.span F {c}} :=
    fun i h => h.2 (Set.mem_singleton _)
  have hsub : ∀ i : ↥(IsoPtsOn σ (Submodule.span F {a, b})),
      IsoPtsOn σ (i.1 ⊔ Submodule.span F {c}) \ {Submodule.span F {c}} ⊆
        {r : Submodule F (Fin 6 → F) | ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}} :=
    fun i x hx => hcont i.1 i.2 x hx.1
  have hpT : Submodule.span F {c} ∈
      {r : Submodule F (Fin 6 → F) | ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}} :=
    ⟨c, hc, hcU, rfl⟩
  have hcount := alow_card_option_sigma
    {r : Submodule F (Fin 6 → F) | ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}}
    (E := fun i : ↥(IsoPtsOn σ (Submodule.span F {a, b})) =>
      IsoPtsOn σ (i.1 ⊔ Submodule.span F {c}) \ {Submodule.span F {c}})
    (p := Submodule.span F {c}) hm hE hdisj' hp hsub hpT
  have hF : Nat.card (Fσ σ) ^ 2 = Nat.card F := card_Fσ_sq hσ
  calc Nat.card F + Nat.card (Fσ σ) + 1 = (Nat.card (Fσ σ) + 1) * Nat.card (Fσ σ) + 1 := by
        rw [← hF]; ring
    _ ≤ Nat.card {r : Submodule F (Fin 6 → F) // ∃ x ∈ S, x ∈ U ∧ r = Submodule.span F {x}} :=
        hcount

end CFSG.RankThree.GF2n.Smith81.S81V
