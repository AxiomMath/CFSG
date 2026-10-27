module

public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

@[expose] def IsoPtsOn (σ : F ≃+* F) (U : Submodule F (Fin 6 → F)) :
    Set (Submodule F (Fin 6 → F)) :=
  {r | r ≤ U ∧ finrank F r = 1 ∧ ∀ v ∈ r, herm σ v v = 0}

private theorem herm_comb_pair (hσ : IsUnitaryInvolution σ) {x y : Fin 6 → F}
    (hx : herm σ x x = 0) (hy : herm σ y y = 0) (hxy : herm σ x y = 1) (a b : F) :
    herm σ (a • x + b • y) (a • x + b • y) = σ a * b + σ b * a := by
  have hyx : herm σ y x = 1 := by rw [herm_conj σ hσ.invol x y, hxy, map_one]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hx, hy, hxy, hyx]
  ring

private theorem card_isoPtsOn_pair_norm (hσ : IsUnitaryInvolution σ) {x y : Fin 6 → F}
    (hx : herm σ x x = 0) (hy : herm σ y y = 0) (hxy : herm σ x y = 1) :
    Nat.card (IsoPtsOn σ (Submodule.span F {x, y})) = Nat.card (Fσ σ) + 1 := by
  have hyx : herm σ y x = 1 := by rw [herm_conj σ hσ.invol x y, hxy, map_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hxy
  have hpt : ∀ t : F, herm σ x (y + t • x) = 1 := by
    intro t
    simp [herm_add_right, herm_smul_right, hx, hxy]
  have hne : ∀ t : F, y + t • x ≠ 0 := by
    intro t h
    have h1 := hpt t
    rw [h, herm_zero_right] at h1
    exact zero_ne_one h1
  have hnot : ∀ t : F, y + t • x ∉ Submodule.span F {x} := by
    intro t hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have h1 := congrArg (herm σ x) hc
    simp only [herm_smul_right, hx, hpt, mul_zero] at h1
    exact zero_ne_one h1
  have hiso : ∀ t : F, σ t = t → herm σ (y + t • x) (y + t • x) = 0 := by
    intro t ht
    have h1 : herm σ (y + t • x) (y + t • x) = t + σ t := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hx, hy, hxy,
        hyx]
      ring
    rw [h1, ht, CharTwo.add_self_eq_zero]
  have hmem : ∀ o : Option (Fσ σ),
      o.elim (Submodule.span F {x}) (fun t => Submodule.span F {y + (t : F) • x}) ∈
        IsoPtsOn σ (Submodule.span F {x, y}) := by
    rintro (_ | t)
    · show Submodule.span F {x} ∈ IsoPtsOn σ (Submodule.span F {x, y})
      simp only [IsoPtsOn, Set.mem_setOf_eq]
      refine ⟨Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)),
        finrank_span_singleton hx0, ?_⟩
      intro v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp [herm_smul_left, herm_smul_right, hx]
    · show Submodule.span F {y + (t : F) • x} ∈ IsoPtsOn σ (Submodule.span F {x, y})
      simp only [IsoPtsOn, Set.mem_setOf_eq]
      refine ⟨?_, finrank_span_singleton (hne _), ?_⟩
      · rw [Submodule.span_le]
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Submodule.add_mem _
          (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      · intro v hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
        rw [herm_smul_left, herm_smul_right, hiso _ (mem_Fσ_iff.1 t.2), mul_zero, mul_zero]
  let f : Option (Fσ σ) → IsoPtsOn σ (Submodule.span F {x, y}) := fun o =>
    ⟨o.elim (Submodule.span F {x}) (fun t => Submodule.span F {y + (t : F) • x}), hmem o⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hgs : a.elim (Submodule.span F {x}) (fun t => Submodule.span F {y + (t : F) • x}) =
        b.elim (Submodule.span F {x}) (fun t => Submodule.span F {y + (t : F) • x}) :=
      congrArg Subtype.val hab
    rcases a with _ | t <;> rcases b with _ | s
    · rfl
    · exfalso
      have hgs' : Submodule.span F {x} = Submodule.span F {y + (s : F) • x} := hgs
      have hmemS : y + (s : F) • x ∈ Submodule.span F {x} := by
        rw [hgs']
        exact Submodule.mem_span_singleton_self _
      exact hnot s hmemS
    · exfalso
      have hgs' : Submodule.span F {y + (t : F) • x} = Submodule.span F {x} := hgs
      have hmemT : y + (t : F) • x ∈ Submodule.span F {x} := by
        rw [← hgs']
        exact Submodule.mem_span_singleton_self _
      exact hnot t hmemT
    · have hgs' : Submodule.span F {y + (t : F) • x} = Submodule.span F {y + (s : F) • x} := hgs
      have hmemS : y + (s : F) • x ∈ Submodule.span F {y + (t : F) • x} := by
        rw [hgs']
        exact Submodule.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmemS
      have hc1 : c = 1 := by
        have h1 := congrArg (herm σ x) hc
        simp only [herm_smul_right, hpt, mul_one] at h1
        exact h1
      rw [hc1, one_smul] at hc
      have hts : (t : F) • x = (s : F) • x := add_left_cancel hc
      have hts' : (t : F) = (s : F) := smul_left_injective F hx0 hts
      exact congrArg some (Subtype.ext hts')
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hrmem⟩
    simp only [IsoPtsOn, Set.mem_setOf_eq] at hrmem
    obtain ⟨hrle, hrfin, hriso⟩ := hrmem
    have hrne : r ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hrfin
      exact zero_ne_one hrfin
    obtain ⟨v, hvr, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrne
    have hr_eq : r = Submodule.span F {v} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hrfin hvr hv0
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hrle hvr)
    have hviso : σ a * b + σ b * a = 0 := by
      have h := hriso v hvr
      rw [← hab, herm_comb_pair hσ hx hy hxy] at h
      exact h
    by_cases hb : b = 0
    · subst hb
      simp only [zero_smul, add_zero] at hab
      have ha0 : a ≠ 0 := by
        rintro rfl
        apply hv0
        rw [← hab, zero_smul]
      refine ⟨none, Subtype.ext ?_⟩
      show Submodule.span F {x} = r
      rw [hr_eq, ← hab]
      exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 ha0) x).symm
    · have hbu : IsUnit b := isUnit_iff_ne_zero.2 hb
      obtain ⟨t, ht⟩ : ∃ t : F, t = a / b := ⟨_, rfl⟩
      have hat : a = t * b := by rw [ht, div_mul_cancel₀ a hb]
      have htfix : σ t = t := by
        have h1 : σ b * b * (σ t + t) = 0 := by
          rw [hat, map_mul] at hviso
          linear_combination hviso
        have hne' : σ b * b ≠ 0 := mul_ne_zero ((map_ne_zero σ).2 hb) hb
        have h2 : σ t + t = 0 := (mul_eq_zero.1 h1).resolve_left hne'
        exact CharTwo.add_eq_zero.1 h2
      refine ⟨some ⟨t, mem_Fσ_iff.2 htfix⟩, Subtype.ext ?_⟩
      show Submodule.span F {y + t • x} = r
      have hvt : v = b • (y + t • x) := by
        rw [← hab, hat]
        module
      rw [hr_eq, hvt, Submodule.span_singleton_smul_eq hbu]
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  rw [← Nat.card_eq_of_bijective f hbij, Finite.card_option]

theorem card_isoPtsOn_pair (hσ : IsUnitaryInvolution σ) {x y : Fin 6 → F}
    (hx : herm σ x x = 0) (hy : herm σ y y = 0) (hxy : herm σ x y ≠ 0) :
    Nat.card (IsoPtsOn σ (Submodule.span F {x, y})) = Nat.card (Fσ σ) + 1 := by
  have hy' : herm σ x ((herm σ x y)⁻¹ • y) = 1 := by
    rw [herm_smul_right, inv_mul_cancel₀ hxy]
  have hy'y : herm σ ((herm σ x y)⁻¹ • y) ((herm σ x y)⁻¹ • y) = 0 := by
    rw [herm_smul_left, herm_smul_right, hy, mul_zero, mul_zero]
  have hspan : Submodule.span F {x, y} = Submodule.span F {x, (herm σ x y)⁻¹ • y} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]
        exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [hz]
        have h1 := Submodule.smul_mem (Submodule.span F {x, (herm σ x y)⁻¹ • y})
          (herm σ x y)
          (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
            (herm σ x y)⁻¹ • y ∈ Submodule.span F {x, (herm σ x y)⁻¹ • y})
        rw [smul_smul, mul_inv_cancel₀ hxy, one_smul] at h1
        exact h1
    · rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]
        exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [hz]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))
  rw [hspan]
  exact card_isoPtsOn_pair_norm hσ hx hy'y hy'

private theorem exists_nonzero_iso (hσ : IsUnitaryInvolution σ) {M : Submodule F (Fin 6 → F)}
    (hM : finrank F M = 2) : ∃ x ∈ M, x ≠ 0 ∧ herm σ x x = 0 := by
  have hM0 : M ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hM
    omega
  obtain ⟨u, huM, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
  obtain ⟨w, hwM, hwu⟩ : ∃ w ∈ M, w ∉ Submodule.span F {u} := by
    by_contra! hcon
    have hle : M ≤ Submodule.span F {u} := fun w hw => hcon w hw
    have hfin : finrank F M ≤ finrank F (Submodule.span F {u}) := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0, hM] at hfin
    omega
  by_cases hα : herm σ u u = 0
  · exact ⟨u, huM, hu0, hα⟩
  obtain ⟨c, hc⟩ : ∃ c : F, c * herm σ u u = herm σ u w :=
    ⟨herm σ u w / herm σ u u, div_mul_cancel₀ _ hα⟩
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 6 → F, v = w - c • u := ⟨_, rfl⟩
  have hvM : v ∈ M := by
    rw [hvdef]
    exact M.sub_mem hwM (M.smul_mem c huM)
  have hv0 : v ≠ 0 := by
    intro h
    apply hwu
    have hwc : w = c • u := by
      rw [hvdef] at h
      exact sub_eq_zero.1 h
    rw [hwc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have huv : herm σ u v = 0 := by
    rw [hvdef, herm_sub_right, herm_smul_right, hc, sub_self]
  have hvu : herm σ v u = 0 := herm_eq_zero_comm σ hσ.invol huv
  by_cases hβ : herm σ v v = 0
  · exact ⟨v, hvM, hv0, hβ⟩
  have hdiv : σ (herm σ v v / herm σ u u) = herm σ v v / herm σ u u := by
    rw [map_div₀, herm_self_fixed σ hσ.invol v, herm_self_fixed σ hσ.invol u]
  obtain ⟨l, hl⟩ := hσ.norm_surj _ hdiv (div_ne_zero hβ hα)
  have key : σ l * l * herm σ u u = herm σ v v := by
    rw [hl, div_mul_cancel₀ _ hα]
  refine ⟨l • u + v, M.add_mem (M.smul_mem l huM) hvM, ?_, ?_⟩
  · intro h
    have h1 : herm σ u (l • u + v) = 0 := by rw [h, herm_zero_right]
    rw [herm_add_right, herm_smul_right, huv, add_zero] at h1
    have hl0 : l = 0 := (mul_eq_zero.1 h1).resolve_right hα
    apply hv0
    rw [hl0, zero_smul, zero_add] at h
    exact h
  · have h2 : herm σ (l • u + v) (l • u + v) = σ l * l * herm σ u u + herm σ v v := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, huv, hvu]
      ring
    rw [h2, key]
    exact CharTwo.add_self_eq_zero _

theorem exists_isotropic_pair (hσ : IsUnitaryInvolution σ) {M : Submodule F (Fin 6 → F)}
    (hM : finrank F M = 2) (hnd : NonDeg σ M) :
    ∃ x ∈ M, ∃ y ∈ M, herm σ x x = 0 ∧ herm σ y y = 0 ∧ herm σ x y ≠ 0 := by
  obtain ⟨x, hxM, hx0, hxx⟩ := exists_nonzero_iso hσ hM
  have hex : ∃ w ∈ M, herm σ x w ≠ 0 := by
    by_contra! hcon
    apply hx0
    apply hnd x hxM
    intro w hw
    rw [herm_conj σ hσ.invol x w, hcon w hw, map_zero]
  obtain ⟨w, hwM, hxw⟩ := hex
  have hxw1 : herm σ x ((herm σ x w)⁻¹ • w) = 1 := by
    rw [herm_smul_right, inv_mul_cancel₀ hxw]
  obtain ⟨c, hc⟩ := exists_isotropize hσ hxx hxw1
  refine ⟨x, hxM, (herm σ x w)⁻¹ • w + c • x,
    M.add_mem (M.smul_mem _ hwM) (M.smul_mem _ hxM), hxx, hc, ?_⟩
  have hval : herm σ x ((herm σ x w)⁻¹ • w + c • x) = 1 := by
    rw [herm_add_right, hxw1, herm_smul_right, hxx, mul_zero, add_zero]
  rw [hval]
  exact one_ne_zero

theorem card_isoPtsOn_le (hσ : IsUnitaryInvolution σ) {M : Submodule F (Fin 6 → F)}
    (hM : finrank F M = 2) (hnd : NonDeg σ M) :
    Nat.card (IsoPtsOn σ M) ≤ Nat.card (Fσ σ) + 1 := by
  obtain ⟨x, hxM, y, hyM, hxx, hyy, hxy⟩ := exists_isotropic_pair hσ hM hnd
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxy (herm_zero_left σ y)
  have hli : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : t * herm σ x y = 0 := by
      have h := congrArg (herm σ x) hst
      simpa [herm_add_right, herm_smul_right, hxx] using h
    have ht : t = 0 := (mul_eq_zero.1 h1).resolve_right hxy
    subst ht
    have hs : s • x = 0 := by simpa using hst
    exact ⟨(smul_eq_zero.1 hs).resolve_right hx0, rfl⟩
  have hr : Set.range ![x, y] = ({x, y} : Set (Fin 6 → F)) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : Submodule.span F ({x, y} : Set (Fin 6 → F)) = M := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxM
      · exact hyM
    · rw [← hr, finrank_span_eq_card hli, hM]
      simp
  rw [← hspan]
  exact le_of_eq (card_isoPtsOn_pair hσ hxx hyy hxy)

end CFSG.RankThree.GF2n.Smith81.S81V
