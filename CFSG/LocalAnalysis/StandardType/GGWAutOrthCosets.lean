module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin TauCeti
open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section OrthOdd

private lemma ggWAutQ_omega_eq_commutator {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) :
    ggOmega Q = ⁅QuadraticMap.orthogonalGroup Q, QuadraticMap.orthogonalGroup Q⁆ := by
  rw [ggOmega, Subgroup.commutator_def]
  congr 1
  ext c
  constructor
  · rintro ⟨g, h, hg, hh, rfl⟩
    exact ⟨g, QuadraticMap.mem_orthogonalGroup_iff.mpr hg, h,
      QuadraticMap.mem_orthogonalGroup_iff.mpr hh, rfl⟩
  · rintro ⟨g, hg, h, hh, rfl⟩
    exact ⟨g, h, QuadraticMap.mem_orthogonalGroup_iff.mp hg,
      QuadraticMap.mem_orthogonalGroup_iff.mp hh, rfl⟩

private lemma ggWAutQ_reflection_isReflLin {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (v : V)
    [Invertible (Q v)] : IsReflLin (QuadraticMap.reflection Q v) := by
  let φ : Module.Dual (ZMod 3) V := ⅟(Q v) • Q.polarBilin v
  have hφ : φ v = 2 := by
    dsimp only [φ]
    calc (⅟(Q v) • Q.polarBilin v) v
        = ⅟(Q v) * Q.polarBilin v v := by rw [LinearMap.smul_apply, smul_eq_mul]
      _ = ⅟(Q v) * QuadraticMap.polar Q v v := by rw [QuadraticMap.polarBilin_apply_apply]
      _ = ⅟(Q v) * (2 * Q v) := by
        rw [QuadraticMap.polar_self, nsmul_eq_mul]
        ring
      _ = 2 * (⅟(Q v) * Q v) := by ring
      _ = 2 * 1 := by rw [invOf_mul_self]
      _ = 2 := by ring
  refine ⟨v, φ, hφ, ?_⟩
  ext y
  rw [QuadraticMap.reflection_apply, Module.reflection_apply]
  simp only [φ, LinearMap.smul_apply, smul_eq_mul, QuadraticMap.polarBilin_apply_apply]

private lemma ggWAutQ_reflection_isom {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (v : V)
    [Invertible (Q v)] : ZS.IsIsom 3 Q (QuadraticMap.reflection Q v) :=
  QuadraticMap.mem_orthogonalGroup_iff.mp (QuadraticMap.reflection_mem_orthogonalGroup Q v)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private noncomputable def ggWAutQ_cls (Q : QuadraticForm (ZMod 3) V) (v : V) :
    Abelianization (QuadraticMap.orthogonalGroup Q) :=
  Abelianization.of (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
    QuadraticMap.orthogonalGroup Q)

private lemma ggWAutQ_cls_def (Q : QuadraticForm (ZMod 3) V) (v : V) :
    ggWAutQ_cls Q v = Abelianization.of (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
      QuadraticMap.orthogonalGroup Q) := rfl

private lemma ggWAutQ_cls_sq (Q : QuadraticForm (ZMod 3) V) (v : V) :
    ggWAutQ_cls Q v ^ 2 = 1 := by
  have h : (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
      QuadraticMap.orthogonalGroup Q) ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact reflect_mul_self Q v)
  rw [ggWAutQ_cls_def, ← map_pow, h, map_one]

private lemma ggWAutQ_cls_eq_of_isSquare (Q : QuadraticForm (ZMod 3) V) (h2 : (2 : ZMod 3) ≠ 0)
    {v w : V} (hv : Q v ≠ 0) (hw : Q w ≠ 0) (hsq : IsSquare (Q v * Q w)) :
    ggWAutQ_cls Q v = ggWAutQ_cls Q w := by
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hv hw (by rw [hc, mul_zero])
  have hw' : Q v = Q ((c / Q w) • w) := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    field_simp
    linear_combination hc
  obtain ⟨g, hg, hgv⟩ := exists_mem_orthogonalGroup_apply_eq h2 hw' (by rwa [← hw'])
  have hconj : (⟨g, hg⟩ : QuadraticMap.orthogonalGroup Q) *
      ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ *
        (⟨g, hg⟩ : QuadraticMap.orthogonalGroup Q)⁻¹ =
      ⟨reflect Q w, reflect_mem_orthogonalGroup Q w⟩ := by
    refine Subtype.ext ?_
    change g * reflect Q v * g⁻¹ = reflect Q w
    rw [reflect_conj hg, hgv, reflect_smul_of_ne_zero (div_ne_zero hc0 hw)]
  rw [ggWAutQ_cls_def, ggWAutQ_cls_def, ← hconj, map_mul, map_mul, map_inv,
    mul_comm (Abelianization.of (⟨g, hg⟩ : QuadraticMap.orthogonalGroup Q)), mul_inv_cancel_right]

private lemma ggWAutQ_cover_of_not_isSquare (Q : QuadraticForm (ZMod 3) V) {u w : V}
    (hu : Q u ≠ 0) (hw : Q w ≠ 0) (hns : ¬ IsSquare (Q u * Q w)) (v : V) (hv : Q v ≠ 0) :
    ggWAutQ_cls Q v = ggWAutQ_cls Q u ∨ ggWAutQ_cls Q v = ggWAutQ_cls Q w := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  by_cases hsq : IsSquare (Q u * Q v)
  · exact Or.inl (ggWAutQ_cls_eq_of_isSquare Q h2 hu hv hsq).symm
  · right
    obtain ⟨c, hc⟩ :=
      isSquare_mul_of_not_isSquare (mul_ne_zero hu hw) (mul_ne_zero hu hv) hns hsq
    refine (ggWAutQ_cls_eq_of_isSquare Q h2 hw hv ?_).symm
    refine ⟨c / Q u, ?_⟩
    field_simp
    linear_combination hc

private lemma ggWAutQ_dichotomy (Q : QuadraticForm (ZMod 3) V) {u : V} (hu : Q u ≠ 0) :
    ∃ w : V, Q w ≠ 0 ∧ ∀ v : V, Q v ≠ 0 →
      ggWAutQ_cls Q v = ggWAutQ_cls Q u ∨ ggWAutQ_cls Q v = ggWAutQ_cls Q w := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  by_cases hex : ∃ w : V, Q w ≠ 0 ∧ ¬ IsSquare (Q u * Q w)
  · obtain ⟨w, hw, hns⟩ := hex
    exact ⟨w, hw, ggWAutQ_cover_of_not_isSquare Q hu hw hns⟩
  · refine ⟨u, hu, fun v hv => Or.inl ?_⟩
    refine (ggWAutQ_cls_eq_of_isSquare Q h2 hu hv ?_).symm
    by_contra h
    exact hex ⟨v, hv, h⟩

private lemma ggWAutQ_coset_of_eq (Q : QuadraticForm (ZMod 3) V)
    {g t : V ≃ₗ[ZMod 3] V} (hg : g ∈ QuadraticMap.orthogonalGroup Q)
    (ht : t ∈ QuadraticMap.orthogonalGroup Q)
    (h : Abelianization.of (⟨g, hg⟩ : QuadraticMap.orthogonalGroup Q) =
      Abelianization.of (⟨t, ht⟩ : QuadraticMap.orthogonalGroup Q)) :
    ∃ ω ∈ ggOmega Q, g = ω * t := by
  refine ⟨g * t⁻¹, ?_, by group⟩
  have h1 : Abelianization.of (⟨g * t⁻¹, mul_mem hg (inv_mem ht)⟩ :
      QuadraticMap.orthogonalGroup Q) = 1 := by
    have heq : (⟨g * t⁻¹, mul_mem hg (inv_mem ht)⟩ : QuadraticMap.orthogonalGroup Q) =
        (⟨g, hg⟩ : QuadraticMap.orthogonalGroup Q) *
          (⟨t, ht⟩ : QuadraticMap.orthogonalGroup Q)⁻¹ := Subtype.ext rfl
    rw [heq, map_mul, map_inv, h, mul_inv_cancel]
  have hker : (⟨g * t⁻¹, mul_mem hg (inv_mem ht)⟩ : QuadraticMap.orthogonalGroup Q) ∈
      (Abelianization.of : QuadraticMap.orthogonalGroup Q →*
        Abelianization (QuadraticMap.orthogonalGroup Q)).ker :=
    MonoidHom.mem_ker.mpr h1
  rw [Abelianization.ker_of (QuadraticMap.orthogonalGroup Q)] at hker
  have hmap : g * t⁻¹ ∈ (commutator (↥(QuadraticMap.orthogonalGroup Q))).map
      (QuadraticMap.orthogonalGroup Q).subtype :=
    Subgroup.mem_map_of_mem _ hker
  rw [Subgroup.map_subtype_commutator] at hmap
  rwa [ggWAutQ_omega_eq_commutator Q]

private lemma ggWAutQ_list_prod_mem {A : Type*} [CommGroup A] {x₁ x₂ : A}
    (h₁ : x₁ ^ 2 = 1) (h₂ : x₂ ^ 2 = 1) (l : List A) (hl : ∀ a ∈ l, a = x₁ ∨ a = x₂) :
    l.prod = 1 ∨ l.prod = x₁ ∨ l.prod = x₂ ∨ l.prod = x₁ * x₂ := by
  suffices h : ∃ i : Fin 4, (![1, x₁, x₂, x₁ * x₂] : Fin 4 → A) i = l.prod by
    obtain ⟨i, hi⟩ := h
    fin_cases i
    · exact Or.inl (by simpa using hi.symm)
    · exact Or.inr (Or.inl (by simpa using hi.symm))
    · exact Or.inr (Or.inr (Or.inl (by simpa using hi.symm)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hi.symm)))
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
      obtain ⟨i, hi⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
      obtain ⟨j, hj⟩ := exists_fin_four_eq_mul h₁ h₂ (hl a List.mem_cons_self) i
      exact ⟨j, by rw [List.prod_cons, hj, hi]⟩

private lemma ggWAutQ_cosets_of_cover [Module.Finite (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u w : V} (_hu : Q u ≠ 0) (_hw : Q w ≠ 0)
    (hcover : ∀ v : V, Q v ≠ 0 →
      ggWAutQ_cls Q v = ggWAutQ_cls Q u ∨ ggWAutQ_cls Q v = ggWAutQ_cls Q w) :
    ∀ g : V ≃ₗ[ZMod 3] V, ZS.IsIsom 3 Q g → ∃ ω ∈ ggOmega Q,
      g = ω ∨ g = ω * reflect Q u ∨ g = ω * reflect Q w ∨ g = ω * (reflect Q u * reflect Q w) := by
  intro g hg
  have hgO : g ∈ QuadraticMap.orthogonalGroup Q := QuadraticMap.mem_orthogonalGroup_iff.mpr hg
  have hK : ringChar (ZMod 3) ≠ 2 := by
    intro h
    have : CharP (ZMod 3) 2 := ringChar.of_eq h
    exact (by decide : (2 : ZMod 3) ≠ 0) (CharP.cast_eq_zero (ZMod 3) 2)
  obtain ⟨l, -, hlQ, hlprod⟩ := orthogonal_odd_reflection_generation hK hQ hgO
  have hlist : ∀ a ∈ l.map (ggWAutQ_cls Q),
      a = ggWAutQ_cls Q u ∨ a = ggWAutQ_cls Q w := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact hcover v (hlQ v hv)
  have hprod := ggWAutQ_list_prod_mem (ggWAutQ_cls_sq Q u) (ggWAutQ_cls_sq Q w)
    (l.map (ggWAutQ_cls Q)) hlist
  have hofg : Abelianization.of (⟨g, hgO⟩ : QuadraticMap.orthogonalGroup Q) =
      (l.map (ggWAutQ_cls Q)).prod := by
    have hsub : (⟨g, hgO⟩ : QuadraticMap.orthogonalGroup Q) =
        (l.map (fun v => (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
          QuadraticMap.orthogonalGroup Q))).prod := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_list_prod, List.map_map]
      simp only
      exact hlprod
    rw [hsub, map_list_prod, List.map_map]
    rfl
  rw [← hofg] at hprod
  rcases hprod with hp | hp | hp | hp
  · obtain ⟨ω, hω, hgω⟩ := ggWAutQ_coset_of_eq Q hgO (one_mem _) (by
      rw [hp]
      exact (map_one (Abelianization.of : QuadraticMap.orthogonalGroup Q →*
        Abelianization (QuadraticMap.orthogonalGroup Q))).symm)
    exact ⟨ω, hω, Or.inl hgω⟩
  · obtain ⟨ω, hω, hgω⟩ := ggWAutQ_coset_of_eq Q hgO (reflect_mem_orthogonalGroup Q u) hp
    exact ⟨ω, hω, Or.inr (Or.inl hgω)⟩
  · obtain ⟨ω, hω, hgω⟩ := ggWAutQ_coset_of_eq Q hgO (reflect_mem_orthogonalGroup Q w) hp
    exact ⟨ω, hω, Or.inr (Or.inr (Or.inl hgω))⟩
  · have hmul : ggWAutQ_cls Q u * ggWAutQ_cls Q w =
        Abelianization.of (⟨reflect Q u * reflect Q w, mul_mem (reflect_mem_orthogonalGroup Q u)
          (reflect_mem_orthogonalGroup Q w)⟩ : QuadraticMap.orthogonalGroup Q) := by
      rw [ggWAutQ_cls_def Q u, ggWAutQ_cls_def Q w, ← map_mul]
      rfl
    obtain ⟨ω, hω, hgω⟩ := ggWAutQ_coset_of_eq Q hgO
      (mul_mem (reflect_mem_orthogonalGroup Q u) (reflect_mem_orthogonalGroup Q w))
      (by rw [hp, hmul])
    exact ⟨ω, hω, Or.inr (Or.inr (Or.inr hgω))⟩

theorem ggWAut_orth_cosets [Module.Finite (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hn : 1 ≤ Module.finrank (ZMod 3) V) :
    ∃ t₁ t₂ : V ≃ₗ[ZMod 3] V, (IsReflLin t₁ ∧ ZS.IsIsom 3 Q t₁) ∧
      (IsReflLin t₂ ∧ ZS.IsIsom 3 Q t₂) ∧
      ∀ g : V ≃ₗ[ZMod 3] V, ZS.IsIsom 3 Q g → ∃ ω ∈ ggOmega Q,
        g = ω ∨ g = ω * t₁ ∨ g = ω * t₂ ∨ g = ω * (t₁ * t₂) := by
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by norm_num) hn)
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hxrad : x ∈ Q.radical := by
      rw [hQ0]
      refine ⟨rfl, ?_⟩
      ext y
      simp [QuadraticMap.polarBilin, QuadraticMap.polar]
    rw [hQnd.radical_eq_bot, Submodule.mem_bot] at hxrad
    exact hx hxrad
  obtain ⟨u, hu⟩ : ∃ u : V, Q u ≠ 0 := by
    by_contra h
    exact hQ_ne (by ext v; exact not_not.mp (not_exists.mp h v))
  have : Invertible (Q u) := invertibleOfNonzero hu
  have hrefl_u : IsReflLin (reflect Q u) := by
    rw [reflect_eq_reflection]
    exact ggWAutQ_reflection_isReflLin Q u
  have hiso_u : ZS.IsIsom 3 Q (reflect Q u) := by
    rw [reflect_eq_reflection]
    exact ggWAutQ_reflection_isom Q u
  obtain ⟨w, hw, hcover⟩ := ggWAutQ_dichotomy Q hu
  have : Invertible (Q w) := invertibleOfNonzero hw
  have hrefl_w : IsReflLin (reflect Q w) := by
    rw [reflect_eq_reflection]
    exact ggWAutQ_reflection_isReflLin Q w
  have hiso_w : ZS.IsIsom 3 Q (reflect Q w) := by
    rw [reflect_eq_reflection]
    exact ggWAutQ_reflection_isom Q w
  exact ⟨reflect Q u, reflect Q w, ⟨hrefl_u, hiso_u⟩, ⟨hrefl_w, hiso_w⟩,
    ggWAutQ_cosets_of_cover Q hQ hu hw hcover⟩

theorem ggWAut_orth_cosets_of_not_isSquare [Module.Finite (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u w : V}
    (hu : Q u ≠ 0) (hw : Q w ≠ 0) (hns : ¬ IsSquare (Q u * Q w)) :
    ∀ g : V ≃ₗ[ZMod 3] V, ZS.IsIsom 3 Q g → ∃ ω ∈ ggOmega Q,
      g = ω ∨ g = ω * reflect Q u ∨ g = ω * reflect Q w ∨ g = ω * (reflect Q u * reflect Q w) :=
  ggWAutQ_cosets_of_cover Q hQ hu hw (ggWAutQ_cover_of_not_isSquare Q hu hw hns)

end OrthOdd

end CFSG.StandardType

end
