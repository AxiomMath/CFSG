module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenCases
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenConfig
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenScalars
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenThreeMinus
import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenTrans
import CFSG.LocalAnalysis.StandardType.ZS.OrthClass
import CFSG.ClassicalGroups.Orthogonal.Represents
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_map_add_perp {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {a : U}
    (ha : a ∈ P.perp) {c : ZMod p} (hQa : Q a = c) :
    Q (a + P.e) = c ∧ Q (a + P.f) = c := by
  obtain ⟨hae, haf⟩ := HypPair.mem_perp.mp ha
  constructor
  · rw [QuadraticMap.map_add Q, hQa, P.Q_e, polar_comm Q a P.e, hae]; ring
  · rw [QuadraticMap.map_add Q, hQa, P.Q_f, polar_comm Q a P.f, haf]; ring

private lemma ocg_exists_of_set {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    {S : Set (U ≃ₗ[ZMod p] U)} (s : Finset (U ≃ₗ[ZMod p] U))
    (hs : (s : Set (U ≃ₗ[ZMod p] U)) = S)
    (hcard : s.card ≤ Module.finrank (ZMod p) U) (hmem : ∀ x ∈ s, x ∈ ClassRefl p Q c)
    (hgen : Subgroup.closure (ClassRefl p Q c) = Subgroup.closure S) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) :=
  ⟨s, hcard, hmem, by rw [hgen, hs]⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_isotropic [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) {a : U}
    (ha : a ∈ P.perp) (hQa : Q a = c) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  classical
  have hgen := closure_classRefl_eq_of_isotropic hp h3 hQ hc P ha hQa
  refine ocg_exists_of_set (S := {reflect Q (a + P.e), reflect Q a, reflect Q (a + P.f)})
    {reflect Q (a + P.e), reflect Q a, reflect Q (a + P.f)} ?_ ?_ ?_ hgen
  · simp
  · rw [h3]; exact Finset.card_le_three
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (mem_classRefl_iff hp hQ hc _).mpr ⟨a + P.e, (ocg_map_add_perp P ha hQa).1, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr ⟨a, hQa, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr ⟨a + P.f, (ocg_map_add_perp P ha hQa).2, rfl⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_anisotropic [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (P : HypPair Q) {x : U} (hx : x ∈ P.perp)
    (hsq : ¬ IsSquare (c / Q x)) {lam t : ZMod p} (hlam : lam ≠ 0) (hlam4 : lam ^ 4 ≠ 1)
    (hκ : -(c / Q x) * (1 - lam ^ 2) = t ^ 2) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  classical
  have hQx : Q x ≠ 0 := by
    intro hx0
    exact hsq (by rw [hx0, div_zero]; exact ⟨0, by ring⟩)
  have hc : c ≠ 0 := by
    intro hc0
    exact hsq (by rw [hc0, zero_div]; exact ⟨0, by ring⟩)
  have hlam1 : lam ^ 2 ≠ 1 := by
    intro h
    exact hlam4 (by rw [show lam ^ 4 = (lam ^ 2) ^ 2 by ring, h]; norm_num)
  have hgen := closure_classRefl_eq_of_anisotropic h3 hQ P hx hsq hlam hlam4 hκ
  have hnorm := threeMinus_map_eq P hx hQx hlam hlam1 hκ
  refine ocg_exists_of_set (S := {reflect Q (lam • P.e + (c / lam) • P.f),
      reflect Q (P.e + c • P.f),
      reflect Q (P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x)})
    {reflect Q (lam • P.e + (c / lam) • P.f), reflect Q (P.e + c • P.f),
      reflect Q (P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x)} ?_ ?_ ?_ hgen
  · simp
  · rw [h3]; exact Finset.card_le_three
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact (mem_classRefl_iff hp hQ hc _).mpr
        ⟨lam • P.e + (c / lam) • P.f, hnorm.1, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr ⟨P.e + c • P.f, hnorm.2.1, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr
        ⟨P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x, hnorm.2.2, rfl⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_four_le [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (P : HypPair Q) (m : ℕ) (hfin : Module.finrank (ZMod p) U = m + 3)
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (a : Fin (m + 1) → U)
    (ha : ∀ i, a i ∈ P.perp ∧ Q (a i) = c)
    (hpol : ∀ i, i ≠ 0 → polar Q (a 0) (a i) ≠ 0)
    (hspan : P.perp ≤ Submodule.span (ZMod p) (Set.range a)) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  classical
  have hgen := closure_classRefl_eq_of_four_le hp h4 hQ hc P a ha hpol hspan
  refine ocg_exists_of_set
    (S := insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
      (Set.range fun i => reflect Q (a i))))
    (insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
      (Finset.univ.image fun i => reflect Q (a i)))) ?_ ?_ ?_ hgen
  · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · rw [hfin]
    calc (insert (reflect Q (a 0 + P.e)) (insert (reflect Q (a 0 + P.f))
          (Finset.univ.image fun i => reflect Q (a i)))).card
        ≤ (insert (reflect Q (a 0 + P.f))
            (Finset.univ.image fun i => reflect Q (a i))).card + 1 := Finset.card_insert_le _ _
      _ ≤ ((Finset.univ.image fun i => reflect Q (a i)).card + 1) + 1 := by
            gcongr; exact Finset.card_insert_le _ _
      _ ≤ ((Finset.univ : Finset (Fin (m + 1))).card + 1) + 1 := by
            gcongr; exact Finset.card_image_le
      _ = m + 3 := by rw [Finset.card_univ, Fintype.card_fin]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨i, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr
        ⟨a 0 + P.e, (ocg_map_add_perp P (ha 0).1 (ha 0).2).1, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr
        ⟨a 0 + P.f, (ocg_map_add_perp P (ha 0).1 (ha 0).2).2, rfl⟩
    · exact (mem_classRefl_iff hp hQ hc _).mpr ⟨a i, (ha i).2, rfl⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_dim_three [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q) {a b : U}
    (hQa : Q a = c) (hQb : Q b = c)
    (hxy : 3 < orderOf (reflect Q a * reflect Q b)) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  by_cases hcaseA : ∃ a' : U, Q a' = c ∧ ∃ u : U, u ≠ 0 ∧ Q u = 0 ∧ polar Q a' u = 0
  · obtain ⟨a', hQa', u, hu0, huQ, hua'⟩ := hcaseA
    have hQa'ne : Q a' ≠ 0 := by rw [hQa']; exact hc
    obtain ⟨P', -, ha'perp⟩ := exists_hypPair_mem_perp h2 hQ hQa'ne hu0 huQ hua'
    exact ocg_isotropic hp h3 hQ hc P' ha'perp hQa'
  · have hperp1 : Module.finrank (ZMod p) P.perp = 1 := by
      have := CFSG.ClassicalInvolution.ModelFacts.finrank_hypPair_perp hQ P
      omega
    have hperp_ne : P.perp ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hperp1
      omega
    obtain ⟨xx, hxxperp, hQxx⟩ :=
      PolarNondegOn.exists_map_ne_zero (HypPair.polarNondegOn_perp hQ P) hperp_ne
    have hsq : ¬ IsSquare (c / Q xx) := by
      rintro ⟨s, hs⟩
      refine hcaseA ⟨s • xx, ?_, P.e, P.e_ne_zero, P.Q_e, ?_⟩
      · rw [map_smul_eq_sq, pow_two, ← hs]
        exact div_mul_cancel₀ c hQxx
      · rw [polar_smul_left_eq, polar_comm Q xx P.e, (HypPair.mem_perp.mp hxxperp).1, mul_zero]
    by_cases hp5 : p = 5
    · exfalso
      have haniso : ∀ u, polar Q a u = 0 → Q u = 0 → u = 0 := by
        intro u hu hQu
        by_contra hu0
        exact hcaseA ⟨a, hQa, u, hu0, hQu, hu⟩
      exact absurd hxy (not_lt.mpr
        (orderOf_reflect_mul_le_three_of_anisotropic hp5 hQa hQb haniso))
    · have hκ : -(c / Q xx) ≠ 0 := by
        rw [neg_ne_zero]
        exact div_ne_zero hc hQxx
      obtain ⟨lam, t, hlam, hlam4, -, hκeq⟩ := exists_threeMinus_scalars hp hp3 hp5 hκ
      exact ocg_anisotropic hp h3 hQ P hxxperp hsq hlam hlam4 hκeq

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_dim_four [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    (h4 : Module.finrank (ZMod p) U = 4) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) (P : HypPair Q)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ Subgroup.closure (ClassRefl p Q c)) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  classical
  rcases exists_conic_config_or_orthogonal hp hp3 h4 hQ hc P with
    ⟨a', ha', hpol', hspan'⟩ | ⟨b', horth', hb', hspanb'⟩
  · have hpol2 : ∀ i : Fin 2, i ≠ 0 → polar Q (a' 0) (a' i) ≠ 0 := by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · exact hpol'
    have h4le : 4 ≤ Module.finrank (ZMod p) U := by omega
    have hfin4 : Module.finrank (ZMod p) U = 1 + 3 := by rw [h4]
    exact ocg_four_le hp hQ hc P 1 hfin4 h4le a' ha' hpol2 hspan'
  · exact absurd (neg_mem_closure_classRefl_of_orthogonal hp hQ hc b' horth' hb' hspanb') hneg

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem exists_classRefl_gen (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∉ Subgroup.closure (ClassRefl p Q c))
    (hd : ∃ x ∈ Subgroup.closure (ClassRefl p Q c), ∃ y ∈ Subgroup.closure (ClassRefl p Q c),
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ Module.finrank (ZMod p) U ∧
      (∀ x ∈ s, x ∈ ClassRefl p Q c) ∧
        Subgroup.closure (ClassRefl p Q c) = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U)) := by
  classical
  obtain ⟨x, hxR, y, hyR, hxrefl, hyrefl, hxy⟩ := hd
  have hp3 : p ≠ 3 := by
    intro hp3
    exact absurd hxy (not_lt.mpr
      (orderOf_mul_le_three_of_classRefl_three hp3 hQ hc hxR hyR hxrefl hyrefl))
  have hxClass := mem_classRefl_of_isRefl_mem_closure hp hQ hc hxR hxrefl
  obtain ⟨a, hQa, rfl⟩ := (mem_classRefl_iff hp hQ hc x).mp hxClass
  have hyClass := mem_classRefl_of_isRefl_mem_closure hp hQ hc hyR hyrefl
  obtain ⟨b, hQb, rfl⟩ := (mem_classRefl_iff hp hQ hc y).mp hyClass
  have hp_odd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨e, he0, heQ⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isotropic_of_finrank_ge_three hp_odd Q hQ h3
  obtain ⟨P, -⟩ := exists_hypPair hQ heQ he0
  by_cases h3fin : Module.finrank (ZMod p) U = 3
  · exact ocg_dim_three hp hp3 h3fin hQ hc P hQa hQb hxy
  · by_cases h4fin : Module.finrank (ZMod p) U = 4
    · exact ocg_dim_four hp hp3 h4fin hQ hc P hneg
    · obtain ⟨m, hm⟩ : ∃ m, Module.finrank (ZMod p) U = m + 3 :=
        ⟨Module.finrank (ZMod p) U - 3, by omega⟩
      have hm2 : 2 ≤ m := by omega
      have h4 : 4 ≤ Module.finrank (ZMod p) U := by omega
      obtain ⟨a', ha', hpol', hspan'⟩ := exists_star_config hp hp3 hm hm2 hQ hc P
      exact ocg_four_le hp hQ hc P m hm h4 a' ha' hpol' hspan'

end CFSG.StandardType.ZS
