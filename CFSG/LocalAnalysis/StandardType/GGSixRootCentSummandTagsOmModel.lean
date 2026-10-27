module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmBasic
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Card

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

section Decomp

variable (Q P₁ P₂) in
@[expose] def omFix : Subgroup (V ≃ₗ[K] V) :=
  elementaryGroup Q ⊓ fixPtSub K {P₁.e, P₁.f, P₂.e, P₂.f}

theorem mem_omFix {g : V ≃ₗ[K] V} :
    g ∈ omFix Q P₁ P₂ ↔ g ∈ elementaryGroup Q ∧ g P₁.e = P₁.e ∧ g P₁.f = P₁.f ∧
      g P₂.e = P₂.e ∧ g P₂.f = P₂.f := by
  simp only [omFix, mem_inf, mem_fixPtSub, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]

theorem omFix_le_rootLevi {g : V ≃ₗ[K] V} (hg : g ∈ omFix Q P₁ P₂) : g ∈ rootLevi Q P₁ P₂ := by
  obtain ⟨hgE, h1, h2, h3, h4⟩ := mem_omFix.mp hg
  exact mem_rootLevi_of_fix (elementaryGroup_le_orthogonalGroup Q hgE) h1 h2 h3 h4

theorem rootRadical_le_elementaryGroup (h₁₂ : P₁.Orth P₂) :
    rootRadical Q P₁ P₂ ≤ elementaryGroup Q :=
  (rootRadical_le_rootPairSub h₁₂).trans
    (sup_le (rootGroup_le_elementaryGroup Q _) (rootGroup_le_elementaryGroup Q _))

theorem centralizer_inf_elementaryGroup_eq (h₁₂ : P₁.Orth P₂) :
    centralizer {eichler Q P₁.e P₂.e} ⊓ elementaryGroup Q =
      rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ ⊔ omFix Q P₁ P₂ := by
  have hE : ∀ u w : V, eichler Q u w ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  apply le_antisymm
  · rintro g ⟨hgC, hgE⟩
    have hgO := elementaryGroup_le_orthogonalGroup Q hgE
    have hgc := mem_centralizer_singleton_iff.mp hgC
    obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hgc
    have hdet := det_eq_one_of_commute h₁₂ hgO hgc
    obtain ⟨m, hm, hm1, hm2⟩ := exists_word h₁₂ (leviFix (elementaryGroup Q) P₁ P₂)
      (fun t => (eichler_mem_leviFix h₁₂ hE t).1) (fun t => (eichler_mem_leviFix h₁₂ hE t).2)
      (a := polar Q (g P₂.f) P₂.e) (b := -polar Q (g P₁.f) P₂.e) (c := -polar Q (g P₂.f) P₁.e)
      (d := polar Q (g P₁.f) P₁.e) (by linear_combination hdet)
    have hmO := leviFix_mem_orthogonalGroup hm
    have hmE := (mem_leviFix.mp hm).1
    have hg'1 : (m⁻¹ * g) P₁.e = P₁.e := by
      rw [LinearEquiv.mul_apply, h1]
      apply m.injective
      rw [LinearEquiv.apply_inv_apply', hm1]
      module
    have hg'2 : (m⁻¹ * g) P₂.e = P₂.e := by
      rw [LinearEquiv.mul_apply, h2]
      apply m.injective
      rw [LinearEquiv.apply_inv_apply', hm2]
      module
    have hg'O : m⁻¹ * g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem (inv_mem hmO) hgO
    obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ :=
      exists_eichler_mul_apply_f h₁₂ hg'O hg'1 hg'2
    set q := eichler Q P₁.e y₁ * eichler Q P₂.e y₂ with hqdef
    have hq : q ∈ rootRadical Q P₁ P₂ := mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
      (eichler_mem_rootRadical_right h₁₂ hy12 hy22)
    have hqE : q ∈ elementaryGroup Q := mul_mem (hE _ _) (hE _ _)
    have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
      apply q.injective
      rw [LinearEquiv.apply_inv_apply', hv]
    have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
      apply q.injective
      rw [LinearEquiv.apply_inv_apply']
    have hqe1 : q P₁.e = P₁.e := hq.2.1
    have hqe2 : q P₂.e = P₂.e := hq.2.2.1
    have hg'' : q⁻¹ * (m⁻¹ * g) ∈ omFix Q P₁ P₂ := by
      refine mem_omFix.mpr ⟨mul_mem (inv_mem hqE) (mul_mem (inv_mem hmE) hgE), ?_, ?_, ?_, ?_⟩
      · rw [LinearEquiv.mul_apply, hg'1, hqi _ hqe1]
      · rw [LinearEquiv.mul_apply, ← hf1, hqi']
      · rw [LinearEquiv.mul_apply, hg'2, hqi _ hqe2]
      · rw [LinearEquiv.mul_apply, ← hf2, hqi']
    have e : g = m * q * (q⁻¹ * (m⁻¹ * g)) := by group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_right hm)) (mem_sup_left (mem_sup_left hq)))
      (mem_sup_right hg'')
  · refine sup_le (sup_le (fun g hg => ⟨rootRadical_le_centralizer hg,
      rootRadical_le_elementaryGroup h₁₂ hg⟩) fun g hg => ⟨(mem_leviFix.mp hg).2.1.1.2,
      (mem_leviFix.mp hg).1⟩) fun g hg => ?_
    obtain ⟨hgE, h1, -, h3, -⟩ := mem_omFix.mp hg
    exact ⟨mem_centralizer_singleton_iff.mpr
      (commute_of_apply_eq (elementaryGroup_le_orthogonalGroup Q hgE) h1 h3), hgE⟩

theorem le_normalizer_rootRadical (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hHC : H ≤ centralizer {eichler Q P₁.e P₂.e}) :
    H ≤ normalizer (rootRadical Q P₁ P₂ : Set (V ≃ₗ[K] V)) := by
  intro m hm
  have hmc := mem_centralizer_singleton_iff.mp (hHC hm)
  have hmc' := mem_centralizer_singleton_iff.mp (hHC (inv_mem hm))
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_rootRadical h₁₂ (hHO hm) hmc hg, fun hg => ?_⟩
  have := conj_mem_rootRadical h₁₂ (hHO (inv_mem hm)) hmc' hg
  rwa [inv_inv, show m⁻¹ * (m * g * m⁻¹) * m = g by group] at this

theorem leviFix_le_normalizer_rootRadical (h₁₂ : P₁.Orth P₂) :
    leviFix (elementaryGroup Q) P₁ P₂ ≤ normalizer (rootRadical Q P₁ P₂ : Set (V ≃ₗ[K] V)) :=
  le_normalizer_rootRadical h₁₂ (fun _ hg => leviFix_mem_orthogonalGroup hg)
    fun _ hg => (mem_leviFix.mp hg).2.1.1.2

theorem omFix_le_normalizer_rootRadical (h₁₂ : P₁.Orth P₂) :
    omFix Q P₁ P₂ ≤ normalizer (rootRadical Q P₁ P₂ : Set (V ≃ₗ[K] V)) :=
  le_normalizer_rootRadical h₁₂ (fun _ hg => (omFix_le_rootLevi hg).1.1)
    fun _ hg => (omFix_le_rootLevi hg).1.2

theorem leviFix_le_centralizer_omFix (h₁₂ : P₁.Orth P₂) :
    leviFix (elementaryGroup Q) P₁ P₂ ≤ centralizer (omFix Q P₁ P₂ : Set (V ≃ₗ[K] V)) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨-, hgL, hgW⟩ := mem_leviFix.mp hg
  obtain ⟨hhE, h1, h2, h3, h4⟩ := mem_omFix.mp hh
  obtain ⟨g1, g2⟩ := apply_e_eq_coeff h₁₂ (mem_centralizer_singleton_iff.mp hgL.1.2)
  obtain ⟨k1, k2⟩ := apply_e_eq_coeff (orth_flipPair_flipPair h₁₂)
    (mem_centralizer_singleton_iff.mp hgL.2)
  simp only [flipPair_e, flipPair_f] at k1 k2
  refine (commute_of_fixW_of_fix h₁₂ hgW (elementaryGroup_le_orthogonalGroup Q hhE)
    ⟨h1, h2, h3, h4⟩ ⟨?_, ?_, ?_, ?_⟩).symm
  · rw [g1, map_add, map_smul, map_smul, h1, h3]
  · rw [k1, map_add, map_smul, map_smul, h2, h4]
  · rw [g2, map_add, map_smul, map_smul, h1, h3]
  · rw [k2, map_add, map_smul, map_smul, h2, h4]

theorem disjoint_rootRadical_sup (h₁₂ : P₁.Orth P₂) :
    Disjoint (rootRadical Q P₁ P₂) (leviFix (elementaryGroup Q) P₁ P₂ ⊔ omFix Q P₁ P₂) := by
  rw [disjoint_iff, ← le_bot_iff, ← rootRadical_inf_rootLevi h₁₂]
  exact inf_le_inf_left _ (sup_le (fun _ hg => (mem_leviFix.mp hg).2.1) fun _ hg =>
    omFix_le_rootLevi hg)

theorem disjoint_leviFix_omFix (h₁₂ : P₁.Orth P₂) :
    Disjoint (leviFix (elementaryGroup Q) P₁ P₂) (omFix Q P₁ P₂) := by
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  obtain ⟨-, hgL, hgW⟩ := mem_leviFix.mp hg
  obtain ⟨-, h1, -, h3, -⟩ := mem_omFix.mp hg'
  exact eq_one_of_fixW_of_fix_e h₁₂ hgL hgW h1 h3

end Decomp

section Comm

theorem rootRadical_le_of_eichler_mem (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (h1 : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 → eichler Q P₁.e y ∈ H)
    (h2 : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 → eichler Q P₂.e y ∈ H) :
    rootRadical Q P₁ P₂ ≤ H := by
  intro g hg
  have hgR := hg
  obtain ⟨hgO, hg1, hg2, -⟩ := hg
  obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ := exists_eichler_mul_apply_f h₁₂ hgO hg1 hg2
  set q := eichler Q P₁.e y₁ * eichler Q P₂.e y₂ with hqdef
  have hqR : q ∈ rootRadical Q P₁ P₂ := mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
    (eichler_mem_rootRadical_right h₁₂ hy12 hy22)
  have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply', hv]
  have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply']
  have hM : q⁻¹ * g ∈ rootLevi Q P₁ P₂ := by
    refine mem_rootLevi_of_fix (mul_mem (inv_mem hqR.1) hgO) ?_ ?_ ?_ ?_
    · rw [LinearEquiv.mul_apply, hg1, hqi _ hqR.2.1]
    · rw [LinearEquiv.mul_apply, ← hf1, hqi']
    · rw [LinearEquiv.mul_apply, hg2, hqi _ hqR.2.2.1]
    · rw [LinearEquiv.mul_apply, ← hf2, hqi']
  have hq1 : q⁻¹ * g ∈ rootRadical Q P₁ P₂ ⊓ rootLevi Q P₁ P₂ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hqR) hgR, hM⟩
  rw [rootRadical_inf_rootLevi h₁₂, mem_bot] at hq1
  have hgq : g = q := by
    rw [← mul_inv_cancel_left q g, hq1, mul_one]
  rw [hgq]
  exact mul_mem (h1 _ hy11 hy21) (h2 _ hy12 hy22)

theorem inW_comm {x : V} : InW P₁ P₂ x ↔ InW P₂ P₁ x :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨c, d, a, b⟩, fun ⟨a, b, c, d⟩ => ⟨c, d, a, b⟩⟩

theorem eichler_mem_of_pieces (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hW : ∀ w, InW P₁ P₂ w → eichler Q P₁.e w ∈ H) (hc : ∀ c : K, eichler Q P₁.e (c • P₂.e) ∈ H)
    {y : V} (hy1 : polar Q P₁.e y = 0) (hy2 : polar Q P₂.e y = 0) : eichler Q P₁.e y ∈ H := by
  set w := y - polar Q y P₁.f • P₁.e - polar Q y P₂.f • P₂.e with hw
  have h21 := h₁₂.symm
  have hwW : InW P₁ P₂ w := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hw, polar_sub_right, polar_smul_right_eq, P₁.polar_ee, P₁.polar_fe, P₂.polar_ee,
        P₂.polar_fe, h₁₂.ee, h₁₂.fe, h21.ee, h21.fe, hy1, hy2]
    · ring
    · rw [polar_comm Q P₁.f y]; ring
    · ring
    · rw [polar_comm Q P₂.f y]; ring
  have he : y = (w + polar Q y P₂.f • P₂.e) + polar Q y P₁.f • P₁.e := by rw [hw]; abel
  have hw1 : polar Q P₁.e w = 0 := hwW.1
  have hc1 : polar Q P₁.e (polar Q y P₂.f • P₂.e) = 0 := by
    rw [polar_smul_right_eq, h₁₂.ee, mul_zero]
  rw [he, eichler_add_smul_self P₁.Q_e, ← eichler_mul hw1 hc1]
  exact mul_mem (hW w hwW) (hc _)

theorem eichler_smul_e_mem_commutator' (h₁₂ : P₁.Orth P₂) {P₃ : HypPair Q} (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {H : Subgroup (V ≃ₗ[K] V)}
    (hR : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ H ∧ eichler Q P₂.e y ∈ H) (c : K) :
    eichler Q P₁.e (c • P₂.e) ∈ ⁅H, H⁆ := by
  have hw : polar Q P₂.e (-c • P₃.f) = 0 := by rw [polar_smul_right_eq, h₂₃.ef, mul_zero]
  have hw1 : polar Q P₁.e (-c • P₃.f) = 0 := by rw [polar_smul_right_eq, h₁₃.ef, mul_zero]
  have hg := eichler_mem_orthogonalGroup Q P₂.e (-c • P₃.f)
  have hgu : eichler Q P₂.e (-c • P₃.f) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero h₁₂.ee hw1
  have h := commutatorElement_eichler hg hgu h₁₃.ee
  have hv : eichler Q P₂.e (-c • P₃.f) P₃.e - P₃.e = c • P₂.e := by
    rw [eichler_apply P₂.Q_e hw, polar_comm Q P₃.e P₂.e, h₂₃.ee, polar_smul_right_eq,
      P₃.polar_ef]
    module
  rw [hv] at h
  rw [← h]
  exact commutator_mem_commutator (hR _ hw1 hw).2 (hR _ h₁₃.ee h₂₃.ee).1

theorem eichler_inW_mem_commutator_levi (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hR : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ H ∧ eichler Q P₂.e y ∈ H) (hx : eichler Q P₁.e P₂.f ∈ H)
    (hc : ∀ c : K, eichler Q P₁.e (c • P₂.e) ∈ ⁅H, H⁆) {w : V} (hw : InW P₁ P₂ w) :
    eichler Q P₁.e w ∈ ⁅H, H⁆ := by
  obtain ⟨hw₁, -, hw₂, hw₂'⟩ := hw
  have hg := eichler_mem_orthogonalGroup Q P₂.e w
  have hgu : eichler Q P₂.e w P₁.e = P₁.e := eichler_apply_of_polar_eq_zero h₁₂.ee hw₁
  have h := commutatorElement_eichler hg hgu h₁₂.ef
  have hv : eichler Q P₂.e w P₂.f - P₂.f = w - Q w • P₂.e := by
    rw [eichler_apply P₂.Q_e hw₂, hw₂', P₂.polar_fe]
    module
  rw [hv] at h
  have h1 : eichler Q P₁.e (w - Q w • P₂.e) ∈ ⁅H, H⁆ := by
    rw [← h]
    exact commutator_mem_commutator (hR w hw₁ hw₂).2 hx
  have hp1 : polar Q P₁.e (w - Q w • P₂.e) = 0 := by
    rw [polar_sub_right, polar_smul_right_eq, hw₁, h₁₂.ee, mul_zero, sub_zero]
  have hp2 : polar Q P₁.e (Q w • P₂.e) = 0 := by rw [polar_smul_right_eq, h₁₂.ee, mul_zero]
  have e : w = (w - Q w • P₂.e) + Q w • P₂.e := by abel
  rw [e, ← eichler_mul hp1 hp2]
  exact mul_mem h1 (hc _)


theorem inW_smul {x : V} (hx : InW P₁ P₂ x) (c : K) : InW P₁ P₂ (c • x) := by
  obtain ⟨a1, a2, a3, a4⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [polar_smul_right_eq, a1, a2, a3, a4, mul_zero]

theorem eichler_inW_mem_commutator_fix {P₃ : HypPair Q} (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    {x x' : V} (hx : InW P₁ P₂ x) (hx' : InW P₁ P₂ x')
    (hx3 : polar Q P₃.e x = 0 ∧ polar Q P₃.f x = 0)
    (hx'3 : polar Q P₃.e x' = 0 ∧ polar Q P₃.f x' = 0) (hxx' : polar Q x x' = 1)
    {H : Subgroup (V ≃ₗ[K] V)}
    (hR : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ H ∧ eichler Q P₂.e y ∈ H)
    (hL : ∀ u v, InW P₁ P₂ u → InW P₁ P₂ v → eichler Q u v ∈ H) {w : V} (hw : InW P₁ P₂ w) :
    eichler Q P₁.e w ∈ ⁅H, H⁆ := by
  obtain ⟨he3, hf3⟩ := inW_of_orth h₁₃.symm h₂₃.symm
  have hx'1 : polar Q P₁.e x' = 0 := hx'.1
  have hx'2 : polar Q P₂.e x' = 0 := hx'.2.2.1
  have hx'x : polar Q x' x = 1 := by rw [polar_comm]; exact hxx'
  have key : ∀ u : V, Q u = 0 → InW P₁ P₂ u → polar Q u x = 0 → polar Q x' u = 0 →
      ∀ c : K, eichler Q P₁.e (c • u) ∈ ⁅H, H⁆ := by
    intro u hu huW hux hx'u c
    have hp : polar Q u (-c • x) = 0 := by rw [polar_smul_right_eq, hux, mul_zero]
    have hg := eichler_mem_orthogonalGroup Q u (-c • x)
    have hgu : eichler Q u (-c • x) P₁.e = P₁.e :=
      eichler_apply_of_polar_eq_zero huW.1 (by rw [polar_smul_right_eq, hx.1, mul_zero])
    have h := commutatorElement_eichler hg hgu hx'1
    have hv : eichler Q u (-c • x) x' - x' = c • u := by
      rw [eichler_apply hu hp, hx'u, polar_smul_right_eq, hx'x]
      module
    rw [hv] at h
    rw [← h]
    exact commutator_mem_commutator (hL _ _ huW (inW_smul hx _)) (hR x' hx'1 hx'2).1
  have hE3 : ∀ c : K, eichler Q P₁.e (c • P₃.e) ∈ ⁅H, H⁆ :=
    key P₃.e P₃.Q_e he3 hx3.1 (by rw [polar_comm]; exact hx'3.1)
  have hF3 : ∀ c : K, eichler Q P₁.e (c • P₃.f) ∈ ⁅H, H⁆ :=
    key P₃.f P₃.Q_f hf3 hx3.2 (by rw [polar_comm]; exact hx'3.2)
  have hW3 : ∀ w' : V, InW P₁ P₂ w' → polar Q P₃.e w' = 0 → polar Q P₃.f w' = 0 →
      eichler Q P₁.e w' ∈ ⁅H, H⁆ := by
    intro w' hw' h3e h3f
    have hg := eichler_mem_orthogonalGroup Q P₃.e w'
    have hgu : eichler Q P₃.e w' P₁.e = P₁.e :=
      eichler_apply_of_polar_eq_zero he3.1 hw'.1
    have h1f3 : polar Q P₁.e P₃.f = 0 := h₁₃.ef
    have h := commutatorElement_eichler hg hgu h1f3
    have hv : eichler Q P₃.e w' P₃.f - P₃.f = w' - Q w' • P₃.e := by
      rw [eichler_apply P₃.Q_e h3e, P₃.polar_fe, h3f]
      module
    rw [hv] at h
    have h1 : eichler Q P₁.e (w' - Q w' • P₃.e) ∈ ⁅H, H⁆ := by
      rw [← h]
      exact commutator_mem_commutator (hL _ _ he3 hw') (hR _ h1f3 h₂₃.ef).1
    have hp1 : polar Q P₁.e (w' - Q w' • P₃.e) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hw'.1, h₁₃.ee, mul_zero, sub_zero]
    have hp2 : polar Q P₁.e (Q w' • P₃.e) = 0 := by rw [polar_smul_right_eq, h₁₃.ee, mul_zero]
    have e : w' = (w' - Q w' • P₃.e) + Q w' • P₃.e := by abel
    rw [e, ← eichler_mul hp1 hp2]
    exact mul_mem h1 (hE3 _)
  set w' := w - polar Q w P₃.f • P₃.e - polar Q w P₃.e • P₃.f with hw'
  have hw'W : InW P₁ P₂ w' := by
    obtain ⟨a1, a2, a3, a4⟩ := hw
    obtain ⟨b1, b2, b3, b4⟩ := he3
    obtain ⟨c1, c2, c3, c4⟩ := hf3
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hw', polar_sub_right, polar_smul_right_eq, a1, a2, a3, a4, b1, b2, b3, b4, c1,
        c2, c3, c4, mul_zero, sub_zero]
  have h3e : polar Q P₃.e w' = 0 := by
    rw [hw', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      P₃.polar_ee, P₃.polar_ef, polar_comm Q P₃.e w]
    ring
  have h3f : polar Q P₃.f w' = 0 := by
    rw [hw', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      P₃.polar_fe, P₃.polar_ff, polar_comm Q P₃.f w]
    ring
  have e : w = polar Q w P₃.f • P₃.e + (polar Q w P₃.e • P₃.f + w') := by rw [hw']; abel
  have hpa : polar Q P₁.e (polar Q w P₃.f • P₃.e) = 0 := by
    rw [polar_smul_right_eq, h₁₃.ee, mul_zero]
  have hpb : polar Q P₁.e (polar Q w P₃.e • P₃.f) = 0 := by
    rw [polar_smul_right_eq, h₁₃.ef, mul_zero]
  have hpc : polar Q P₁.e w' = 0 := hw'W.1
  rw [e, ← eichler_mul hpa (by rw [polar_add_right, hpb, hpc, add_zero]), ← eichler_mul hpb hpc]
  exact mul_mem (hE3 _) (mul_mem (hF3 _) (hW3 w' hw'W h3e h3f))

theorem eichler_mem_rootRadical_sup (h₁₂ : P₁.Orth P₂) (X : Subgroup (V ≃ₗ[K] V)) :
    ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ rootRadical Q P₁ P₂ ⊔ X ∧ eichler Q P₂.e y ∈ rootRadical Q P₁ P₂ ⊔ X :=
  fun _ h1 h2 => ⟨mem_sup_left (eichler_mem_rootRadical_left h₁₂ h1 h2),
    mem_sup_left (eichler_mem_rootRadical_right h₁₂ h1 h2)⟩

theorem rootRadical_le_commutator_omFix (h₁₂ : P₁.Orth P₂) {P₃ : HypPair Q} (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {x x' : V} (hx : InW P₁ P₂ x) (hx' : InW P₁ P₂ x')
    (hx3 : polar Q P₃.e x = 0 ∧ polar Q P₃.f x = 0)
    (hx'3 : polar Q P₃.e x' = 0 ∧ polar Q P₃.f x' = 0) (hxx' : polar Q x x' = 1) :
    rootRadical Q P₁ P₂ ≤
      ⁅rootRadical Q P₁ P₂ ⊔ omFix Q P₁ P₂, rootRadical Q P₁ P₂ ⊔ omFix Q P₁ P₂⁆ := by
  have hR := eichler_mem_rootRadical_sup h₁₂ (omFix Q P₁ P₂)
  have hL : ∀ u v, InW P₁ P₂ u → InW P₁ P₂ v →
      eichler Q u v ∈ rootRadical Q P₁ P₂ ⊔ omFix Q P₁ P₂ := fun u v hu hv =>
    mem_sup_right (mem_omFix.mpr ⟨eichler_mem_elementaryGroup Q u v,
      eichler_apply_of_polar_eq_zero hu.1 hv.1, eichler_apply_of_polar_eq_zero hu.2.1 hv.2.1,
      eichler_apply_of_polar_eq_zero hu.2.2.1 hv.2.2.1,
      eichler_apply_of_polar_eq_zero hu.2.2.2 hv.2.2.2⟩)
  have hR' : ∀ y, polar Q P₂.e y = 0 → polar Q P₁.e y = 0 →
      eichler Q P₂.e y ∈ rootRadical Q P₁ P₂ ⊔ omFix Q P₁ P₂ ∧
        eichler Q P₁.e y ∈ rootRadical Q P₁ P₂ ⊔ omFix Q P₁ P₂ :=
    fun y h2 h1 => (hR y h1 h2).symm
  refine rootRadical_le_of_eichler_mem h₁₂ (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
  · exact eichler_mem_of_pieces h₁₂ (fun w hw => eichler_inW_mem_commutator_fix h₁₃ h₂₃ hx hx'
      hx3 hx'3 hxx' hR hL hw) (eichler_smul_e_mem_commutator' h₁₂ h₁₃ h₂₃ hR) h1 h2
  · exact eichler_mem_of_pieces h₁₂.symm (fun w hw => eichler_inW_mem_commutator_fix h₂₃ h₁₃
      (inW_comm.mp hx) (inW_comm.mp hx') hx3 hx'3 hxx' hR'
      (fun u v hu hv => hL u v (inW_comm.mpr hu) (inW_comm.mpr hv)) hw)
      (eichler_smul_e_mem_commutator' h₁₂.symm h₂₃ h₁₃ hR') h2 h1

theorem rootRadical_le_commutator_leviFix (h₁₂ : P₁.Orth P₂) {P₃ : HypPair Q}
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    rootRadical Q P₁ P₂ ≤ ⁅rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂,
      rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂⁆ := by
  have hE : ∀ u w : V, eichler Q u w ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have hR := eichler_mem_rootRadical_sup h₁₂ (leviFix (elementaryGroup Q) P₁ P₂)
  have hR' : ∀ y, polar Q P₂.e y = 0 → polar Q P₁.e y = 0 →
      eichler Q P₂.e y ∈ rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ ∧
        eichler Q P₁.e y ∈ rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ :=
    fun y h2 h1 => (hR y h1 h2).symm
  have hx : eichler Q P₁.e P₂.f ∈ rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ := by
    have := (eichler_mem_leviFix h₁₂ hE 1).1
    rw [one_smul] at this
    exact mem_sup_right this
  have hy : eichler Q P₂.e P₁.f ∈ rootRadical Q P₁ P₂ ⊔ leviFix (elementaryGroup Q) P₁ P₂ := by
    have := (eichler_mem_leviFix h₁₂ hE 1).2
    rw [one_smul] at this
    exact mem_sup_right this
  refine rootRadical_le_of_eichler_mem h₁₂ (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
  · exact eichler_mem_of_pieces h₁₂ (fun w hw => eichler_inW_mem_commutator_levi h₁₂ hR hx
      (eichler_smul_e_mem_commutator' h₁₂ h₁₃ h₂₃ hR) hw)
      (eichler_smul_e_mem_commutator' h₁₂ h₁₃ h₂₃ hR) h1 h2
  · exact eichler_mem_of_pieces h₁₂.symm (fun w hw => eichler_inW_mem_commutator_levi h₁₂.symm
      hR' hy (eichler_smul_e_mem_commutator' h₁₂.symm h₂₃ h₁₃ hR') hw)
      (eichler_smul_e_mem_commutator' h₁₂.symm h₂₃ h₁₃ hR') h2 h1

end Comm

end RCSTOm

end CFSG.StandardType
