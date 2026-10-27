module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L71

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T73Inf

section Generic

variable {G : Type*} [Group G]

theorem zOf_inf_centralizer_le_zOf_inf {A S F : Subgroup G} (hFA : F ≤ A) :
    zOf S ⊓ Subgroup.centralizer (A : Set G) ≤ zOf (S ⊓ Subgroup.centralizer (F : Set G)) := by
  intro v hv
  refine mem_zOf_iff.mpr ⟨Subgroup.mem_inf.mpr ⟨zOf_le S hv.1,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hFA) hv.2⟩, fun w hw => ?_⟩
  exact (mem_zOf_iff.mp hv.1).2 w (Subgroup.mem_inf.mp hw).1

end Generic

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem exists_line_inf_eq_bot (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) :
    ∃ K' ∈ signalizerFunctorEk p 1 A, B ⊓ K' = ⊥ ∧ B ⊔ K' = A := by
  have hnle : ¬ A ≤ B := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [h.card, hB.2] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  obtain ⟨k, hkA, hkB⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hk1 : k ≠ 1 := fun h1 => hkB (h1 ▸ one_mem B)
  have hK' := h.zpowers_mem_E1 hkA hk1
  have hdisj : B ⊓ Subgroup.zpowers k = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers hkA hk1)
      (fun hle => hkB (hle (Subgroup.mem_zpowers k)))
  refine ⟨Subgroup.zpowers k, hK', hdisj, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (sup_le hB.1 hK'.1) ?_
  rw [card_sup_of_le_elemAbelian h.elemAbelian hB.1 hK'.1 hdisj, hB.2, hK'.2, h.card]
  rw [← pow_add]

theorem le_normalizer_zOf_inf_centralizer (h : Counterexample p A θ) (hS : IsSr p A θ r S)
    {X : Subgroup G} (hXA : X ≤ A) :
    A ≤ Subgroup.normalizer (zOf (S ⊓ Subgroup.centralizer (X : Set G)) : Set G) := by
  have := h.elemAbelian.1
  intro a ha
  apply mem_normalizer_zOf
  have hC : a ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Near.Lemma212.map_conj_centralizer_of_commute X fun b hb =>
      setLike_mul_comm (hXA hb) ha
  exact Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.mpr ⟨Counterexample.normalizes_of_isSr hS ha, hC⟩)

theorem le_normalizer_inf_zOf (h : Counterexample p A θ) (hS : IsSr p A θ r S) {X Y : Subgroup G}
    (hXA : X ≤ A) (hYA : Y ≤ A) :
    A ≤ Subgroup.normalizer (zOf (S ⊓ Subgroup.centralizer (X : Set G)) ⊓
      zOf (S ⊓ Subgroup.centralizer (Y : Set G)) : Subgroup G) := fun _ ha =>
  Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
    ⟨le_normalizer_zOf_inf_centralizer h hS hXA ha, le_normalizer_zOf_inf_centralizer h hS hYA ha⟩)

theorem zOf_inf_centralizer_le_thetaOf (h : Counterexample p A θ) (hS : IsSr p A θ r S)
    {B : Subgroup G} (hBA : B ≤ A) (hB1 : B ≠ ⊥) :
    zOf S ⊓ Subgroup.centralizer (A : Set G) ≤ thetaOf θ B := fun _ hv =>
  Counterexample.inf_centralizer_le_thetaOf_of_isSr h hS hBA hB1 (Subgroup.mem_inf.mpr
    ⟨zOf_le S hv.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA) hv.2⟩)

theorem inf_zOf_inf_centralizer_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {F K' : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) (hK' : K' ∈ signalizerFunctorEk p 1 A)
    (hK'F : (E ⊔ F) ⊓ K' = ⊥) :
    zOf (S ⊓ Subgroup.centralizer (E : Set G)) ⊓ zOf (S ⊓ Subgroup.centralizer (F : Set G)) ⊓
        Subgroup.centralizer (K' : Set G) ≤ zOf S ⊓ Subgroup.centralizer (A : Set G) := by
  have hπ : E ⊔ F ∈ signalizerFunctorEk p 2 A := h.sup_mem_E2_of_ne hB.mem hF (Ne.symm hFE)
  have hFK' : F ≠ K' := by
    rintro rfl
    have h1 : F ≤ (E ⊔ F) ⊓ F := le_inf le_sup_right le_rfl
    rw [hK'F] at h1
    exact h.ne_bot_of_mem_E1 hF (le_bot_iff.mp h1)
  have hBpl : F ⊔ K' ∈ signalizerFunctorEk p 2 A := h.sup_mem_E2_of_ne hF hK' hFK'
  have hEB : ¬ E ≤ F ⊔ K' := by
    intro hle
    have hle' : E ⊔ F ≤ F ⊔ K' := sup_le hle le_sup_left
    have heq : E ⊔ F = F ⊔ K' := Subgroup.eq_of_le_of_card_ge hle' (by rw [hπ.2, hBpl.2])
    have h1 : K' ≤ (E ⊔ F) ⊓ K' := le_inf (heq ▸ le_sup_right) le_rfl
    rw [hK'F] at h1
    exact h.ne_bot_of_mem_E1 hK' (le_bot_iff.mp h1)
  have hEA : E ⊔ (F ⊔ K') = A := by
    rw [← sup_assoc]
    refine Subgroup.eq_of_le_of_card_ge (sup_le hπ.1 hK'.1) ?_
    rw [card_sup_of_le_elemAbelian h.elemAbelian hπ.1 hK'.1 hK'F, hπ.2, hK'.2, h.card,
      ← pow_add]
  have hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ ¬ E ≤ F ⊔ K' :=
    Or.inr ⟨E, K, hB, hEB⟩
  intro x hx
  obtain ⟨⟨hxE, hxF⟩, hxK'⟩ := hx
  obtain ⟨a, haF, ha1⟩ := h.exists_ne_one_of_mem_E1 hF
  have hFa : F = Subgroup.zpowers a := h.line_eq_zpowers hF haF ha1
  have hCF : Subgroup.centralizer (F : Set G) = Subgroup.centralizer {a} := by
    rw [hFa, centralizer_zpowers_eq_singleton]
  have hxZF : x ∈ zOf (S ⊓ Subgroup.centralizer {a}) := hCF ▸ hxF
  have hxCB : x ∈ Subgroup.centralizer ((F ⊔ K' : Subgroup G) : Set G) := by
    rw [centralizer_sup]
    exact ⟨(zOf_le _ hxF).2, hxK'⟩
  have h1 := Counterexample.lemma_7_1_a h hr hS hBpl hT (Subgroup.mem_sup_left haF) ha1
  have hx2 : x ∈ zOf (S ⊓ Subgroup.centralizer ((F ⊔ K' : Subgroup G) : Set G)) :=
    h1 ▸ Subgroup.mem_inf.mpr ⟨hxZF, hxCB⟩
  rw [Counterexample.lemma_7_1_b h hr hS hBpl hT] at hx2
  refine Subgroup.mem_inf.mpr ⟨hx2.1, ?_⟩
  rw [← hEA, centralizer_sup]
  exact Subgroup.mem_inf.mpr ⟨(zOf_le _ hxE).2, hx2.2⟩

end T73Inf

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
