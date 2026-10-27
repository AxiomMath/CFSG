module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L71

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem theorem_7_2
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    (hA : TypeA p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    zOf (S ⊓ Subgroup.centralizer {a}) = zOf S ⊓ Subgroup.centralizer {a} := by
  have hge : zOf S ⊓ Subgroup.centralizer {a} ≤ zOf (S ⊓ Subgroup.centralizer {a}) :=
    fun x hx => mem_zOf_iff.mpr ⟨⟨zOf_le S hx.1, hx.2⟩, fun w hw =>
      (mem_zOf_iff.mp hx.1).2 w hw.1⟩
  refine le_antisymm ?_ hge
  obtain ⟨-, -, -, hAP⟩ := sylow_of_isSr h hr hS ha ha1
  have hXA : A ≤ Subgroup.normalizer (zOf (S ⊓ Subgroup.centralizer {a}) : Set G) :=
    fun g hg => mem_normalizer_zOf (hAP hg)
  have hXS : zOf (S ⊓ Subgroup.centralizer {a}) ≤ S := (zOf_le _).trans inf_le_left
  have hX : Nat.Coprime p (Nat.card (zOf (S ⊓ Subgroup.centralizer {a}))) :=
    hS.1.1.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hXS)
  have hrank : p ^ 2 * Nat.card (Subgroup.zpowers a) ≤ Nat.card A := by
    rw [h.card_zpowers ha ha1, h.card]
    exact (by ring : p ^ 2 * p = p ^ 3).le
  refine (iSup_inf_centralizer_sdiff h.prime h.elemAbelian (Subgroup.zpowers_le.mpr ha) hrank hXA
    hX).symm.le.trans ?_
  refine iSup_le fun b => iSup_le fun hbA => iSup_le fun hb x hx => ?_
  have hb1 : b ≠ 1 := fun h1 => hb (h1 ▸ one_mem _)
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers hbA hb1)
      (fun hle => hb (hle (Subgroup.mem_zpowers b)))
  have hBE := h.zpowers_sup_mem_E2 ha hbA ha1 hb1 hdisj
  have haB : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hxP : x ∈ zOf (S ⊓ Subgroup.centralizer {a}) := hx.1
  have hxa : x ∈ Subgroup.centralizer {a} := (zOf_le _ hxP).2
  have hxB : x ∈ Subgroup.centralizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [centralizer_sup, centralizer_zpowers_eq_singleton, centralizer_zpowers_eq_singleton]
    exact ⟨hxa, hx.2⟩
  have h1 : x ∈ zOf (S ⊓ Subgroup.centralizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) := by
    rw [← lemma_7_1_a h hr hS hBE (Or.inl hA) haB ha1]
    exact ⟨hxP, hxB⟩
  rw [lemma_7_1_b h hr hS hBE (Or.inl hA)] at h1
  exact ⟨h1.1, hxa⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
