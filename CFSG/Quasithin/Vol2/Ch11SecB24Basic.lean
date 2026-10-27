module

public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.Vol2.Ch11SecABasic
public import CFSG.Quasithin.Vol2.Ch11StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem setup24 (h1122 : Stmt11_2_2) (hyp : Hyp11 G T L I n) {V₁ V₂ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hW : ⁅fsuV T I, E3.wClos (fsuV T I) 0 T⁆ ≠ ⊥)
    (hSL3 : KindSL3 L (fsuV T I) n →
      Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ¬ KindG2 L (fsuV T I) n ∧ (∀ hV : IsElemAbelian 2 (fsuV T I), E3.sParam hV = n) ∧
      (n : ℕ∞) < E3.rParam (fsuV T I) := by
  have hG2 : ¬ KindG2 L (fsuV T I) n := by
    intro hG2
    have h := (h1122 G T L I n (2 * n) V₁ V₂ hyp hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.2.2.1 hG2
    apply hW
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.1.trans inf_le_right
  have h := h1122 G T L I n n V₁ V₂ hyp hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)
  refine ⟨hG2, h.2.2.2.1, ?_⟩
  rcases h.2.2.1 with h3 | ⟨hk, -, hC⟩
  · exact h3
  · exact absurd (hSL3 hk) hC

omit [Finite G] in
theorem not_mem_normalizer_of_ne_bot {V V₁ : Subgroup G}
    (hab : IsMulCommutative ↥(conjClosure V (Subgroup.normalizer (V₁ : Set G)))) {g : G}
    (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) : g ∉ Subgroup.normalizer (V₁ : Set G) := by
  intro hg
  apply hnc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hv' : v ∈ conjClosure V (Subgroup.normalizer (V₁ : Set G)) := le_conjClosure _ _ hv
  have hw' : w ∈ conjClosure V (Subgroup.normalizer (V₁ : Set G)) := by
    have h1 : g * w * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp hw
    have := mem_conjClosure (Subgroup.inv_mem _ hg) h1
    simpa [mul_assoc] using this
  exact congrArg Subtype.val (hab.is_comm.comm ⟨w, hw'⟩ ⟨v, hv'⟩)

theorem exists_conj_le_T {V : Subgroup G} (hV2 : IsPGroup 2 ↥V)
    (hW : ⁅V, E3.wClos V 0 T⁆ ≠ ⊥) :
    ∃ g : G, conjSubgroup V g ≤ T ∧ ⁅V, conjSubgroup V g⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply hW
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hA0⟩ := hA
  have hAeq : A = conjSubgroup V g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).mp hA0
  subst hAeq
  have h1 := hall g hAT
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  exact h1

theorem centralizer_le_normalizer_of_lt {V B : Subgroup G} {g : G} (hBV : B ≤ conjSubgroup V g)
    (hlt : (E3.mQuot (conjSubgroup V g) B : ℕ∞) < E3.rParam V) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  by_contra hC
  have h := E3.rParam_le_mQuot hBV hC
  rw [E3.rParam_conj] at h
  exact absurd hlt (not_lt.mpr h)

end CFSG.Quasithin.Vol2.Ch11.SecB
