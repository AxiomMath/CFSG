module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_ne_one (h : Counterexample p A θ) : ∃ a ∈ A, a ≠ 1 := by
  by_contra! hcon
  have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hcon
  have h1 : Nat.card A = 1 := by rw [this]; simp
  rw [h.card] at h1
  exact absurd h1 (Nat.one_lt_pow (by norm_num) h.prime.one_lt).ne'

theorem isElemAbelian_of_le (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≤ A) :
    IsElemAbelian p B :=
  CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.elemAbelian hB

theorem card_zpowers (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Nat.card (Subgroup.zpowers a) = p := by
  rw [(zpowers_mem_signalizerFunctorEk_one h.prime h.elemAbelian ha ha1).2, pow_one]

theorem exists_complement_zpowers (h : Counterexample p A θ) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : ∃ F : Subgroup G, F ≤ A ∧ Nat.card F = p ^ 2 ∧
      Subgroup.zpowers a ⊓ F = ⊥ ∧ Subgroup.zpowers a ⊔ F = A := by
  obtain ⟨F, hFA, -, hEF, hsup⟩ := exists_complement_containing h.prime h.elemAbelian
    (Subgroup.zpowers_le.mpr ha) (bot_le : (⊥ : Subgroup G) ≤ A) (inf_bot_eq _)
  refine ⟨F, hFA, ?_, hEF, hsup⟩
  have hcard := card_mul_card_complement h.elemAbelian (Subgroup.zpowers_le.mpr ha) hFA hEF hsup
  rw [h.card_zpowers ha ha1, h.card] at hcard
  exact Nat.eq_of_mul_eq_mul_left h.prime.pos (hcard.trans (by ring))

theorem zpowers_sup_mem_E2 (h : Counterexample p A θ) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b ∈ signalizerFunctorEk p 2 A := by
  refine ⟨sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb), ?_⟩
  rw [card_sup_of_le_elemAbelian h.elemAbelian (Subgroup.zpowers_le.mpr ha)
    (Subgroup.zpowers_le.mpr hb) hdisj, h.card_zpowers ha ha1, h.card_zpowers hb hb1, sq]

theorem hypB_thetaOf (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≤ A) (hB1 : B ≠ ⊥) :
    signalizerMcBrideHypothesisB p (thetaOf θ B) := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1' : b ≠ 1 := fun h' => hb1 (Subtype.ext h')
  exact hypB_mono (thetaOf_le_apply hb hb1') (h.hypC b (hB hb) hb1')

theorem thetaOf_mem_msig (h : Counterexample p A θ) {B : Subgroup G} (hB : B ≤ A)
    (hB1 : B ≠ ⊥) : thetaOf θ B ∈ Msig p A θ :=
  h.isFunctor.thetaOf_mem_signalizers hB hB1 (h.hypB_thetaOf hB hB1)

theorem apply_mem_msig (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    θ a ∈ Msig p A θ :=
  h.isFunctor.apply_mem_signalizers ha ha1 (h.hypC a ha ha1)

theorem sSup_msig_eq_thetaSup (h : Counterexample p A θ) :
    sSup (Msig p A θ) = thetaSup A θ :=
  sSup_signalizers_eq_thetaSup h.prime h.elemAbelian h.rank_two_le h.isFunctor h.hypC

theorem normalizes_sSup_msig (h : Counterexample p A θ) :
    A ≤ Subgroup.normalizer ((sSup (Msig p A θ) : Subgroup G) : Set G) := by
  rw [h.sSup_msig_eq_thetaSup]
  exact h.isFunctor.normalizes_thetaSup

theorem apply_le_sSup_msig (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    θ a ≤ sSup (Msig p A θ) :=
  le_sSup (h.apply_mem_msig ha ha1)

end Counterexample

theorem kOf_mem_msig {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G}
    {θ : G → Subgroup G} {X : Subgroup G} (hX : X ∈ Msig p A θ) : kOf X ∈ Msig p A θ :=
  mem_signalizers_of_le hX (kOf_le X) (le_normalizer_kOf_of_le_normalizer hX.1)
    (fun hP => hypB_mono (kOf_le X) hP)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
