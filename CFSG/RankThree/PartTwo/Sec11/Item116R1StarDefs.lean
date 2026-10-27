module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.PartOne.Assembly

public section

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

@[expose] def FiveLocalRankHyp (G : Type*) [Group G] : Prop :=
  ∀ r : ℕ, r.Prime → 3 < r → ∀ Q : Subgroup G, IsPGroup r Q → ∀ u : G, u ≠ 1 →
    IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank r ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2

@[expose] def fiveStarR {G : Type*} [Group G] (S : Subgroup G) (w : G) : Subgroup G :=
  ⁅S, Subgroup.zpowers w⁆

@[expose] def FiveStarData {G : Type} [Group G] (S : Subgroup G) (w : G) : Prop :=
  Nonempty (↥(fiveStarR S w) ≃* QD32) ∧
  (∀ r ∈ fiveStarR S w, w * r * w⁻¹ * r⁻¹ ∈ inSubgroup Subgroup.center (fiveStarR S w) →
      r ∈ inSubgroup Subgroup.center (fiveStarR S w)) ∧
  ∃ (p : ℕ) (D : Subgroup G), p.Prime ∧ 3 < p ∧ IsPGroup p D ∧ (∀ d ∈ D, d ^ p = 1) ∧
    S ≤ Subgroup.normalizer (D : Set G) ∧ fiveStarR S w ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧
    3 ≤ CFSG.pRank p ↥D ∧ IsFrattiniIrreducibleFor (fiveStarR S w) D

@[expose] def FiveStarAt {G : Type} [Group G] (θ S : Subgroup G) : Prop :=
  ∀ w : G, IsPGroup 5 (Subgroup.zpowers w) → w ∈ Subgroup.normalizer (θ : Set G) →
    w ∈ Subgroup.normalizer (S : Set G) → (∃ s ∈ S, w * s * w⁻¹ ≠ s) → FiveStarData S w

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type*} [Group G]

theorem h1_comm_zpow (s x : G) (n : ℤ) : ⁅s, x ^ n⁆ = s * (x ^ n * s * (x ^ n)⁻¹)⁻¹ := by
  rw [commutatorElement_def]
  group

theorem h1_succ_conj (x : G) (n : ℤ) (s : G) :
    x ^ (n + 1) * s * (x ^ (n + 1))⁻¹ = x ^ n * (x * s * x⁻¹) * (x ^ n)⁻¹ := by
  rw [zpow_add_one]
  group

theorem h1_pred_conj (x : G) (n : ℤ) (s : G) :
    x ^ (n - 1) * s * (x ^ (n - 1))⁻¹ = x ^ n * (x⁻¹ * s * x) * (x ^ n)⁻¹ := by
  rw [zpow_sub_one]
  group

theorem h1_pow_conj {S : Subgroup G} {w w' : G} (hw : w ∈ normalizer (S : Set G))
    (h : ∀ s ∈ S, w * s * w⁻¹ = w' * s * w'⁻¹) (n : ℤ) :
    ∀ s ∈ S, w ^ n * s * (w ^ n)⁻¹ = w' ^ n * s * (w' ^ n)⁻¹ := by
  have hconj : ∀ s ∈ S, w * s * w⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.mp hw s).mp hs
  have hconjinv : ∀ s ∈ S, w⁻¹ * s * w ∈ S := by
    intro s hs
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) s).mp hs
    rwa [inv_inv] at this
  have hinv : ∀ s ∈ S, w⁻¹ * s * w = w'⁻¹ * s * w' := by
    intro s hs
    have hst := h _ (hconjinv s hs)
    have e1 : w * (w⁻¹ * s * w) * w⁻¹ = s := by group
    rw [e1] at hst
    calc w⁻¹ * s * w = w'⁻¹ * (w' * (w⁻¹ * s * w) * w'⁻¹) * w' := by group
      _ = w'⁻¹ * s * w' := by rw [← hst]
  induction n using Int.induction_on with
  | zero => intro s _; simp
  | succ i ih =>
    intro s hs
    rw [h1_succ_conj w, ih _ (hconj s hs), h s hs, h1_succ_conj w']
  | pred i ih =>
    intro s hs
    rw [h1_pred_conj w, ih _ (hconjinv s hs), hinv s hs, h1_pred_conj w']

theorem h1_le_of_action {S : Subgroup G} {w w' : G} (hw : w ∈ normalizer (S : Set G))
    (h : ∀ s ∈ S, w * s * w⁻¹ = w' * s * w'⁻¹) : fiveStarR S w ≤ fiveStarR S w' := by
  show ⁅S, Subgroup.zpowers w⁆ ≤ ⁅S, Subgroup.zpowers w'⁆
  refine Subgroup.commutator_le.mpr fun s hs g hg => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [h1_comm_zpow s w n, h1_pow_conj hw h n s hs, ← h1_comm_zpow s w' n]
  exact Subgroup.commutator_mem_commutator hs (Subgroup.zpow_mem_zpowers w' n)

theorem h1_conj_le {S : Subgroup G} {w c : G} (hw : w ∈ normalizer (S : Set G))
    (hc : c ∈ normalizer (S : Set G))
    (h : ∀ s ∈ S, w * (c * s * c⁻¹) * w⁻¹ = c * (w * s * w⁻¹) * c⁻¹) :
    ∀ x ∈ fiveStarR S w, c * x * c⁻¹ ∈ fiveStarR S w := by
  have hw' : c * w * c⁻¹ ∈ normalizer (S : Set G) := mul_mem (mul_mem hc hw) (inv_mem hc)
  have hact : ∀ s ∈ S, c * w * c⁻¹ * s * (c * w * c⁻¹)⁻¹ = w * s * w⁻¹ := by
    intro s hs
    have ht : c⁻¹ * s * c ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hc) s).mp hs
      rwa [inv_inv] at this
    have hst := h _ ht
    have e1 : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
    rw [e1] at hst
    rw [hst]
    group
  have hle : fiveStarR S (c * w * c⁻¹) ≤ fiveStarR S w := h1_le_of_action hw' hact
  have key : fiveStarR S w ≤ (fiveStarR S w).comap (MulEquiv.toMonoidHom (MulAut.conj c)) := by
    show ⁅S, Subgroup.zpowers w⁆ ≤
      (⁅S, Subgroup.zpowers w⁆ : Subgroup G).comap (MulEquiv.toMonoidHom (MulAut.conj c))
    refine Subgroup.commutator_le.mpr fun s hs g hg => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hs' : c * s * c⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hc s).mp hs
    have e : c * ⁅s, w ^ n⁆ * c⁻¹ = ⁅c * s * c⁻¹, (c * w * c⁻¹) ^ n⁆ := by
      rw [conjugate_commutatorElement, conj_zpow]
    have hmem : ⁅c * s * c⁻¹, (c * w * c⁻¹) ^ n⁆ ∈ fiveStarR S (c * w * c⁻¹) :=
      Subgroup.commutator_mem_commutator hs' (Subgroup.zpow_mem_zpowers _ n)
    change c * ⁅s, w ^ n⁆ * c⁻¹ ∈ ⁅S, Subgroup.zpowers w⁆
    rw [e]
    exact hle hmem
  intro x hx
  exact Subgroup.mem_comap.mp (key hx)

theorem fiveStarR_le {S : Subgroup G} {w : G} (hw : w ∈ normalizer (S : Set G)) : fiveStarR S w ≤ S := by
  have hXS : Subgroup.zpowers w ≤ Subgroup.normalizer (S : Set G) := Subgroup.zpowers_le.mpr hw
  exact (Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers w) (K := S)).mp hXS

theorem le_normalizer_fiveStarR {S : Subgroup G} {w : G} (hw : w ∈ normalizer (S : Set G)) :
    S ≤ normalizer (fiveStarR S w : Set G) := by
  exact Subgroup.normalizer_commutator_ge_left S (Subgroup.zpowers w)

theorem mem_normalizer_fiveStarR_self (S : Subgroup G) (w : G) :
    w ∈ normalizer (fiveStarR S w : Set G) := by
  exact Subgroup.normalizer_commutator_ge_right S (Subgroup.zpowers w) (Subgroup.mem_zpowers w)

theorem mem_normalizer_fiveStarR_of_commute {S : Subgroup G} {w b : G} (hw : w ∈ normalizer (S : Set G))
    (hb : b ∈ normalizer (S : Set G))
    (h : ∀ s ∈ S, w * (b * s * b⁻¹) * w⁻¹ = b * (w * s * w⁻¹) * b⁻¹) :
    b ∈ normalizer (fiveStarR S w : Set G) := by
  have hb' : ∀ s ∈ S, w * (b⁻¹ * s * b⁻¹⁻¹) * w⁻¹ = b⁻¹ * (w * s * w⁻¹) * b⁻¹⁻¹ := by
    intro s hs
    have ht : b⁻¹ * s * b⁻¹⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) s).mp hs
    have hst := h _ ht
    have e1 : b * (b⁻¹ * s * b⁻¹⁻¹) * b⁻¹ = s := by group
    rw [e1] at hst
    rw [hst]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1_conj_le hw hb h x hx
  · intro hx
    have h2 := h1_conj_le hw (inv_mem hb) hb' (b * x * b⁻¹) hx
    have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rw [e] at h2
    exact h2

end CFSG.RankThree.PartTwo.Sec11

end
