module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofTypeOne
public import CFSG.LieType.SeitzGeneration.OutdiagHeis

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LieType.SeitzGeneration (heisC)
open Matrix (ProjGenLinGroup)

@[expose] def invSet142 {M : Type*} [Group M] (σ τ : MulAut M) : Set (Subgroup M) :=
  {X | ¬ 3 ∣ Nat.card X ∧ X.map σ.toMonoidHom ≤ X ∧ X.map τ.toMonoidHom ≤ X}

@[expose] def KS142L3PGLGenModel : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K] (hπ : π = false → UnitaryFieldData p f K),
    PiField π p f K → ModThree π (p ^ f) → Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) →
    ∀ (y s : GL (Fin 3) K) (hy : y ∈ glPi π 3 (p ^ f) K) (hs : s ∈ glPi π 3 (p ^ f) K),
      Type123 π (p ^ f) K y 3 → s ∈ slPi π 3 (p ^ f) K → s ∉ StatedScalars (Fin 3) K →
      s ^ 3 ∈ StatedScalars (Fin 3) K → y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K →
      sSup (invSet142 (Res8Hess.conjM' hπ hy) (Res8Hess.conjM' hπ hs)) = ⊤

@[expose] def KS142L3PGLGenStd : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K] (hπ : π = false → UnitaryFieldData p f K),
    PiField π p f K → ModThree π (p ^ f) → Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) →
    ∀ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 → ∀ (β : K) (cβ : GL (Fin 3) K)
      (hcβ : cβ ∈ glPi π 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi π 3 (p ^ f) K),
      (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β → (¬ ∃ μ : K, μ ^ 3 = β) →
      sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤

@[expose] def KS142L3PGLGenStdU : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (hπ : false = false → UnitaryFieldData p f K),
    PiField false p f K → ModThree false (p ^ f) →
    Group.IsPerfect (projImage (slPi false 3 (p ^ f) K)) →
    ∀ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 → ∀ (β : K) (cβ : GL (Fin 3) K)
      (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K),
      (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β → (¬ ∃ μ : K, μ ^ 3 = β) →
      sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤

@[expose] def KS142L3PGLGenStdFour : Prop :=
  ∀ (K : Type) [Field K] (hπ : true = false → UnitaryFieldData 2 2 K),
    PiField true 2 2 K → Group.IsPerfect (projImage (slPi true 3 (2 ^ 2) K)) →
    ∀ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 → ∀ (β : K) (cβ : GL (Fin 3) K)
      (hcβ : cβ ∈ glPi true 3 (2 ^ 2) K) (hd : diagTau hτ ∈ glPi true 3 (2 ^ 2) K),
      (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β → (¬ ∃ μ : K, μ ^ 3 = β) →
      sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤

namespace L3PGL

open scoped commutatorElement

variable {M : Type*} [Group M]

theorem heisC_pow_three {K : Type*} [Field K] (β : K) :
    heisC β ^ 3 = β • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, pow_three, Matrix.mul_apply, Fin.sum_univ_three]

theorem map_sSup_le {σ : MulAut M} {S : Set (Subgroup M)} (h : ∀ X ∈ S, X.map σ.toMonoidHom ≤ X) :
    (sSup S).map σ.toMonoidHom ≤ sSup S := by
  rw [sSup_eq_iSup', Subgroup.map_iSup]
  exact iSup_le fun X => (h X X.2).trans (le_iSup (fun Y : S => (Y : Subgroup M)) X)

theorem map_sSup_invSet142_le {σ τ : MulAut M} :
    (sSup (invSet142 σ τ)).map σ.toMonoidHom ≤ sSup (invSet142 σ τ) ∧
      (sSup (invSet142 σ τ)).map τ.toMonoidHom ≤ sSup (invSet142 σ τ) :=
  ⟨map_sSup_le fun _ hX => hX.2.1, map_sSup_le fun _ hX => hX.2.2⟩

theorem eq_top_of_sup_zpowers [Finite M] [Group.IsPerfect M] {N : Subgroup M} {g : M}
    (hN : N.map (MulAut.conj g).toMonoidHom ≤ N) (htop : N ⊔ Subgroup.zpowers g = ⊤) :
    N = ⊤ := by
  have heq : N.map (MulAut.conj g).toMonoidHom = N :=
    Subgroup.eq_of_le_of_card_ge hN (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hgN : g ∈ Subgroup.normalizer (N : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hN ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', he⟩ := hh
      have : h' = h := by
        change g * h' * g⁻¹ = g * h * g⁻¹ at he
        simpa using he
      rwa [← this]
  have hnorm : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hgN)
  have hcyc : ∀ x : M ⧸ N, x ∈ Subgroup.zpowers (QuotientGroup.mk' N g) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ N ⊔ Subgroup.zpowers g := htop ▸ Subgroup.mem_top y
    have hmap := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hy
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers] at hmap
    exact hmap
  have hcomm : ∀ a b : M, ⁅a, b⁆ ∈ N := by
    intro a b
    obtain ⟨i, hi⟩ := hcyc (QuotientGroup.mk' N a)
    obtain ⟨j, hj⟩ := hcyc (QuotientGroup.mk' N b)
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    change QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hi, ← hj]
    rw [← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add, ← zpow_add]
    rw [show i + j + -i + -j = 0 by ring, zpow_zero]
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := M), commutator_def,
    Subgroup.commutator_le]
  intro a _ b _
  exact hcomm a b

theorem not_three_dvd_card_of_pow_three {X : Subgroup M} [Finite X]
    (h : ∀ x ∈ X, x ^ 3 = 1 → x = 1) : ¬ 3 ∣ Nat.card X := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : (x : M) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have h1 := h x x.2 hx3
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  norm_num at hx

end L3PGL

end CFSG.RankThree.PartTwo.Sec14
