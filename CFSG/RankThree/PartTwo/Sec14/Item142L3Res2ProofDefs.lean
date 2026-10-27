module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofDefs
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LieType.SeitzGeneration (heisC)

@[expose] def KS142L3PGLGenStdUNine : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (hπ : false = false → UnitaryFieldData p f K),
    PiField false p f K → ModThree false (p ^ f) → p ^ f % 9 = 8 →
    Group.IsPerfect (projImage (slPi false 3 (p ^ f) K)) →
    ∀ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 → ∀ (β : K) (cβ : GL (Fin 3) K)
      (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K),
      (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β → (¬ ∃ μ : K, μ ^ 3 = β) →
      sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤

namespace L3PGLU

variable {M : Type} [Group M]

theorem mem_normalizer_of_map_le [Finite M] {N : Subgroup M} {g : M}
    (hN : N.map (MulAut.conj g).toMonoidHom ≤ N) : g ∈ Subgroup.normalizer (N : Set M) := by
  have heq : N.map (MulAut.conj g).toMonoidHom = N :=
    Subgroup.eq_of_le_of_card_ge hN (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
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

theorem eq_top_of_sup_zpowers_two [Finite M] [Group.IsPerfect M] {N : Subgroup M} {a b : M}
    (hab : a * b = b * a) (ha : N.map (MulAut.conj a).toMonoidHom ≤ N)
    (hb : N.map (MulAut.conj b).toMonoidHom ≤ N)
    (htop : N ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊤) : N = ⊤ := by
  have haN := mem_normalizer_of_map_le ha
  have hbN := mem_normalizer_of_map_le hb
  have hnorm : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer
      (sup_le (Subgroup.zpowers_le.mpr haN) (Subgroup.zpowers_le.mpr hbN))
  set π := QuotientGroup.mk' N with hπ
  have hab' : π a * π b = π b * π a := by rw [← map_mul, hab, map_mul]
  have hgen : ∀ x : M ⧸ N, x ∈ Subgroup.zpowers (π a) ⊔ Subgroup.zpowers (π b) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ N ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := htop ▸ Subgroup.mem_top y
    have hmap := Subgroup.mem_map_of_mem π hy
    rw [Subgroup.map_sup, Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
    exact hmap
  have hcomm : ∀ x y : M ⧸ N, x * y = y * x := by
    intro x y
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab' (hgen x)
    obtain ⟨k, l, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab' (hgen y)
    have hc : ∀ (s t : ℤ), π b ^ s * π a ^ t = π a ^ t * π b ^ s := fun s t =>
      (Commute.zpow_zpow hab' t s).eq.symm
    calc π a ^ i * π b ^ j * (π a ^ k * π b ^ l)
        = π a ^ i * (π b ^ j * π a ^ k) * π b ^ l := by group
      _ = π a ^ i * (π a ^ k * π b ^ j) * π b ^ l := by rw [hc]
      _ = π a ^ (i + k) * π b ^ (j + l) := by group
      _ = π a ^ (k + i) * π b ^ (l + j) := by rw [add_comm i k, add_comm j l]
      _ = π a ^ k * (π a ^ i * π b ^ l) * π b ^ j := by group
      _ = π a ^ k * (π b ^ l * π a ^ i) * π b ^ j := by rw [hc]
      _ = π a ^ k * π b ^ l * (π a ^ i * π b ^ j) := by group
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := M), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  change π (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm (π x) (π y)]
  group

end L3PGLU

end CFSG.RankThree.PartTwo.Sec14
