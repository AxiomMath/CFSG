module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R898Res (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, IsSU3 (Bar2 L) n → ∀ s : ℕ, Odd s → s ∣ n →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 → ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
      normalizer (X : Set G) ≤ D.M → (n = 3 ∨ n = 3 * r) → X ∈ uniqueSet D.M

theorem mem_map_conj_inv {X : Subgroup G} (g z : G) :
    z ∈ X.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ X := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨g * z * g⁻¹, h, by group⟩

theorem conj_mem_normalizer_of_mem_normalizer_conj {X : Subgroup G} (g n : G)
    (hn : n ∈ normalizer ((X.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    g * n * g⁻¹ ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  have h := hn (g⁻¹ * x * g)
  rw [mem_map_conj_inv, mem_map_conj_inv] at h
  have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  have e2 : g * (n * (g⁻¹ * x * g) * n⁻¹) * g⁻¹ = g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹ := by group
  rw [e1, e2] at h
  exact h

theorem exists_generator {Y : Subgroup G} {r : ℕ} (hr : r.Prime) (hY : Nat.card Y = r) :
    ∃ y ∈ Y, orderOf y = r ∧ ∀ x ∈ Y, ∃ k : ℕ, y ^ k = x := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsCyclic ↥Y := isCyclic_of_prime_card (p := r) hY
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := ↥Y)
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hY]
  · intro x hx
    have hxy : (⟨x, hx⟩ : ↥Y) ∈ Subgroup.zpowers y := hy _
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 hxy)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
