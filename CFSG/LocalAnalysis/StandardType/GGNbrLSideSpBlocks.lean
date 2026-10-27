module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympCent
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitTameSp
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitTameGL
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitTameGU

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI
open CFSG.LocalAnalysis.GLTheoremA.K1419
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

private theorem sup_induction_join {G : Type*} [Group G] {A A' : Subgroup G} {P : G → Prop}
    (hA : ∀ x ∈ A, P x) (hA' : ∀ x ∈ A', P x) (h1 : P 1)
    (hmul : ∀ x y, x ∈ A ⊔ A' → y ∈ A ⊔ A' → P x → P y → P (x * y))
    (hinv : ∀ x, x ∈ A ⊔ A' → P x → P x⁻¹) {x : G} (hx : x ∈ A ⊔ A') : P x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => P x) ?_ h1 ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact hA y hy
    · exact hA' y hy
  · intro x y hx hy hpx hpy
    rw [← Subgroup.sup_eq_closure] at hx hy
    exact hmul x y hx hy hpx hpy
  · intro x hx hpx
    rw [← Subgroup.sup_eq_closure] at hx
    exact hinv x hx hpx

theorem ggNbrLSideSp_blocks {ℓ n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (x y : StatedSp ℓ K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxy : x * y = y * x) :
    ∃ (A₁ A₂ : Subgroup (StatedSp ℓ K)) (y₁ y₂ : StatedSp ℓ K),
      (∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) ∧
      A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp ℓ K)) ∧
      y₁ ∈ A₁ ∧ y₂ ∈ A₂ ∧ y = y₁ * y₂ ∧
      (CFSG.IsQuasisimple ↥⁅A₁, A₁⁆ ∨ Group.IsSolvable ↥A₁) ∧
      (CFSG.IsQuasisimple ↥⁅A₂, A₂⁆ ∨ Group.IsSolvable ↥A₂) ∧
      (∃ s : ℕ, Nonempty (↥A₁ ≃* ↥(StatedSp s K))) ∧
      ((∃ r : ℕ, 1 ≤ r ∧ Nonempty (↥A₂ ≃* GL (Fin r) K)) ∨
        ∃ (r : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 1 ≤ r ∧ Nat.card E = Nat.card K ^ 2 ∧
          (∀ y, τ y = y ^ Nat.card K) ∧ Nonempty (↥A₂ ≃* heldGU r E τ hτ)) := by
  classical
  obtain ⟨A₁, A₂, hc, hjoin, _hxA₂, ⟨s, ⟨φ₁⟩⟩, hshape⟩ :=
    k1419ClsSympCent (m := ℓ) (n := n) hK hn hℓ x hx3 hx1
  have hyC : y ∈ Subgroup.centralizer ({x} : Set (StatedSp ℓ K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  have hyjoin : y ∈ A₁ ⊔ A₂ := hjoin ▸ hyC
  have hsplit : ∃ y₁ ∈ A₁, ∃ y₂ ∈ A₂, y = y₁ * y₂ := by
    refine sup_induction_join (A := A₁) (A' := A₂)
      (P := fun z => ∃ y₁ ∈ A₁, ∃ y₂ ∈ A₂, z = y₁ * y₂) ?_ ?_ ?_ ?_ ?_ hyjoin
    · intro a ha
      exact ⟨a, ha, 1, A₂.one_mem, by simp⟩
    · intro b hb
      exact ⟨1, A₁.one_mem, b, hb, by simp⟩
    · exact ⟨1, A₁.one_mem, 1, A₂.one_mem, by simp⟩
    · intro p q hp hq hpP hqP
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hpP
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hqP
      refine ⟨a₁ * b₁, A₁.mul_mem ha₁ hb₁, a₂ * b₂, A₂.mul_mem ha₂ hb₂, ?_⟩
      calc (a₁ * a₂) * (b₁ * b₂)
          = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [(hc b₁ hb₁ a₂ ha₂).symm]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
    · intro z hz hzP
      obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hzP
      refine ⟨p₁⁻¹, A₁.inv_mem hp₁, p₂⁻¹, A₂.inv_mem hp₂, ?_⟩
      have h : p₂ * p₁ = p₁ * p₂ := (hc p₁ hp₁ p₂ hp₂).symm
      rw [← h, mul_inv_rev]
  obtain ⟨y₁, hy₁, y₂, hy₂, hyEq⟩ := hsplit
  have htame₁ : CFSG.IsQuasisimple ↥⁅A₁, A₁⁆ ∨ Group.IsSolvable ↥A₁ :=
    ggNbrLSideTame_sp φ₁
  have htame₂ : CFSG.IsQuasisimple ↥⁅A₂, A₂⁆ ∨ Group.IsSolvable ↥A₂ := by
    rcases hshape with ⟨r, _hr, ⟨φ₂⟩⟩ | ⟨r, E, hEfield, hEfinite, τ, hτ, _hr, hEc, hτQ, ⟨φ₂⟩⟩
    · exact ggNbrLSideTame_gl φ₂
    · exact ggNbrLSideTame_gu hK hn hEc hτQ φ₂
  exact ⟨A₁, A₂, y₁, y₂, hc, hjoin, hy₁, hy₂, hyEq, htame₁, htame₂,
    ⟨s, ⟨φ₁⟩⟩, hshape⟩

end CFSG.StandardType
