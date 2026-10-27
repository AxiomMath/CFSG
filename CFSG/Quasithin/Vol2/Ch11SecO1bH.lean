module

public import CFSG.Quasithin.Vol2.Ch11SecO1bD
public import CFSG.Quasithin.Vol2.Ch11SecO1bG
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin KGNat
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] {V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M]
  [Module K M]

@[expose] def unipSub (f : ↥V → M) (V₂ : Subgroup G) (u₀ : M) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
    x ∈ Subgroup.normalizer (V₂ : Set G) ∧
      ∀ v : ↥V, (v : G) ∈ V₂ → ∃ c : K, f (SecA.conjV V x hx v) = f v + c • u₀}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun v _ => ⟨0, by
    rw [zero_smul, add_zero]
    congr 1
    exact Subtype.ext (by rw [SecA.conjV_apply_coe, one_mul, inv_one, mul_one])⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hx₂, hxs⟩ ⟨hy, hy₂, hys⟩
    refine ⟨Subgroup.mul_mem _ hx hy, Subgroup.mul_mem _ hx₂ hy₂, fun v hv => ?_⟩
    obtain ⟨c, hc⟩ := hys v hv
    have hv' : ((SecA.conjV V y hy v : ↥V) : G) ∈ V₂ := by
      rw [SecA.conjV_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hy₂ v).mp hv
    obtain ⟨c', hc'⟩ := hxs _ hv'
    refine ⟨c + c', ?_⟩
    rw [SecA.conjV_mul V hx hy, MulAut.mul_apply, hc', hc, add_smul, add_assoc]
  inv_mem' := by
    rintro x ⟨hx, hx₂, hxs⟩
    refine ⟨Subgroup.inv_mem _ hx, Subgroup.inv_mem _ hx₂, fun v hv => ?_⟩
    have hw : ((SecA.conjV V x⁻¹ (Subgroup.inv_mem _ hx) v : ↥V) : G) ∈ V₂ := by
      rw [SecA.conjV_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx₂) v).mp hv
    obtain ⟨c, hc⟩ := hxs _ hw
    refine ⟨-c, ?_⟩
    rw [SecA.conjV_inv V hx, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at hc
    rw [SecA.conjV_inv V hx, neg_smul, hc, add_neg_cancel_right]

variable [CharP K 2]

theorem pointComm_of_coords {f : ↥V → M} (hmul : ∀ a b : ↥V, f (a * b) = f a + f b)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) {u₀ u₁ p : M}
    (hind : ∀ c d : K, c • u₀ + d • u₁ = 0 → c = 0 ∧ d = 0) {V₁ V₂ P : Subgroup G}
    (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀)
    (hV₂ : ∀ v : ↥V, (v : G) ∈ V₂ ↔ ∃ c d : K, f v = c • u₀ + d • u₁)
    (hP : ∀ v : ↥V, (v : G) ∈ P ↔ ∃ c : K, f v = c • p) {a : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (haV₁ : a ∈ Subgroup.normalizer (V₁ : Set G))
    (haV₂ : a ∈ Subgroup.normalizer (V₂ : Set G)) {k : ℕ} (ha2 : a ^ 2 ^ k = 1)
    {T : M →+ M} {σ : K →+* K} (hσ : ∀ (c : K) (x : M), T (c • x) = σ c • T x)
    (hT : ∀ w, T (f w) = f (SecA.conjV V a haV w))
    (hle : ⁅V₂, Subgroup.zpowers a⁆ ≤ P) :
    ⁅V₂, Subgroup.zpowers a⁆ = ⊥ ∨ ⁅V₂, Subgroup.zpowers a⁆ = V₁ := by
  have hfinv : ∀ w : ↥V, f w⁻¹ = - f w := fun w => by
    have h1 : f 1 = 0 := by
      have h := hmul 1 1
      rw [mul_one] at h
      exact left_eq_add.mp h
    have h := hmul w w⁻¹
    rw [mul_inv_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hcomm : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V),
      ⁅(v : G), x⁆ = (((SecA.conjV V x hx v * v⁻¹)⁻¹ : ↥V) : G) := fun x hx v =>
    commutator_coe_eq hx v
  obtain ⟨w₀, hw₀⟩ := hsurj u₀
  obtain ⟨w₁, hw₁⟩ := hsurj u₁
  have hmV₁ : ∀ w : ↥V, (w : G) ∈ V₁ → ((SecA.conjV V a haV w : ↥V) : G) ∈ V₁ := fun w hw => by
    rw [SecA.conjV_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp haV₁ w).mp hw
  have hmV₂ : ∀ w : ↥V, (w : G) ∈ V₂ → ((SecA.conjV V a haV w : ↥V) : G) ∈ V₂ := fun w hw => by
    rw [SecA.conjV_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp haV₂ w).mp hw
  obtain ⟨α, hα⟩ := (hV₁ _).mp (hmV₁ w₀ ((hV₁ w₀).mpr ⟨1, by rw [hw₀, one_smul]⟩))
  obtain ⟨β, γ, hβγ⟩ := (hV₂ _).mp (hmV₂ w₁ ((hV₂ w₁).mpr ⟨0, 1, by
    rw [hw₁, zero_smul, zero_add, one_smul]⟩))
  have h0 : T u₀ = α • u₀ := by rw [← hw₀, hT, hα, hw₀]
  have h1 : T u₁ = β • u₀ + γ • u₁ := by rw [← hw₁, hT, hβγ, hw₁]
  have hk : ∀ x, T^[2 ^ k] x = x := fun x => by
    obtain ⟨w, rfl⟩ := hsurj x
    rw [iterate_eq_of_intertwine hT, SecA.conjV_pow_eq_one V haV ha2, MulAut.one_apply]
  have hline : ∀ c d : K, ∃ t : K, T (c • u₀ + d • u₁) - (c • u₀ + d • u₁) = t • p := by
    intro c d
    obtain ⟨v, hv⟩ := hsurj (c • u₀ + d • u₁)
    have hvV₂ : (v : G) ∈ V₂ := (hV₂ v).mpr ⟨c, d, hv⟩
    have hmem : ⁅(v : G), a⁆ ∈ P := hle (Subgroup.commutator_mem_commutator hvV₂
      (Subgroup.mem_zpowers a))
    rw [hcomm a haV v] at hmem
    obtain ⟨t, ht⟩ := (hP _).mp hmem
    refine ⟨-t, ?_⟩
    rw [hfinv, hmul, hfinv, ← hT, hv] at ht
    rw [neg_smul, ← ht]
    abel
  obtain ⟨hσ1, hα1, hγ1⟩ := shape_of_comm_line hσ hind h0 h1 hk hline
  have hTx : ∀ c d : K, T (c • u₀ + d • u₁) = (c • u₀ + d • u₁) + (d * β) • u₀ := by
    intro c d
    rw [map_add, hσ, hσ, h0, h1, hσ1, hσ1, hα1, hγ1, one_smul, one_smul, smul_add, smul_smul]
    abel
  have haU : a ∈ unipSub f V₂ u₀ := ⟨haV, haV₂, fun v hv => by
    obtain ⟨c, d, hcd⟩ := (hV₂ v).mp hv
    exact ⟨d * β, by rw [← hT, hcd, hTx]⟩⟩
  have hzU : Subgroup.zpowers a ≤ unipSub f V₂ u₀ := Subgroup.zpowers_le.mpr haU
  have hleV₁ : ⁅V₂, Subgroup.zpowers a⁆ ≤ V₁ := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    obtain ⟨hxV, -, hxs⟩ := hzU hx
    obtain ⟨c, hc⟩ := hxs ⟨v, hV₂V hv⟩ hv
    rw [hcomm x hxV ⟨v, hV₂V hv⟩]
    refine (hV₁ _).mpr ⟨-c, ?_⟩
    rw [hfinv, hmul, hfinv, hc, neg_smul]
    abel
  by_cases hβ : β = 0
  · left
    have haC : a ∈ Subgroup.centralizer (V₂ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨c, d, hcd⟩ := (hV₂ ⟨u, hV₂V hu⟩).mp hu
      have h1 : SecA.conjV V a haV ⟨u, hV₂V hu⟩ = ⟨u, hV₂V hu⟩ := hinj (by
        rw [← hT, hcd, hTx, hβ, mul_zero, zero_smul, add_zero])
      have h2 := congrArg Subtype.val h1
      rw [SecA.conjV_apply_coe] at h2
      calc u * a = a * u * a⁻¹ * a := by rw [h2]
        _ = a * u := by group
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv x hx
    have hxC : x ∈ Subgroup.centralizer (V₂ : Set G) := (Subgroup.zpowers_le.mpr haC) hx
    rw [Subgroup.mem_bot, commutatorElement_def, Subgroup.mem_centralizer_iff.mp hxC v hv]
    group
  · right
    refine le_antisymm hleV₁ fun u hu => ?_
    obtain ⟨c, hc⟩ := (hV₁ ⟨u, hV₁V hu⟩).mp hu
    obtain ⟨v, hv⟩ := hsurj ((c / β) • u₁)
    have hv' : f v = (0 : K) • u₀ + (c / β) • u₁ := by rw [hv, zero_smul, zero_add]
    have hvV₂ : (v : G) ∈ V₂ := (hV₂ v).mpr ⟨0, c / β, hv'⟩
    have h1 : SecA.conjV V a haV v * v⁻¹ = ⟨u, hV₁V hu⟩ := hinj (by
      rw [hmul, hfinv, ← hT, hv', hTx, hc, div_mul_cancel₀ c hβ]
      abel)
    have h2 : (u : G) = ⁅(v : G), a⁆⁻¹ := by
      rw [hcomm a haV v, h1, Subgroup.coe_inv, inv_inv]
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hvV₂ (Subgroup.mem_zpowers a))

end CFSG.Quasithin.Vol2.Ch11.SecO1b
