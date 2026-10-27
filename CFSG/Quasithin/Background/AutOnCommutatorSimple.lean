module

public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_autOn_eq_of_simple {Y K W : Subgroup G}
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hKY : K ≤ Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K ⊔ Subgroup.centralizer (W : Set G))
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hs : IsSimpleGroup ↥(autOn K W))
    (hna : ∃ a b : ↥(autOn K W), a * b ≠ b * a) {A : Subgroup (MulAut ↥W)}
    (hAY : A ≤ autOn Y W) (hA : A ≠ ⊥) : ⁅autOn K W, A⁆ = autOn K W := by
  set X := autOn Y W with hX
  set Ks := autOn K W with hKs
  have hXn : X ≤ Subgroup.normalizer (Ks : Set (MulAut ↥W)) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => InternalSec.autOn_normal_of hYK x hx k hk, fun hk => ?_⟩
    have := InternalSec.autOn_normal_of hYK x⁻¹ (X.inv_mem hx) _ hk
    simpa [mul_assoc] using this
  have hle : ⁅Ks, A⁆ ≤ Ks :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hAY.trans hXn)
  have hN : ((⁅Ks, A⁆ : Subgroup (MulAut ↥W)).subgroupOf Ks).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left Ks A)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((⁅Ks, A⁆ : Subgroup (MulAut ↥W)).subgroupOf Ks) with h | h
  · exfalso
    have hcomm : ⁅Ks, A⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hle hx⟩ : ↥Ks) ∈ (⁅Ks, A⁆ : Subgroup (MulAut ↥W)).subgroupOf Ks := hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
    set Cc := X ⊓ Subgroup.centralizer (Ks : Set (MulAut ↥W)) with hCc
    have hAC : A ≤ Cc := by
      intro a ha
      refine ⟨hAY ha, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have h1 : ⁅k, a⁆ ∈ ⁅Ks, A⁆ := Subgroup.commutator_mem_commutator hk ha
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hX2 := InternalSec.autOn_two_of (Y := Y) (U := W) (L := K) (hKY.trans hYW) h2
    have hZ : Subgroup.center ↥Ks = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Ks) with h' | h'
      · exact h'
      · exfalso
        obtain ⟨a, b, hab⟩ := hna
        exact hab (Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top b) a)
    have hCc2 : IsPGroup 2 ↥Cc := by
      intro c
      obtain ⟨e, he⟩ := hX2 c c.2.1
      refine ⟨e, Subtype.ext ?_⟩
      have hmem : (⟨(c : MulAut ↥W) ^ 2 ^ e, he⟩ : ↥Ks) ∈ Subgroup.center ↥Ks := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        have hc := Subgroup.mem_centralizer_iff.1 (Cc.pow_mem c.2 (2 ^ e)).2 k k.2
        simpa using hc
      rw [hZ, Subgroup.mem_bot] at hmem
      have := congrArg Subtype.val hmem
      simpa using this
    have hCcn : X ≤ Subgroup.normalizer (Cc : Set (MulAut ↥W)) := by
      have key : ∀ y ∈ X, ∀ c ∈ Cc, y * c * y⁻¹ ∈ Cc := by
        intro y hy c hc
        refine ⟨X.mul_mem (X.mul_mem hy hc.1) (X.inv_mem hy),
          Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
        have hk' : y⁻¹ * k * y ∈ Ks := by
          have := InternalSec.autOn_normal_of hYK y⁻¹ (X.inv_mem hy) k hk
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hk'
        calc k * (y * c * y⁻¹) = y * ((y⁻¹ * k * y) * c) * y⁻¹ := by group
          _ = y * (c * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
          _ = y * c * y⁻¹ * k := by group
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro c
      refine ⟨fun hc => key x hx c hc, fun hc => ?_⟩
      have := key x⁻¹ (X.inv_mem hx) _ hc
      simpa [mul_assoc] using this
    have hCcO : Cc ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCcn hCc2
    rw [hO2, le_bot_iff] at hCcO
    exact hA (le_bot_iff.1 (hCcO ▸ hAC))
  · refine le_antisymm hle fun x hx => ?_
    have : (⟨x, hx⟩ : ↥Ks) ∈ (⁅Ks, A⁆ : Subgroup (MulAut ↥W)).subgroupOf Ks := by
      rw [h]
      trivial
    exact this

end CFSG.Quasithin.AutOn
