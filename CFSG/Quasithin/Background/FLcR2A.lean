module

public import CFSG.Quasithin.Background.FLcP0Main

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

theorem sq_centralizes {A B : Subgroup G} {x : G} (hAB : A ≤ B) (hA : Nat.card ↥A = 2)
    (hB : Nat.card ↥B = 4) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) : ∀ w ∈ B, x ^ 2 * w * (x ^ 2)⁻¹ = w := by
  have hA1 : ∀ a ∈ A, ∀ a' ∈ A, a ≠ 1 → a' ≠ 1 → a = a' := by
    intro a ha a' ha' h1 h2
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).1 hA
    have e1 : (⟨a, ha⟩ : ↥A) = y := huniq _ (fun h => h1 (congrArg Subtype.val h))
    have e2 : (⟨a', ha'⟩ : ↥A) = y := huniq _ (fun h => h2 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hxa : ∀ a ∈ A, x * a * x⁻¹ = a := by
    intro a ha
    by_cases h1 : a = 1
    · subst h1
      simp
    · have hxa' : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hxA a).1 ha
      have hne : x * a * x⁻¹ ≠ 1 := fun h => h1 (by simpa using h)
      exact hA1 _ hxa' a ha hne h1
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h0 : (⟨a, ha⟩ : ↥A) ^ Nat.card ↥A = 1 := pow_card_eq_one'
    rw [hA] at h0
    have h := congrArg Subtype.val h0
    simpa [pow_two] using h
  have hidx : (A.subgroupOf B).index = 2 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf B)
    have h2 : Nat.card ↥(A.subgroupOf B) = 2 := by
      rw [← hA]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
    rw [h2, hB] at h1
    omega
  intro w hw
  by_cases hwA : w ∈ A
  · have h1 := hxa w hwA
    calc x ^ 2 * w * (x ^ 2)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by rw [pow_two]; group
      _ = w := by rw [h1, h1]
  · have hxw : x * w * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hxB w).1 hw
    have hxwA : x * w * x⁻¹ ∉ A := fun h => hwA ((Subgroup.mem_normalizer_iff.1 hxA w).2 h)
    have hmem : w⁻¹ * (x * w * x⁻¹) ∈ A := by
      have hmem' : (⟨w⁻¹, B.inv_mem hw⟩ : ↥B) * ⟨x * w * x⁻¹, hxw⟩ ∈ A.subgroupOf B := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        constructor
        · intro h
          exact absurd (inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 h)) hwA
        · intro h
          exact absurd (Subgroup.mem_subgroupOf.1 h) hxwA
      exact hmem'
    calc x ^ 2 * w * (x ^ 2)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by rw [pow_two]; group
      _ = x * (w * (w⁻¹ * (x * w * x⁻¹))) * x⁻¹ := by group
      _ = (x * w * x⁻¹) * (x * (w⁻¹ * (x * w * x⁻¹)) * x⁻¹) := by group
      _ = (x * w * x⁻¹) * (w⁻¹ * (x * w * x⁻¹)) := by rw [hxa _ hmem]
      _ = w * ((w⁻¹ * (x * w * x⁻¹)) * (w⁻¹ * (x * w * x⁻¹))) := by group
      _ = w := by rw [hsq _ hmem, mul_one]

theorem odd_mem_centralizer {A B : Subgroup G} {x : G} (hAB : A ≤ B) (hA : Nat.card ↥A = 2)
    (hB : Nat.card ↥B = 4) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ Subgroup.centralizer (B : Set G) := by
  obtain ⟨k, hk⟩ := hodd
  have hx2 : x ^ 2 ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := sq_centralizes hAB hA hB hxA hxB w hw
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hxe : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    have h : x ^ (2 * (k + 1)) = x ^ (orderOf x + 1) := by
      congr 1
      omega
    rw [h, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hxe]
  exact Subgroup.pow_mem _ hx2 _

theorem pCoreOf_oTwoUpper_le [Finite G] {S P' C : Subgroup G} (hS : pCoreOf 2 P' ≤ S)
    (hY : oTwoUpper P' ≤ C) : pCoreOf 2 (oTwoUpper P') ≤ S ⊓ C := by
  refine le_inf ?_ ((pCoreOf_le 2 (oTwoUpper P')).trans hY)
  have hRP : pCoreOf 2 (oTwoUpper P') ≤ P' := (pCoreOf_le 2 (oTwoUpper P')).trans (oTwoUpper_le P')
  have hnorm : P' ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper P') : Set G) :=
    Subgroup.le_normalizer.trans ((normalizer_le_normalizer_oTwoUpper P').trans
      (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper P')))
  exact (le_pCoreOf_of_le_normalizer 2 hRP hnorm (pCoreOf_isPGroup 2 (oTwoUpper P'))).trans hS

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem W_one_le_two : W 1 ≤ W 2 := by
  have hn : 3 ≤ n := D.three_le
  intro y hy
  obtain ⟨hyU, hyF⟩ := (D.W_mem le_rfl (by omega) y).1 hy
  exact (D.W_mem (by norm_num) (by omega) y).2 ⟨hyU, flagSpace_mono (by norm_num) hyF⟩

theorem pCoreOf_le_S_node [Finite G] (i : ℕ) : pCoreOf 2 (parab (L ⊔ S) n W i) ≤ S := by
  have hsyl : IsSylowTwoOf S (parab (L ⊔ S) n W i) :=
    isSylowTwoOf_restrict D.syl (D.S_le_parab i) (parab_le _ _ _ _)
  refine A4.le_of_normal_of_isSylowTwoOf hsyl (pCoreOf_le 2 _) ?_ (pCoreOf_isPGroup 2 _)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).2
    (le_normalizer_pCoreOf 2 _)

theorem rank2_a [Finite G] (hn4 : 4 ≤ n) :
    pCoreOf 2 (oTwoUpper (parab (L ⊔ S) n W (n - 1))) ≤ pCoreOf 2 (parab (L ⊔ S) n W 1) := by
  have hN1 : ∀ x ∈ parab (L ⊔ S) n W (n - 1), x ∈ Subgroup.normalizer (W 1 : Set G) := fun x hx =>
    (mem_parab.1 hx).2 1 le_rfl (by omega) (by omega)
  have hN2 : ∀ x ∈ parab (L ⊔ S) n W (n - 1), x ∈ Subgroup.normalizer (W 2 : Set G) := fun x hx =>
    (mem_parab.1 hx).2 2 (by omega) (by omega) (by omega)
  have hW1c : Nat.card ↥(W 1) = 2 := by
    rw [D.W_card 1 le_rfl (by omega)]
    norm_num
  have hW2c : Nat.card ↥(W 2) = 4 := by
    rw [D.W_card 2 (by norm_num) (by omega)]
    norm_num
  have hY : oTwoUpper (parab (L ⊔ S) n W (n - 1)) ≤ Subgroup.centralizer (W 2 : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact odd_mem_centralizer D.W_one_le_two hW1c hW2c (hN1 x hx.1) (hN2 x hx.1) hx.2
  rw [D.pCoreOf_eq]
  exact pCoreOf_oTwoUpper_le (D.pCoreOf_le_S_node (n - 1)) hY

end P0Setup

end CFSG.Quasithin.FLc
