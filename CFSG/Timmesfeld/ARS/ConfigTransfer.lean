module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfig

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem special_of_commutator_mem [Finite G] (hR : IsRootClass R) {X Y : Subgroup G}
    (hX : X ∈ R) (hY : Y ∈ R) (hXY : X ≠ Y) (hC : ⁅X, Y⁆ ∈ R) : Special R X Y := by
  rcases hR.rel X hX Y hY hXY with hc | ho | hs
  · exact absurd (commuting_iff_commutator_eq_bot.1 hc) (hR.ne_bot _ hC)
  · exfalso
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
    obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hY
    have hodd := ho.odd_orderOf_mul (hR.mul_self X hX) hx hx1 hy hy1
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ ⁅X, Y⁆ := Subgroup.commutator_mem_commutator hx hy
    have hx' : x⁻¹ = x := hR.inv_eq hX hx
    have hy' : y⁻¹ = y := hR.inv_eq hY hy
    rw [hx', hy'] at hmem
    have h4 : (x * y) ^ 4 = 1 := by
      have := hR.mul_self _ hC _ hmem
      calc (x * y) ^ 4 = x * y * x * y * (x * y * x * y) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    have hdvd : orderOf (x * y) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have h1 : orderOf (x * y) = 1 := by
      have hle : orderOf (x * y) ∣ 2 ^ 2 := hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hle
      interval_cases k
      · simpa using hk'
      · rw [hk'] at hodd; exact absurd hodd (by decide)
      · rw [hk'] at hodd; exact absurd hodd (by decide)
    have hxy : x * y = 1 := orderOf_eq_one_iff.1 h1
    have hyx : y = x := by
      have := eq_inv_of_mul_eq_one_right hxy
      rw [this, hx']
    have hmem' : x ∈ X ⊓ Y := ⟨hx, hyx ▸ hy⟩
    rw [ho.inf_eq_bot, Subgroup.mem_bot] at hmem'
    exact hx1 hmem'
  · exact hs

variable {G' : Type*} [Group G'] {R' : Set (Subgroup G')}

theorem IsConfig.of_correspondence [Finite G'] (hR' : IsRootClass R')
    (π : Subgroup G → Subgroup G') {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ R)
    (hmap : ∀ X ∈ Δ, π X ∈ R') (hsurj : ∀ X' ∈ R', ∃ X ∈ Δ, π X = X')
    (hinj : Set.InjOn π Δ)
    (hcomm : ∀ X ∈ Δ, ∀ Y ∈ Δ, Commuting (π X) (π Y) → Commuting X Y)
    (hopp : ∀ X ∈ Δ, ∀ Y ∈ Δ, Opposite (π X) (π Y) → Opposite X Y)
    (hspec : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R' (π X) (π Y) → Special R X Y)
    (hcl : ∀ X ∈ Δ, ∀ Y ∈ Δ, Special R X Y → ⁅X, Y⁆ ∈ Δ ∧ π ⁅X, Y⁆ = ⁅π X, π Y⁆)
    {r : ℕ} {adj : Fin r → Fin r → Prop} {A' B' : Fin r → Subgroup G'}
    (hX' : IsConfig R' adj A' B') :
    ∃ A B : Fin r → Subgroup G, IsConfig R adj A B ∧
      ∀ k, A k ∈ Δ ∧ B k ∈ Δ ∧ π (A k) = A' k ∧ π (B k) = B' k := by
  choose! s hsΔ hsπ using hsurj
  have mA : ∀ k, s (A' k) ∈ Δ := fun k => hsΔ _ (hX'.memA k)
  have mB : ∀ k, s (B' k) ∈ Δ := fun k => hsΔ _ (hX'.memB k)
  have pA : ∀ k, π (s (A' k)) = A' k := fun k => hsπ _ (hX'.memA k)
  have pB : ∀ k, π (s (B' k)) = B' k := fun k => hsπ _ (hX'.memB k)
  have hceq : ∀ X ∈ Δ, ∀ Y ∈ Δ, ∀ Z ∈ Δ, X ≠ Y → ⁅π X, π Y⁆ = π Z → ⁅X, Y⁆ = Z := by
    intro X hX Y hY Z hZ hXY he
    have hXY' : π X ≠ π Y := fun e => hXY (hinj hX hY e)
    have hs' : Special R' (π X) (π Y) :=
      special_of_commutator_mem hR' (hmap X hX) (hmap Y hY) hXY' (he ▸ hmap Z hZ)
    obtain ⟨hmem, hπ⟩ := hcl X hX Y hY (hspec X hX Y hY hs')
    exact hinj hmem hZ (hπ.trans he)
  have hne : ∀ X' ∈ R', ∀ Y' : Subgroup G', ∀ Z' ∈ R', ⁅X', Y'⁆ = Z' → X' ≠ Y' := by
    rintro X' hX' Y' Z' hZ' he rfl
    rw [hR'.commutator_self_eq_bot hX'] at he
    exact hR'.ne_bot Z' hZ' he.symm
  refine ⟨fun k => s (A' k), fun k => s (B' k), ⟨fun k => hΔ (mA k), fun k => hΔ (mB k),
    fun k => hopp _ (mA k) _ (mB k) (by rw [pA, pB]; exact hX'.opp k),
    fun i j hij => ?_, fun i j hij h1 h2 => ?_⟩, fun k => ⟨mA k, mB k, pA k, pB k⟩⟩
  · obtain ⟨s1, c2, e3, c4, e5, s6⟩ := hX'.edge i j hij
    have hsA : Special R (s (A' i)) (s (A' j)) :=
      hspec _ (mA i) _ (mA j) (by rw [pA, pA]; exact s1)
    obtain ⟨hCΔ, hCπ⟩ := hcl _ (mA i) _ (mA j) hsA
    rw [pA, pA] at hCπ
    refine ⟨hsA, hcomm _ (mB i) _ (mA j) (by rw [pB, pA]; exact c2), ?_,
      hcomm _ (mA i) _ (mB j) (by rw [pA, pB]; exact c4), ?_,
      hspec _ (mB i) _ (mB j) (by rw [pB, pB]; exact s6)⟩
    · refine hceq _ (mB i) _ hCΔ _ (mA j) (fun e => ?_) (by rw [pB, hCπ, pA]; exact e3)
      have := congrArg π e
      rw [pB, hCπ] at this
      exact hne _ (hX'.memB i) _ _ (hX'.memA j) e3 this
    · refine hceq _ hCΔ _ (mB j) _ (mA i) (fun e => ?_) (by rw [hCπ, pB, pA]; exact e5)
      have h' : ⁅A' i, A' j⁆ = B' j := by
        have := congrArg π e
        rwa [pB, hCπ] at this
      rw [h'] at e5
      exact hne _ (hX'.memB j) _ _ (hX'.memA i) e5 rfl
  · obtain ⟨c1, c2, c3, c4⟩ := hX'.nonadj i j hij h1 h2
    exact ⟨hcomm _ (mA i) _ (mA j) (by rw [pA, pA]; exact c1),
      hcomm _ (mA i) _ (mB j) (by rw [pA, pB]; exact c2),
      hcomm _ (mB i) _ (mA j) (by rw [pB, pA]; exact c3),
      hcomm _ (mB i) _ (mB j) (by rw [pB, pB]; exact c4)⟩

end CFSG.Timmesfeld.ARS
