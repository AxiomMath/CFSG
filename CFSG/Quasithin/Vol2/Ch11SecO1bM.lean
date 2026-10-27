module

public import CFSG.Quasithin.Vol2.Ch11SecO1bL
public import CFSG.Quasithin.Vol2.Ch11SecO1bK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

variable {G : Type} [Group G] {V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M]
  [Module K M]

@[expose] def twistSub (σ : K →+* K) (α γ : K) : AddSubgroup K where
  carrier := {x | σ x * α = γ * x}
  add_mem' := fun {x y} (hx : σ x * α = γ * x) (hy : σ y * α = γ * y) =>
    show σ (x + y) * α = γ * (x + y) by rw [map_add, add_mul, hx, hy, mul_add]
  zero_mem' := show σ 0 * α = γ * 0 by rw [map_zero, zero_mul, mul_zero]
  neg_mem' := fun {x} (hx : σ x * α = γ * x) =>
    show σ (-x) * α = γ * (-x) by rw [map_neg, neg_mul, hx, mul_neg]

theorem mem_twistSub {σ : K →+* K} {α γ x : K} : x ∈ twistSub σ α γ ↔ σ x * α = γ * x :=
  Iff.rfl

theorem mul_mem_centralizer [Finite K] [CharP K 2] {f : ↥V → M} (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) {u₀ : M} (hu₀ : u₀ ≠ 0) {V₁ : Subgroup G} (hV₁V : V₁ ≤ V)
    (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀) {a b : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (haV₁ : a ∈ Subgroup.normalizer (V₁ : Set G)) (hbV₁ : b ∈ Subgroup.normalizer (V₁ : Set G))
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab2 : (a * b) ^ 2 = 1)
    (ha : ∃ (T : M →+ M) (σ : K →+* K), (∀ (c : K) (x : M), T (c • x) = σ c • T x) ∧
      ∀ w, T (f w) = f (SecA.conjV V a haV w))
    (hb : ∃ (T : M →+ M) (σ : K →+* K), (∀ (c : K) (x : M), T (c • x) = σ c • T x) ∧
      ∀ w, T (f w) = f (SecA.conjV V b hbV w))
    (haC : a ∉ Subgroup.centralizer (V₁ : Set G)) (hbC : b ∉ Subgroup.centralizer (V₁ : Set G)) :
    a * b ∈ Subgroup.centralizer (V₁ : Set G) := by
  obtain ⟨Ta, σa, hσa, hTa⟩ := ha
  obtain ⟨Tb, σb, hσb, hTb⟩ := hb
  obtain ⟨αa, h0a, -, hσσa, hααa⟩ := exists_scalar_inv hsurj hu₀ hV₁ haV haV₁ ha2 hσa hTa
  obtain ⟨αb, h0b, -, hσσb, hααb⟩ := exists_scalar_inv hsurj hu₀ hV₁ hbV hbV₁ hb2 hσb hTb
  have hea := exists_ne_of_not_mem_centralizer hinj hV₁V hV₁ haV hσa hTa h0a hααa haC
  have heb := exists_ne_of_not_mem_centralizer hinj hV₁V hV₁ hbV hσb hTb h0b hααb hbC
  have heq := eq_of_involution hσσa hσσb hea heb
  have habV : a * b ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ haV hbV
  have hform : ∀ (v : ↥V) (c : K), f v = c • u₀ →
      f (SecA.conjV V (a * b) habV v) = (c * (σa αb * αa)) • u₀ := by
    intro v c hv
    rw [conjV_mul_apply haV hbV, ← hTa, ← hTb, hv, hσb, h0b, smul_smul, hσa, h0a, smul_smul,
      map_mul, ← heq c, hσσa c, mul_assoc]
  obtain ⟨v₀, hv₀⟩ := hsurj u₀
  have h1 := hform v₀ 1 (by rw [hv₀, one_smul])
  rw [one_mul] at h1
  have h2 := hform _ _ h1
  rw [conjV_conjV_of_sq habV hab2, hv₀] at h2
  have hl : σa αb * αa = 1 := by
    refine eq_one_of_mul_self (coeff_eq_of_smul_eq hu₀ ?_).symm
    rw [one_smul]
    exact h2
  refine mem_centralizer_of_fixes hinj hV₁V habV fun v hv => ?_
  obtain ⟨c, hc⟩ := (hV₁ v).mp hv
  rw [hform v c hc, hl, mul_one, hc]

theorem rankV2_of_coords [Finite K] [CharP K 2] {f : ↥V → M} (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) {u₀ u₁ : M}
    (hind : ∀ c d : K, c • u₀ + d • u₁ = 0 → c = 0 ∧ d = 0) {V₁ V₂ : Subgroup G}
    (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀)
    (hV₂ : ∀ v : ↥V, (v : G) ∈ V₂ ↔ ∃ c d : K, f v = c • u₀ + d • u₁) {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hAV₁ : A ≤ Subgroup.normalizer (V₁ : Set G)) (hAV₂ : A ≤ Subgroup.normalizer (V₂ : Set G))
    (hsemi : ∀ a (ha : a ∈ A), ∃ (T : M →+ M) (σ : K →+* K),
      (∀ (c : K) (x : M), T (c • x) = σ c • T x) ∧
        ∀ w, T (f w) = f (SecA.conjV V a (hAV ha) w)) :
    (A ⊓ Subgroup.centralizer (V₂ : Set G)).relIndex A ≤ Nat.card K := by
  have hu₀ : u₀ ≠ 0 := fun h =>
    one_ne_zero (hind 1 0 (by rw [h, smul_zero, zero_smul, add_zero])).1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2
  have hV₁₂ : V₁ ≤ V₂ := fun v hv => by
    obtain ⟨c, hc⟩ := (hV₁ ⟨v, hV₁V hv⟩).mp hv
    exact (hV₂ ⟨v, hV₁V hv⟩).mpr ⟨c, 0, by rw [hc, zero_smul, add_zero]⟩
  set A₁ := A ⊓ Subgroup.centralizer (V₁ : Set G) with hA₁
  set C₂ := A ⊓ Subgroup.centralizer (V₂ : Set G) with hC₂
  have hC₂A₁ : C₂ ≤ A₁ :=
    inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV₁₂))
  have hA₁A : A₁ ≤ A := inf_le_left
  rw [← Subgroup.relIndex_mul_relIndex C₂ A₁ A hC₂A₁ hA₁A]
  obtain ⟨w₁, hw₁⟩ := hsurj u₁
  have htr : ∀ b (hb : b ∈ A₁), ∃ s : K, ∀ (v : ↥V) (x y : K), f v = x • u₀ + y • u₁ →
      f (SecA.conjV V b (hAV (hA₁A hb)) v) = (x + y * s) • u₀ + y • u₁ := fun b hb => by
    obtain ⟨T, σ, hσ, hT⟩ := hsemi b (hA₁A hb)
    exact exists_transv hsurj hind hV₁ hV₂ _ (hAV₂ (hA₁A hb)) (Subgroup.mem_inf.mp hb).2
      (hA2 b (hA₁A hb)) hσ hT
  have hfib : ∀ S : AddSubgroup K, (∀ b (hb : b ∈ A₁) (s : K),
      f (SecA.conjV V b (hAV (hA₁A hb)) w₁) = s • u₀ + u₁ → s ∈ S) →
      C₂.relIndex A₁ ≤ Nat.card S := by
    intro S hS
    refine relIndex_le_card_of_fiber (S := ↥S)
      (fun s b => f (SecA.conjV V b (hAV (hA₁A b.2)) w₁) = (s : K) • u₀ + u₁) (fun b => ?_) ?_
    · obtain ⟨s, hs⟩ := htr b b.2
      have h := hs w₁ 0 1 (by rw [hw₁, zero_smul, zero_add, one_smul])
      rw [zero_add, one_mul, one_smul] at h
      exact ⟨⟨s, hS b b.2 s h⟩, h⟩
    · intro s b b' hb hb'
      have he := congrArg Subtype.val (hinj (hb.trans hb'.symm))
      simp only [SecA.conjV_apply_coe] at he
      have hcA₁ : ((b⁻¹ * b' : ↥A₁) : G) ∈ A₁ := (b⁻¹ * b').2
      obtain ⟨s', hs'⟩ := htr _ hcA₁
      have hfix : SecA.conjV V ((b⁻¹ * b' : ↥A₁) : G) (hAV (hA₁A hcA₁)) w₁ = w₁ := by
        apply Subtype.ext
        rw [SecA.conjV_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv]
        calc (b : G)⁻¹ * b' * w₁ * ((b : G)⁻¹ * b')⁻¹ =
            (b : G)⁻¹ * (b' * w₁ * (b' : G)⁻¹) * b := by group
          _ = (b : G)⁻¹ * (b * w₁ * (b : G)⁻¹) * b := by rw [← he]
          _ = w₁ := by group
      have h := hs' w₁ 0 1 (by rw [hw₁, zero_smul, zero_add, one_smul])
      rw [hfix, hw₁] at h
      have hs0 : s' = 0 := by
        have h3 := (coord_eq hind (c := 0) (d := 1)
          ((by rw [zero_smul, zero_add, one_smul] : (0 : K) • u₀ + (1 : K) • u₁ = u₁).trans h)).1
        simpa using h3.symm
      refine Subgroup.mem_inf.mpr ⟨hA₁A hcA₁,
        mem_centralizer_of_fixes hinj hV₂V (hAV (hA₁A hcA₁)) fun v hv => ?_⟩
      obtain ⟨x, y, hxy⟩ := (hV₂ v).mp hv
      rw [hs' v x y hxy, hxy, hs0, mul_zero, add_zero]
  by_cases hAC : A ≤ Subgroup.centralizer (V₁ : Set G)
  · rw [Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hAC), mul_one]
    have h := hfib ⊤ fun _ _ _ _ => AddSubgroup.mem_top _
    rwa [AddSubgroup.card_top] at h
  obtain ⟨a₁, ha₁A, ha₁C⟩ := Set.not_subset.mp hAC
  obtain ⟨T₁, σ₁, hσ₁, hT₁⟩ := hsemi a₁ ha₁A
  obtain ⟨α₁, h0, -, -, hαα⟩ :=
    exists_scalar_inv hsurj hu₀ hV₁ (hAV ha₁A) (hAV₁ ha₁A) (hA2 a₁ ha₁A) hσ₁ hT₁
  have hσne := exists_ne_of_not_mem_centralizer hinj hV₁V hV₁ (hAV ha₁A) hσ₁ hT₁ h0 hαα ha₁C
  have hw₁V₂ : (w₁ : G) ∈ V₂ := (hV₂ w₁).mpr ⟨0, 1, by rw [hw₁, zero_smul, zero_add, one_smul]⟩
  obtain ⟨β₁, γ₁, hβγ⟩ := (hV₂ _).mp (show ((SecA.conjV V a₁ (hAV ha₁A) w₁ : ↥V) : G) ∈ V₂ by
    rw [SecA.conjV_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hAV₂ ha₁A) w₁).mp hw₁V₂)
  have h1 : T₁ u₁ = β₁ • u₀ + γ₁ • u₁ := by rw [← hw₁, hT₁, hβγ, hw₁]
  have hSne : twistSub σ₁ α₁ γ₁ ≠ ⊤ := by
    intro hS
    have hmem : ∀ x, σ₁ x * α₁ = γ₁ * x := fun x => by
      have hx : x ∈ twistSub σ₁ α₁ γ₁ := by
        rw [hS]
        exact AddSubgroup.mem_top x
      exact mem_twistSub.mp hx
    have hγ : α₁ = γ₁ := by simpa using hmem 1
    have hα0 : α₁ ≠ 0 := fun h => by
      rw [h, mul_zero] at hαα
      exact zero_ne_one hαα
    obtain ⟨x, hx⟩ := hσne
    apply hx
    have h2 := hmem x
    rw [← hγ] at h2
    exact mul_right_cancel₀ hα0 (h2.trans (mul_comm _ _))
  have hbS : ∀ b (hb : b ∈ A₁) (s : K), f (SecA.conjV V b (hAV (hA₁A hb)) w₁) = s • u₀ + u₁ →
      s ∈ twistSub σ₁ α₁ γ₁ := by
    intro b hb s hs
    obtain ⟨s', hs'⟩ := htr b hb
    have h2 := hs' w₁ 0 1 (by rw [hw₁, zero_smul, zero_add, one_smul])
    rw [hs, zero_add, one_mul, one_smul] at h2
    have hss : s = s' :=
      (coord_eq hind (d := 1) (d' := 1) (by simpa only [one_smul] using h2)).1
    rw [← hss] at hs'
    have hbA := hA₁A hb
    have hcomm : a₁ * b = b * a₁ := congrArg Subtype.val (hA.1.is_comm.comm ⟨a₁, ha₁A⟩ ⟨b, hbA⟩)
    have hc : SecA.conjV V a₁ (hAV ha₁A) (SecA.conjV V b (hAV hbA) w₁) =
        SecA.conjV V b (hAV hbA) (SecA.conjV V a₁ (hAV ha₁A) w₁) := by
      apply Subtype.ext
      simp only [SecA.conjV_apply_coe]
      calc a₁ * (b * w₁ * b⁻¹) * a₁⁻¹ = (a₁ * b) * w₁ * (a₁ * b)⁻¹ := by group
        _ = (b * a₁) * w₁ * (b * a₁)⁻¹ := by rw [hcomm]
        _ = b * (a₁ * w₁ * a₁⁻¹) * b⁻¹ := by group
    have hL : f (SecA.conjV V a₁ (hAV ha₁A) (SecA.conjV V b (hAV hbA) w₁)) =
        (σ₁ s * α₁ + β₁) • u₀ + γ₁ • u₁ := by
      rw [← hT₁, hs, map_add, hσ₁, h0, h1, smul_smul, add_smul]
      abel
    rw [hc, hs' _ β₁ γ₁ hβγ] at hL
    have h3 := (coord_eq hind hL).1
    exact mem_twistSub.mpr (by linear_combination -h3)
  have hidx : A₁.relIndex A ≤ 2 := by
    refine relIndex_le_two_of_mul_mem fun a ha b hb haA₁ hbA₁ => ?_
    have haC : a ∉ Subgroup.centralizer (V₁ : Set G) := fun h =>
      haA₁ (Subgroup.mem_inf.mpr ⟨ha, h⟩)
    have hbC : b ∉ Subgroup.centralizer (V₁ : Set G) := fun h =>
      hbA₁ (Subgroup.mem_inf.mpr ⟨hb, h⟩)
    exact Subgroup.mem_inf.mpr ⟨A.mul_mem ha hb, mul_mem_centralizer hinj hsurj hu₀ hV₁V hV₁
      (hAV ha) (hAV hb) (hAV₁ ha) (hAV₁ hb) (hA2 a ha) (hA2 b hb) (hA2 _ (A.mul_mem ha hb))
      (hsemi a ha) (hsemi b hb) haC hbC⟩
  have hS2 := card_le_half hSne
  calc C₂.relIndex A₁ * A₁.relIndex A ≤ Nat.card (twistSub σ₁ α₁ γ₁) * 2 :=
      Nat.mul_le_mul (hfib _ hbS) hidx
    _ ≤ Nat.card K := by omega

end CFSG.Quasithin.Vol2.Ch11.SecO1b
