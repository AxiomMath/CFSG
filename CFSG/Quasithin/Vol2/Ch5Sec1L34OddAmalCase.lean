module

public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizer_le_card {P Z : Subgroup G} {y : G}
    (h : ∀ u ∈ P, u * y * u⁻¹ * y⁻¹ ∈ Z) :
    (Subgroup.centralizer ({y} : Set G)).relIndex P ≤ Nat.card Z := by
  set K := (Subgroup.centralizer ({y} : Set G)).subgroupOf P with hK
  have key : ∀ a b : ↥P, a⁻¹ * b ∈ K ↔ (a : G) * y * (a : G)⁻¹ = b * y * (b : G)⁻¹ := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hab
      calc (a : G) * y * (a : G)⁻¹ = a * (y * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = a * ((a : G)⁻¹ * b * y) * (b : G)⁻¹ := by rw [hab]
        _ = b * y * (b : G)⁻¹ := by group
    · intro hab
      calc (a : G)⁻¹ * b * y = (a : G)⁻¹ * (b * y * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * (a * y * (a : G)⁻¹) * b := by rw [hab]
        _ = y * ((a : G)⁻¹ * b) := by group
  let F : ↥P ⧸ K → ↥Z := Quotient.lift (fun u : ↥P => (⟨u * y * (u : G)⁻¹ * y⁻¹, h u u.2⟩ : ↥Z))
    (fun a b hab => by
      have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
      apply Subtype.ext
      simp only
      rw [(key a b).mp hab'])
  have hF : Function.Injective F := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H a =>
      induction q using QuotientGroup.induction_on with
      | H b =>
        have h1 : (a : G) * y * (a : G)⁻¹ * y⁻¹ = b * y * (b : G)⁻¹ * y⁻¹ :=
          congrArg Subtype.val hpq
        have h2 : (a : G) * y * (a : G)⁻¹ = b * y * (b : G)⁻¹ := mul_right_cancel h1
        exact QuotientGroup.eq.mpr ((key a b).mpr h2)
  exact Nat.card_le_card_of_injective F hF

theorem amalgam_counting {n : ℕ} (hn : 1 ≤ n) {X Q Z U Z' U' D D' : Subgroup G}
    (hDU : D ≤ U) (hU'Q : ∀ y ∈ U', y ∈ Q ↔ y ∈ D') (hU'X : U' ≤ X)
    (hUNZ : U ≤ Subgroup.normalizer (Z : Set G)) (hU : IsElemAbelian 2 U)
    (hU' : IsElemAbelian 2 U') (hDD' : ∀ a ∈ D, ∀ b ∈ D', a * b = b * a)
    (hU'D : ∀ w ∈ U', ∀ d ∈ D, w * d * w⁻¹ * d⁻¹ ∈ Z')
    (hmNine : ∀ y ∈ X, y ∉ Q → y ^ 2 ∈ Q →
      2 ^ 9 ≤ (centralizerMod Z U (Subgroup.zpowers y)).relIndex U)
    (hrank : ∀ E : Subgroup G, E ≤ X → IsElemAbelian 2 E → Q.relIndex E ≤ 2 ^ 4)
    (𝒲' : Set (Subgroup G)) (hgen : ∀ S : Subgroup G, (∀ W ∈ 𝒲', W ≤ S) → U' ≤ S)
    (hWZ : ∀ W ∈ 𝒲', Z' ≤ W) (hWU : ∀ W ∈ 𝒲', W ≤ U')
    (hnat : ∀ W ∈ 𝒲', ∀ E : Subgroup G, E ≤ Subgroup.normalizer (W : Set G) → IsPGroup 2 E →
      (Subgroup.centralizer (W : Set G)).relIndex E ≤ 2 ^ n ∧
        (¬ E ≤ Subgroup.centralizer (W : Set G) →
          2 ^ n ≤ (Subgroup.centralizer (E : Set G)).relIndex W))
    (hlt : ∃ y ∈ U', y ∉ D') (hle : D.relIndex U ≤ D'.relIndex U') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ∀ {A B : Subgroup G}, A.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hsq : ∀ {y : G}, y ∈ U' → y ^ 2 ∈ Q := fun hy => by
    rw [hU'.2 _ hy]
    exact Q.one_mem
  have hU'D' : D'.relIndex U' ≤ 2 ^ 4 := by
    have h1 : D' ⊓ U' = Q ⊓ U' := by
      ext y
      exact ⟨fun hy => ⟨(hU'Q y hy.2).mpr hy.1, hy.2⟩, fun hy => ⟨(hU'Q y hy.2).mp hy.1, hy.2⟩⟩
    have h2 : D'.relIndex U' = Q.relIndex U' := by
      rw [← Subgroup.inf_relIndex_right, h1, Subgroup.inf_relIndex_right]
    rw [h2]
    exact hrank U' hU'X hU'
  by_cases hDU'Z : ∀ d ∈ D, ∀ w ∈ U', d * w * d⁻¹ * w⁻¹ ∈ Z
  · obtain ⟨y, hyU', hyD'⟩ := hlt
    have hyQ : y ∉ Q := fun h => hyD' ((hU'Q y hyU').mp h)
    have h9 := hmNine y (hU'X hyU') hyQ (hsq hyU')
    have hDC : D ≤ centralizerMod Z U (Subgroup.zpowers y) := by
      intro d hd
      refine ⟨hDU hd, hUNZ (hDU hd), fun w hw => ?_⟩
      exact hDU'Z d hd w ((Subgroup.zpowers_le.mpr hyU') hw)
    have h1 := Subgroup.relIndex_le_of_le_left hDC (hne (A := D) (B := U))
    omega
  push Not at hDU'Z
  obtain ⟨d₀, hd₀, w₀, hw₀, hdw₀⟩ := hDU'Z
  have hD2 : IsPGroup 2 D := fun x => ⟨1, Subtype.ext (by simpa using hU.2 _ (hDU x.2))⟩
  obtain ⟨W, hW𝒲, hWD⟩ : ∃ W ∈ 𝒲', ¬ D ≤ Subgroup.centralizer (W : Set G) := by
    by_contra hall
    push Not at hall
    have hU'C : U' ≤ Subgroup.centralizer (D : Set G) := hgen _ fun W hW => by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (Subgroup.mem_centralizer_iff.mp (hall W hW hd) w hw).symm
    apply hdw₀
    have hc := Subgroup.mem_centralizer_iff.mp (hU'C hw₀) d₀ hd₀
    rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    exact Z.one_mem
  have hDN : D ≤ Subgroup.normalizer (W : Set G) := by
    have hconj : ∀ d ∈ D, ∀ x ∈ W, d * x * d⁻¹ ∈ W := by
      intro d hd x hx
      have h1 : x * d * x⁻¹ * d⁻¹ ∈ W := hWZ W hW𝒲 (hU'D x (hWU W hW𝒲 hx) d hd)
      have e : d * x * d⁻¹ = (x * d * x⁻¹ * d⁻¹)⁻¹ * x := by group
      rw [e]
      exact W.mul_mem (W.inv_mem h1) hx
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj d hd x, fun hx => ?_⟩
    have := hconj d⁻¹ (D.inv_mem hd) _ hx
    simpa [mul_assoc] using this
  obtain ⟨hDW, hWD'⟩ := hnat W hW𝒲 D hDN hD2
  have hWC := hWD' hWD
  have hWW : W ≤ U' := hWU W hW𝒲
  have hWab : IsElemAbelian 2 W :=
    ⟨⟨⟨fun a b => Subtype.ext (F7.isElemAbelian_comm hU' (hWW a.2) (hWW b.2))⟩⟩,
      fun x hx => hU'.2 x (hWW hx)⟩
  have hQW : Q ⊓ W ≤ Subgroup.centralizer (D : Set G) ⊓ W := by
    rintro x ⟨hxQ, hxW⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun d hd => ?_, hxW⟩
    exact hDD' d hd x ((hU'Q x (hWW hxW)).mp hxQ)
  have hWQ : (Subgroup.centralizer (D : Set G)).relIndex W ≤ Q.relIndex W := by
    have h1 := Subgroup.relIndex_le_of_le_left (L := W) hQW (hne (A := Q ⊓ W) (B := W))
    rwa [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at h1
  have hn4 : 2 ^ n ≤ 2 ^ 4 := hWC.trans (hWQ.trans (hrank W (hWW.trans hU'X) hWab))
  obtain ⟨y, hyW, hyQ⟩ : ∃ y ∈ W, y ∉ Q := by
    by_contra hall
    push Not at hall
    have h1 : Q.relIndex W = 1 := Subgroup.relIndex_eq_one.mpr hall
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h9 := hmNine y (hU'X (hWW hyW)) hyQ (hsq (hWW hyW))
  have hDC : D ⊓ Subgroup.centralizer (W : Set G) ≤ centralizerMod Z U (Subgroup.zpowers y) := by
    rintro d ⟨hd, hdC⟩
    refine ⟨hDU hd, hUNZ (hDU hd), fun w hw => ?_⟩
    have hw' : w ∈ W := (Subgroup.zpowers_le.mpr hyW) hw
    have hc := Subgroup.mem_centralizer_iff.mp hdC w hw'
    rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
    exact Z.one_mem
  have h1 := Subgroup.relIndex_le_of_le_left hDC
    (hne (A := D ⊓ Subgroup.centralizer (W : Set G)) (B := U))
  have h2 : (D ⊓ Subgroup.centralizer (W : Set G)).relIndex U =
      (Subgroup.centralizer (W : Set G)).relIndex D * D.relIndex U := by
    rw [← Subgroup.relIndex_mul_relIndex _ D U inf_le_left hDU, Subgroup.inf_relIndex_left]
  have h3 : (Subgroup.centralizer (W : Set G)).relIndex D * D.relIndex U ≤ 2 ^ 4 * 2 ^ 4 :=
    Nat.mul_le_mul (hDW.trans hn4) (hle.trans hU'D')
  omega

end CFSG.Quasithin.H13
