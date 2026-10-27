module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L128A

namespace HatU

variable {G : Type} [Group G]

open Classical in
noncomputable def eps (x : G) : ZMod 2 := if x = 1 then 0 else 1

theorem eps_of_eq_one {x : G} (h : x = 1) : eps x = 0 := by
  unfold eps
  simp [h]

theorem eps_of_ne_one {x : G} (h : x ≠ 1) : eps x = 1 := by
  unfold eps
  simp [h]

theorem eps_eq_zero_iff {x : G} : eps x = 0 ↔ x = 1 := by
  by_cases h : x = 1
  · exact ⟨fun _ => h, fun _ => eps_of_eq_one h⟩
  · refine ⟨fun h0 => ?_, fun h1 => absurd h1 h⟩
    rw [eps_of_ne_one h] at h0
    exact absurd h0 (by decide)

theorem eps_conj (x y : G) : eps (x * y * x⁻¹) = eps y := by
  by_cases hy : y = 1
  · rw [eps_of_eq_one hy, eps_of_eq_one (by simp [hy])]
  · rw [eps_of_ne_one hy, eps_of_ne_one]
    intro h
    exact hy (by simpa [mul_assoc] using congrArg (fun z => x⁻¹ * z * x) h)

theorem eps_inv (x : G) : eps x⁻¹ = eps x := by
  by_cases hx : x = 1
  · rw [eps_of_eq_one hx, eps_of_eq_one (by simp [hx])]
  · rw [eps_of_ne_one hx, eps_of_ne_one (by simpa using hx)]

theorem eps_mul [Finite G] {V₁ : Subgroup G} (hV : Nat.card V₁ = 2) {x y : G} (hx : x ∈ V₁)
    (hy : y ∈ V₁) : eps (x * y) = eps x + eps y := by
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, eps_of_eq_one rfl, zero_add]
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, eps_of_eq_one rfl, add_zero]
  have hxy : x = y := SteinbergBS.eq_of_card_le_two hV.le hx hy hx1 hy1
  subst hxy
  have h2 : x ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := ↥V₁) (x := ⟨x, hx⟩)
    rw [hV] at h
    simpa [Subtype.ext_iff] using h
  have h3 : x * x = 1 := by rw [← pow_two, h2]
  rw [h3, eps_of_eq_one rfl, eps_of_ne_one hx1]
  decide

theorem sq_eq_one_of_frattiniOf_eq_bot [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X)
    (h : frattiniOf X = ⊥) {x : G} (hx : x ∈ X) : x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥X) := ⟨hX⟩
  have h1 : (⟨x, hx⟩ : ↥X) ^ 2 ∈ frattini ↥X := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    exact Subgroup.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)
  have h3 : ((⟨x, hx⟩ : ↥X) ^ 2 : ↥X).1 ∈ frattiniOf X := ⟨_, h1, rfl⟩
  rw [h, Subgroup.mem_bot] at h3
  simpa using h3

variable {U V₁ : Subgroup G} (D : HatModelU U)

theorem sq_eq_of_π_eq (hZ : ∀ z ∈ centerOf U, z ^ 2 = 1) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (h : D.π a = D.π b) : a ^ 2 = b ^ 2 := by
  have hz : a⁻¹ * b ∈ centerOf U := (D.π_eq_iff a ha b hb).1 h
  have hcomm : a * (a⁻¹ * b) = (a⁻¹ * b) * a := Subgroup.mem_centralizer_iff.mp hz.2 a ha
  have e : b ^ 2 = a ^ 2 * (a⁻¹ * b) ^ 2 := by
    calc b ^ 2 = (a * (a⁻¹ * b)) * (a * (a⁻¹ * b)) := by rw [pow_two]; group
      _ = a * ((a⁻¹ * b) * a) * (a⁻¹ * b) := by group
      _ = a * (a * (a⁻¹ * b)) * (a⁻¹ * b) := by rw [← hcomm]
      _ = a ^ 2 * (a⁻¹ * b) ^ 2 := by simp only [pow_two]; group
  rw [e, hZ _ hz, mul_one]

theorem exists_quadratic [Finite G] (hV : Nat.card V₁ = 2) (hVc : V₁ ≤ centerOf U)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁) (hsq : ∀ a ∈ U, a ^ 2 ∈ V₁)
    (hZ : ∀ z ∈ centerOf U, z ^ 2 = 1) :
    ∃ q : D.V → ZMod 2, (∀ u ∈ U, q (D.π u) = eps (u ^ 2)) ∧
      (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
      ∀ (x : Subgroup.normalizer (U : Set G)) (v : D.V), q (D.ρ x v) = q v := by
  classical
  have hu₀ : ∀ v : D.V, Classical.choose (D.π_surj v) ∈ U ∧
      D.π (Classical.choose (D.π_surj v)) = v := fun v => Classical.choose_spec (D.π_surj v)
  have hq : ∀ u ∈ U, eps (Classical.choose (D.π_surj (D.π u)) ^ 2) = eps (u ^ 2) := by
    intro u hu
    rw [sq_eq_of_π_eq D hZ (hu₀ (D.π u)).1 hu (hu₀ (D.π u)).2]
  refine ⟨fun v => eps (Classical.choose (D.π_surj v) ^ 2), hq, ?_, ?_⟩
  · intro v w
    obtain ⟨a, ha, rfl⟩ := D.π_surj v
    obtain ⟨b, hb, rfl⟩ := D.π_surj w
    simp only
    rw [← D.π_mul a ha b hb, hq _ (U.mul_mem ha hb), hq a ha, hq b hb]
    have hB : D.B (D.π a) (D.π b) = eps (a * b * a⁻¹ * b⁻¹) :=
      zmod_two_eq_of_iff ((D.B_spec a ha b hb).trans eps_eq_zero_iff.symm)
    have hc : a * b * a⁻¹ * b⁻¹ ∈ V₁ := hcomm a ha b hb
    have hci : Commute a (a * b * a⁻¹ * b⁻¹)⁻¹ :=
      (show Commute a (a * b * a⁻¹ * b⁻¹) from
        Subgroup.mem_centralizer_iff.mp (hVc hc).2 a ha).inv_right
    have e1 : (a * b) ^ 2 = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a ^ 2 * b ^ 2) := by
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
        _ = a * ((a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b)) * b := by group
        _ = (a * (a * b * a⁻¹ * b⁻¹)⁻¹) * (a * b) * b := by group
        _ = ((a * b * a⁻¹ * b⁻¹)⁻¹ * a) * (a * b) * b := by rw [hci.eq]
        _ = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a ^ 2 * b ^ 2) := by simp only [pow_two]; group
    rw [e1, eps_mul hV (V₁.inv_mem hc) (V₁.mul_mem (hsq a ha) (hsq b hb)),
      eps_mul hV (hsq a ha) (hsq b hb), eps_inv, hB]
    ring
  · intro x v
    obtain ⟨a, ha, rfl⟩ := D.π_surj v
    simp only
    rw [D.ρ_π x a ha, hq _ (conj_mem x.2 ha), hq a ha]
    have e : ((x : G) * a * (x : G)⁻¹) ^ 2 = (x : G) * a ^ 2 * (x : G)⁻¹ := by
      simp only [pow_two]; group
    rw [e, eps_conj]

end HatU

end L128A

theorem lemma12_8_8_two_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : Lemma12_8_8_two := by
  intro G _ _ T L V n V₁ V₂ hs D
  have hA := hs.almostSpecial h1222 h12213
  refine ⟨L128A.HatU.B_isAlt D, L128A.HatU.B_nondegenerate D, ?_, ?_⟩
  · intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
  · intro hΦ
    have hU2 : IsPGroup 2 ↥(u128 V V₁) := hs.hyp.hyp.sylow.1.to_le hA.G22_three.1
    have hZ : ∀ z ∈ zU128 V V₁, z ^ 2 = 1 := fun z hz =>
      L128A.HatU.sq_eq_one_of_frattiniOf_eq_bot (hU2.to_le inf_le_left) hΦ hz
    obtain ⟨q, hq1, hq2, hq3⟩ := L128A.HatU.exists_quadratic D (by simpa using hs.v1.2.1)
      (hs.le_centerOf h1222 h12213) (fun a ha b hb => hA.G22_commutator_mem ha hb)
      (fun a ha => hA.G22_sq_mem ha) hZ
    refine ⟨q, fun u hu => ?_, hq2, fun γ hγ v => ?_⟩
    · rw [hq1 u hu, L128A.HatU.eps_eq_zero_iff]
    · obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
      exact hq3 ⟨x, hxN⟩ v

end CFSG.Quasithin.H13
