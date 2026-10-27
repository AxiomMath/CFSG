module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterC0
public import CFSG.Walter.J1Props.Aut

public section

namespace CFSG.Quasithin.H13.S3320

open CFSG.QuasithinUnique CFSG.Walter.J1Props CFSG.Open

variable {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q}

omit [Finite Q] in
theorem eq_top_of_J1 [Y.Normal]
    (hC : Subgroup.centralizer (Y : Set Q) = ⊥) (eJ : ↥Y ≃* walterJ1) : Y = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, hg⟩ := J3_aut (MulAut.congr eJ (MulAut.conjNormal x))
  exact mem_of_congr_conjNormal_eq hC eJ hg

theorem not_J1 [Y.Normal]
    (hC : Subgroup.centralizer (Y : Set Q) = ⊥) (eJ : ↥Y ≃* walterJ1) {S H : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSH : S ≤ H)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) : False := by
  classical
  have hY := eq_top_of_J1 hC eJ
  obtain ⟨W, hWS, hW2, hWc, -, hSW, h₀, hh₀H, hh₀, -⟩ := o2_facts hS hab hSH e
  let E : Q ≃* walterJ1 := ((MulEquiv.subgroupCongr hY).trans Subgroup.topEquiv).symm.trans eJ
  have hQcard : Nat.card Q = 2 ^ 3 * 21945 := by
    rw [Nat.card_congr E.toEquiv, J1_card]
    norm_num
  obtain ⟨-, hS2, hSodd⟩ := hS
  obtain ⟨b, hb⟩ := hS2.exists_card_eq
  have hidx : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [hidx] at hSodd
  have hcop : Nat.Coprime 2 S.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSodd
  have h1 : 2 ^ b * S.index = 2 ^ 3 * 21945 := by
    rw [← hb, Subgroup.card_mul_index, hQcard]
  have hb3 : b = 3 := by
    have hA : 2 ^ b ∣ 2 ^ 3 :=
      (Nat.Coprime.pow_left b (by norm_num : Nat.Coprime 2 21945)).dvd_of_dvd_mul_right
        ⟨S.index, by rw [← h1, mul_comm]⟩
    have hB : 2 ^ 3 ∣ 2 ^ b :=
      (Nat.Coprime.pow_left 3 hcop).dvd_of_dvd_mul_right ⟨21945, by rw [h1, mul_comm]⟩
    exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hA)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hB)
  have hW4 : Nat.card W = 4 := by
    rw [hb, hb3] at hSW
    omega
  obtain ⟨w₁', hw₁'⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 (by rw [hW4]; norm_num)
  set w₁ : Q := (w₁' : Q) with hw₁def
  have hw₁W : w₁ ∈ W := w₁'.2
  have hw₁2 : orderOf w₁ = 2 := by rw [hw₁def, Subgroup.orderOf_coe, hw₁']
  obtain ⟨w₂, hw₂W, hw₂1, hw₂w₁⟩ : ∃ w₂ ∈ W, w₂ ≠ 1 ∧ w₂ ≠ w₁ := by
    by_contra hall
    push Not at hall
    let f : ↥W → Fin 2 := fun w => if (w : Q) = 1 then 0 else 1
    have hf : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      have hu := hall u u.2
      have hv := hall v v.2
      by_cases hu1 : (u : Q) = 1 <;> by_cases hv1 : (v : Q) = 1 <;>
        simp only [f, hu1, hv1, ↓reduceIte] at huv
      · rw [hu1, hv1]
      · exact absurd huv (by decide)
      · exact absurd huv (by decide)
      · rw [hu hu1, hv hv1]
    have := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    rw [hW4] at this
    omega
  set J := jankoHyp₀ with hJ
  have hEw₁ : orderOf (E w₁) = 2 := by rw [MulEquiv.orderOf_eq, hw₁2]
  obtain ⟨g, hg⟩ := J.exists_conj_eq_t hEw₁
  let c : Q ≃* walterJ1 := E.trans (MulAut.conj g)
  have hc : ∀ x, c x = g * E x * g⁻¹ := fun x => rfl
  have hcw₁ : c w₁ = J.t := by rw [hc, hg]
  have hh₀w : ∀ w ∈ W, h₀ * w = w * h₀ := fun w hw => hWc w hw h₀ hh₀H
  have hWab : w₂ * w₁ = w₁ * w₂ := hWc w₁ hw₁W w₂ (hSH (hWS hw₂W))
  have hct : ∀ x, x * w₁ = w₁ * x → c x ∈ Subgroup.centralizer ({J.t} : Set walterJ1) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hcw₁, ← map_mul, ← map_mul, hx]
  have hch₀3 : orderOf (c h₀) = 3 := by rw [MulEquiv.orderOf_eq, hh₀]
  have hch₀F : c h₀ ∈ J.F :=
    J.mem_F_of_odd (hct h₀ (hh₀w w₁ hw₁W)) (by rw [hch₀3]; decide)
  have hcw₂C := hct w₂ hWab
  have hcomm₂ : c h₀ * c w₂ = c w₂ * c h₀ := by rw [← map_mul, ← map_mul, hh₀w w₂ hw₂W]
  have hcommt : c h₀ * J.t = J.t * c h₀ := by
    rw [← hcw₁, ← map_mul, ← map_mul, hh₀w w₁ hw₁W]
  obtain ⟨k, hk⟩ := hW2 ⟨w₂, hw₂W⟩
  have hw₂k : w₂ ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hct2 : J.t ^ 2 = 1 := by rw [← J.orderOf_t, pow_orderOf_eq_one]
  obtain ⟨f, hfF, hf1, hfc, hf2⟩ : ∃ f ∈ J.F, f ≠ 1 ∧ c h₀ * f = f * c h₀ ∧
      f ^ 2 ^ (k + 1) = 1 := by
    have hcw₂k : c w₂ ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul, ← map_pow, hw₂k, map_one, one_pow]
    rcases J.mem_centralizer_t.mp hcw₂C with hF | hF
    · refine ⟨c w₂, hF, ?_, hcomm₂, hcw₂k⟩
      rw [Ne, MulEquiv.map_eq_one_iff]
      exact hw₂1
    · refine ⟨J.t * c w₂, hF, ?_, ?_, ?_⟩
      · intro h
        apply hw₂w₁
        apply c.injective
        rw [hcw₁, eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right J.t_mul_t]
      · rw [← mul_assoc, hcommt, mul_assoc, hcomm₂, mul_assoc]
      · have hcomm' : Commute J.t (c w₂) := (Subgroup.mem_centralizer_singleton_iff.mp hcw₂C).symm
        rw [hcomm'.mul_pow, hcw₂k, mul_one, pow_succ', pow_mul, hct2, one_pow]
  have hch₀1 : c h₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hch₀3
    omega
  have hch₀3' : c h₀ ^ 3 = 1 := by rw [← hch₀3, pow_orderOf_eq_one]
  have hfz := CFSG.Walter.J1.A5Sub.mem_zpowers_of_commute_three J.iso hch₀F hfF hch₀3' hch₀1 hfc
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hfz
  have hf3 : f ^ 3 = 1 := by
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hch₀3', one_zpow]
  have hord : orderOf f ∣ Nat.gcd 3 (2 ^ (k + 1)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf3) (orderOf_dvd_of_pow_eq_one hf2)
  rw [(Nat.Coprime.pow_right (k + 1) (by norm_num : Nat.Coprime 3 2)).gcd_eq_one,
    Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact hf1 hord

end CFSG.Quasithin.H13.S3320
