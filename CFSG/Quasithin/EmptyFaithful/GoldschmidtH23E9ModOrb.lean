module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModVE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModOdd

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem eq_of_invariant_of_card_four {L B : Subgroup W} (hL : Nat.card L = 4) (hBL : B ≤ L)
    (hB : B ≠ ⊥) {ε : MulAut W} (hε : ∀ w ∈ B, ε w ∈ B)
    (hfree : ∀ w ∈ L, w ≠ 1 → ε w ≠ w) : B = L := by
  have hdvd : Nat.card B ∣ 4 := hL ▸ Subgroup.card_dvd_of_le hBL
  have hne1 : Nat.card B ≠ 1 := fun h => hB (Subgroup.card_eq_one.mp h)
  have hle : Nat.card B ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card B := Nat.card_pos
  have h24 : Nat.card B = 2 ∨ Nat.card B = 4 := by
    generalize Nat.card B = n at hdvd hne1 hle hpos
    interval_cases n <;> omega
  rcases h24 with h | h
  · exfalso
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥B)).mp h
    have hz1 : (y : W) ≠ 1 := fun e => hy (Subtype.ext e)
    have hεz : ε (y : W) ≠ 1 := fun e => hz1 (ε.injective (e.trans (map_one ε).symm))
    have e2 := huniq ⟨ε (y : W), hε y y.2⟩ (fun e => hεz (congrArg Subtype.val e))
    have e1 : ε (y : W) = y := congrArg Subtype.val e2
    exact hfree y (hBL y.2) hz1 e1
  · exact Subgroup.eq_of_le_of_card_ge hBL (by rw [h, hL])

omit [Finite W] in
theorem eps_quot_eq {ε : MulAut W} {l₁ l₂ : W} (hε₁ : ∀ w ∈ S.W₁, ε w = w) (hl₁ : l₁ ∈ S.W₁) :
    ε (l₁ * l₂) * (l₁ * l₂)⁻¹ = ε l₂ * l₂⁻¹ := by
  rw [map_mul, hε₁ l₁ hl₁]
  calc l₁ * ε l₂ * (l₁ * l₂)⁻¹ = (ε l₂ * l₂⁻¹) * (l₁ * l₁⁻¹) := by rw [mul_inv]; ac_rfl
    _ = ε l₂ * l₂⁻¹ := by rw [mul_inv_cancel, mul_one]

theorem eq_vEMod_of_orbit (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {x₁ x₂ ε₁ ε₂ t : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₂ : x₂ ∈ S.A₂) (hx₁2 : orderOf x₁ = 2) (hx₂2 : orderOf x₂ = 2)
    (hε₁f : ∀ w ∈ S.W₁, w ≠ 1 → ε₁ w ≠ w) (hε₁₂ : ∀ w ∈ S.W₂, ε₁ w = w)
    (hε₁W : ∀ w ∈ S.W₁, ε₁ w ∈ S.W₁) (hε₁V : ∀ w ∈ S.vEMod x₁ x₂, ε₁ w ∈ S.vEMod x₁ x₂)
    (hε₂f : ∀ w ∈ S.W₂, w ≠ 1 → ε₂ w ≠ w) (hε₂₁ : ∀ w ∈ S.W₁, ε₂ w = w)
    (hε₂W : ∀ w ∈ S.W₂, ε₂ w ∈ S.W₂) (hε₂V : ∀ w ∈ S.vEMod x₁ x₂, ε₂ w ∈ S.vEMod x₁ x₂)
    (ht : S.Swap₁₂ t) {U : Subgroup W} (hUV : U ≤ S.vEMod x₁ x₂)
    (hU₁ : ∀ w ∈ U, ε₁ w ∈ U) (hU₂ : ∀ w ∈ U, ε₂ w ∈ U) {w₀ : W} (hw₀ : w₀ ∈ U) (hw₀1 : w₀ ≠ 1)
    (htw : t w₀ = w₀) : U = S.vEMod x₁ x₂ := by
  have hL₁4 : Nat.card ↥(S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) = 4 :=
    S.card_fix_reflection₁ hW hcard hx₁ hx₁2
  have hL₂4 : Nat.card ↥(S.W₂ ⊓ fixV (Subgroup.zpowers x₂)) = 4 :=
    S.card_fix_reflection₂ hW hcard hx₂ hx₂2
  obtain ⟨l₁, hl₁, l₂, hl₂, hw⟩ := Subgroup.mem_sup.mp (hUV hw₀)
  have hl₂1 : l₂ ≠ 1 := by
    intro h
    have hw1 : w₀ ∈ S.W₁ := by rw [← hw, h, mul_one]; exact hl₁.1
    have h3 := ht.1 w₀ hw1
    rw [htw] at h3
    have h2 : w₀ ∈ S.W₁ ⊓ S.W₂ := ⟨hw1, h3⟩
    rw [S.winf, Subgroup.mem_bot] at h2
    exact hw₀1 h2
  have hl₁1 : l₁ ≠ 1 := by
    intro h
    have hw1 : w₀ ∈ S.W₂ := by rw [← hw, h, one_mul]; exact hl₂.1
    have h3 := ht.2 w₀ hw1
    rw [htw] at h3
    have h2 : w₀ ∈ S.W₁ ⊓ S.W₂ := ⟨h3, hw1⟩
    rw [S.winf, Subgroup.mem_bot] at h2
    exact hw₀1 h2
  have hL₂U : S.W₂ ⊓ fixV (Subgroup.zpowers x₂) ≤ U := by
    have hu : ε₂ w₀ * w₀⁻¹ = ε₂ l₂ * l₂⁻¹ := by
      rw [← hw]
      exact S.eps_quot_eq hε₂₁ hl₁.1
    have huU : ε₂ l₂ * l₂⁻¹ ∈ U := by
      rw [← hu]
      exact U.mul_mem (hU₂ w₀ hw₀) (U.inv_mem hw₀)
    have huL : ε₂ l₂ * l₂⁻¹ ∈ S.W₂ ⊓ fixV (Subgroup.zpowers x₂) := by
      rw [← S.vEMod_inf_W₂ x₁ x₂]
      exact ⟨hUV huU, S.W₂.mul_mem (hε₂W l₂ hl₂.1) (S.W₂.inv_mem hl₂.1)⟩
    have hu1 : ε₂ l₂ * l₂⁻¹ ≠ 1 := fun h => hε₂f l₂ hl₂.1 hl₂1 (mul_inv_eq_one.mp h)
    have hB : U ⊓ (S.W₂ ⊓ fixV (Subgroup.zpowers x₂)) = S.W₂ ⊓ fixV (Subgroup.zpowers x₂) := by
      refine eq_of_invariant_of_card_four (ε := ε₂) hL₂4 inf_le_right ?_ ?_ ?_
      · intro hbot
        have h3 : ε₂ l₂ * l₂⁻¹ ∈ U ⊓ (S.W₂ ⊓ fixV (Subgroup.zpowers x₂)) := ⟨huU, huL⟩
        rw [hbot, Subgroup.mem_bot] at h3
        exact hu1 h3
      · intro w hw
        refine ⟨hU₂ w hw.1, ?_⟩
        rw [← S.vEMod_inf_W₂ x₁ x₂]
        exact ⟨hε₂V w (hUV hw.1), hε₂W w hw.2.1⟩
      · exact fun w hw hw1 => hε₂f w hw.1 hw1
    exact inf_eq_right.mp hB
  have hL₁U : S.W₁ ⊓ fixV (Subgroup.zpowers x₁) ≤ U := by
    have hu : ε₁ w₀ * w₀⁻¹ = ε₁ l₁ * l₁⁻¹ := by
      rw [← hw, map_mul, hε₁₂ l₂ hl₂.1]
      calc ε₁ l₁ * l₂ * (l₁ * l₂)⁻¹ = (ε₁ l₁ * l₁⁻¹) * (l₂ * l₂⁻¹) := by rw [mul_inv]; ac_rfl
        _ = ε₁ l₁ * l₁⁻¹ := by rw [mul_inv_cancel, mul_one]
    have huU : ε₁ l₁ * l₁⁻¹ ∈ U := by
      rw [← hu]
      exact U.mul_mem (hU₁ w₀ hw₀) (U.inv_mem hw₀)
    have huL : ε₁ l₁ * l₁⁻¹ ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁) := by
      rw [← S.vEMod_inf_W₁ x₁ x₂]
      exact ⟨hUV huU, S.W₁.mul_mem (hε₁W l₁ hl₁.1) (S.W₁.inv_mem hl₁.1)⟩
    have hu1 : ε₁ l₁ * l₁⁻¹ ≠ 1 := fun h => hε₁f l₁ hl₁.1 hl₁1 (mul_inv_eq_one.mp h)
    have hB : U ⊓ (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) = S.W₁ ⊓ fixV (Subgroup.zpowers x₁) := by
      refine eq_of_invariant_of_card_four (ε := ε₁) hL₁4 inf_le_right ?_ ?_ ?_
      · intro hbot
        have h3 : ε₁ l₁ * l₁⁻¹ ∈ U ⊓ (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) := ⟨huU, huL⟩
        rw [hbot, Subgroup.mem_bot] at h3
        exact hu1 h3
      · intro w hw
        refine ⟨hU₁ w hw.1, ?_⟩
        rw [← S.vEMod_inf_W₁ x₁ x₂]
        exact ⟨hε₁V w (hUV hw.1), hε₁W w hw.2.1⟩
      · exact fun w hw hw1 => hε₁f w hw.1 hw1
    exact inf_eq_right.mp hB
  exact le_antisymm hUV (sup_le hL₁U hL₂U)

theorem odd_trivial_on_vE (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {x₁ x₂ ε : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₂ : x₂ ∈ S.A₂) (hx₁2 : orderOf x₁ = 2) (hx₂2 : orderOf x₂ = 2)
    (hε : ε ∈ Mb) (hε3 : orderOf ε = 3) (hε₁ : ∀ w ∈ S.W₁, ε w = w)
    (hεf : ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w) (hεa : ε * S.a₂ = S.a₂ * ε) {g : MulAut W}
    (hg : g ∈ ptFix (stabSub Mb (S.vEMod x₁ x₂)) (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)))
    (hodd : Odd (orderOf g)) (htriv : ∀ v ∈ S.vEMod x₁ x₂, g v = v) : g = 1 := by
  have hgε := S.odd_mem_zpowers_eps hW hcard hnorm hx₁ hx₂ hx₁2 hx₂2 hε hε3 hε₁ hεf hεa hg hodd
  by_contra hg1
  have hle : Subgroup.zpowers g ≤ Subgroup.zpowers ε := Subgroup.zpowers_le.mpr hgε
  have hcard' : Nat.card (Subgroup.zpowers ε) = 3 := by rw [Nat.card_zpowers, hε3]
  have hdvd : Nat.card (Subgroup.zpowers g) ∣ 3 := hcard' ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (Subgroup.zpowers g) ≠ 1 := by
    rw [Nat.card_zpowers]
    exact fun h => hg1 (orderOf_eq_one_iff.mp h)
  have h3 : Nat.card (Subgroup.zpowers g) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  have heq : Subgroup.zpowers g = Subgroup.zpowers ε :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hcard'])
  have hεg : ε ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers ε
  obtain ⟨z, hzL, hz1⟩ : ∃ z ∈ S.W₂ ⊓ fixV (Subgroup.zpowers x₂), z ≠ 1 := by
    by_contra hcon
    have hbot : S.W₂ ⊓ fixV (Subgroup.zpowers x₂) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    have h4 := S.card_fix_reflection₂ hW hcard hx₂ hx₂2
    omega
  have hzfix : g z = z := htriv z (Subgroup.mem_sup_right hzL)
  have hzp : z ∈ fixV (Subgroup.zpowers g) := mem_fixV_zpowers_iff.mpr hzfix
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hεg
  apply hεf z hzL.1 hz1
  rw [← hk]
  exact mem_fixV.mp hzp _ (Subgroup.zpow_mem_zpowers g k)

end CFSG.Quasithin.SixData151b
