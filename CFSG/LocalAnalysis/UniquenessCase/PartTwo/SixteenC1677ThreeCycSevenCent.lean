module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s168e3_cyc7_card_autSub_dvd [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup W}
    (hY : Nat.card ↥Y = 8) {x : MulAut W} (hxY : x ∈ stabSub Y) (hx7 : x ^ 7 = 1)
    (hxn : ∃ y ∈ Y, x y ≠ y) {H : Subgroup (MulAut W)} (hH : H ≤ stabSub Y)
    (hHx : ∀ h ∈ H, h * x = x * h) : Nat.card ↥(autSub H Y) ∣ 7 := by
  have h2Y : ∀ v : ↥Y, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW (v : W))
  let xb : MulAut ↥Y := resHom Y ⟨x, hxY⟩
  have hxb7 : xb ^ 7 = 1 := by
    show resHom Y ⟨x, hxY⟩ ^ 7 = 1
    rw [← map_pow]
    have h : (⟨x, hxY⟩ : stabSub Y) ^ 7 = 1 := Subtype.ext hx7
    rw [h, map_one]
  have hxb1 : xb ≠ 1 := by
    intro h1
    have h1' : resHom Y ⟨x, hxY⟩ = 1 := h1
    obtain ⟨y, hyY, hxy⟩ := hxn
    have h2 := congrArg (fun (φ : MulAut ↥Y) => ((φ ⟨y, hyY⟩ : ↥Y) : W)) h1'
    simp only [MulAut.one_apply] at h2
    rw [resHom_apply] at h2
    exact hxy (by simpa using h2)
  have hxb_order : orderOf xb = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hxb7 hxb1
  let Q : Subgroup (MulAut ↥Y) := Subgroup.zpowers xb
  have hQ : Nat.card Q = 7 := by
    show Nat.card (Subgroup.zpowers xb) = 7
    rw [Nat.card_zpowers, hxb_order]
  have hcomm_of : ∀ φ ∈ autSub H Y, Commute φ xb := by
    intro φ hφ
    obtain ⟨hs, hhsH, hres⟩ := mem_autSub.mp hφ
    have hhx : (hs : MulAut W) * x = x * (hs : MulAut W) := hHx (hs : MulAut W) hhsH
    have hcalc : φ * xb = xb * φ := by
      calc φ * xb = resHom Y hs * resHom Y ⟨x, hxY⟩ := by
              rw [show φ = resHom Y hs from hres.symm]
           _ = resHom Y (hs * ⟨x, hxY⟩) := by rw [← map_mul]
           _ = resHom Y (⟨x, hxY⟩ * hs) := by
                 rw [show hs * ⟨x, hxY⟩ = ⟨x, hxY⟩ * hs from Subtype.ext hhx]
           _ = resHom Y ⟨x, hxY⟩ * resHom Y hs := by rw [map_mul]
           _ = xb * φ := by rw [hres]
    exact hcalc
  have hcent : autSub H Y ≤ Subgroup.centralizer (Q : Set (MulAut ↥Y)) := by
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    exact (((hcomm_of φ hφ).zpow_right n).symm).eq
  have hle : autSub H Y ≤ normalizer (Q : Set (MulAut ↥Y)) :=
    le_trans hcent (Subgroup.centralizer_le_normalizer (Q : Set (MulAut ↥Y)))
  have h21 : Nat.card (autSub H Y) ∣ 21 :=
    s16e_d3_card_dvd_of_le_normalizer (Y := ↥Y) h2Y hY hQ hle
  have h3not : ¬ 3 ∣ Nat.card (autSub H Y) := by
    intro h3dvd
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨φ, hφord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autSub H Y)) 3 h3dvd
    have hcommφ : Commute (φ : MulAut ↥Y) xb := hcomm_of (φ : MulAut ↥Y) φ.2
    have hφ3 : (φ : MulAut ↥Y) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (φ : MulAut ↥Y)
      rw [Subgroup.orderOf_coe φ, hφord] at h
      exact h
    have hφ1' : (φ : MulAut ↥Y) = 1 :=
      s16e_d3_eq_one_of_commute (Y := ↥Y) h2Y hY hcommφ hφ3 hxb7 hxb1
    have hφ1 : φ = 1 := Subtype.ext hφ1'
    rw [hφ1, orderOf_one] at hφord
    omega
  have hcop : Nat.Coprime (Nat.card (autSub H Y)) 3 :=
    ((show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr h3not).symm
  have h21' : Nat.card (autSub H Y) ∣ 3 * 7 := by
    rwa [show (3 : ℕ) * 7 = 21 by norm_num]
  exact hcop.dvd_of_dvd_mul_left h21'

theorem s168e3_cyc7_card_dvd [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {W₁ W₂ : Subgroup W}
    (h₁ : Nat.card ↥W₁ = 8) (h₂ : Nat.card ↥W₂ = 8) (hsup : W₁ ⊔ W₂ = ⊤) {x : MulAut W}
    (hx₁ : x ∈ stabSub W₁) (hx₂ : x ∈ stabSub W₂) (hx7 : x ^ 7 = 1)
    (hn₁ : ∃ y ∈ W₁, x y ≠ y) (hn₂ : ∃ y ∈ W₂, x y ≠ y) {C : Subgroup (MulAut W)}
    (hC₁ : C ≤ stabSub W₁) (hC₂ : C ≤ stabSub W₂) (hCx : ∀ c ∈ C, c * x = x * c) :
    Nat.card ↥(autSub C W₂) ∣ 7 ∧ Nat.card ↥(C ⊓ centSub W₂) ∣ 7 := by
  have hX : C ⊓ centSub W₂ ≤ stabSub W₁ := fun g hg => hC₁ hg.1
  have hinf_bot : (C ⊓ centSub W₂) ⊓ centSub W₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hg2 : g ∈ centSub W₂ := hg.1.2
    have hg1 : g ∈ centSub W₁ := hg.2
    refine MulEquiv.ext fun w => ?_
    simp only [MulAut.one_apply]
    have hw : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
    rw [Subgroup.mem_sup] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    have h1 : g a = a := (mem_centSub.mp hg1) a ha
    have h2 : g b = b := (mem_centSub.mp hg2) b hb
    rw [← hab, map_mul, h1, h2]
  have hcard := card_autSub_mul (A := C ⊓ centSub W₂) (U := W₁) hX
  have hcard1 : Nat.card ↥((C ⊓ centSub W₂) ⊓ centSub W₁) = 1 := by
    rw [hinf_bot, Subgroup.card_bot]
  rw [hcard1, mul_one] at hcard
  refine ⟨s168e3_cyc7_card_autSub_dvd hW h₂ hx₂ hx7 hn₂ hC₂ hCx, ?_⟩
  rw [← hcard]
  exact s168e3_cyc7_card_autSub_dvd hW h₁ hx₁ hx7 hn₁ hX (fun g hg => hCx g hg.1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
