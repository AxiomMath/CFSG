module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModRefl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModFree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2b

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

omit [Finite W] in
theorem vEMod_inf_W₂ (x₁ x₂ : MulAut W) :
    S.vEMod x₁ x₂ ⊓ S.W₂ = S.W₂ ⊓ fixV (Subgroup.zpowers x₂) := by
  apply le_antisymm
  · rintro w ⟨hwV, hw2⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Subgroup.mem_sup.mp hwV
    have hl₁2 : l₁ ∈ S.W₂ := by
      have : l₁ = (l₁ * l₂) * l₂⁻¹ := by group
      rw [this]
      exact S.W₂.mul_mem hw2 (S.W₂.inv_mem hl₂.1)
    have h3 : l₁ ∈ S.W₁ ⊓ S.W₂ := ⟨hl₁.1, hl₁2⟩
    rw [S.winf, Subgroup.mem_bot] at h3
    rw [h3, one_mul]
    exact hl₂
  · intro w hw
    exact ⟨Subgroup.mem_sup_right hw, hw.1⟩

omit [Finite W] in
theorem le_vEMod₂ (x₁ x₂ : MulAut W) : S.W₂ ⊓ fixV (Subgroup.zpowers x₂) ≤ S.vEMod x₁ x₂ :=
  le_sup_right

theorem stab_of_mem_ptFix (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {x₁ x₂ : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₁2 : orderOf x₁ = 2) {g : MulAut W}
    (hg : g ∈ ptFix (stabSub Mb (S.vEMod x₁ x₂)) (S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) :
    S.Stab₁ g ∧ S.Stab₂ g ∧
      ∀ w ∈ S.W₂ ⊓ fixV (Subgroup.zpowers x₂), g w ∈ S.W₂ ⊓ fixV (Subgroup.zpowers x₂) := by
  obtain ⟨z, hzL, hz1⟩ : ∃ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), z ≠ 1 := by
    by_contra hcon
    have hbot : S.W₁ ⊓ fixV (Subgroup.zpowers x₁) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    have h4 := S.card_fix_reflection₁ hW hcard hx₁ hx₁2
    omega
  have hs := S.stab_of_mem_of_fix₁ hW hnorm hg.1.1 ⟨z, hzL.1, hz1, hg.2 z hzL⟩
  refine ⟨hs.1, hs.2, fun w hw => ?_⟩
  have hV : g w ∈ S.vEMod x₁ x₂ := (hg.1.2 w).mp (S.le_vEMod₂ x₁ x₂ hw)
  have h2 : g w ∈ S.W₂ := (hs.2 w).mp hw.1
  rw [← S.vEMod_inf_W₂ x₁ x₂]
  exact ⟨hV, h2⟩

theorem odd_mem_zpowers_eps (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {x₁ x₂ ε : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₂ : x₂ ∈ S.A₂) (hx₁2 : orderOf x₁ = 2) (hx₂2 : orderOf x₂ = 2)
    (hε : ε ∈ Mb) (hε3 : orderOf ε = 3) (hε₁ : ∀ w ∈ S.W₁, ε w = w)
    (_hεf : ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w) (hεa : ε * S.a₂ = S.a₂ * ε) {g : MulAut W}
    (hg : g ∈ ptFix (stabSub Mb (S.vEMod x₁ x₂)) (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)))
    (hodd : Odd (orderOf g)) : g ∈ Subgroup.zpowers ε := by
  obtain ⟨hs1, hs2, hL₂⟩ := S.stab_of_mem_ptFix hW hcard hnorm hx₁ hx₁2 hg
  have hgMb : g ∈ Mb := hg.1.1
  have hc₁ : g * S.a₁ = S.a₁ * g :=
    commute_of_conj_odd_five151b S.orderOf_a₁_five
      (S.mem_zpowers_a₁_conj hW hcard (hnorm g hgMb) ⟨hs1, hs2⟩) hodd
  have hc₂ : g * S.a₂ = S.a₂ * g :=
    commute_of_conj_odd_five151b S.orderOf_a₂_five
      (S.mem_zpowers_a₂_conj hW hcard (hnorm g hgMb) ⟨hs1, hs2⟩) hodd
  obtain ⟨z, hzL, hz1⟩ : ∃ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), z ≠ 1 := by
    by_contra hcon
    have hbot : S.W₁ ⊓ fixV (Subgroup.zpowers x₁) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    have h4 := S.card_fix_reflection₁ hW hcard hx₁ hx₁2
    omega
  have hgW₁ : ∀ w ∈ S.W₁, g w = w :=
    S.fix_W₁_of_commute hW hcard hc₁ hzL.1 hz1 (hg.2 z hzL)
  have hgC : g ∈ S.cenW₂ := ⟨hgW₁, hc₂, hs2⟩
  have hεs := S.stab_of_mem_of_fix₁ hW hnorm hε ⟨z, hzL.1, hz1, hε₁ z hzL.1⟩
  have hεC : ε ∈ S.cenW₂ := ⟨hε₁, hεa, hεs.2⟩
  have hg3 : g ^ 3 = 1 :=
    S.cube_eq_one_of_stabilizes hW hcard hgC (L := S.W₂ ⊓ fixV (Subgroup.zpowers x₂))
      inf_le_left (S.card_fix_reflection₂ hW hcard hx₂ hx₂2) hL₂ hodd
  exact S.mem_zpowers_of_cube_eq_one hW hcard hεC hε3 hgC hg3

theorem normal_two_group_trivial_on_vE (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {x₁ x₂ ε : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₂ : x₂ ∈ S.A₂) (hx₁2 : orderOf x₁ = 2) (hx₂2 : orderOf x₂ = 2)
    (hε : ε ∈ stabSub Mb (S.vEMod x₁ x₂)) (_hε3 : orderOf ε = 3) (hε₁ : ∀ w ∈ S.W₁, ε w = w)
    (hεf : ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w) {P : Subgroup (MulAut W)}
    (hP2 : IsPGroup 2 P)
    (hPC : P ≤ ptFix (stabSub Mb (S.vEMod x₁ x₂)) (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)))
    (hPn : ∀ g ∈ ptFix (stabSub Mb (S.vEMod x₁ x₂)) (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)),
      ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    ∀ p ∈ P, ∀ w ∈ S.vEMod x₁ x₂, p w = w := by
  set L₂ : Subgroup W := S.W₂ ⊓ fixV (Subgroup.zpowers x₂) with hL₂
  have hεC : ε ∈ ptFix (stabSub Mb (S.vEMod x₁ x₂)) (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) :=
    ⟨hε, fun z hz => hε₁ z hz.1⟩
  have hPL : ∀ p ∈ P, ∀ w ∈ L₂, p w ∈ L₂ := fun p hp =>
    (S.stab_of_mem_ptFix hW hcard hnorm hx₁ hx₁2 (hPC hp)).2.2
  have hεL : ∀ w ∈ L₂, ε w ∈ L₂ := (S.stab_of_mem_ptFix hW hcard hnorm hx₁ hx₁2 hεC).2.2
  have hL4 : Nat.card L₂ = 4 := S.card_fix_reflection₂ hW hcard hx₂ hx₂2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_card_inf_fixV151b (U := L₂) hP2 (fun g hg u hu => hPL g hg u hu)
  set C : Subgroup W := L₂ ⊓ fixV P with hC
  have hCε : ∀ z ∈ C, ε z ∈ C := by
    intro z hz
    refine ⟨hεL z hz.1, fun p hp => ?_⟩
    have hq : ε⁻¹ * p * ε ∈ P := by
      have := hPn ε⁻¹ ((ptFix (stabSub Mb (S.vEMod x₁ x₂))
        (S.W₁ ⊓ fixV (Subgroup.zpowers x₁))).inv_mem hεC) p hp
      rwa [inv_inv] at this
    have h1 : p * ε = ε * (ε⁻¹ * p * ε) := by group
    calc p (ε z) = (p * ε) z := rfl
      _ = (ε * (ε⁻¹ * p * ε)) z := by rw [h1]
      _ = ε ((ε⁻¹ * p * ε) z) := rfl
      _ = ε z := by rw [hz.2 _ hq]
  have hCle : C ≤ L₂ := inf_le_left
  have hCdvd : Nat.card C ∣ 4 := hL4 ▸ Subgroup.card_dvd_of_le hCle
  have heven : Nat.card C % 2 = 0 := by
    rw [hL4] at hmod
    unfold Nat.ModEq at hmod
    omega
  have h24 : Nat.card C = 2 ∨ Nat.card C = 4 := by
    have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hCdvd
    have hpos : 0 < Nat.card C := Nat.card_pos
    generalize Nat.card C = n at hCdvd heven hle hpos
    interval_cases n <;> omega
  have hCL : C = L₂ := by
    rcases h24 with h | h
    · exfalso
      obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' (1 : ↥C)).mp h
      have hz1 : (y : W) ≠ 1 := fun e => hy (Subtype.ext e)
      have hzW₂ : (y : W) ∈ S.W₂ := y.2.1.1
      have hεz : ε (y : W) ≠ 1 := fun e => hz1 (ε.injective (e.trans (map_one ε).symm))
      obtain ⟨y', -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥C)).mp h
      have e1 := huniq y hy
      have e2 := huniq ⟨ε (y : W), hCε y y.2⟩ (fun e => hεz (congrArg Subtype.val e))
      have : ε (y : W) = y := congrArg Subtype.val (e2.trans e1.symm)
      exact hεf y hzW₂ hz1 this
    · exact Subgroup.eq_of_le_of_card_ge hCle (by rw [h, hL4])
  intro p hp w hw
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Subgroup.mem_sup.mp hw
  have h1 : p l₁ = l₁ := (hPC hp).2 l₁ hl₁
  have h2 : p l₂ = l₂ := by
    have : l₂ ∈ C := by rw [hCL]; exact hl₂
    exact this.2 p hp
  rw [map_mul, h1, h2]

end CFSG.Quasithin.SixData151b
