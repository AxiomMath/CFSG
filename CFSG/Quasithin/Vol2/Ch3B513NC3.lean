module

public import CFSG.Quasithin.Vol2.Ch3B513NC3F
import CFSG.Adapters.StatedSLPerfect
public import CFSG.Quasithin.Vol2.Ch3B513NC3E

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank

theorem perfect_statedSL3 (K : Type) [Field K] : Group.IsPerfect ↥(StatedSL 3 K) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K

theorem perfect_statedSL2 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect ↥(StatedSL 2 K) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK

theorem card_le_two_sl2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (E : Subgroup ↥(StatedSL 2 K)) (hE2 : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 2 := by
  have hcard := card_statedSL_two1527d (F := K)
  rw [hK] at hcard
  calc Nat.card E ≤ 2 ^ 1 :=
        card_le_of_card_eq (m := 3) (by decide) (by rw [hcard]; norm_num) hE2
    _ = 2 := by norm_num

variable {W : Type} [CommGroup W]

theorem commutator_eq_of_surjective {L : Subgroup (MulAut W)} {Γ : Type*} [Group Γ]
    (hΓ : Group.IsPerfect Γ) {π : Γ →* ↥L} (hπ : Function.Surjective π) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective hπ)

theorem card_le_two_of_sl2 {L : Subgroup (MulAut W)} {U Z : Subgroup W} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {π : (FFModel.nat (StatedSL 2 K)).Gam →* ↥L}
    (hr : (FFModel.nat (StatedSL 2 K)).RealizesVia L U Z π) (E : Subgroup (MulAut W))
    (hEL : E ≤ L) (hE : IsElemAbelian2 E) : Nat.card E ≤ 2 :=
  card_le_of_equiv hEL
    (MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hr, hr.1⟩).symm
    (card_le_two_sl2 hK) hE.2

variable [Finite W]

theorem card_le_two_mul_fix_of_c {G Gi Gj : Subgroup (MulAut W)} {Wi Wj : Subgroup W}
    (hGi : Gi ≤ G) (hGj : Gj ≤ G) (hc : ∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a)
    (hWi : commV Gi ≤ Wi) (hinvj : ∀ g ∈ G, ∀ w ∈ Wj, g w ∈ Wj) (hinf : Wi ⊓ Wj = fixV G)
    (hCj : fixV G ≤ Wj) (hcard : Nat.card ↥Wj = 2 ^ 4 * Nat.card ↥(fixV G))
    (hnat : BinaryNaturalSL Gj (XMod.commOf ↥Gj Wj ⊔ fixV G) (fixV G) 3 1) :
    ∀ g ∈ Gi, Nat.card Wj ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ Wj) := by
  intro g hg
  obtain ⟨K, _, _, hK, π, hr⟩ := hnat
  have hM : Nat.card ↥(XMod.commOf ↥Gj Wj ⊔ fixV G) = Nat.card ↥(fixV G) * Nat.card K ^ 3 :=
    card_commV_of_nat hr
  have hle : XMod.commOf ↥Gj Wj ⊔ fixV G ≤ fixV (Subgroup.zpowers g) ⊓ Wj := by
    refine sup_le (le_inf ?_ ?_) (le_inf (fun c hc' => B1.zpowers_fix (hc' g (hGi hg))) hCj)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, l, hl, rfl⟩
      apply B1.zpowers_fix
      have hx := mul_inv_mem_fixV hGi hWi hinvj hinf hg hl
      have hgl : g l = (g l * l⁻¹) * l := by rw [inv_mul_cancel_right]
      have hga : g ((a : MulAut W) l) = (a : MulAut W) (g l) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, hc g hg a a.2]
      show g ((a : MulAut W) l * l⁻¹) = (a : MulAut W) l * l⁻¹
      rw [map_mul, map_inv, hga, hgl, map_mul, hx _ (hGj a.2)]
      rw [← hgl]
      calc g l * l⁻¹ * (a : MulAut W) l * (g l)⁻¹
          = (a : MulAut W) l * l⁻¹ * (g l * (g l)⁻¹) := by ac_rfl
        _ = (a : MulAut W) l * l⁻¹ := by rw [mul_inv_cancel, mul_one]
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, l, hl, rfl⟩
      exact Wj.mul_mem (hinvj _ (hGj a.2) l hl) (Wj.inv_mem hl)
  calc Nat.card Wj = 2 ^ 4 * Nat.card ↥(fixV G) := hcard
    _ = 2 * (Nat.card ↥(fixV G) * Nat.card K ^ 3) := by rw [hK]; ring
    _ = 2 * Nat.card ↥(XMod.commOf ↥Gj Wj ⊔ fixV G) := by rw [hM]
    _ ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers g) ⊓ Wj) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

theorem cent_or_hasGood (hW : ∀ w : W, w ^ 2 = 1) {G Gi Gj : Subgroup (MulAut W)}
    (hJ : G = ffJ G) (hsup : Gi ⊔ Gj = G) (hd : Gi ⊓ Gj = ⊥)
    (hc : ∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) {Wi Wj : Subgroup W} (hCj : fixV G ≤ Wj)
    (hinvi : XMod.IsInv ↥G Wi) (hinvj : XMod.IsInv ↥G Wj) (hsupW : Wi ⊔ Wj = ⊤)
    (hinf : Wi ⊓ Wj = fixV G) (hPi : B56Piece Gi Wi (fixV G)) (hPj : B56Piece Gj Wj (fixV G)) :
    (∀ g ∈ Gi, ∀ w ∈ Wj, g w = w) ∨ HasGood G := by
  have hGi : Gi ≤ G := hsup ▸ le_sup_left
  have hGj : Gj ≤ G := hsup ▸ le_sup_right
  have hinvi' : ∀ g ∈ G, ∀ w ∈ Wi, g w ∈ Wi := fun g hg w hw => hinvi ⟨g, hg⟩ w hw
  have hinvj' : ∀ g ∈ G, ∀ w ∈ Wj, g w ∈ Wj := fun g hg w hw => hinvj ⟨g, hg⟩ w hw
  have hcommV : ∀ {X : Subgroup (MulAut W)} {Y : Subgroup W}, B56Piece X Y (fixV G) →
      commV X ≤ Y := by
    rintro X Y (⟨hY, -⟩ | ⟨hY, -⟩ | ⟨-, hXY, -⟩)
    · rw [hY]
      exact le_sup_left
    · rw [hY]
      exact le_sup_left
    · exact hXY
  have hWi := hcommV hPi
  have hWj := hcommV hPj
  have hperf : ⁅Gi, Gi⁆ = Gi → ∀ g ∈ Gi, ∀ w ∈ Wj, g w = w := fun h =>
    fix_of_perfect hGi h hWi hinvj' hinf
  rcases hPj with ⟨hWj', -⟩ | ⟨hWj', -⟩ | ⟨-, -, hcard, -, hnat⟩
  · exact Or.inl (fix_of_eq_sup hGi hGj hc hWi hinvi' hinvj' hinf hsupW hWj')
  · exact Or.inl (fix_of_eq_sup hGi hGj hc hWi hinvi' hinvj' hinf hsupW hWj')
  rcases hPi with ⟨hWi', hSL2 | hS5 | hSL3⟩ | ⟨-, m, K, _, _, -, hds⟩ | ⟨⟨e⟩, -⟩
  · obtain ⟨n, K, _, _, hK, π, hr⟩ := hSL2
    rcases Nat.lt_or_ge n 2 with hn | hn
    ·
      have hn1 : n = 1 := by
        rcases Nat.lt_or_ge n 1 with h0 | h1
        · have h00 : n = 0 := by omega
          subst h00
          have h1K := Finite.one_lt_card (α := K)
          rw [hK] at h1K
          norm_num at h1K
        · omega
      subst hn1
      by_cases hbot : Gi = ⊥
      · left
        intro g hg w _
        rw [hbot, Subgroup.mem_bot] at hg
        subst hg
        rfl
      right
      have hc' : ∀ a ∈ Gj, ∀ b ∈ Gi, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
      have hsupW' : Wj ⊔ Wi = ⊤ := by rw [sup_comm]; exact hsupW
      have hinf' : Wj ⊓ Wi = fixV G := by rw [inf_comm]; exact hinf
      exact hasGood_of_transfer_two hW hJ hsup hd hc hbot hsupW
        (fix_of_eq_sup hGj hGi hc' hWj hinvj' hinvi' hinf' hsupW' hWi')
        (fun E hE hE2 => card_le_two_of_sl2 (hK.trans (pow_one 2)) hr E hE hE2)
        (card_le_two_mul_fix_of_c hGi hGj hc hWi hinvj' hinf hCj hcard hnat)
    · have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      let π' : ↥(StatedSL 2 K) →* ↥Gi := π
      have hπ' : Function.Surjective π' := hr.1
      exact Or.inl (hperf (commutator_eq_of_surjective (perfect_statedSL2 h4) hπ'))
  · exact Or.inr (hasGood_of_sym5 hW hGi rfl hWi' hS5)
  · obtain ⟨m, K, _, _, -, π, hr⟩ := hSL3
    let π' : ↥(StatedSL 3 K) →* ↥Gi := π
    have hπ' : Function.Surjective π' := hr.1
    exact Or.inl (hperf (commutator_eq_of_surjective (perfect_statedSL3 K) hπ'))
  · obtain ⟨I, π, -, -, -, hreal⟩ := hds
    let π' : ↥(StatedSL 3 K) →* ↥Gi := π
    have hπ' : Function.Surjective π' := (hreal 0).1
    exact Or.inl (hperf (commutator_eq_of_surjective (perfect_statedSL3 K) hπ'))
  · exact Or.inl (hperf (commutator_eq_of_surjective (π := e.symm.toMonoidHom)
      (perfect_statedSL3 (ZMod 2)) e.symm.surjective))

theorem hasGood_of_left (hW : ∀ w : W, w ^ 2 = 1) {G G₁ G₂ : Subgroup (MulAut W)}
    (hJ : G = ffJ G) (hsup : G₁ ⊔ G₂ = G) (hd : G₁ ⊓ G₂ = ⊥)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hne : G₁ ≠ ⊥) {W₁ W₂ : Subgroup W}
    (hW12 : W₁ ⊔ W₂ = ⊤) (h12 : ∀ g ∈ G₁, ∀ w ∈ W₂, g w = w)
    (h21 : ∀ g ∈ G₂, ∀ w ∈ W₁, g w = w) (hP : B56Piece G₁ W₁ (fixV G)) : HasGood G := by
  obtain ⟨D, hD, hDG₁⟩ := exists_isFFStarMin_le_left hJ hsup hd hc hne hW12 h12 h21
  have hG₁ : G₁ ≤ G := hsup ▸ le_sup_left
  have hC : fixV G ≤ fixV G₁ := fun c hc' g hg => hc' g (hG₁ hg)
  have hW2 : W₂ ≤ fixV G₁ := fun w hw g hg => h12 g hg w hw
  have hsupW : W₁ ⊔ fixV G₁ = ⊤ := eq_top_iff.2 (hW12 ▸ sup_le_sup_left hW2 W₁)
  exact hasGood_of_piece hW hD hDG₁ hC hsupW hP

theorem case3_holds : Case3 := by
  intro W _ _ hW G _ hne hB53 h3
  have hJ : G = ffJ G := hB53.2.1
  obtain ⟨G₁, G₂, hsup, hd, hc, -, -, W₁, W₂, hC₁, hC₂, hinv₁, hinv₂, hW12, hinf, hP₁, hP₂⟩ := h3
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hsup' : G₂ ⊔ G₁ = G := by rw [sup_comm]; exact hsup
  have hd' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hd
  have hW21 : W₂ ⊔ W₁ = ⊤ := by rw [sup_comm]; exact hW12
  have hinf' : W₂ ⊓ W₁ = fixV G := by rw [inf_comm]; exact hinf
  rcases cent_or_hasGood hW hJ hsup hd hc hC₂ hinv₁ hinv₂ hW12 hinf hP₁ hP₂ with h12 | h
  swap
  · exact h
  rcases cent_or_hasGood hW hJ hsup' hd' hc' hC₁ hinv₂ hinv₁ hW21 hinf' hP₂ hP₁ with h21 | h
  swap
  · exact h
  by_cases h₁ : G₁ = ⊥
  · have h₂ : G₂ ≠ ⊥ := by
      intro h₂
      apply hne
      rw [← hsup, h₁, h₂, sup_bot_eq]
    exact hasGood_of_left hW hJ hsup' hd' hc' h₂ hW21 h21 h12 hP₂
  · exact hasGood_of_left hW hJ hsup hd hc h₁ hW12 h12 h21 hP₁

end CFSG.Quasithin.B513N
