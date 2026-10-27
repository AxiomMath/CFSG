module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Lib
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Order
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Prop33
import CFSG.RankThree.PartTwo.Sec21.FF81Fusion
import CFSG.LocalAnalysis.StandardType.GGSixFusion

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_cube_into {L : Subgroup G} {t₀ : G} (hLt : L ≤ Cen t₀)
    (hCt : Nat.card (Cen t₀) = 2 ^ 24 * 3 ^ 4 * 5 * 7) (hL : Nat.card L = 1451520) {w : G}
    (hw : w ∈ Cen t₀) (hw3 : orderOf w = 3) : ∃ c ∈ Cen t₀, c * w * c⁻¹ ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ, -⟩ := exists_isSylowOf_le (p := 3) (bot_le : (⊥ : Subgroup G) ≤ L)
    (IsPGroup.of_card (n := 0) (by simp))
  have hQcard : Nat.card Q = 3 ^ 4 :=
    card_eq_of_isSylowOf hQ (m := 2 ^ 9 * 5 * 7) (by rw [hL]; norm_num) (by norm_num)
  have hQt : IsSylowOf 3 Q (Cen t₀) :=
    isSylowOf_of_card (hQ.1.trans hLt) hQ.2.1 hQcard (m := 2 ^ 24 * 5 * 7)
      (by rw [hCt]; ring) (by norm_num)
  have hwp : IsPGroup 3 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw3, pow_one])
  obtain ⟨c, hc, hcle⟩ := exists_conj_le_of_isSylowOf hQt (A := Subgroup.zpowers w)
    (Subgroup.zpowers_le.mpr hw) hwp
  refine ⟨c, hc, hQ.1 (hcle ⟨w, Subgroup.mem_zpowers w, rfl⟩)⟩

section Steps

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G} {Y : Subgroup G}

theorem holt6_step2 (hB : FF81Basis b L B b₁ b₂ b₃) (ht₀b : t₀ * b * t₀⁻¹ = b⁻¹)
    (ht₀Y : t₀ ∈ Y) (hBY : B ≤ Y) (hNBY : Nor B ≤ Y) (hYCB : Y ⊓ CenS B = B)
    (hnd : ∀ g : G, g * b * g⁻¹ ∈ Y → ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen (g * b * g⁻¹)))
    (K9 : ∀ E : Subgroup G, E ≤ Y → IsElemAb 3 4 E → Y ⊓ CenS E = E → ∀ x ∈ Y, orderOf x = 3 →
      ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) → ∃ y ∈ Y, y * x * y⁻¹ ∈ E) :
    ∀ x ∈ Y, (∃ g : G, g * b * g⁻¹ = x) → ∃ y ∈ Y, y * b * y⁻¹ = x := by
  have hb3 := hB.hyp.ord
  have hord3 : ∀ g : G, orderOf (g * b * g⁻¹) = 3 := fun g => by
    rw [show g * b * g⁻¹ = MulAut.conj g b from rfl, MulEquiv.orderOf_eq]
    exact hb3
  rintro x hxY ⟨g, rfl⟩
  obtain ⟨y, hy, hyx⟩ := K9 B hBY hB.mono.1 hYCB _ hxY (hord3 g) (hnd g hxY)
  have hwconj : y * (g * b * g⁻¹) * y⁻¹ = (y * g) * b * (y * g)⁻¹ := by group
  have hD : Subgroup.zpowers (y * (g * b * g⁻¹) * y⁻¹) ∈ ConjLines B b := by
    refine ⟨Subgroup.zpowers_le.mpr hyx, y * g, ?_⟩
    rw [conjBy_zpowers, hwconj]
  obtain ⟨n, hn, hnD⟩ := hB.fus _ hD
  have hnY := hNBY hn
  have hwD : y * (g * b * g⁻¹) * y⁻¹ ∈ conjBy n (Subgroup.zpowers b) := by
    rw [hnD]
    exact Subgroup.mem_zpowers _
  obtain ⟨v, hv, hvw⟩ := hwD
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hvw' : n * b ^ k * n⁻¹ = y * (g * b * g⁻¹) * y⁻¹ := hvw
  have hbk : b ^ k = 1 ∨ b ^ k = b ∨ b ^ k = b⁻¹ := by
    have h1 := zpow_mod_orderOf b k
    rw [hb3] at h1
    rw [← h1]
    have h3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
      omega
    rcases h3 with h | h | h
    · left
      rw [h, zpow_zero]
    · right
      left
      rw [h, zpow_one]
    · right
      right
      rw [h]
      have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
      rw [zpow_two]
      refine eq_inv_of_mul_eq_one_left ?_
      calc b * b * b = b ^ 3 := by rw [pow_succ, pow_two]
        _ = 1 := hb3'
  have hxy : (g * b * g⁻¹) = y⁻¹ * (n * b ^ k * n⁻¹) * y := by
    rw [hvw']
    group
  rcases hbk with h | h | h
  · exfalso
    rw [h] at hxy
    have h1 : g * b * g⁻¹ = 1 := by rw [hxy]; group
    have := hord3 g
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · refine ⟨y⁻¹ * n, Y.mul_mem (Y.inv_mem hy) hnY, ?_⟩
    rw [hxy, h]
    group
  · refine ⟨y⁻¹ * n * t₀, Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hnY) ht₀Y, ?_⟩
    rw [hxy, h]
    have : b⁻¹ = t₀ * b * t₀⁻¹ := ht₀b.symm
    rw [this]
    group

theorem holt6_step3 (hB : FF81Basis b L B b₁ b₂ b₃) (hbY : b ∈ Y) (hLY : L ≤ Y)
    (hsup : Subgroup.zpowers b ⊔ L = Y ⊓ Cen b)
    (K12 : ∀ x ∈ Y, orderOf x = 3 → ∀ K : Subgroup G, K ≤ Y →
      Subgroup.zpowers x ⊔ K = Y ⊓ Cen x → StatedClassicalModel K .PSp 3 2 1 →
      ∀ x₁ ∈ K, ∀ x₂ ∈ K, (∃ y ∈ Y, y * x * y⁻¹ = x₁) → (∃ y ∈ Y, y * x * y⁻¹ = x₂) →
      ∃ k ∈ K, k * x₁ * k⁻¹ = x₂)
    (hStep2 : ∀ x ∈ Y, (∃ g : G, g * b * g⁻¹ = x) → ∃ y ∈ Y, y * b * y⁻¹ = x) :
    ∀ x₁ ∈ L, ∀ x₂ ∈ L, (∃ g : G, g * b * g⁻¹ = x₁) → (∃ g : G, g * b * g⁻¹ = x₂) →
      ∃ k ∈ L, k * x₁ * k⁻¹ = x₂ := by
  intro x₁ hx₁ x₂ hx₂ h₁ h₂
  exact K12 b hbY hB.hyp.ord L hLY hsup hB.hyp.model x₁ hx₁ x₂ hx₂ (hStep2 x₁ (hLY hx₁) h₁)
    (hStep2 x₂ (hLY hx₂) h₂)

theorem holt6_step4 (hB : FF81Basis b L B b₁ b₂ b₃) (hLt : L ≤ Cen t₀)
    (hCt : Nat.card (Cen t₀) = 2 ^ 24 * 3 ^ 4 * 5 * 7) {n₁ : G} (hn₁b : n₁ * b * n₁⁻¹ = b₁)
    (hb₁Y : b₁ ∈ Y) (hCb₁ : Cen b₁ ≤ Y) (hb₁3 : orderOf b₁ = 3)
    (hnd₁ : ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen b₁))
    (K11 : ∀ t ∈ Y, orderOf t = 2 → ∀ x ∈ Y, orderOf x = 3 → ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      ∃ y ∈ Y, y * x * y⁻¹ ∈ Cen t)
    (hStep3 : ∀ x₁ ∈ L, ∀ x₂ ∈ L, (∃ g : G, g * b * g⁻¹ = x₁) → (∃ g : G, g * b * g⁻¹ = x₂) →
      ∃ k ∈ L, k * x₁ * k⁻¹ = x₂) :
    ∀ τ ∈ Y, orderOf τ = 2 → ∀ g : G, g * τ * g⁻¹ = t₀ → ∃ y ∈ Y, y * τ * y⁻¹ = t₀ := by
  intro τ hτY hτ2 g hg
  obtain ⟨y₀, hy₀, hy₀τ⟩ := K11 τ hτY hτ2 b₁ hb₁Y hb₁3 hnd₁
  have hxτ : y₀ * b₁ * y₀⁻¹ * τ = τ * (y₀ * b₁ * y₀⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hy₀τ
  have hgx : g * (y₀ * b₁ * y₀⁻¹) * g⁻¹ ∈ Cen t₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc g * (y₀ * b₁ * y₀⁻¹) * g⁻¹ * (g * τ * g⁻¹)
        = g * (y₀ * b₁ * y₀⁻¹ * τ) * g⁻¹ := by group
      _ = g * (τ * (y₀ * b₁ * y₀⁻¹)) * g⁻¹ := by rw [hxτ]
      _ = g * τ * g⁻¹ * (g * (y₀ * b₁ * y₀⁻¹) * g⁻¹) := by group
  have hgx3 : orderOf (g * (y₀ * b₁ * y₀⁻¹) * g⁻¹) = 3 := by
    rw [show g * (y₀ * b₁ * y₀⁻¹) * g⁻¹ = MulAut.conj g (MulAut.conj y₀ b₁) from rfl,
      MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hb₁3
  obtain ⟨c, hc, hcL⟩ := exists_conj_cube_into hLt hCt hB.card_L hgx hgx3
  have hx'conj : ∃ g' : G, g' * b * g'⁻¹ = c * (g * (y₀ * b₁ * y₀⁻¹) * g⁻¹) * c⁻¹ :=
    ⟨c * g * y₀ * n₁, by rw [← hn₁b]; group⟩
  obtain ⟨l, hl, hlx⟩ := hStep3 _ hcL b₁ hB.hb₁ hx'conj ⟨n₁, hn₁b⟩
  obtain ⟨h, hh⟩ : ∃ h : G, h = l * c * g * y₀ := ⟨_, rfl⟩
  have hhb₁ : h * b₁ * h⁻¹ = b₁ := by
    calc h * b₁ * h⁻¹
        = l * (c * (g * (y₀ * b₁ * y₀⁻¹) * g⁻¹) * c⁻¹) * l⁻¹ := by rw [hh]; group
      _ = b₁ := hlx
  have hhY : h ∈ Y :=
    hCb₁ (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hhb₁))
  have hct : c * t₀ * c⁻¹ = t₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have hlt : l * t₀ * l⁻¹ = t₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLt hl), mul_inv_cancel_right]
  refine ⟨h * y₀⁻¹, Y.mul_mem hhY (Y.inv_mem hy₀), ?_⟩
  calc h * y₀⁻¹ * τ * (h * y₀⁻¹)⁻¹ = l * (c * (g * τ * g⁻¹) * c⁻¹) * l⁻¹ := by rw [hh]; group
    _ = t₀ := by rw [hg, hct, hlt]

theorem holt6_step5 (ht₀ : orderOf t₀ = 2) (hCtY : Cen t₀ ≤ Y)
    (hA5 : ∀ τ ∈ Y, orderOf τ = 2 → ∀ g : G, g * τ * g⁻¹ = t₀ → ∃ y ∈ Y, y * τ * y⁻¹ = t₀) :
    ∃! q : G ⧸ Y, t₀ • q = q := by
  have ht₀2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [ht₀, sq] at this
  have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
  have ht₀Y : t₀ ∈ Y := hCtY (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine ⟨((1 : G) : G ⧸ Y), ?_, ?_⟩
  · show t₀ • ((1 : G) : G ⧸ Y) = ((1 : G) : G ⧸ Y)
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    simpa using ht₀Y
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hq
    have hτY : g⁻¹ * t₀ * g ∈ Y := by rwa [mul_inv_rev, ht₀inv] at hq
    have hτ2 : orderOf (g⁻¹ * t₀ * g) = 2 := by
      rw [show g⁻¹ * t₀ * g = MulAut.conj g⁻¹ t₀ by simp [MulAut.conj_apply],
        MulEquiv.orderOf_eq]
      exact ht₀
    obtain ⟨y, hy, hyτ⟩ := hA5 _ hτY hτ2 g (by group)
    have hyg : y * g⁻¹ ∈ Cen t₀ := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * g⁻¹ * t₀ = y * (g⁻¹ * t₀ * g) * y⁻¹ * (y * g⁻¹) := by group
        _ = t₀ * (y * g⁻¹) := by rw [hyτ]
    have hgY : g ∈ Y := by
      have : g = (y * g⁻¹)⁻¹ * y := by group
      rw [this]
      exact Y.mul_mem (Y.inv_mem (hCtY hyg)) hy
    show (g : G ⧸ Y) = ((1 : G) : G ⧸ Y)
    rw [QuotientGroup.eq]
    simpa using hgY

theorem holt6_step6 (ht₀ : orderOf t₀ = 2) (hCtY : Cen t₀ ≤ Y)
    (hCt : Nat.card (Cen t₀) = 2 ^ 24 * 3 ^ 4 * 5 * 7) (hY : Nat.card Y = 3311126603366400)
    (hA5 : ∀ τ ∈ Y, orderOf τ = 2 → ∀ g : G, g * τ * g⁻¹ = t₀ → ∃ y ∈ Y, y * τ * y⁻¹ = t₀)
    (K13 : ∀ U : Subgroup G, IsSylowOf 2 U Y → ∀ z₁ ∈ U, ∀ z₂ ∈ U, (∀ u ∈ U, z₁ * u = u * z₁) →
      (∀ u ∈ U, z₂ * u = u * z₂) → (∃ y ∈ Y, y * z₁ * y⁻¹ = z₂) → z₁ = z₂) :
    ∃ S : Sylow 2 G, t₀ ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Cen t₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Cen t₀)) := inferInstance
  set S := (P : Subgroup (Cen t₀)).map (Cen t₀).subtype with hS
  have hSC : S ≤ Cen t₀ := Subgroup.map_subtype_le _
  have hSY : S ≤ Y := hSC.trans hCtY
  have ht₀S : t₀ ∈ S := by
    obtain ⟨t₀', ht₀'⟩ : ∃ t : Cen t₀, (t : G) = t₀ :=
      ⟨⟨t₀, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, rfl⟩
    haveI hK : (Subgroup.zpowers t₀').Normal := ⟨fun z hz g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hgc : Commute g t₀' := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ht₀']
        exact Subgroup.mem_centralizer_singleton_iff.mp g.2)
      rw [(hgc.zpow_right k).eq, mul_inv_cancel_right]
      exact hz⟩
    have hKp : IsPGroup 2 (Subgroup.zpowers t₀') := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, ht₀', ht₀, pow_one])
    exact ⟨t₀', hKp.le_sylow_of_normal P (Subgroup.mem_zpowers t₀'), ht₀'⟩
  have hYc : Nat.card Y = 2 ^ 24 * 197358525 := by rw [hY]; norm_num
  have hSsyl : IsSylowOf 2 S Y := by
    have hScard : Nat.card S = 2 ^ 24 :=
      card_eq_of_isSylowOf (isSylowOf_map_sylow P) (m := 3 ^ 4 * 5 * 7)
        (by rw [hCt]; ring) (by norm_num)
    exact isSylowOf_of_card hSY (P.isPGroup'.map _) hScard hYc (by norm_num)
  have hNS : Subgroup.normalizer (S : Set G) ≤ Cen t₀ := by
    intro g hg
    have hz₂S : g * t₀ * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg t₀).mp ht₀S
    have hcen : ∀ u ∈ S, t₀ * u = u * t₀ := fun u hu =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hSC hu)).symm
    have hcen2 : ∀ u ∈ S, g * t₀ * g⁻¹ * u = u * (g * t₀ * g⁻¹) := by
      intro u hu
      have hv : g⁻¹ * u * g ∈ S :=
        (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * u * g)).mpr
          (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
      have := hcen _ hv
      calc g * t₀ * g⁻¹ * u = g * (t₀ * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * t₀) * g⁻¹ := by rw [this]
        _ = u * (g * t₀ * g⁻¹) := by group
    have hz2 : orderOf (g * t₀ * g⁻¹) = 2 := by
      rw [show g * t₀ * g⁻¹ = MulAut.conj g t₀ from rfl, MulEquiv.orderOf_eq]
      exact ht₀
    obtain ⟨y, hy, hyz⟩ := hA5 _ (hSY hz₂S) hz2 g⁻¹ (by group)
    have := K13 S hSsyl t₀ ht₀S _ hz₂S hcen hcen2 ⟨y⁻¹, Y.inv_mem hy, by
      calc y⁻¹ * t₀ * y⁻¹⁻¹ = y⁻¹ * (y * (g * t₀ * g⁻¹) * y⁻¹) * y⁻¹⁻¹ := by rw [hyz]
        _ = g * t₀ * g⁻¹ := by group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t₀ = g * t₀ * g⁻¹ * g := by group
      _ = t₀ * g := by rw [← this]
  obtain ⟨Tsyl, hTsyl⟩ := CFSG.StandardType.exists_sylow_eq_map_of_normalizer_le P hNS
  exact ⟨Tsyl, by rw [hTsyl]; exact ht₀S, by rw [hTsyl]; exact hSC⟩

theorem holt6_step7 (hB4 : IsElemAb 3 4 B) (hBY : B ≤ Y) (hNBY : Nor B ≤ Y)
    (hY : Nat.card Y = 3311126603366400)
    (K10 : ∀ Q : Subgroup G, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup G, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂) :
    padicValNat 3 (Nat.card G) = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := IsPGroup.of_card hB4.2
  obtain ⟨Q, hQ, hBQ⟩ := exists_isSylowOf_le hBY hBp
  have hQN : Nor Q ≤ Y := by
    intro g hg
    have h1 : conjBy g B ≤ Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hBQ hx)
    have h2 : conjBy g B = B := K10 Q hQ _ _ h1 hBQ (isElemAb_conjBy hB4 g) hB4
    have hgB : g ∈ Nor B := Subgroup.mem_normalizer_fintype fun x hx => by
      have : g * x * g⁻¹ ∈ conjBy g B := ⟨x, hx, rfl⟩
      rwa [h2] at this
    exact hNBY hgB
  obtain ⟨Q', hQ'⟩ := exists_sylow_top_of_isSylowOf hQ hQN
  have hYc : Nat.card Y = 3 ^ 6 * 4542011801600 := by rw [hY]; norm_num
  have hQcard : Nat.card Q = 3 ^ 6 := card_eq_of_isSylowOf hQ hYc (by norm_num)
  have h := Q'.card_eq_multiplicity
  rw [hQ', hQcard] at h
  rw [← Nat.factorization_def _ Nat.prime_three]
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm

end Steps

theorem ff81_holtHyp6_core {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
    (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
    (h58 : setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧ ∃ T₀ T₁ : Subgroup G, IsElemAb 2 6 T₀ ∧
      IsExtraspecialPlus 4 T₁ ∧ T₀ ⊔ T₁ = Op 2 (Cen t₀) ∧ T₀ ⊓ T₁ = ⊥)
    (Y : Subgroup G) (hY : Nat.card Y = 3311126603366400)
    (hCtY : Cen t₀ ≤ Y) (hBY : B ≤ Y) (hCbY : Cen b ≤ Y) (hNBY : Nor B ≤ Y)
    (hIIa : CaseIIa b B b₁ b₂ b₃)
    (K3 : ∀ x ∈ Y, orderOf x = 3 → 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) ∨
      Nat.card ↥(Y ⊓ Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7)
    (K9 : ∀ E : Subgroup G, E ≤ Y → IsElemAb 3 4 E → Y ⊓ CenS E = E → ∀ x ∈ Y, orderOf x = 3 →
      ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) → ∃ y ∈ Y, y * x * y⁻¹ ∈ E)
    (K10 : ∀ Q : Subgroup G, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup G, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂)
    (K11 : ∀ t ∈ Y, orderOf t = 2 → ∀ x ∈ Y, orderOf x = 3 → ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      ∃ y ∈ Y, y * x * y⁻¹ ∈ Cen t)
    (K12 : ∀ x ∈ Y, orderOf x = 3 → ∀ K : Subgroup G, K ≤ Y →
      Subgroup.zpowers x ⊔ K = Y ⊓ Cen x → StatedClassicalModel K .PSp 3 2 1 →
      ∀ x₁ ∈ K, ∀ x₂ ∈ K, (∃ y ∈ Y, y * x * y⁻¹ = x₁) → (∃ y ∈ Y, y * x * y⁻¹ = x₂) →
      ∃ k ∈ K, k * x₁ * k⁻¹ = x₂)
    (K13 : ∀ U : Subgroup G, IsSylowOf 2 U Y → ∀ z₁ ∈ U, ∀ z₂ ∈ U, (∀ u ∈ U, z₁ * u = u * z₁) →
      (∀ u ∈ U, z₂ * u = u * z₂) → (∃ y ∈ Y, y * z₁ * y⁻¹ = z₂) → z₁ = z₂) :
    padicValNat 3 (Nat.card G) = 6 ∧
      (∃ S : Sylow 2 G, t₀ ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Cen t₀) ∧
      ∃! q : G ⧸ Y, t₀ • q = q := by
  have hB := h5.basis
  obtain ⟨hbB, hb1B, -, -⟩ := hB.mem
  have hbY : b ∈ Y := hBY hbB
  have hb3 := hB.hyp.ord
  have ht₀ := h5.ht₀
  have ht₀Y : t₀ ∈ Y := hCtY (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hLt : L ≤ Cen t₀ := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h5.ht₀L x hx)
  have hLY : L ≤ Y := hB.hyp.hLC.trans hCbY
  obtain ⟨hCbcard, hCbsup⟩ := cen_eq_sup_of_le hB hCbY K3
  have hCBeq : CenS B = B := cenS_eq_of_cen_eq hB hCbsup
  have hYCB : Y ⊓ CenS B = B := by rw [hCBeq]; exact inf_of_le_right hBY
  have hCt := card_cen_t₀ hB h5.ht₀L h58 hCtY hY
  have hord3 : ∀ g : G, orderOf (g * b * g⁻¹) = 3 := fun g => by
    rw [show g * b * g⁻¹ = MulAut.conj g b from rfl, MulEquiv.orderOf_eq]
    exact hb3
  have hcenY : ∀ g : G, g * b * g⁻¹ ∈ Y → Cen (g * b * g⁻¹) ≤ Y := fun g hg =>
    cen_le_of_card K3 hg (hord3 g) (by rw [card_cen_conj, hCbcard])
  have hnd : ∀ g : G, g * b * g⁻¹ ∈ Y → ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen (g * b * g⁻¹)) := by
    intro g hg
    rw [inf_of_le_right (hcenY g hg), card_cen_conj, hCbcard]
    norm_num
  obtain ⟨n₁, hn₁, hn₁b, -⟩ := hIIa.1.2.2.2.1
  have hb₁Y : b₁ ∈ Y := hBY hb1B
  have hCb₁ : Cen b₁ ≤ Y := by
    rw [← hn₁b]
    exact hcenY n₁ (by rw [hn₁b]; exact hb₁Y)
  have hb₁3 : orderOf b₁ = 3 := by rw [← hn₁b]; exact hord3 n₁
  have hnd₁ : ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen b₁) := by
    rw [← hn₁b]
    exact hnd n₁ (by rw [hn₁b]; exact hb₁Y)
  have hsup : Subgroup.zpowers b ⊔ L = Y ⊓ Cen b := by
    rw [inf_of_le_right hCbY]
    exact hCbsup.symm
  have hStep2 := holt6_step2 hB h5.ht₀b ht₀Y hBY hNBY hYCB hnd K9
  have hStep3 := holt6_step3 hB hbY hLY hsup K12 hStep2
  have hA5 := holt6_step4 hB hLt hCt hn₁b hb₁Y hCb₁ hb₁3 hnd₁ K11 hStep3
  exact ⟨holt6_step7 hB.mono.1 hBY hNBY hY K10, holt6_step6 ht₀ hCtY hCt hY hA5 K13,
    holt6_step5 ht₀ hCtY hA5⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.S6
