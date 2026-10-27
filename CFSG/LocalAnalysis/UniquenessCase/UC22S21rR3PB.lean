module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3PA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XH
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace R3Pair

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem exists_le_or_le (u : R3Pair D L K n p) {H₁ H₂ : Subgroup G} (hH₁ : D.T ≤ H₁)
    (hH₂ : D.T ≤ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ r = 1) (hx₁q : x₁ ^ r = 1) (hx₀1 : x₀ ≠ 1) {b : ↥D.M}
    (hbN : (b : G) ∈ normalizer (D.T : Set G)) (hbx : uc22p21cPi D.M b = x₀ * x₁) :
    ∃ X : Subgroup G, X ≤ D.M ∧ D.T ≤ X ∧ (X ≤ H₁ ∨ X ≤ H₂) ∧
      Nat.card X ∣ r * Nat.card D.T ∧ (b : G) ∈ normalizer (X : Set G) ∧
      x₀ * x₁⁻¹ ∈ barImage D.M X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hinf, -, -, -, hXn, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hT := u4x_isSylowOf_barImage (p := 2) D.sylowM
  have hβ : x₀ * x₁ ∈ normalizer (barImage D.M D.T : Set (Bar2 D.M)) :=
    hbx ▸ uc22ine229_mk_mem_normalizer hbN
  obtain ⟨h0, h1⟩ := u4x_mem_normalizer_inf hcomm hinf hXn hT hx₀ hx₁ hβ
  set S := barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K) with hS
  set y := x₀ * x₁⁻¹ with hy
  set W := barImage D.M D.T ⊔ (zpowers y ⊔ S) with hW
  have hyS : y ∈ normalizer (S : Set (Bar2 D.M)) := mul_mem h0 (inv_mem h1)
  have hc : Commute x₀ x₁⁻¹ := hcomm x₀ hx₀ _ (inv_mem hx₁)
  have hyr : y ^ r = 1 := by
    rw [hy, hc.mul_pow, hx₀q, inv_pow, hx₁q, inv_one, one_mul]
  have hTV : barImage D.M D.T ≤ normalizer ((zpowers y ⊔ S : Subgroup (Bar2 D.M)) : Set _) := by
    intro τ hτ
    obtain ⟨t, ht, rfl⟩ := uc22p21c_mem_barImage.1 hτ
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have hle : zpowers y ⊔ S ≤
        (zpowers y ⊔ S).comap (MulAut.conj (uc22p21cPi D.M t)).toMonoidHom := by
      refine sup_le (zpowers_le.2 (Subgroup.mem_comap.2 (u.conj_mem_V hx₀ hx₁ hβ ht)))
        fun s hs => Subgroup.mem_comap.2 ?_
      have h1 : uc22p21cPi D.M t * s * (uc22p21cPi D.M t)⁻¹ ∈ barImage D.M D.T :=
        mul_mem (mul_mem hτ hs.1) (inv_mem hτ)
      exact mem_sup_right ⟨h1, hXn.conj_mem _ hs.2 _⟩
    exact hle hv
  have hWd := u4x_card_sup_dvd (S := S) (T := barImage D.M D.T) inf_le_left hyS hTV hyr
  have hOT := uc22p22c_pCoreOf_le_T D
  have hTT : barPreimage D.M (barImage D.M D.T) = D.T :=
    barPreimage_barImage_of_pCoreOf_le D.sylowM.le hOT
  have hcT : Nat.card D.T = Nat.card ↥(pCoreOf 2 D.M) * Nat.card ↥(barImage D.M D.T) := by
    rw [← uc22p22u_card_barPreimage, hTT]
  have hTX : D.T ≤ barPreimage D.M W := hTT.symm.le.trans (barPreimage_mono le_sup_left)
  have hXM : barPreimage D.M W ≤ D.M := uc22p21c_barPreimage_le D.M W
  have hXd : Nat.card ↥(barPreimage D.M W) ∣ r * Nat.card D.T := by
    rw [uc22p22u_card_barPreimage, hcT, mul_left_comm]
    exact Nat.mul_dvd_mul_left _ hWd
  have hy1 : y ≠ 1 := fun h => hx₀1 <| by
    have h' : x₀ = x₁ := mul_inv_eq_one.1 h
    have hmem : x₀ ∈ barImage D.M L ⊓ barImage D.M K := ⟨hx₀, h' ▸ hx₁⟩
    rwa [hinf, Subgroup.mem_bot] at hmem
  have hyW : y ∈ W := mem_sup_right (mem_sup_left (mem_zpowers y))
  obtain ⟨m, hm⟩ := uc22p21c_pi_surjective D.M y
  have hmX : (m : G) ∈ barPreimage D.M W :=
    uc22p21c_mem_barPreimage.2 ⟨m.2, show uc22p21cPi D.M m ∈ W from hm ▸ hyW⟩
  have hmT : (m : G) ∉ D.T := fun hmT =>
    hy1 (u4x_eq_one_of_isPGroup hT.isPGroup (hm ▸ uc22p21c_mem_barImage.2 ⟨m, hmT, rfl⟩)
      hr hr2 hyr)
  have hlt : D.T < barPreimage D.M W := SetLike.lt_iff_le_and_exists.2 ⟨hTX, (m : G), hmX, hmT⟩
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup.exists_card_eq
  have hsol : Group.IsSolvable ↥(barPreimage D.M W) :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (a := a) (b := 1) Nat.prime_two
      hr (by rw [pow_one, mul_comm, ← ha]; exact hXd)
  have hle := uc22s21ru3a_le_or_le (uc22p22ta_isSylowIn D hTX) (u4x_covBy hlt hr hXd)
    hsol hH₁ hH₂ (hfX _ hXM hTX)
  have hcy : Commute (x₀ * x₁) y := by
    have e : x₁ * x₀ = x₀ * x₁ := (hcomm x₀ hx₀ x₁ hx₁).symm
    have e' : x₁⁻¹ * x₀ = x₀ * x₁⁻¹ := (hcomm x₀ hx₀ _ (inv_mem hx₁)).symm
    show x₀ * x₁ * (x₀ * x₁⁻¹) = x₀ * x₁⁻¹ * (x₀ * x₁)
    calc x₀ * x₁ * (x₀ * x₁⁻¹) = x₀ * (x₁ * x₀) * x₁⁻¹ := by group
      _ = x₀ * (x₀ * x₁) * x₁⁻¹ := by rw [e]
      _ = x₀ * (x₀ * x₁⁻¹) * x₁ := by group
      _ = x₀ * (x₁⁻¹ * x₀) * x₁ := by rw [e']
      _ = x₀ * x₁⁻¹ * (x₀ * x₁) := by group
  have hβy : x₀ * x₁ ∈ normalizer ((zpowers y : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
    Subgroup.mem_normalizer_fintype fun z hz => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [(hcy.zpow_right i).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers y) i
  have hβS : x₀ * x₁ ∈ normalizer (S : Set (Bar2 D.M)) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hβ, u4x_top_le_normalizer hXn (mem_top _)⟩
  have hbW : uc22p21cPi D.M b ∈ normalizer (W : Set (Bar2 D.M)) := by
    rw [hbx]
    exact u4x_mem_normalizer_sup hβ (u4x_mem_normalizer_sup hβy hβS)
  exact ⟨_, hXM, hTX, hle, hXd, uc22ine229_mem_normalizer_barPreimage hbW,
    by rw [barImage_barPreimage]; exact hyW⟩

theorem false_of_eq_one (u : R3Pair D L K n p) {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = r)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ r = 1) (hx₁q : x₁ ^ r = 1) (hx₀1 : x₀ ≠ 1)
    (hbx : uc22p21cPi D.M ⟨b, c.hBM hb⟩ = x₀ * x₁) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨X, hXM, hTX, hXH, hXd, hbX, hyX⟩ :=
    u.exists_le_or_le hH₁.1 hH₂.1 hfX hr hr2 hx₀ hx₁ hx₀q hx₁q hx₀1 (b := ⟨b, c.hBM hb⟩) hbN hbx
  replace hbX : b ∈ normalizer (X : Set G) := hbX
  obtain ⟨H, hH, hXH, hbH⟩ : ∃ H ∈ hSet D.T D.M, X ≤ H ∧ b ∈ H := by
    rcases hXH with h | h
    exacts [⟨H₁, hH₁, h, (hL0 (c.hB0.1 hb)).1⟩, ⟨H₂, hH₂, h, (hL0 (c.hB0.1 hb)).2⟩]
  have hYM : zpowers b ⊔ X ≤ D.M := sup_le (zpowers_le.2 (c.hBM hb)) hXM
  have hOY : pCoreOf 2 D.M ≤ zpowers b ⊔ X :=
    (uc22p22c_pCoreOf_le_T D).trans (hTX.trans le_sup_right)
  have hYd : Nat.card ↥(zpowers b ⊔ X) ∣ r ^ 2 * Nat.card D.T := by
    have h := PartTwo.card_sup_mul_card_inf_of_le_normalizer (zpowers_le.2 hbX)
    rw [Nat.card_zpowers, hbo] at h
    calc Nat.card ↥(zpowers b ⊔ X) ∣ Nat.card X * r := ⟨_, h.symm⟩
      _ ∣ r * Nat.card D.T * r := Nat.mul_dvd_mul_right hXd _
      _ = r ^ 2 * Nat.card D.T := by ring
  obtain ⟨l, hlL, hl⟩ := uc22p21c_mem_barImage.1 hx₀
  have hll : ((l * l : ↥D.M) : G) ∈ zpowers b ⊔ X := by
    refine (barPreimage_barImage_of_pCoreOf_le hYM hOY).le
      (uc22p21c_mem_barPreimage.2 ⟨(l * l).2, ?_⟩)
    show uc22p21cPi D.M (l * l) ∈ barImage D.M (zpowers b ⊔ X)
    have e : x₀ * x₀ = x₀ * x₁⁻¹ * (x₀ * x₁) := by
      calc x₀ * x₀ = x₀ * (x₀ * x₁⁻¹) * x₁ := by group
        _ = x₀ * (x₁⁻¹ * x₀) * x₁ := by rw [hcomm x₀ hx₀ _ (inv_mem hx₁)]
        _ = x₀ * x₁⁻¹ * (x₀ * x₁) := by group
    rw [map_mul, hl, e, ← hbx]
    exact mul_mem (barImage_mono le_sup_right hyX)
      (uc22p21c_mem_barImage.2 ⟨⟨b, c.hBM hb⟩, mem_sup_left (mem_zpowers b), rfl⟩)
  have hx₀o : orderOf x₀ = r := orderOf_eq_prime hx₀q hx₀1
  have hw1 : x₀ * x₀ ≠ 1 := fun h => hr2 <| by
    have h2 : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hx₀o] at h2
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2
  have hwq : (x₀ * x₀) ^ r = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hx₀q, one_pow]
  have hdvd : r ∣ orderOf (l * l) := by
    have h := orderOf_map_dvd (uc22p21cPi D.M) (l * l)
    rwa [map_mul, hl, orderOf_eq_prime hwq hw1] at h
  set w : ↥D.M := (l * l) ^ (orderOf (l * l) / r) with hw
  have hwo : orderOf (w : G) = r := by
    rw [Subgroup.orderOf_coe, hw, orderOf_pow_orderOf_div (orderOf_pos _).ne' hdvd]
  have hwL : (w : G) ∈ L := by
    rw [hw, Subgroup.coe_pow, Subgroup.coe_mul]
    exact pow_mem (mul_mem hlL hlL) _
  have hwY : (w : G) ∈ zpowers b ⊔ X := by
    rw [hw, Subgroup.coe_pow]
    exact pow_mem hll _
  have hle : zpowers (w : G) ⊔ D.T ≤ zpowers b ⊔ X :=
    sup_le (zpowers_le.2 hwY) (hTX.trans le_sup_right)
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup.exists_card_eq
  have hcard : Nat.card ↥(zpowers (w : G) ⊔ D.T) ∣ 2 ^ a * r ^ 2 := by
    rw [mul_comm, ← ha]
    exact (Subgroup.card_dvd_of_le hle).trans hYd
  have hwr : Nat.card (zpowers (w : G)) = r := by rw [Nat.card_zpowers, hwo]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := u4x_s21_1Hyp hr hr2 hwr hcard
    (hA _ (zpowers_le.2 hwL) hwr)
  exact uc22s21rn_not_le_of_uniqueMax D hH (h211 h1930 c _ h1 h2 h3 h4 h5 h6).1
    (hle.trans (sup_le (zpowers_le.2 hbH) hXH))

theorem false_of_ne_one (u : R3Pair D L K n p) {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrL : r ∣ Nat.card L)
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = r)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ r = 1) (hx₁q : x₁ ^ r = 1)
    (hc₀ : ∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₀ * f * x₀⁻¹)
    (hc₁ : ∀ f ∈ barImage D.M K, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₁ * f * x₁⁻¹)
    (hc : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)))
    (hc1 : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ≠ 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, -, -, -, hX, hXn, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hbq : b ^ r = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hβq : uc22p21cPi D.M ⟨b, c.hBM hb⟩ ^ r = 1 := by
    rw [← map_pow, show (⟨b, c.hBM hb⟩ : ↥D.M) ^ r = 1 from
      Subtype.ext (by simpa using hbq), map_one]
  have hcq := u4x_pow_eq_one hcomm hx₀ hx₁ hc₀ hc₁ hβq hx₀q hx₁q
  have hxX : x₀ * x₁ ∈ barImage D.M L ⊔ barImage D.M K :=
    mul_mem (mem_sup_left hx₀) (mem_sup_right hx₁)
  haveI := hXn
  have hcN : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈
      normalizer (barImage D.M D.T : Set (Bar2 D.M)) := by
    refine u4x_mem_normalizer_right (fun x hx y hy => Subgroup.mem_centralizer_iff.1 hy x hx)
      hXC hXn inferInstance (u4x_isSylowOf_barImage D.sylowM) hxX hc ?_
    rw [Subgroup.mem_centralizer_iff.1 hc _ hxX, inv_mul_cancel_right]
    exact uc22ine229_mk_mem_normalizer hbN
  obtain ⟨m, hmN, hmo, hmC⟩ := u4x_exists_lift D.sylowM.le (uc22p22c_pCoreOf_le_T D) hc hcN hc1
    hr hcq
  have hmo' : orderOf (m : G) = r := by rw [Subgroup.orderOf_coe]; exact hmo
  have hN := u4p_normalizer_le h869 u.hL u.pX m.2 hr hr2 hmo' (by rw [hX]; exact hmC)
  have hU := u4x_mem_uniqueSet u.hL.1.le u.hc2 hr hr2 hrL hA m.2 hmo' hN
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uc22ine229_s21_1Hyp hr hr2
    (by rw [Nat.card_zpowers, hmo']) (zpowers_le.2 hmN) hU
  exact (h211 h1930 c _ h1 h2 h3 h4 h5 h6).2 (zpowers_le.2 hmN)

end R3Pair

end CFSG.LocalAnalysis.UniquenessCase.UC22
