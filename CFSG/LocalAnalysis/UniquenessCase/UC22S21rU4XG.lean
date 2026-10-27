module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XF
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem exists_le_or_le (u : U4X D L K n) {H₁ H₂ : Subgroup G} (hH₁ : D.T ≤ H₁) (hH₂ : D.T ≤ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ (2 ^ n - 1) = 1) (hx₁q : x₁ ^ (2 ^ n - 1) = 1) (hx₀1 : x₀ ≠ 1) {b : ↥D.M}
    (hbN : (b : G) ∈ normalizer (D.T : Set G)) (hbx : uc22p21cPi D.M b = x₀ * x₁) :
    ∃ X : Subgroup G, X ≤ D.M ∧ D.T ≤ X ∧ (X ≤ H₁ ∨ X ≤ H₂) ∧
      Nat.card X ∣ (2 ^ n - 1) * Nat.card D.T ∧ (b : G) ∈ normalizer (X : Set G) ∧
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
  have hyr : y ^ (2 ^ n - 1) = 1 := by
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
  have hXd : Nat.card ↥(barPreimage D.M W) ∣ (2 ^ n - 1) * Nat.card D.T := by
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
      u.prime_r u.r_ne_two hyr)
  have hlt : D.T < barPreimage D.M W := SetLike.lt_iff_le_and_exists.2 ⟨hTX, (m : G), hmX, hmT⟩
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup.exists_card_eq
  have hsol : Group.IsSolvable ↥(barPreimage D.M W) :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (a := a) (b := 1) Nat.prime_two
      u.prime_r (by rw [pow_one, mul_comm, ← ha]; exact hXd)
  have hle := uc22s21ru3a_le_or_le (uc22p22ta_isSylowIn D hTX) (u4x_covBy hlt u.prime_r hXd)
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

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
