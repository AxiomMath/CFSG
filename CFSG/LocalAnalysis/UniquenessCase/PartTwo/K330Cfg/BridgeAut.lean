module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Generic
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy)

namespace OneComp

variable {K : Type} [Group K] [Finite K] {J M X P : Subgroup K}

theorem exists_automorphism_seven (h : OneComp J M X P) (h7 : ¬ 7 ∣ Nat.card J) :
    ∃ W : Subgroup (MulAut ↥J), Nat.card W = 7 ∧
      (∀ w ∈ W, ∀ x ∈ X.subgroupOf J, w x = x) ∧ ∀ x ∈ fixedBy W, (x : K) ∈ M := by
  have h7M : 7 ∣ Nat.card M := h.strong.2.1
  have h7P : 7 ∣ Nat.card P := by
    rw [h.sylowSeven.card_eq]
    exact pow_dvd_pow 7 (Nat.succ_le_of_lt <|
      Nat.Prime.factorization_pos_of_dvd (by norm_num) (Nat.card_pos (α := M)).ne' h7M)
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 7 h7P
  let yK : K := y
  have hyKP : yK ∈ P := y.2
  have hyKord : orderOf yK = 7 := by
    simpa [yK] using (Subgroup.orderOf_coe y).trans hyord
  letI : J.Normal := h.normal
  let ρ : K →* MulAut ↥J := MulAut.conjNormal
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hgcent : g ∈ Subgroup.centralizer (J : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hval : g * j * g⁻¹ = j := by
        have h := congrArg (fun z : ↥J => (z : K))
          (congrArg (fun f : MulAut ↥J => f ⟨j, hj⟩) hg)
        simpa [ρ, MulAut.conjNormal_apply] using h
      exact (mul_inv_eq_iff_eq_mul.1 hval).symm
    rw [h.centralizer_eq_bot] at hgcent
    simpa using hgcent
  let W : Subgroup (MulAut ↥J) := (Subgroup.zpowers yK).map ρ
  have hcardW : Nat.card W = 7 := by
    rw [show W = (Subgroup.zpowers yK).map ρ from rfl,
      Subgroup.card_map_of_injective hρinj, Nat.card_zpowers, hyKord]
  have hfixW : ∀ w ∈ W, ∀ x ∈ X.subgroupOf J, w x = x := by
    intro w hw x hx
    rw [Subgroup.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzP : z ∈ P := Subgroup.zpowers_le.mpr hyKP hz
    have hxX : (x : K) ∈ X := hx
    have hcomm : (x : K) * z = z * (x : K) :=
      Subgroup.mem_centralizer_iff.1 (h.le_centralizer hzP) (x : K) hxX
    apply Subtype.ext
    simp only [ρ, MulAut.conjNormal_apply]
    exact mul_inv_eq_iff_eq_mul.2 hcomm.symm
  have hfixedM : ∀ x ∈ fixedBy W, (x : K) ∈ M := by
    intro x hx
    have hmem : ρ yK ∈ W :=
      Subgroup.mem_map.mpr ⟨yK, Subgroup.mem_zpowers yK, rfl⟩
    have hfix := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven.mem_fixedBy.1 hx) (ρ yK) hmem
    have hval : yK * (x : K) * yK⁻¹ = (x : K) := by
      have h := congrArg (fun z : ↥J => (z : K)) hfix
      simpa [ρ, MulAut.conjNormal_apply] using h
    have hxy : (x : K) * yK = yK * (x : K) :=
      (mul_inv_eq_iff_eq_mul.1 hval).symm
    have hxcent : (x : K) ∈ Subgroup.centralizer (Subgroup.zpowers yK : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      change z ∈ Subgroup.zpowers yK at hz
      rw [Subgroup.mem_zpowers_iff] at hz
      obtain ⟨k, rfl⟩ := hz
      exact (Commute.zpow_left hxy.symm k).eq
    have hxnorm : (x : K) ∈ Subgroup.normalizer (Subgroup.zpowers yK : Set K) :=
      Subgroup.centralizer_le_normalizer _ hxcent
    exact h.normalizer_le_of_seven (R := Subgroup.zpowers yK)
      (Subgroup.zpowers_le.mpr (h.sylowSeven.le hyKP))
      (by rw [Nat.card_zpowers, hyKord]) hxnorm
  exact ⟨W, hcardW, hfixW, hfixedM⟩

end OneComp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
