module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Overgroup
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Bender
import CFSG.SignalizerFunctorTheorem.NearModels.Main
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.NearSolvable
open CFSG.SignalizerFunctorTheorem.NearModels

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

variable {p : ℕ}

theorem five_le_of_coprime (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) :
    5 ≤ p := by
  rw [card_psu3 hp.one_le] at hcop
  have hp2 : p ≠ 2 := by
    rintro rfl
    revert hcop
    norm_num
  have hp3 : p ≠ 3 := by
    rintro rfl
    revert hcop
    norm_num
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have := hp.two_le
  omega

theorem card_fixedSubgroup (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    Nat.card (signalizerFixedSubgroup f) = 72 := by
  obtain ⟨e⟩ := psu3_fixedSubgroup_mulEquiv hp hcop f hf
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one

theorem order72_fixedSubgroup (hp : p.Prime) (h5 : 5 ≤ p)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    Order72 (signalizerFixedSubgroup f) :=
  ⟨card_fixedSubgroup hp hcop f hf, fun x t ht hxt => by
    have := not_three_dvd_orderOf_of_commute_involution hp h5 (x := (x : PSU3 2 p))
      (t := (t : PSU3 2 p)) (by rwa [Subgroup.orderOf_coe]) (congrArg Subtype.val hxt)
    rwa [Subgroup.orderOf_coe] at this⟩

theorem frame_of_heisenbergInput
    (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (inp : HeisenbergInput p)
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) : Frame p 3 f := by
  have h5 := five_le_of_coprime hp hcop
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hF⟩ := exists_fixedData (order72_fixedSubgroup hp h5 hcop f hf)
  have hFit : fixedFitting f = P := hF.fitting
  have hNeq : fixedNormalizer f = signalizerFixedSubgroup f := by
    rw [fixedNormalizer, hFit]
    exact hF.normalizer_eq inp
  have hPcomm : IsMulCommutative P := Order72.isMulCommutative_of_card_nine P hF.card_P
  have hPne : P ≠ ⊥ := by
    intro hbot
    have := hF.card_P
    rw [hbot, Subgroup.card_bot] at this
    omega
  refine
    { prime := hp
      prime_ℓ := Nat.prime_three
      ord := hf
      coprime := hcop
      simple := CFSG.ShultStronglyClosedTI.unitaryCover_native_simple p hp.two_le
      nonabelian := ?_
      fixed_solvable := ?_
      C0_ne_bot := ?_
      C0_pgroup := ?_
      C0_comm := ?_
      C0_sylow := ?_
      C0_ne := ?_
      C1_ne := ?_
      minimal := ?_
      centralizer_comm := ?_
      fpf := ?_
      normalizer_le := ?_
      overgroup := ?_ }
  ·
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := signalizerFixedSubgroup f) 2
      (by rw [hF.card_C]; norm_num)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 (by rw [hF.card_P]; norm_num)
    have hu2 : orderOf (u : PSU3 2 p) = 2 := by rw [Subgroup.orderOf_coe, hu]
    have hx3 : orderOf (x : PSU3 2 p) = 3 := by rw [Subgroup.orderOf_coe, hx]
    have hx1 : (x : PSU3 2 p) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx3
      omega
    refine ⟨u, x, fun hcomm => ?_⟩
    have huP : (u : PSU3 2 p) ∈ P := hF.mem_of_commute u u.2 x x.2 hx1 hcomm
    have hdvd : orderOf (u : PSU3 2 p) ∣ 9 := hF.card_P ▸ Subgroup.orderOf_dvd_natCard P huP
    rw [hu2] at hdvd
    omega
  · exact nearSimpleModel_fixedSubgroup_solvable hp (Or.inr (Or.inr (Or.inr ⟨MulEquiv.refl _⟩)))
      hcop f hf
  · rw [hFit]
    exact hPne
  · rw [hFit]
    exact IsPGroup.of_card (n := 2) (by rw [hF.card_P]; norm_num)
  · rw [hFit]
    exact hPcomm
  · intro Q hQ hle
    rw [hFit] at hle ⊢
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have hkle : k < 3 := by
      by_contra hk3
      push Not at hk3
      apply not_twentyseven_dvd_card_psu3 hp h5
      have h27 : 27 ∣ Nat.card Q := by
        rw [hk]
        exact (pow_dvd_pow 3 hk3)
      exact h27.trans (Subgroup.card_subgroup_dvd_card Q)
    have hQle : Nat.card Q ≤ 9 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF.card_P]; exact hQle)).symm
  · rw [hFit]
    intro heq
    have := hF.card_C
    rw [← heq, hF.card_P] at this
    omega
  · rw [hFit]
    intro heq
    obtain ⟨z, hzC, hzP, hzcomm⟩ := hF.exists_central
    apply hzP
    rw [← heq]
    exact ⟨hzC, fun x hx => by rw [hFit]; exact hzcomm x hx⟩
  · intro N hNC hNn hN1
    rw [hFit]
    exact hF.normal_le N hNC hNn hN1
  · rw [hFit, inp.centralizer_eq P hF.isElemAbelian hF.card_P]
    exact hPcomm
  · intro v hv hvP z hz hvz
    rw [hFit] at hvP hz
    rw [inp.centralizer_eq P hF.isElemAbelian hF.card_P] at hz
    by_contra hz1
    exact hvP (hF.mem_of_commute v hv z hz hz1 hvz)
  · intro x hx
    rw [hNeq] at hx
    exact ⟨1, Subgroup.one_mem _, x, hx, (one_mul x).symm⟩
  · intro H hCH hH
    rw [hNeq]
    rw [hFit] at *
    exact (eq_of_le_psu3 hp h5 hnear inp hF hCH hH).le


theorem fixedNormalizer_eq_of_heisenbergInput (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) (inp : HeisenbergInput p)
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    fixedNormalizer f = signalizerFixedSubgroup f := by
  obtain ⟨P, hF⟩ := exists_fixedData
    (order72_fixedSubgroup hp (five_le_of_coprime hp hcop) hcop f hf)
  rw [fixedNormalizer, show fixedFitting f = P from hF.fitting]
  exact hF.normalizer_eq inp


theorem isCoatom_fixedNormalizer_of_heisenbergInput
    (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (inp : HeisenbergInput p)
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) : IsCoatom (fixedNormalizer f) := by
  have hF := frame_of_heisenbergInput hp hcop hnear inp f hf
  have hMtop : fixedNormalizer f ≠ ⊤ := by
    intro htop
    have hnorm : (fixedFitting f).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hF.simple.eq_bot_or_eq_top_of_normal (fixedFitting f) with h1 | h1
    · exact hF.C0_ne_bot h1
    · exact hF.C0_ne (le_antisymm (fixedFitting_le f) (h1 ▸ le_top))
  refine ⟨hMtop, fun b hb => ?_⟩
  by_contra hbtop
  exact not_le_of_gt hb (hF.overgroup b ((fixed_le_fixedNormalizer f).trans hb.le) hbtop)

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
