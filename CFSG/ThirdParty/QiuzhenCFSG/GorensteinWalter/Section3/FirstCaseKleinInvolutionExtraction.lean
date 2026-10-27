module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinSylowNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
open scoped Pointwise
namespace CFSG.GorensteinWalter
noncomputable section
universe u

/-- Extract an involution outside a normal Klein four with the same action on a point. -/
public theorem firstCase_klein_extract_inverting_involution
    {A X : Type u} [Group A] [Finite A] [Group X] [Finite X]
    (V : Subgroup A) (S : Sylow 2 A)
    (hVnormal : V.Normal) (hVklein : IsKleinFour V)
    (hScard : Nat.card (S : Subgroup A) = 8)
    (eS : S ≃* DihedralGroup 4)
    (φ : A →* MulAut X)
    (x : X)
    (hφVx : ∀ v : A, v ∈ V → φ v x = x)
    {a : A} (haInv : φ a x = x⁻¹) (hxneinv : x⁻¹ ≠ x) :
    ∃ s : A, IsInvolution s ∧ s ∉ V ∧
      φ s x = x⁻¹ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAfac : (Nat.card A).factorization 2 = 3 := by
    have hPcard := Sylow.card_eq_multiplicity S
    rw [hScard] at hPcard
    have hpow : 2 ^ (Nat.card A).factorization 2 = 2 ^ 3 := by
      norm_num at hPcard ⊢
      exact hPcard.symm
    exact (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2)) hpow
  have hVcard : Nat.card V = 4 := hVklein.card_four
  let q : A →* (A ⧸ V) := QuotientGroup.mk' V
  have hVcardeq : Nat.card A = Nat.card (A ⧸ V) * Nat.card V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  have hQfac : (Nat.card (A ⧸ V)).factorization 2 = 1 := by
    have hAeq : Nat.card A = Nat.card (A ⧸ V) * 4 := by
      rw [hVcardeq, hVcard]
    have hAne : Nat.card A ≠ 0 := Nat.card_pos.ne'
    have hQne : Nat.card (A ⧸ V) ≠ 0 := Nat.card_pos.ne'
    have hfac := hAfac
    rw [hAeq, Nat.factorization_mul hQne (by norm_num : (4 : ℕ) ≠ 0)] at hfac
    change (Nat.card (A ⧸ V)).factorization 2 +
      (Nat.factorization 4) 2 = 3 at hfac
    have hfac4 : (Nat.factorization 4) 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self]
    rw [hfac4] at hfac
    omega
  let qa : A ⧸ V := q a
  have hφa_inv : φ a (x⁻¹) = x := by
    rw [map_inv, haInv]
    simp
  have hodd_action : ∀ k : ℕ, Odd k → φ (a ^ k) x = x⁻¹ := by
    intro k hk
    obtain ⟨qk, hqk⟩ := hk
    rw [map_pow, hqk]
    have hqk' : 2 * qk + 1 = 1 + 2 * qk := by omega
    rw [hqk', pow_add, MulAut.mul_apply]
    have hsq : ((φ a) ^ 2) x = x := by
      rw [pow_two, MulAut.mul_apply, haInv, hφa_inv]
    have hfix : ∀ n : ℕ, (((φ a) ^ 2) ^ n) x = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, MulAut.mul_apply, hsq, ih]
    have heven : ((φ a) ^ (2 * qk)) x = x := by
      rw [pow_mul]
      exact hfix qk
    rw [heven, pow_one, haInv]
  have hqa_even : 2 ∣ orderOf qa := by
    by_contra hnot
    have hnotEven : ¬ Even (orderOf qa) := by
      simpa [even_iff_two_dvd] using hnot
    have hqaodd : Odd (orderOf qa) := Nat.not_even_iff_odd.mp hnotEven
    obtain ⟨k, hk⟩ := hqaodd
    have hqpow : qa ^ orderOf qa = 1 := pow_orderOf_eq_one qa
    have hqpow' : q (a ^ orderOf qa) = 1 := by
      simpa [qa, map_pow] using hqpow
    have haV : a ^ orderOf qa ∈ V :=
      (QuotientGroup.eq_one_iff (N := V) (a ^ orderOf qa)).mp hqpow'
    have hInvPow : φ (a ^ orderOf qa) x = x⁻¹ :=
      hodd_action _ ⟨k, hk⟩
    have hFixPow : φ (a ^ orderOf qa) x = x := hφVx _ haV
    exact hxneinv (hInvPow.symm.trans hFixPow)
  let d := orderOf qa
  have hdpos : 0 < d := orderOf_pos qa
  have hdvdQ : d ∣ Nat.card (A ⧸ V) := orderOf_dvd_natCard qa
  have hnot4Q : ¬ 4 ∣ Nat.card (A ⧸ V) := by
    intro h4
    have hfac4 := (Nat.prime_two.pow_dvd_iff_le_factorization (k := 2)
      (Nat.card_pos (α := A ⧸ V)).ne').mp (by
        simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using h4)
    rw [hQfac] at hfac4
    norm_num at hfac4
  have hhalfOdd : Odd (d / 2) := by
    by_contra hnotOdd
    have hEven : Even (d / 2) := Nat.not_odd_iff_even.mp hnotOdd
    obtain ⟨k, hk⟩ := hEven
    have hdEq : 2 * (d / 2) = d := Nat.mul_div_cancel' hqa_even
    have h4d : 4 ∣ d := by
      rw [← hdEq, hk]
      refine ⟨k, ?_⟩
      omega
    exact hnot4Q (h4d.trans hdvdQ)
  let rbar : A ⧸ V := qa ^ (d / 2)
  have hrbar_order : orderOf rbar = 2 := by
    dsimp [rbar]
    exact orderOf_pow_orderOf_div (x := qa) (n := 2)
      (by exact (orderOf_pos qa).ne') hqa_even
  have hrbar_inv : IsInvolution rbar := by
    exact ⟨by
      intro h
      have : orderOf rbar = 1 := by rw [h, orderOf_one]
      omega, by
      have h := pow_orderOf_eq_one rbar
      rw [hrbar_order] at h
      simpa [pow_two] using h⟩
  obtain ⟨r, hrq⟩ := QuotientGroup.mk'_surjective V rbar
  have hInvHalf : φ (a ^ (d / 2)) x = x⁻¹ :=
    hodd_action _ hhalfOdd
  have hqra : q r = q (a ^ (d / 2)) := by
    change (↑r : A ⧸ V) = _
    simpa [rbar, qa] using hrq
  obtain ⟨z, hzV, hza⟩ := (QuotientGroup.mk'_eq_mk' (N := V)).mp hqra
  have hFixZ : φ z x = x := hφVx z hzV
  have hInvR : φ r x = x⁻¹ := by
    have hza' : r * z = a ^ (d / 2) := hza
    have hmap := congrArg (fun y : X => y) hInvHalf
    calc
      φ r x = φ r (φ z x) := by rw [hFixZ]
      _ = φ (r * z) x := by rw [map_mul, MulAut.mul_apply]
      _ = φ (a ^ (d / 2)) x := by rw [hza']
      _ = x⁻¹ := hInvHalf
  have hrnotV : r ∉ V := by
    intro hrV
    exact hxneinv (hInvR.symm.trans (hφVx r hrV))
  have hr2V : r ^ 2 ∈ V := by
    have hq2 : q (r ^ 2) = 1 := by
      rw [map_pow, hrq]
      have h := pow_orderOf_eq_one rbar
      rw [hrbar_order] at h
      simpa [pow_two] using h
    exact (QuotientGroup.eq_one_iff (N := V) (r ^ 2)).mp hq2
  have hr4 : r ^ 4 = 1 := by
    have hzsq : (r ^ 2) ^ 2 = 1 := by
      simpa [pow_two] using congrArg Subtype.val
        (hVklein.mul_self ⟨r ^ 2, hr2V⟩)
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact hzsq
  have hrord_dvd : orderOf r ∣ 4 :=
    orderOf_dvd_of_pow_eq_one hr4
  have hrp : IsPGroup 2 (Subgroup.zpowers r) := by
    have hcard : Nat.card (Subgroup.zpowers r) ∣ 4 := by
      rw [Nat.card_zpowers]
      exact hrord_dvd
    obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow (m := 2) Nat.prime_two).mp
      (by simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcard)
    have hcardeq : Nat.card (Subgroup.zpowers r) = orderOf r :=
      Nat.card_zpowers r
    have hcardpow : Nat.card (Subgroup.zpowers r) = 2 ^ k :=
      hcardeq.trans hpow
    exact IsPGroup.of_card hcardpow
  have hVp : IsPGroup 2 V := by
    have hVcardPow : Nat.card V = 2 ^ 2 := by rw [hVcard]; norm_num
    exact IsPGroup.of_card hVcardPow
  have hVnormR : Subgroup.zpowers r ≤ Subgroup.normalizer (V : Set A) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact hVnormal.conj_mem v hv z
    · intro hv
      have hback := hVnormal.conj_mem (z * v * z⁻¹) hv z⁻¹
      simpa [mul_assoc] using hback
  let P : Subgroup A := V ⊔ Subgroup.zpowers r
  have hPp : IsPGroup 2 P := by
    exact hVp.to_sup_of_normal_left' hrp hVnormR
  obtain ⟨S', hPS'⟩ := hPp.exists_le_sylow
  have eS' : S' ≃* DihedralGroup 4 := by
    let e : S' ≃* S := Sylow.equiv S' S
    exact e.trans eS
  have hS'card : Nat.card (S' : Subgroup A) = 8 := by
    calc
      Nat.card (S' : Subgroup A) = Nat.card S' := by rfl
      _ = Nat.card S := Nat.card_congr (Sylow.equiv S' S).toEquiv
      _ = 8 := hScard
  have hPcard_ge : 8 ≤ Nat.card P := by
    have hVleP : V ≤ P := le_sup_left
    have hVltP : V < P := lt_of_le_of_ne hVleP (by
      intro hEq
      apply hrnotV
      exact hEq ▸ (le_sup_right : Subgroup.zpowers r ≤ P)
        (Subgroup.mem_zpowers r))
    have hVcardle : Nat.card V ≤ Nat.card P := Subgroup.card_le_of_le hVleP
    have hVcardne : Nat.card V ≠ Nat.card P := by
      intro heq
      apply hVltP.ne
      exact Subgroup.eq_of_le_of_card_ge hVleP heq.ge
    have hVcardlt : Nat.card V < Nat.card P := lt_of_le_of_ne hVcardle hVcardne
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hVcard] at hVcardlt
    rw [hk] at hVcardlt
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hklt : k < 3 := by omega
      interval_cases k <;> norm_num at hVcardlt
    have hpow : 2 ^ 3 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : (2 : ℕ) > 0) hk3
    simpa [hk] using hpow
  have hPcard : Nat.card P = 8 := by
    have hPle : Nat.card P ≤ Nat.card (S' : Subgroup A) :=
      Subgroup.card_le_of_le hPS'
    rw [hS'card] at hPle
    exact le_antisymm hPle hPcard_ge
  have hPeqS' : P = (S' : Subgroup A) := by
    exact Subgroup.eq_of_le_of_card_ge hPS' (by rw [hPcard, hS'card])
  have hVindex : (V.subgroupOf P).index = 2 := by
    have hmul := (V.subgroupOf P).card_mul_index
    have hVsubcard : Nat.card (V.subgroupOf P) = 4 := by
      rw [natCard_subgroupOf_eq V P le_sup_left, hVcard]
    rw [hVsubcard, hPcard] at hmul
    omega
  let V' : Subgroup S' := V.subgroupOf (S' : Subgroup A)
  have hV'card : Nat.card V' = 4 := by
    rw [natCard_subgroupOf_eq V (S' : Subgroup A) (le_sup_left.trans hPS'), hVcard]
  have hV'neTop : V' ≠ ⊤ := by
    intro htop
    have hcardeq : Nat.card V' = Nat.card (S' : Subgroup A) := by
      rw [htop]
      calc
        Nat.card (⊤ : Subgroup S') = Nat.card S' :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
        _ = Nat.card (S' : Subgroup A) := by rfl
    rw [hV'card, hS'card] at hcardeq
    omega
  obtain ⟨s0, hsOrder, hsnot⟩ :=
    GorensteinWalter.exists_involution_not_mem_of_dihedral_mulEquiv
      (m := 2) eS' V' hV'neTop
  let s : A := (s0 : A)
  have hsV : s ∉ V := by
    intro hs
    apply hsnot
    exact Subgroup.mem_subgroupOf.mpr (by simpa [s] using hs)
  have hsrV : s * r⁻¹ ∈ V := by
    let sP : P := ⟨s, by
      rw [hPeqS']
      exact s0.2⟩
    let rP : P := ⟨r, (le_sup_right : Subgroup.zpowers r ≤ P)
      (Subgroup.mem_zpowers r)⟩
    have hsrVP : sP * rP⁻¹ ∈ V.subgroupOf P := by
      apply (Subgroup.mul_mem_iff_of_index_two hVindex).2
      constructor
      · intro hsPmem
        exfalso
        exact hsV (Subgroup.mem_subgroupOf.mp hsPmem)
      · intro hrPmem
        exfalso
        apply hrnotV
        have hinv : r⁻¹ ∈ V := by simpa [rP] using
          (Subgroup.mem_subgroupOf.mp hrPmem)
        simpa using V.inv_mem hinv
    exact Subgroup.mem_subgroupOf.mp hsrVP
  have hFixSR : φ (s * r⁻¹) x = x := hφVx _ hsrV
  have hInvRinv : φ (r⁻¹) x = x⁻¹ := by
    have hcomp : φ (r⁻¹) (φ r x) = x := by
      simp [map_inv]
    rw [hInvR] at hcomp
    have hcomp' := congrArg (fun w : X => w⁻¹) hcomp
    simpa [map_inv] using hcomp'
  have hInvS : φ s x = x⁻¹ := by
    calc
      φ s x = φ (s * r⁻¹ * r) x := by simp
      _ = φ (s * r⁻¹) (φ r x) := by rw [map_mul, MulAut.mul_apply]
      _ = φ (s * r⁻¹) (x⁻¹) := by rw [hInvR]
      _ = (φ (s * r⁻¹) x)⁻¹ := by rw [map_inv]
      _ = x⁻¹ := by rw [hFixSR]
  have hsne : s ≠ 1 := by
    intro hs1
    apply hsV
    simpa [hs1] using (V.one_mem)
  have hssq : s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s0
    rw [hsOrder] at h
    exact congrArg Subtype.val h
  exact ⟨s, ⟨hsne, hssq⟩, hsV, hInvS⟩

end
end CFSG.GorensteinWalter
