module

public import CFSG.Sporadic.HNOddCore.SylowTwo
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HN.Local.ClassCount
public import CFSG.Sporadic.HN.Local.AltInvolutions
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HN.Local
open Equiv Equiv.Perm

theorem card_type_one :
    (Finset.univ.filter fun g : Perm (Fin 12) => g.cycleType = Multiset.replicate 1 2).card =
      66 := by
  rw [Equiv.Perm.card_of_cycleType]; decide +kernel

theorem card_type_three :
    (Finset.univ.filter fun g : Perm (Fin 12) => g.cycleType = Multiset.replicate 3 2).card =
      13860 := by
  rw [Equiv.Perm.card_of_cycleType]; decide +kernel

theorem card_type_five :
    (Finset.univ.filter fun g : Perm (Fin 12) => g.cycleType = Multiset.replicate 5 2).card =
      62370 := by
  rw [Equiv.Perm.card_of_cycleType]; decide +kernel

theorem involution_odd_type {σ : Perm (Fin 12)} (h : σ ^ 2 = 1) (hs : sign σ = -1) :
    σ.cycleType = Multiset.replicate 1 2 ∨ σ.cycleType = Multiset.replicate 3 2 ∨
      σ.cycleType = Multiset.replicate 5 2 := by
  have hs' : (-1 : ℤˣ) ^ Multiset.card σ.cycleType = -1 := by
    rw [← sign_involution h]; exact hs
  have hle : 2 * Multiset.card σ.cycleType ≤ 12 := by
    have h1 := involution_cycleType h
    have h2 : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
    have h3 : σ.support.card ≤ 12 := by
      simpa using Finset.card_le_univ σ.support
    rw [h1] at h2
    simp only [Multiset.sum_replicate, smul_eq_mul] at h2
    omega
  have hodd : Odd (Multiset.card σ.cycleType) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rw [hev.neg_one_pow] at hs'
    exact absurd hs' (by decide)
  obtain ⟨m, hm⟩ := hodd
  have hk : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 3 ∨
      Multiset.card σ.cycleType = 5 := by omega
  rw [involution_cycleType h]
  rcases hk with hk | hk | hk
  · left; rw [hk]
  · right; left; rw [hk]
  · right; right; rw [hk]

theorem sign_of_type {σ : Perm (Fin 12)} {k : ℕ} (h : σ.cycleType = Multiset.replicate k 2) :
    sign σ = (-1) ^ k := by
  rw [sign_involution (sq_eq_one_of_cycleType_replicate h), h, Multiset.card_replicate]

theorem isConj_RV_of_cycleType
    {r s : RV} (h : (thetaR r).cycleType = (thetaR s).cycleType) :
    IsConj (r : RH) (s : RH) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 h)
  have h2 : IsConj r s := by
    refine isConj_iff.2 ⟨thetaR.symm c, ?_⟩
    apply thetaR.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  exact RV.subtype.map_isConj h2

theorem isConj_HJ_of_cycleType
    {a b : HJ} (ha : (thetaJ a : Perm (Fin 12)) ^ 2 = 1)
    (ha1 : (thetaJ a : Perm (Fin 12)) ≠ 1)
    (h : (thetaJ a : Perm (Fin 12)).cycleType = (thetaJ b : Perm (Fin 12)).cycleType) :
    IsConj (a : JH) (b : JH) := by
  obtain ⟨c, hcA, hc⟩ := exists_conj_alt ha ha1 h
  have h2 : IsConj a b := by
    refine isConj_iff.2 ⟨thetaJ.symm ⟨c, hcA⟩, ?_⟩
    apply thetaJ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  exact HJ.subtype.map_isConj h2

theorem isConj_jR
    {a b : JH} (h : IsConj a b) : IsConj (jR a) (jR b) := jR.map_isConj h

theorem isOuter_cR :
    IsOuter cR := cU_not_mem

theorem isOuter_iff_not_mem
    (r : RH) : IsOuter r ↔ r ∉ jR.range := by
  rw [mem_range_jR_iff]
  rfl

theorem isOuter_conj
    (g r : RH) : IsOuter (g * r * g⁻¹) ↔ IsOuter r := by
  rw [isOuter_iff_not_mem, isOuter_iff_not_mem, not_iff_not]
  constructor
  · intro h
    have := range_jR_normal.conj_mem _ h g⁻¹
    rwa [inv_inv, show g⁻¹ * (g * r * g⁻¹) * g = r by group] at this
  · intro h
    exact range_jR_normal.conj_mem _ h g

theorem isOuter_of_isConj
    {a b : RH} (h : IsConj a b) : IsOuter a ↔ IsOuter b := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact (isOuter_conj g a).symm

theorem not_isOuter_mul
    {r s : RH} (hr : IsOuter r) (hs : IsOuter s) : ¬ IsOuter (r * s) := by
  obtain ⟨a, rfl⟩ := exists_of_isOuter hr
  obtain ⟨b, rfl⟩ := exists_of_isOuter hs
  rw [show jR a * cR * (jR b * cR) = jR (a * conjC b) by
    rw [← mul_assoc, mul_assoc (jR a), cR_mul_jR, map_mul, ← mul_assoc, mul_assoc _ cR,
      cR_mul_self, mul_one]]
  exact not_isOuter_jR _

theorem isOuter_iff_sign
    (r : RV) : IsOuter (r : RH) ↔ sign (thetaR r) = -1 := by
  obtain ⟨r, hr⟩ := r
  rcases (mem_RV_iff r).1 hr with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
  · have e : thetaR ⟨jR h, hr⟩ = (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := thetaR_jR hh
    rw [e, Equiv.Perm.mem_alternatingGroup.1 (thetaJ ⟨h, hh⟩).2]
    exact ⟨fun h' => absurd h' (not_isOuter_jR h), fun h' => absurd h' (by decide)⟩
  · have e : thetaR ⟨jR h * cR, hr⟩ = (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * swap 0 1 := by
      rw [thetaR_apply, thetaRHom_apply, Subtype.coe_mk, thetaFn_jR_mul_cR hh]
    rw [e, Perm.sign_mul, Equiv.Perm.mem_alternatingGroup.1 (thetaJ ⟨h, hh⟩).2, one_mul,
      sign_swap (by decide)]
    exact ⟨fun _ => rfl, fun _ => isOuter_jR_mul_cR h⟩

theorem thetaR_sq
    {r : RV} (h : (r : RH) ^ 2 = 1) : thetaR r ^ 2 = 1 := by
  have e : r ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
  rw [← map_pow, e, map_one]

theorem thetaR_ne_one
    {r : RV} (h : (r : RH) ≠ 1) : thetaR r ≠ 1 := by
  intro e
  apply h
  have e' : r = 1 := thetaR.injective (e.trans (map_one thetaR).symm)
  rw [e', Subgroup.coe_one]

theorem thetaR_jR'
    {h : JH} (hh : jR h ∈ RV) :
    thetaR ⟨jR h, hh⟩ = (thetaJ ⟨h, (jR_mem_RV_iff h).1 hh⟩ : Perm (Fin 12)) :=
  thetaR_jR _

theorem sq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) (ha : a ^ 2 = 1) :
    b ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  rw [conj_pow, ha, mul_one, mul_inv_cancel]

theorem ne_one_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) (ha : a ≠ 1) :
    b ≠ 1 := by
  rintro rfl
  exact ha (isConj_one_left.1 h)

theorem R_pretransitive :
    MulAction.IsPretransitive RH X := by
  have := hns_pretransitive
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq JH x y
  exact ⟨jR g, by rw [jR_smul, hg]⟩

theorem card_CR_c :
    Nat.card (Subgroup.centralizer {cR}) = 7257600 := by
  rw [card_of_split mem_centralizer_cR_iff, card_CJc]

theorem card_T1 :
    Nat.card {h : RH // h ∈ RV ∧ IsConj cR h} = 76296 := by
  have := R_pretransitive
  have h := card_centralizer_mul_card_inter (G := RH) (X := X) x0 cR
  rw [card_CR_c, card_fix_t1, card_RV, show Nat.factorial 12 = 479001600 from rfl] at h
  generalize Nat.card {h : RH // h ∈ MulAction.stabilizer RH x0 ∧ IsConj cR h} = x at h ⊢
  omega

theorem stabilizer_JH :
    MulAction.stabilizer JH x0 = HJ := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_HJ_iff_fix]

theorem card_fix_aJ :
    Nat.card {x : X // aJ • x = x} = 8800 := by
  rw [← card_fix_t6]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [jR_smul])

theorem card_T6 :
    Nat.card {h : JH // h ∈ HJ ∧ IsConj aJ h} = 11880 := by
  have := hns_pretransitive
  have h := card_centralizer_mul_card_inter (G := JH) (X := X) x0 aJ
  rw [card_CJ_t6, card_fix_aJ, stabilizer_JH, card_HJ] at h
  generalize Nat.card {h : JH // h ∈ HJ ∧ IsConj aJ h} = x at h ⊢
  omega

end CFSG.Sporadic.HNOddCore
