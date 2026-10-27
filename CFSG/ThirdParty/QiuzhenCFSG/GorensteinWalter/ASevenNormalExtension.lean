module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGroupExtension

namespace CFSG
end CFSG
open CFSG

/-!
# Normal A₇ extensions with dihedral Sylow 2-subgroups

The automorphism theorem for A₇ leaves only two possible orders for a faithful
extension of a normal A₇: 2520 and 5040. The second possibility is excluded
because S₇ has no dihedral Sylow 2-subgroup.
-/

noncomputable section

open Equiv
open Equiv.Perm
open GroupTheory.AutAlternating

namespace CFSG.GorensteinWalter

universe u

/-- An element of S₇ whose eighth power is one already has fourth power one.
Cycle lengths divide eight, and every nontrivial cycle has length at most
seven, so only lengths two and four can occur. -/
private theorem perm_fin_seven_pow_four_eq_one_of_pow_eight_eq_one
    (p : Equiv.Perm (Fin 7)) (hp : p ^ 8 = 1) :
    p ^ 4 = 1 := by
  apply (orderOf_dvd_iff_pow_eq_one).mp
  rw [← lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hn2 : 2 ≤ n := two_le_of_mem_cycleType hn
  have hn7 : n ≤ 7 := by
    exact (le_card_support_of_mem_cycleType hn).trans
      (by simpa using Finset.card_le_univ p.support)
  have hndvd8 : n ∣ 8 :=
    (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hp)
  have hndvd : n ∣ 2 ^ 3 := by norm_num at hndvd8 ⊢; exact hndvd8
  obtain ⟨k, hk, hnk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  subst n
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkcases with rfl | rfl | rfl | rfl
  · norm_num at hn2
  · norm_num
  · norm_num
  · norm_num at hn7

/-- The symmetric group on seven letters has no dihedral Sylow 2-subgroup. -/
public theorem not_hasDihedralSylowTwo_perm_fin_seven :
    ¬ HasDihedralSylowTwo (Equiv.Perm (Fin 7)) := by
  intro h
  let S : Sylow 2 (Equiv.Perm (Fin 7)) := Classical.choice Sylow.nonempty
  rcases h S with ⟨m, hm, ⟨e⟩⟩
  have hcardG : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have hfac : (Nat.card (Equiv.Perm (Fin 7))).factorization 2 = 4 := by
    rw [hcardG]
    rw [show 5040 = 2 ^ 4 * 315 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  have hcardS : Nat.card (↥(S : Subgroup (Equiv.Perm (Fin 7)))) = 16 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hcardD : Nat.card (DihedralGroup (2 ^ m)) = 16 := by
    rw [← Nat.card_congr e.toEquiv, hcardS]
  rw [DihedralGroup.nat_card] at hcardD
  have hpow : 2 ^ m = 2 ^ 3 := by
    norm_num at hcardD ⊢
    omega
  have hm3 : m = 3 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  subst m
  let rD : DihedralGroup (2 ^ 3) := DihedralGroup.r 1
  have hrD : orderOf rD = 8 := by
    change orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ 3)) = 8
    rw [DihedralGroup.orderOf_r_one]
    norm_num
  have hrDpow : rD ^ 8 = 1 := by
    simpa [hrD] using pow_orderOf_eq_one rD
  have hrDnot : rD ^ 4 ≠ 1 := by
    intro hh
    have hdiv : orderOf rD ∣ 4 := orderOf_dvd_of_pow_eq_one hh
    rw [hrD] at hdiv
    omega
  let rS : ↥S := e.symm rD
  have hrSpow : rS ^ 8 = 1 := by
    change (e.symm rD) ^ 8 = 1
    calc
      (e.symm rD) ^ 8 = e.symm (rD ^ 8) := by
        exact (map_pow (e.symm : DihedralGroup (2 ^ 3) →* ↥S) rD 8).symm
      _ = 1 := by rw [hrDpow, map_one]
  let pS : Equiv.Perm (Fin 7) := rS
  have hpSpow : pS ^ 8 = 1 := by
    simpa [pS] using congrArg Subtype.val hrSpow
  have hpS4 : pS ^ 4 = 1 :=
    perm_fin_seven_pow_four_eq_one_of_pow_eight_eq_one pS hpSpow
  have hbadS : rS ^ 4 = 1 := by
    apply Subtype.ext
    simpa [pS] using hpS4
  have hbadD : rD ^ 4 = 1 := by
    simpa [rS] using congrArg e hbadS
  exact hrDnot hbadD

/-- A self-centralizing normal subgroup isomorphic to A₇ is the whole ambient
group when the ambient Sylow 2-subgroups are dihedral. -/
public theorem aSeven_normal_extension_eq_top_of_dihedralSylow
    {G : Type u} [Group G] [Finite G]
    (hSylow : HasDihedralSylowTwo G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (eH : H ≃* alternatingGroup (Fin 7))
    (hCH : Subgroup.centralizer (H : Set G) = ⊥) :
    H = ⊤ := by
  let : H.Normal := hHnormal
  rcases quotient_centralizer_mulAut_embedding H with ⟨φ, hφ⟩
  let q : G ≃* G ⧸ Subgroup.centralizer (H : Set G) :=
    ((QuotientGroup.quotientMulEquivOfEq (G := G) hCH).trans
      (QuotientGroup.quotientBot (G := G))).symm
  let ψ : G →* MulAut H := φ.comp q.toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp q.injective
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  have hc : Function.Bijective c :=
    aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num)
  let eAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective c hc
  have hHcard : Nat.card H = 2520 := by
    calc
      Nat.card H = Nat.card (alternatingGroup (Fin 7)) :=
        Nat.card_congr eH.toEquiv
      _ = 2520 := by
        rw [nat_card_alternatingGroup]
        norm_num
  have hPermCard : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have hAutAcard : Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 :=
    (Nat.card_congr eAut.toEquiv).symm.trans hPermCard
  have hAutHcard : Nat.card (MulAut H) = 5040 := by
    calc
      Nat.card (MulAut H) = Nat.card (MulAut (alternatingGroup (Fin 7))) :=
        Nat.card_congr (MulAut.congr eH).toEquiv
      _ = 5040 := hAutAcard
  have hGle : Nat.card G ≤ 5040 := by
    exact (Nat.card_le_card_of_injective ψ hψ).trans_eq hAutHcard
  have hHdvd : Nat.card H ∣ Nat.card G := H.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := hHdvd
  rw [hHcard] at hk
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    exact Nat.card_pos.ne' hk
  have hkle : k ≤ 2 := by omega
  have hkcases : k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl
  · apply Subgroup.eq_top_of_card_eq H
    rw [hHcard, hk]
  · have hGcard : Nat.card G = 5040 := by
      simpa using hk
    have hψbij : Function.Bijective ψ :=
      (Nat.bijective_iff_injective_and_card ψ).mpr
        ⟨hψ, hGcard.trans hAutHcard.symm⟩
    let eGAut : G ≃* MulAut H := MulEquiv.ofBijective ψ hψbij
    let eGS7 : G ≃* Equiv.Perm (Fin 7) :=
      (eGAut.trans (MulAut.congr eH)).trans eAut.symm
    have hS7 : HasDihedralSylowTwo (Equiv.Perm (Fin 7)) :=
      hasDihedralSylowTwo_of_mulEquiv eGS7.symm hSylow
    exact (not_hasDihedralSylowTwo_perm_fin_seven hS7).elim

end CFSG.GorensteinWalter
