module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd inner automorphisms fixing two commuting involutions

The reflected-torus endpoint in Section 4 supplies two distinct commuting
involutions fixed by the local Fitting action.  Once Fact 1.10(ii) places
that action in the inner automorphism group of `PSL₂`, the two involutions
generate a Klein four.  Its self-centralizer contains the inner
representative; the representative has odd order, so it is trivial.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An odd-order inner automorphism of `PSL₂(K)` fixing two distinct
commuting involutions is trivial. -/
public theorem psl2_odd_inner_fixing_commuting_involutions_eq_one
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (φ : MulAut (PSL2 K)) (n : ℕ) (hn : Odd n)
    (hφpow : φ ^ n = 1)
    (t s : PSL2 K) (ht : IsInvolution t) (hs : IsInvolution s)
    (hts : t ≠ s) (hcomm : Commute t s)
    (hφt : φ t = t) (hφs : φ s = s)
    (hinner : ∃ a : PSL2 K, φ = MulAut.conj a) :
    φ = 1 := by
  classical
  rcases hinner with ⟨a, rfl⟩
  obtain ⟨V, hV, htV, hsV⟩ :=
    exists_kleinFour_of_commuting_involutions t s ht hs hts hcomm
  have hφt' : a * t * a⁻¹ = t := by
    simpa [MulAut.conj_apply] using hφt
  have hφs' : a * s * a⁻¹ = s := by
    simpa [MulAut.conj_apply] using hφs
  have ha_cent_t : a * t = t * a := by
    calc
      a * t = (a * t * a⁻¹) * a := by group
      _ = t * a := by rw [hφt']
  have ha_cent_s : a * s = s * a := by
    calc
      a * s = (a * s * a⁻¹) * a := by group
      _ = s * a := by rw [hφs']
  have ha_cent_V : a ∈ Subgroup.centralizer (V : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let : IsKleinFour V := hV
    let : Fintype V := Fintype.ofFinite V
    let tV : V := ⟨t, htV⟩
    let sV : V := ⟨s, hsV⟩
    let xV : V := ⟨x, hx⟩
    have htVne : tV ≠ 1 := fun h => ht.1 (congrArg Subtype.val h)
    have hsVne : sV ≠ 1 := fun h => hs.1 (congrArg Subtype.val h)
    have htsV : tV ≠ sV := fun h => hts (congrArg Subtype.val h)
    have huniv : ({tV * sV, tV, sV, (1 : V)} : Finset V) = Finset.univ :=
      IsKleinFour.eq_finset_univ htVne hsVne htsV
    have hx_cases : xV = tV * sV ∨ xV = tV ∨ xV = sV ∨ xV = 1 := by
      have hxmem : xV ∈ ({tV * sV, tV, sV, (1 : V)} : Finset V) := by
        rw [huniv]
        exact Finset.mem_univ xV
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxmem
    rcases hx_cases with h | h | h | h
    · have hx' : x = t * s := congrArg Subtype.val h
      rw [hx']
      calc
        t * s * a = t * (s * a) := by simp [mul_assoc]
        _ = t * (a * s) := by rw [ha_cent_s.symm]
        _ = (t * a) * s := by simp [mul_assoc]
        _ = (a * t) * s := by rw [ha_cent_t.symm]
        _ = a * (t * s) := by simp [mul_assoc]
    · have hx' : x = t := congrArg Subtype.val h
      simpa [hx'] using ha_cent_t.symm
    · have hx' : x = s := congrArg Subtype.val h
      simpa [hx'] using ha_cent_s.symm
    · have hx' : x = 1 := congrArg Subtype.val h
      simp [hx']
  have haV : a ∈ V := by
    rw [← psl2_kleinFour_centralizer_eq_self K hK V hV]
    exact ha_cent_V
  have hconjpow : MulAut.conj (a ^ n) = 1 := by
    simpa [map_pow] using hφpow
  have hacenter : a ^ n ∈ Subgroup.center (PSL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun hconjpow x
    change a ^ n * x * (a ^ n)⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hx)).symm
  have hcenter : Subgroup.center (PSL2 K) = ⊥ := psl2_center_eq_bot K
  have han : a ^ n = 1 := by
    rw [hcenter] at hacenter
    exact Subgroup.mem_bot.mp hacenter
  have haorder_dvd : orderOf a ∣ n := (orderOf_dvd_iff_pow_eq_one).2 han
  have haodd : Odd (orderOf a) := Odd.of_dvd_nat hn haorder_dvd
  have ha2 : a ^ 2 = 1 := by
    let : IsKleinFour V := hV
    simpa [pow_two] using
      congrArg Subtype.val (IsKleinFour.mul_self (⟨a, haV⟩ : V))
  have haorder_dvd_two : orderOf a ∣ 2 := (orderOf_dvd_iff_pow_eq_one).2 ha2
  have haorder : orderOf a = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp haorder_dvd_two with h | h
    · exact h
    · exfalso
      rw [h] at haodd
      exact haodd.not_two_dvd_nat (by simp)
  have haone : a = 1 := orderOf_eq_one_iff.mp haorder
  rw [haone]
  simp

end CFSG.GorensteinWalter
