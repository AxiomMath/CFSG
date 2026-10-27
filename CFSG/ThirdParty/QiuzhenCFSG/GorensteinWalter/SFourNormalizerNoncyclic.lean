module
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourCentralizerOrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter
universe u

public theorem sfour_normalizer_not_cyclic
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hPcard : Nat.card (P : Subgroup H) = 3)
    (he : Nonempty (H ≃* Equiv.Perm (Fin 4))) :
    ¬ IsCyclic (Subgroup.normalizer (P : Set H)) := by
  classical
  have hp : p = 3 := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hnpos : n ≠ 0 := by
      intro hn0
      rw [hn0, pow_zero] at hn
      omega
    have hpdiv : p ∣ 3 := by
      rw [← hPcard, hn]
      exact dvd_pow_self p hnpos
    exact (Nat.dvd_prime Nat.prime_three).mp hpdiv |>.resolve_left
      ((Fact.out : Nat.Prime p).ne_one)
  subst p
  let e : H ≃* Equiv.Perm (Fin 4) := he.some
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (show (P : Subgroup H) ≠ ⊥ by
      rw [← Subgroup.one_lt_card_iff_ne_bot]
      simpa [hPcard])
  have hxP : (x : H) ∈ (P : Subgroup H) := x.property
  have hxneH : (x : H) ≠ 1 := by
    intro h
    apply hxne
    exact Subtype.ext h
  have hxorderP : orderOf (x : H) = 3 := by
    have hxdiv : orderOf (x : H) ∣ Nat.card (P : Subgroup H) :=
      Subgroup.orderOf_dvd_natCard (P : Subgroup H) hxP
    have hxpow : (x : H) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      simpa [hPcard] using hxdiv
    exact orderOf_eq_prime hxpow hxneH
  have hxeorder : orderOf (e (x : H)) = 3 := by
    exact (orderOf_injective e.toMonoidHom e.injective (x : H)).trans hxorderP
  intro hNcyc
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hNleC : N ≤ Subgroup.centralizer ({(x : H)} : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y = (x : H) := by simpa using hy
    subst y
    have hcomm : (n : H) * (x : H) = (x : H) * (n : H) := by
      let nN : N := ⟨n, hn⟩
      let yN : N := ⟨(x : H), Subgroup.le_normalizer hxP⟩
      exact congrArg Subtype.val
        (hNcyc.isMulCommutative.is_comm.comm nN yN)
    exact hcomm.symm
  let Nmap : Subgroup (Equiv.Perm (Fin 4)) := N.map e.toMonoidHom
  have hNmaple : Nmap ≤
      Subgroup.centralizer ({e (x : H)} : Set (Equiv.Perm (Fin 4))) := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y = e (x : H) := by simpa using hy
    subst y
    have hnx := hNleC hn
    have hcomm : (x : H) * n = n * (x : H) :=
      hnx (x : H) (by simp)
    change e (x : H) * e n = e n * e (x : H)
    simpa using congrArg e hcomm
  have hNcard_le : Nat.card N ≤ 3 := by
    have hdiv : Nat.card Nmap ∣ Nat.card (Subgroup.centralizer
        ({e (x : H)} : Set (Equiv.Perm (Fin 4)))) :=
      Subgroup.card_dvd_of_le hNmaple
    have hcent : Nat.card (Subgroup.centralizer
        ({e (x : H)} : Set (Equiv.Perm (Fin 4)))) = 3 := by
      rw [sFour_centralizer_order_three_eq_zpowers hxeorder,
        Nat.card_zpowers, hxeorder]
    have hmapcard : Nat.card Nmap = Nat.card N :=
      Subgroup.card_map_of_injective e.injective
    rw [hmapcard, hcent] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hPsubN : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
  have hNcard_ge : 3 ≤ Nat.card N := by
    have hdiv : Nat.card (P : Subgroup H) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le hPsubN
    rw [hPcard] at hdiv
    exact Nat.le_of_dvd (Nat.card_pos) hdiv
  have hNcard : Nat.card N = 3 := by omega
  have hNP : N = (P : Subgroup H) := by
    exact (Subgroup.eq_of_le_of_card_ge hPsubN
      (by simpa [hPcard, hNcard])).symm
  have hSylowCount : Nat.card (Sylow 3 H) = 8 := by
    calc
      Nat.card (Sylow 3 H) = N.index := P.card_eq_index_normalizer
      _ = (P : Subgroup H).index := by rw [hNP]
      _ = 8 := by
        have hi := (P : Subgroup H).index_mul_card
        have hHcard : Nat.card H = 24 := by
          calc
            Nat.card H = Nat.card (Equiv.Perm (Fin 4)) := Nat.card_congr e.toEquiv
            _ = 24 := by simp [Fintype.card_perm, Nat.factorial]
        rw [hPcard, hHcard] at hi
        omega
  have hmod := card_sylow_modEq_one 3 H
  rw [hSylowCount] at hmod
  norm_num at hmod

public theorem sfour_normalizer_not_cyclic_of_prime_card
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (P : Sylow p H)
    (hPcard : Nat.card (P : Subgroup H) = p)
    (he : Nonempty (H ≃* Equiv.Perm (Fin 4))) :
    ¬ IsCyclic (Subgroup.normalizer (P : Set H)) := by
  have hp3 : p = 3 := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hnpos : n ≠ 0 := by
      intro hn0
      rw [hn0, pow_zero] at hn
      exact (Fact.out : Nat.Prime p).ne_one (hPcard.symm.trans hn)
    have hpdivP : p ∣ Nat.card (P : Subgroup H) := by
      rw [hPcard]
    have hPdivH : Nat.card (P : Subgroup H) ∣ Nat.card H := by
      simpa using (Subgroup.card_dvd_of_le
        (H := (P : Subgroup H)) (K := (⊤ : Subgroup H)) le_top)
    have hpdivH : p ∣ Nat.card H := hpdivP.trans hPdivH
    have hHcard : Nat.card H = 24 := by
      calc
        Nat.card H = Nat.card (Equiv.Perm (Fin 4)) :=
          Nat.card_congr he.some.toEquiv
        _ = 24 := by simp [Fintype.card_perm, Nat.factorial]
    rw [hHcard] at hpdivH
    have hpdiv : p ∣ 2 ^ 3 * 3 := by simpa using hpdivH
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime p)).mp hpdiv with hp2 | hp3
    · have hp2' : p ∣ 2 :=
        (Fact.out : Nat.Prime p).dvd_of_dvd_pow hp2
      have hp2eq : p = 2 := by
        exact (Nat.dvd_prime Nat.prime_two).mp hp2' |>.resolve_left
          ((Fact.out : Nat.Prime p).ne_one)
      exact (hpodd.not_two_dvd_nat (by simpa [hp2eq])).elim
    · exact (Nat.dvd_prime Nat.prime_three).mp hp3 |>.resolve_left
        ((Fact.out : Nat.Prime p).ne_one)
  subst p
  exact sfour_normalizer_not_cyclic P (by simpa using hPcard) he

end CFSG.GorensteinWalter
