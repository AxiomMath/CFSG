module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

set_option maxHeartbeats 400000

/-- In `A₇`, no nontrivial involution centralizes an element of prime order
`5` or `7`. -/
public theorem aSeven_no_involution_centralizes_prime_five_seven
    {p : ℕ} (hp : p.Prime) (hp57 : p = 5 ∨ p = 7)
    (x t : alternatingGroup (Fin 7))
    (hx : x ≠ 1) (hxp : x ^ p = 1)
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hcomm : t * x = x * t) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let σ : Equiv.Perm (Fin 7) := x
  let τ : Equiv.Perm (Fin 7) := t
  have hσp : σ ^ p = 1 := by
    exact congrArg Subtype.val hxp
  have hσne : σ ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact h
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσne
  have hcard : σ.support.card < 2 * orderOf σ := by
    have hle : σ.support.card ≤ 7 := by
      simpa using Finset.card_le_card (Finset.subset_univ σ.support)
    have hlt : 7 < 2 * p := by
      rcases hp57 with rfl | rfl <;> norm_num
    omega
  have hc : σ.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order (by simpa [hord] using hp) (by simpa [hord] using hcard)
  have hcommτσ : Commute τ σ := by
    exact congrArg Subtype.val hcomm
  rcases (hc.commute_iff).mp hcommτσ with ⟨hc', hpow⟩
  rcases Subgroup.mem_zpowers_iff.mp hpow with ⟨k, hk⟩
  have hres (y : Fin 7) (hy : y ∈ σ.support) : τ y = (σ ^ k) y := by
    have h := congrArg (fun f : Equiv.Perm (Fin 7) => f y) hk.symm
    have hsub : Equiv.Perm.ofSubtype (τ.subtypePerm hc') y = τ y := by
      rw [Equiv.Perm.ofSubtype_apply_of_mem
        (p := fun z : Fin 7 => z ∈ σ.support) (τ.subtypePerm hc') hy]
      rfl
    simpa [hsub] using h
  have hτ2 : τ ^ 2 = 1 := by
    change (τ ^ 2 = 1)
    simpa [τ, pow_two] using
      congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) ht2
  obtain ⟨a, ha⟩ := hc.nonempty_support
  have hfix : (σ ^ k) ((σ ^ k) a) = a := by
    have h1 : τ (τ a) = a := by
      have hc : (τ ^ 2) a = a :=
        congrArg (fun f : Equiv.Perm (Fin 7) => f a) hτ2
      simpa [τ, pow_two] using hc
    have h2 : τ a = (σ ^ k) a := hres a ha
    have h3 : τ ((σ ^ k) a) = (σ ^ k) ((σ ^ k) a) := by
      have hmem : (σ ^ k) a ∈ σ.support := by
        exact Equiv.Perm.zpow_apply_mem_support.mpr ha
      exact hres ((σ ^ k) a) hmem
    calc
      (σ ^ k) ((σ ^ k) a) = τ ((σ ^ k) a) := h3.symm
      _ = τ (τ a) := by rw [h2]
      _ = a := h1
  have hcOn : σ.IsCycleOn (σ.support : Set (Fin 7)) := by
    convert hc.isCycleOn using 1
    ext y
    simp [Equiv.Perm.mem_support]
  have hzpow : (σ ^ (2 * k : ℤ)) a = a := by
    simpa [zpow_add, two_mul] using hfix
  have hzdiv : ((σ.support.card : ℤ) ∣ 2 * k) :=
    (hcOn.zpow_apply_eq ha).mp hzpow
  have hnat : p ∣ (2 * k).natAbs := by
    rw [← hc.orderOf, hord] at hzdiv
    exact Int.natCast_dvd_natCast.1 (Int.dvd_natAbs.2 hzdiv)
  have hnat2 : p ∣ 2 * k.natAbs := by
    simpa [Int.natAbs_mul] using hnat
  have hp2 : p ≠ 2 := by
    rcases hp57 with rfl | rfl <;> norm_num
  have hpk : p ∣ k.natAbs := by
    rcases (hp.dvd_mul.mp hnat2) with h | h
    · exact False.elim (hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
    · exact h
  have hpz0 : (p : ℤ) ∣ (k.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hpk
  have hpz : (p : ℤ) ∣ k := by
    simpa using Int.natAbs_dvd.mpr hpz0
  have hτfix : ∀ y : Fin 7, y ∈ σ.support → τ y = y := by
    intro y hy
    have hk1 : (σ ^ k) y = y := by
      have hd : ((σ.support.card : ℤ) ∣ k) := by
        rw [← hc.orderOf, hord]
        exact hpz
      exact (hcOn.zpow_apply_eq hy).mpr hd
    rw [hres y hy, hk1]
  have hsp : σ.support.card = p := by
    rw [← hc.orderOf, hord]
  have hsub : τ.support ⊆ σ.supportᶜ := by
    intro y hy
    rw [Finset.mem_compl]
    intro hyσ
    have hyne : τ y ≠ y := Equiv.Perm.mem_support.mp hy
    exact hyne (hτfix y hyσ)
  have hcardle : τ.support.card ≤ 7 - σ.support.card := by
    have hle := Finset.card_le_card hsub
    rwa [Finset.card_compl] at hle
  rcases hp57 with hp5 | hp7
  · subst p
    have hle2 : τ.support.card ≤ 2 := by
      omega
    have hne0 : τ.support.card ≠ 0 := by
      intro h0
      apply ht
      apply Subtype.ext
      exact Equiv.Perm.card_support_eq_zero.mp h0
    have hne1 : τ.support.card ≠ 1 := Equiv.Perm.card_support_ne_one τ
    have hcard2 : τ.support.card = 2 := by omega
    have hswap : τ.IsSwap := Equiv.Perm.card_support_eq_two.mp hcard2
    have hsign : Equiv.Perm.sign τ = -1 := hswap.sign_eq
    have hsign1 : Equiv.Perm.sign τ = 1 := by
      change Equiv.Perm.sign τ = 1
      exact (MonoidHom.mem_ker (f := Equiv.Perm.sign)).mp t.property
    have hbad : (-1 : ℤˣ) = 1 := hsign.symm.trans hsign1
    norm_num at hbad
  · subst p
    have hle0 : τ.support.card ≤ 0 := by omega
    have hcard0 : τ.support.card = 0 := by omega
    have hτ1 : τ = 1 := Equiv.Perm.card_support_eq_zero.mp hcard0
    apply ht
    apply Subtype.ext
    exact hτ1

/-- In `A₇`, no nontrivial involution centralizes a nontrivial `p`-subgroup
for `p = 5` or `p = 7`. -/
public theorem aSeven_no_involution_centralizes_oddP_five_seven
    {p : ℕ} (hp : p.Prime) (hp57 : p = 5 ∨ p = 7)
    (P : Subgroup (alternatingGroup (Fin 7)))
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥)
    {t : alternatingGroup (Fin 7)} (ht : IsInvolution t)
    (hPcent : P ≤ Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) :
    False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hcard_ne1 : Nat.card (↥P) ≠ 1 := by
    intro h1
    apply hPne
    exact (Subgroup.eq_bot_iff_card P).2 h1
  have hpcard : p ∣ Nat.card (↥P) := by
    rcases (IsPGroup.iff_card.mp hPp) with ⟨n, hn⟩
    have hnpos : n ≠ 0 := by
      intro h0
      apply hcard_ne1
      rw [hn, h0]
      norm_num
    rw [hn]
    exact dvd_pow_self p hnpos
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hpcard
  have hxne : x ≠ 1 := by
    intro hx1
    have hord1 : orderOf x = 1 := by
      rw [hx1]
      simp
    rw [hxord] at hord1
    exact hp.ne_one hord1
  have hxpow : x ^ p = 1 := by
    have hord_dvd : orderOf x ∣ p := by rw [hxord]
    exact (orderOf_dvd_iff_pow_eq_one).mp hord_dvd
  have hxneG : (x : alternatingGroup (Fin 7)) ≠ 1 := by
    intro h
    apply hxne
    apply Subtype.ext
    exact h
  have hxpowG : (x : alternatingGroup (Fin 7)) ^ p = 1 := by
    exact congrArg Subtype.val hxpow
  have hcent : t * (x : alternatingGroup (Fin 7)) =
      (x : alternatingGroup (Fin 7)) * t := by
    have hxcent : (x : alternatingGroup (Fin 7)) ∈
        Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))) :=
      hPcent x.2
    exact ((Subgroup.mem_centralizer_singleton_iff.mp hxcent).symm)
  exact aSeven_no_involution_centralizes_prime_five_seven
    hp hp57 (x : alternatingGroup (Fin 7)) t hxneG hxpowG ht.1 ht.2 hcent

end CFSG.GorensteinWalter
