module

public import CFSG.OddTranspositions.PartFour.LineCount
import CFSG.OddTranspositions.PartFour.OrbitPower
import CFSG.CGT.Stroth77.WeakTransport
import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ncard_blockLine_ne_three_of_orderOf_mul (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hV : ∀ v ∈ imageClass hC, Odd (Vmem (imageClass hC) v).ncard)
    {u w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hu : u ∈ imageClass hC) (hw : w ∈ imageClass hC) (hodd : Odd (orderOf (u * w)))
    (h1 : orderOf (u * w) ≠ 1) (h3 : ¬ 3 ∣ orderOf (u * w))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) : (blockLine D hC.alpha β).ncard ≠ 3 := by
  classical
  intro hline
  set H := Halpha D hC.alpha
  set R := CFSG.solvableRadical H
  set Q := CFSG.pCore 2 H
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQ : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hD : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  have hN : IsNormalSet (DstarH hC) := fun _ _ hx => DstarH_conj_mem hC hx
  have horb : ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 :=
    ncard_orbit_eq_two_pow h89 h113 hC hrad hW hn3 hMZ hHns hV hβ (e := 1)
      (by rw [hline]; norm_num)
  have hidx : ∀ d ∈ DstarH hC, (Q ⊓ Subgroup.centralizer ({d} : Set H)).relIndex Q = 2 := by
    intro d hd
    obtain ⟨δ, hδ, hdδ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hd)
    have h := ncard_orbit_Malpha_eq_ncard_conj h89 h113 hC hrad hW hn3 hHns hδ (b := d) hdδ
    rw [ncard_orbit_Malpha_eq hC hβ hδ, horb] at h
    rw [CFSG.ComponentClassification.HSFLit.relIndex_inf_centralizer_eq_ncard]
    exact h.symm
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨c, hc, rfl⟩ := hw
  have hac : ¬ Commute a c := by
    intro hcomm
    apply h1
    have hsq : (a * c) ^ 2 = 1 := by
      rw [hcomm.mul_pow, pow_two, pow_two, hD.mul_self_eq_one ha, hD.mul_self_eq_one hc,
        one_mul]
    have hdvd : orderOf (QuotientGroup.mk' R a * QuotientGroup.mk' R c) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_mul, ← map_pow, hsq, map_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  set g := a * c with hg
  set k := orderOf (QuotientGroup.mk' R a * QuotientGroup.mk' R c) with hk
  have hgodd : Odd (orderOf g) := hD.odd_of_not_commute ha hc hac
  have hinv : a * g * a⁻¹ = g⁻¹ := by
    calc a * g * a⁻¹ = (a * a) * c * a⁻¹ := by rw [hg]; group
      _ = c⁻¹ * a⁻¹ := by rw [hD.mul_self_eq_one ha, one_mul, hD.inv_eq hc]
      _ = g⁻¹ := by rw [hg, mul_inv_rev]
  have hgkR : g ^ k ∈ R := by
    have h' : QuotientGroup.mk' R (g ^ k) = 1 := by
      rw [map_pow, hg, map_mul, hk, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff _).mp h'
  have hcommQ : g ^ k * a * (g ^ k)⁻¹ * a⁻¹ ∈ Q :=
    commutator_mem_pCore_of_mem_solvableRadical h113 hC hrad hn3 hgkR a
  have h2k : g ^ k * a * (g ^ k)⁻¹ * a⁻¹ = g ^ (2 * k) := by
    have hpow : a * g ^ k * a⁻¹ = (g ^ k)⁻¹ := by rw [← conj_pow, hinv, inv_pow]
    calc g ^ k * a * (g ^ k)⁻¹ * a⁻¹ = g ^ k * (a * g ^ k * a⁻¹)⁻¹ := by group
      _ = g ^ (2 * k) := by rw [hpow, inv_inv, two_mul, pow_add]
  rw [h2k] at hcommQ
  have hg2k : g ^ (2 * k) = 1 := by
    obtain ⟨j, hj⟩ := exists_orderOf_eq_two_pow hQ hcommQ
    have hdvd : 2 ^ j ∣ orderOf g := hj ▸ orderOf_pow_dvd (2 * k)
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hgodd)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hj0).trans hdvd))
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  have hgk : orderOf g ∣ k :=
    (Nat.coprime_two_right.mpr hgodd).dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hg2k)
  have hg3 : Nat.Coprime 3 (orderOf g) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => h3 (h.trans hgk)
  set B := Q ⊓ Subgroup.centralizer ({g} : Set H)
  have hBle : (Q ⊓ Subgroup.centralizer ({a} : Set H)) ⊓
      (Q ⊓ Subgroup.centralizer ({c} : Set H)) ≤ B := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyQ, hya⟩ := Subgroup.mem_inf.mp hy1
    obtain ⟨-, hyc⟩ := Subgroup.mem_inf.mp hy2
    refine Subgroup.mem_inf.mpr ⟨hyQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hya hyc ⊢
    rw [hg, ← mul_assoc, hya, mul_assoc, hyc, ← mul_assoc]
  have hBidx : B.relIndex Q ≤ 4 := by
    have hne : ((Q ⊓ Subgroup.centralizer ({a} : Set H)) ⊓
        (Q ⊓ Subgroup.centralizer ({c} : Set H))).relIndex Q ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero (by rw [hidx a ha]; norm_num) (by rw [hidx c hc]; norm_num)
    calc B.relIndex Q ≤ ((Q ⊓ Subgroup.centralizer ({a} : Set H)) ⊓
          (Q ⊓ Subgroup.centralizer ({c} : Set H))).relIndex Q :=
          Subgroup.relIndex_le_of_le_left hBle hne
      _ ≤ (Q ⊓ Subgroup.centralizer ({a} : Set H)).relIndex Q *
          (Q ⊓ Subgroup.centralizer ({c} : Set H)).relIndex Q := Subgroup.relIndex_inf_le
      _ = 4 := by rw [hidx a ha, hidx c hc]
  have hcard : Nat.card Q ≤ 4 * Nat.card B := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := Q)
    rw [inf_eq_left.mpr (inf_le_left : B ≤ Q)] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hBidx
  have hgQ : g ∈ Subgroup.normalizer (Q : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hgB : g ∈ Subgroup.normalizer (B : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyB
      obtain ⟨-, hyg⟩ := Subgroup.mem_inf.mp hyB
      rw [Subgroup.mem_centralizer_singleton_iff] at hyg
      have hy : g * y * g⁻¹ = y := by rw [← hyg, mul_inv_cancel_right]
      rw [hy]
      exact hyB
    · intro hyB
      obtain ⟨-, hyg⟩ := Subgroup.mem_inf.mp hyB
      rw [Subgroup.mem_centralizer_singleton_iff] at hyg
      have hy : y = g * y * g⁻¹ := by
        have h' : g * y = g * (g * y * g⁻¹) := by
          calc g * y = g * y * g⁻¹ * g := by group
            _ = g * (g * y * g⁻¹) := hyg
        exact mul_left_cancel h'
      rw [hy]
      exact hyB
  have hg3B : g ^ 3 ∈ Subgroup.centralizer (B : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyg : Commute y g :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2
    exact (hyg.pow_right 3).eq
  have hcube := CFSG.CGT.Stroth77.cube_mem_centralizer_of_index_le_four
    (inf_le_left : B ≤ Q) hQ hcard hgB hgQ hgodd hg3B
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hg3
  have hgcent : g ∈ Subgroup.centralizer (Q : Set H) := by
    rw [← hm]
    exact Subgroup.pow_mem _ hcube m
  have haQ : Q ⊓ Subgroup.centralizer ({a} : Set H) = Q := by
    refine inf_eq_left.mpr fun y hy => ?_
    have hyg : Commute y g := (Subgroup.mem_centralizer_iff.mp hgcent) y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((commute_iff_of_mem hD hN hQ ha hc hac hy).mp hyg).1.eq
  have h2 := hidx a ha
  rw [haQ, Subgroup.relIndex_self] at h2
  exact absurd h2 (by norm_num)

end CFSG.OddTranspositions.PartFour
