module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailInv717
public import CFSG.RankThree.GF2n.Stroth80.Sec717InvDivisible
public import CFSG.RankThree.GF2n.Stroth80.Sec717PairingCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec717_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  have hpK : Nat.card K = ringChar K ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hdvd : ringChar K ∣ 2 ^ n := by
    rw [← h, hpK]
    exact dvd_pow_self _ m.ne_zero
  have h2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  rw [← h2]
  exact ringChar.charP K

theorem sec717Inv_of_parts (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h78 : Stroth78Statement) (hZc : Sec7ZCardStatement) (hCN : Sec7CommNStatement)
    (cited : IrrQ4NoPairingStatement) : Sec717InvStatement := by
  intro G _ _ M Q Z B hc n t hs hp3 Z0 hZ0 A hZA hAN hAR'
  have hp3c := hp3
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQnorm : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hZ0n : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun ρ hρ y hy => hQnorm ρ (hRM hρ) y hy) hg) y).mp hy
  have hAn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ A, x * y * x⁻¹ ∈ A := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ ∈ conjSubgroup x A := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    rwa [hAR' x hx] at h1
  have hZR : ∀ z ∈ Z0, ∀ r ∈ Rt M (LB M Q B) t, ⁅z, r⁆ ∈ Q := fun z hz r hr =>
    ((hZ0 z).mp hz).2 r hr
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Z0 := fun a ha a' ha' =>
    hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator (hAN ha) (hAN ha'))
  have hQZ0 : Q ≤ Z0 := fun x hx => (hZ0 x).mpr ⟨hc.Q_le_Rt ht hx, fun r hr => by
    have h1 := hQnorm r (hRM hr) x⁻¹ (Q.inv_mem hx)
    have h2 := Q.mul_mem hx h1
    simpa [commutatorElement_def, mul_assoc] using h2⟩
  have hQnorm' : ∀ r ∈ Rt M (LB M Q B) t, ∀ q ∈ Q, r * q * r⁻¹ ∈ Q := fun r hr q hq =>
    hQnorm r (hRM hr) q hq
  have hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z := hZc G M Q Z B hc n t hs Z0 hZ0
  have hcN78 := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (le_refl 2 |>.trans (by
      norm_num))
    (Or.inl hp3c)
  unfold Conc78 at hcN78
  have hNcard : Nat.card (hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    rcases hcN78 with ⟨-, -, h9⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
    · exact h9
    all_goals omega
  have hq1 : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  obtain ⟨k, hk⟩ := sec717CardDvd_of_omegaPlus h51 hA hPts hc hs (le_refl 3) hp3c hZ0 hZA hAN hAR'
  have h4 : (2 : ℕ) ^ (3 - 1) = 4 := by norm_num
  rw [h4] at hk
  obtain ⟨K, hKf, hKfin, hKZ, φ, hφr, hker, -⟩ := hp3c
  obtain ⟨n0, -, hZn0, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := sec717_charP_two (n := n0) (by rw [hKZ, hZn0])
  by_cases h0 : A = Z0
  · exact Or.inl h0
  by_cases hN : A = hc.CN t
  · exact Or.inr (Or.inl hN)
  right
  right
  have hkpos : k ≠ 0 := by
    rintro rfl
    apply h0
    have hle : Nat.card A ≤ Nat.card Z0 := by
      rw [hk]
      simp
    exact (Subgroup.eq_of_le_of_card_ge hZA hle).symm
  have hk_le : k ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    apply hN
    apply Subgroup.eq_of_le_of_card_ge hAN
    have h8 : Nat.card Z ^ 8 ≤ Nat.card Z ^ (4 * k) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [hNcard, hk, hZ0card]
    calc Nat.card Q * Nat.card Z ^ 9 = Nat.card Q * Nat.card Z * Nat.card Z ^ 8 := by ring
      _ ≤ Nat.card Q * Nat.card Z * Nat.card Z ^ (4 * k) := Nat.mul_le_mul_left _ h8
  have hk1 : k = 1 := by omega
  have hcardA : Nat.card A = Nat.card Q * Nat.card Z ^ 5 := by
    rw [hk, hk1, hZ0card]
    ring
  have hlat : ∀ C : Subgroup G, Z0 ≤ C → C ≤ A →
      (∀ r ∈ Rt M (LB M Q B) t, ∀ c ∈ C, r * c * r⁻¹ ∈ C) → C = Z0 ∨ C = A := by
    intro C hZC hCA hCinv
    have hCinv' : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r C = C := by
      intro r hr
      apply le_antisymm
      · intro x hx
        rw [mem_conjSubgroup] at hx
        have := hCinv r hr _ hx
        simpa [mul_assoc] using this
      · intro x hx
        rw [mem_conjSubgroup]
        have := hCinv r⁻¹ (Subgroup.inv_mem _ hr) x hx
        simpa [mul_assoc] using this
    obtain ⟨k', hk'⟩ := sec717CardDvd_of_omegaPlus h51 hA hPts hc hs (le_refl 3) hp3 hZ0 hZC
      (hCA.trans hAN) hCinv'
    rw [h4] at hk'
    have hk'le : k' ≤ 1 := by
      have hle := Subgroup.card_le_of_le hCA
      rw [hk', hk, hk1] at hle
      have h2 : Nat.card Z ^ (4 * k') ≤ Nat.card Z ^ 4 :=
        Nat.le_of_mul_le_mul_left hle Nat.card_pos
      have h3 : 4 * k' ≤ 4 := (Nat.pow_le_pow_iff_right hq1).mp h2
      omega
    obtain rfl | rfl : k' = 0 ∨ k' = 1 := by omega
    · left
      have hle : Nat.card C ≤ Nat.card Z0 := by
        rw [hk']
        simp
      exact (Subgroup.eq_of_le_of_card_ge hZC hle).symm
    · right
      have hle : Nat.card A ≤ Nat.card C := by
        rw [hk, hk', hk1]
      exact Subgroup.eq_of_le_of_card_ge hCA hle
  have hRA : ∀ r ∈ Rt M (LB M Q B) t, ∀ a ∈ A, r * a * r⁻¹ ∈ A := fun r hr a ha => hAn r hr a ha
  have hφcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ Q := by
    apply sec717_pairing_trivial cited φ hφr (fun x hx => (Ctx.mem_CN.mp (hAN hx)).1) hZA le_rfl
      hRA hZ0n hZ0n hQnorm' hZR hAcomm
    · intro b hb a ha
      exact hZR b hb a ((Ctx.mem_CN.mp (hAN ha)).1)
    · intro h hh a ha
      have hmem : (h : G) ∈ hc.CN t := by
        have hh' : h ∈ φ.ker := MonoidHom.mem_ker.mpr hh
        rw [hker] at hh'
        exact Subgroup.mem_subgroupOf.mp hh'
      have hid : ((h : G) * a * (h : G)⁻¹)⁻¹ * a = ⁅(h : G), a⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      show ((h : G) * a * (h : G)⁻¹)⁻¹ * a ∈ Z0
      rw [hid]
      exact hCN G M Q Z B hc n t hs Z0 hZ0
        (Subgroup.commutator_mem_commutator hmem (hAN (A.inv_mem ha)))
    · exact hlat
    · rw [hKZ, hk, hk1]
  unfold Sec717L
  exact ⟨hQZ0.trans hZA, hAN, hcardA, hAR', fun x hx y hy => hφcomm x hx y hy, hZA⟩

end CFSG.RankThree.GF2n.Stroth80
