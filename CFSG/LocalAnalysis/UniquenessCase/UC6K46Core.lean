module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K46Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Dd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

section TwoModule

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem le_center_of_le_centralizer_of_normalClosure {H D : Subgroup G} [H.Normal]
    (hgen : Subgroup.normalClosure (D : Set G) = ⊤) (hD : H ≤ Subgroup.centralizer (D : Set G)) :
    H ≤ Subgroup.center G := by
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  haveI : C.Normal := ⟨fun n hn g => Subgroup.mem_centralizer_iff.2 fun h hh => by
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (inferInstance : H.Normal).conj_mem h hh g⁻¹
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hn _ hh'
    calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * h := by group⟩
  have hDC : D ≤ C := fun d hd h hh => by
    have := Subgroup.mem_centralizer_iff.1 (hD hh) d hd
    exact this.symm
  have hnc : Subgroup.normalClosure (D : Set G) ≤ C := Subgroup.normalClosure_le_normal hDC
  rw [hgen] at hnc
  intro h hh
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.1 (hnc (Subgroup.mem_top g)) h hh).symm

theorem pPrimeCore_three_le_center (hSz : KSz) (hK : CFSG.Open.IsKGroup G) (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) [ρ.IsIrreducible] {D : Subgroup G} (hD : Nat.card D = 3)
    (hgen : Subgroup.normalClosure (D : Set G) = ⊤) (hfix : fixV ρ D = ⊥) :
    CFSG.pPrimeCore 3 G ≤ Subgroup.center G := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hHn : (CFSG.pPrimeCore 3 G).Normal := CFSG.pPrimeCore_normal
  set H : Subgroup G := CFSG.pPrimeCore 3 G with hH
  have hcop : Nat.Coprime 3 (Nat.card H) := CFSG.pPrimeCore_coprime_card
  have hcent : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ H → IsPGroup q Q →
      D ≤ normalizer (Q : Set G) → Q ≤ centralizer (D : Set G) := by
    intro q hq hq2 Q hQH hQ hDQ
    by_cases hq3 : q = 3
    · subst hq3
      haveI : Fact (Nat.Prime 3) := ⟨hq⟩
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      have hdvd : Nat.card Q ∣ Nat.card H := Subgroup.card_dvd_of_le hQH
      have hk0 : k = 0 := by
        by_contra hk0
        have h3 : 3 ∣ Nat.card H := by
          refine (dvd_pow_self 3 hk0).trans ?_
          rw [← hk]
          exact hdvd
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3
      have hQbot : Q = ⊥ := by
        rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]
      rw [hQbot]
      exact bot_le
    · have h1 := commutator_eq_bot_of_normalizes_two hK ρ hρ hD hfix hq hq2 hq3 hQ hDQ
      rw [Subgroup.commutator_comm] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
  have hDN : D ≤ normalizer (H : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hHn]
    exact le_top
  obtain ⟨k, hk⟩ := lemmaC_of_KSz hSz G hK H D hDN hD hcop hcent
  have hRH : ⁅H, D⁆ ≤ H := Subgroup.commutator_le_left H D
  have hHN : H ≤ normalizer ((⁅H, D⁆ : Subgroup G) : Set G) := Subgroup.normalizer_commutator_ge_left H D
  have hnormR : ((⁅H, D⁆ : Subgroup G).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).2 hHN
  have hpR : IsPGroup 2 ((⁅H, D⁆ : Subgroup G).subgroupOf H) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply IsPGroup.of_card (n := k)
    rw [← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hle : ((⁅H, D⁆ : Subgroup G).subgroupOf H) ≤ CFSG.pCore 2 H :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hnormR hpR
  have hbot : ⁅H, D⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxH : x ∈ H := hRH hx
    have hx' : (⟨x, hxH⟩ : H) ∈ CFSG.pCore 2 H := hle (Subgroup.mem_subgroupOf.2 hx)
    have := CFSG.BaerSuzuki.Helpers.mem_pCore_of_mem_pCore_normal hHn hxH hx'
    rw [pCore_two_eq_bot ρ hρ] at this
    exact this
  exact le_center_of_le_centralizer_of_normalClosure hgen
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot)

end TwoModule

end CFSG.LocalAnalysis.UniquenessCase.UCK
