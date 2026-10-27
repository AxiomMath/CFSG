module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem abelianPSubgroupLeFStar_of_forall_mem {p : ℕ} {X : Type*} [Group X] {N : Subgroup X}
    (h : ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ CFSG.generalizedFitting X) :
    AbelianPSubgroupLeFStar p N := fun _ hBN hB _ _ b hb =>
  h b (hBN hb) (hB.to_le (Subgroup.zpowers_le.2 hb))

theorem goodZ_of_pElements {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type*} [Group X]
    {N : Subgroup X}
    (h : (∀ x y : X, x ∈ N → y ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) →
      (orderOf y).Prime → orderOf y ≠ p → x * y = y * x →
      ∃ c ∈ CFSG.generalizedFitting X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧
        c ∉ N) ∧
      ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ CFSG.generalizedFitting X) :
    InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N :=
  ⟨involutionCentralizerHasPElementOutside_of_single hp fun x t hxN htN hx1 hxp ht2 hxt =>
      h.1 x t hxN htN hx1 hxp (by rw [ht2]; exact Nat.prime_two) (by rw [ht2]; exact hp2.symm)
        hxt,
    abelianPSubgroupLeFStar_of_forall_mem h.2⟩

theorem goodZ_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) {X : Type} [Group X]
    [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N :=
  goodZ_of_pElements Fact.out hp2 (SEFive.pElements_psl2GF hp2 hn hO hN e)

theorem goodZ_unitary {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N :=
  goodZ_of_pElements Fact.out hp2 (SEFive.pElements_unitary hd hO hN e)

theorem goodZ_of_sylow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type*} [Group X] [Finite X]
    (hR : ∀ R : Sylow p X, Nat.card (R : Subgroup X) = p ^ 2 ∧
      Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R) (N : Subgroup X) :
    InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N := by
  have hp : p.Prime := Fact.out
  refine ⟨fun A _ hA hAc t _ ht2 htA => ?_, fun B _ hB _ hBc => ?_⟩
  · obtain ⟨R, hAR⟩ := hA.isPGroup.exists_le_sylow
    have hAR' : A = R := Subgroup.eq_of_le_of_card_ge hAR (hAc.trans (hR R).1.symm).ge
    have htR : t ∈ (R : Subgroup X) := (hR R).2 (Subgroup.mem_centralizer_iff.2 fun a ha =>
      htA a (by rw [hAR']; exact ha))
    have h := Subgroup.orderOf_dvd_natCard _ htR
    rw [ht2, (hR R).1] at h
    exact (hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h)).symm).elim
  · obtain ⟨R, hBR⟩ := hB.exists_le_sylow
    have h := Subgroup.card_le_of_le hBR
    rw [(hR R).1] at h
    have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
    omega

theorem goodZ_of_heis {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type*} [Group X] [Finite X]
    {N : Subgroup X} (hN : IsStronglyPEmbedded p N) {R : Sylow p X} (hRN : (R : Subgroup X) ≤ N)
    (hcard : Nat.card (R : Subgroup X) = p ^ 3)
    (hmax : ∀ Y : Subgroup X, Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ Y →
      Y = Subgroup.normalizer ((R : Subgroup X) : Set X) ∨ Y = ⊤)
    (hC : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R)
    (hZ : Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
      Subgroup X) = p)
    (hcomm : ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
      (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X)) :
    InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N := by
  have hp : p.Prime := Fact.out
  have hR1 : (R : Subgroup X) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow (by norm_num) hp.one_lt).ne hcard
  have hNR : N = Subgroup.normalizer ((R : Subgroup X) : Set X) := by
    rcases hmax N (hN.normalizer_le hR1 R.isPGroup' hRN) with h | h
    · exact h
    · exact absurd h hN.1
  have hle : ∀ {A : Subgroup X}, A ≤ N → IsPGroup p A → A ≤ R := by
    intro A hAN hA x hx
    have hAN' : A ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := hNR ▸ hAN
    exact (Subgroup.mem_inf.1 (le_of_eq (hA.inf_normalizer_sylow R)
      (Subgroup.mem_inf.2 ⟨hx, hAN' hx⟩))).2
  refine ⟨fun A hAN hA hAc t htN ht2 htA => ?_, fun B hBN hB hBab hBc => ?_⟩
  · exfalso
    have hAR := hle hAN hA.isPGroup
    have htn : t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) := hNR ▸ htN
    haveI := hA.1
    have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
    obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ (R : Subgroup X) ⊓
        Subgroup.centralizer ((R : Subgroup X) : Set X) := by
      by_contra h
      push Not at h
      have h1 := Subgroup.card_le_of_le (show A ≤ _ from h)
      rw [hAc, hZ] at h1
      have := Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by norm_num)
      rw [pow_one] at this
      omega
    have hCa : ∀ d ∈ (R : Subgroup X), d * a = a * d → d ∈ A := by
      intro d hdR hda
      let H : Subgroup X := (R : Subgroup X) ⊓ Subgroup.centralizer {a}
      have hAH : A ≤ H := fun x hx =>
        ⟨hAR hx, Subgroup.mem_centralizer_singleton_iff.2 (hAcomm x hx a haA)⟩
      have hHR : H ≤ R := inf_le_left
      have hHne : H ≠ R := by
        intro h
        refine haZ ⟨hAR haA, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
        have hrH : r ∈ H := by rw [h]; exact hr
        exact Subgroup.mem_centralizer_singleton_iff.1 hrH.2
      obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).1
        (show Nat.card H ∣ p ^ 3 by rw [← hcard]; exact Subgroup.card_dvd_of_le hHR)
      have h2k : 2 ≤ k := by
        have h := Subgroup.card_dvd_of_le hAH
        rw [hAc, hk] at h
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
      have hk2 : k = 2 := by
        rcases (show k = 2 ∨ k = 3 by omega) with h | h
        · exact h
        · exact absurd (Subgroup.eq_of_le_of_card_ge hHR (le_of_eq (by rw [hk, hcard, h])))
            hHne
      have hAH' : A = H := Subgroup.eq_of_le_of_card_ge hAH (le_of_eq (by rw [hk, hAc, hk2]))
      rw [hAH']
      exact ⟨hdR, Subgroup.mem_centralizer_singleton_iff.2 hda⟩
    have hZA : (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ A :=
      fun z hz => hCa z hz.1 ((Subgroup.mem_centralizer_iff.1 hz.2) a (hAR haA)).symm
    have hfix : ∀ x ∈ A, t * x * t⁻¹ = x := fun x hx => by
      rw [← htA x hx]
      group
    have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    have hcent : ∀ b ∈ (R : Subgroup X), t * b * t⁻¹ = b := by
      intro b hb
      have hb'R : t * b * t⁻¹ ∈ (R : Subgroup X) := (Subgroup.mem_normalizer_iff.1 htn b).1 hb
      have hcA : a * b * a⁻¹ * b⁻¹ ∈ A := by
        have h := Subgroup.commutator_mem_commutator (hAR haA) hb
        rw [hcomm, commutatorElement_def] at h
        exact hZA h
      have h1 : a * b * a⁻¹ * b⁻¹ = a * (t * b * t⁻¹) * a⁻¹ * (t * b * t⁻¹)⁻¹ := by
        calc a * b * a⁻¹ * b⁻¹ = t * (a * b * a⁻¹ * b⁻¹) * t⁻¹ := (hfix _ hcA).symm
          _ = (t * a * t⁻¹) * (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by group
          _ = a * (t * b * t⁻¹) * a⁻¹ * (t * b * t⁻¹)⁻¹ := by rw [hfix a haA]
      have h2 : a⁻¹ * (b⁻¹ * (t * b * t⁻¹)) = (b⁻¹ * (t * b * t⁻¹)) * a⁻¹ := by
        calc a⁻¹ * (b⁻¹ * (t * b * t⁻¹))
            = b⁻¹ * a⁻¹ * (a * b * a⁻¹ * b⁻¹) * (t * b * t⁻¹) := by group
          _ = b⁻¹ * a⁻¹ * (a * (t * b * t⁻¹) * a⁻¹ * (t * b * t⁻¹)⁻¹) * (t * b * t⁻¹) := by
              rw [h1]
          _ = (b⁻¹ * (t * b * t⁻¹)) * a⁻¹ := by group
      have hda : (b⁻¹ * (t * b * t⁻¹)) * a = a * (b⁻¹ * (t * b * t⁻¹)) := by
        calc (b⁻¹ * (t * b * t⁻¹)) * a = a * (a⁻¹ * (b⁻¹ * (t * b * t⁻¹))) * a := by group
          _ = a * ((b⁻¹ * (t * b * t⁻¹)) * a⁻¹) * a := by rw [h2]
          _ = a * (b⁻¹ * (t * b * t⁻¹)) := by group
      have hdA : b⁻¹ * (t * b * t⁻¹) ∈ A :=
        hCa _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hb'R) hda
      have h4 : b = (t * b * t⁻¹) * (b⁻¹ * (t * b * t⁻¹)) := by
        calc b = (t * t) * b * (t * t)⁻¹ := by rw [htt]; group
          _ = t * (b * (b⁻¹ * (t * b * t⁻¹))) * t⁻¹ := by group
          _ = (t * b * t⁻¹) * (t * (b⁻¹ * (t * b * t⁻¹)) * t⁻¹) := by group
          _ = (t * b * t⁻¹) * (b⁻¹ * (t * b * t⁻¹)) := by rw [hfix _ hdA]
      have hdd : (b⁻¹ * (t * b * t⁻¹)) ^ 2 = 1 := by
        calc (b⁻¹ * (t * b * t⁻¹)) ^ 2
            = b⁻¹ * ((t * b * t⁻¹) * (b⁻¹ * (t * b * t⁻¹))) := by rw [sq]; group
          _ = 1 := by rw [← h4, inv_mul_cancel]
      have hd1 : b⁻¹ * (t * b * t⁻¹) = 1 := by
        have h7 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdd)
          (orderOf_dvd_of_pow_eq_one (hA.2 _ hdA))
        rw [(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm, Nat.dvd_one,
          orderOf_eq_one_iff] at h7
        exact h7
      calc t * b * t⁻¹ = b * (b⁻¹ * (t * b * t⁻¹)) := by group
        _ = b := by rw [hd1, mul_one]
    have htC : t ∈ Subgroup.centralizer ((R : Subgroup X) : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun b hb => by
        calc b * t = (t * b * t⁻¹) * t := by rw [hcent b hb]
          _ = t * b := by group
    have h := Subgroup.orderOf_dvd_natCard _ (hC htC)
    rw [ht2, hcard] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  · exfalso
    have hBR : B = R := Subgroup.eq_of_le_of_card_ge (hle hBN hB) (by rw [hcard]; exact hBc)
    have hRab : ⁅(R : Subgroup X), (R : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hBR] at hx hy
      exact hBab y hy x hx
    rw [hcomm] at hRab
    rw [hRab, Subgroup.card_bot] at hZ
    exact hp.one_lt.ne hZ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
