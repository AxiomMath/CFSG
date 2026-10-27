module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326ZWrN
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Act
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326S

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem noncomp_D_nonabelian (h : Hyp326 G n P) {D : Subgroup G} (hD : D.Normal)
    (hDQ : D ≤ CFSG.pCore 3 G) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hCD : Subgroup.centralizer (D : Set G) ≤ CFSG.pCore 3 G)
    (hA : ¬ jOf P ≤ CFSG.pCore 3 G) : ¬ IsMulCommutative D := by
  intro hcomm
  have hDP : D ≤ P := hDQ.trans (pCore_le_sylow h.sylow)
  have hEab : CFSG.Open.IsElemAbelian 3 D := ⟨hcomm, hexp⟩
  have hDJ : D ≤ jOf P :=
    (jOf_spec h).2.2.2.2 D hDP (hD.subgroupOf P) hEab
  haveI : IsMulCommutative (jOf P) := ((jOf_spec h).2.1).1
  have hJD : jOf P ≤ Subgroup.centralizer (D : Set G) :=
    (Subgroup.le_centralizer (jOf P)).trans (Subgroup.centralizer_le hDJ)
  exact hA (hJD.trans hCD)

theorem noncomp_n_eq_one (h : Hyp326 G n P) {D : Subgroup G} (hD : D.Normal)
    (hDQ : D ≤ CFSG.pCore 3 G) (hexp : ∀ x ∈ D, x ^ 3 = 1) (hnab : ¬ IsMulCommutative D) :
    n = 1 := by
  obtain ⟨e⟩ := h.wr
  have hDP : D ≤ P := hDQ.trans (pCore_le_sylow h.sylow)
  refine zwr_n_eq_one_of_normal_exp3 h.one_le e (hD.subgroupOf P) ?_ ?_
  · intro x hx
    apply Subtype.ext
    simpa using hexp (x : G) hx
  · intro hc
    apply hnab
    have e' : D.subgroupOf P ≃* D := Subgroup.subgroupOfEquivOfLe hDP
    rw [isMulCommutative_iff] at hc ⊢
    intro a b
    have h := congrArg e' (hc (e'.symm a) (e'.symm b))
    simpa using h

private lemma isMulCommutative_of_card_dvd_nine {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 9) : IsMulCommutative H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h9 : Nat.card H ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact h
  obtain ⟨k, hk, hkH⟩ :=
    (Nat.dvd_prime_pow (p := 3) (m := 2) (show Nat.Prime 3 by norm_num)).mp h9
  interval_cases k
  · haveI : Subsingleton H :=
      Finite.card_le_one_iff_subsingleton.mp (by simpa using hkH.le)
    infer_instance
  · exact (isCyclic_of_prime_card (p := 3) (by simpa using hkH)).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using hkH)

theorem noncomp_core_card (h : Hyp326 G n P) (hn1 : n = 1) {D : Subgroup G}
    (hDQ : D ≤ CFSG.pCore 3 G) (hnab : ¬ IsMulCommutative D)
    (hA : ¬ jOf P ≤ CFSG.pCore 3 G) :
    Nat.card (CFSG.pCore 3 G) = 27 ∧ D = CFSG.pCore 3 G := by
  have hp3 : Nat.Prime 3 := by norm_num
  obtain ⟨e⟩ := h.wr
  have hPpow : Nat.card P = 3 ^ 4 := by
    have hc := (zwr_card_center h.one_le e).1
    rw [hn1] at hc
    rwa [show 3 * 1 + 1 = 4 by norm_num] at hc
  have hP81 : Nat.card P = 81 := by rw [hPpow]; norm_num
  have hQleP : CFSG.pCore 3 G ≤ P := pCore_le_sylow h.sylow
  have hQneP : CFSG.pCore 3 G ≠ P := by
    intro hEq
    apply hA
    rw [hEq]
    exact (jOf_spec h).1
  have hQne81 : Nat.card (CFSG.pCore 3 G) ≠ 81 := by
    intro hc
    exact hQneP (Subgroup.eq_of_le_of_card_ge hQleP (by omega))
  have hQdvd : Nat.card (CFSG.pCore 3 G) ∣ 3 ^ 4 := by
    have hd : Nat.card (CFSG.pCore 3 G) ∣ Nat.card P := Subgroup.card_dvd_of_le hQleP
    rwa [hPpow] at hd
  obtain ⟨j, hj4, hjQ⟩ := (Nat.dvd_prime_pow hp3).mp hQdvd
  have hjne : j ≠ 4 := by
    intro hj
    exact hQne81 (by rw [hjQ, hj]; norm_num)
  have hQle27 : Nat.card (CFSG.pCore 3 G) ≤ 27 := by
    rw [hjQ]
    calc 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 27 := by norm_num
  have hDdvd : Nat.card D ∣ 3 ^ 4 := by
    have hd : Nat.card D ∣ Nat.card P := Subgroup.card_dvd_of_le (hDQ.trans hQleP)
    rwa [hPpow] at hd
  obtain ⟨k, hk4, hkD⟩ := (Nat.dvd_prime_pow hp3).mp hDdvd
  have hk3 : 3 ≤ k := by
    rcases Nat.lt_or_ge k 3 with hk | hk
    · exfalso
      have hkdvd : Nat.card D ∣ 9 := by
        rw [hkD, show (9 : ℕ) = 3 ^ 2 by norm_num]
        exact Nat.pow_dvd_pow 3 (by omega)
      exact hnab (isMulCommutative_of_card_dvd_nine hkdvd)
    · exact hk
  have h27leD : 27 ≤ Nat.card D := by
    rw [hkD]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hDleQ : Nat.card D ≤ Nat.card (CFSG.pCore 3 G) := Subgroup.card_le_of_le hDQ
  have hDcard : Nat.card D = 27 := le_antisymm (hDleQ.trans hQle27) h27leD
  have hQcard : Nat.card (CFSG.pCore 3 G) = 27 :=
    le_antisymm hQle27 (by rw [← hDcard]; exact hDleQ)
  exact ⟨hQcard, Subgroup.eq_of_le_of_card_ge hDQ (by omega)⟩

@[expose] def NoCompStruct (G : Type) [Group G] [Finite G] : Prop :=
  Nat.card (CFSG.pCore 3 G) = 27 ∧ ¬ IsMulCommutative (CFSG.pCore 3 G) ∧
    (∀ x ∈ CFSG.pCore 3 G, x ^ 3 = 1) ∧
    Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G ∧
    Nat.card (CFSG.GH74.GLS.oPrimeResidual 3 G) = 648 ∧
    CFSG.pCore 3 G ≤ CFSG.GH74.GLS.oPrimeResidual 3 G

theorem noncomp_case (h : Hyp326 G n P)
    (hnc : ∀ L : Subgroup G, ¬ CFSG.Open.IsComponentOf L ⊤)
    (hA : ¬ jOf P ≤ CFSG.pCore 3 G) : n = 1 ∧ NoCompStruct G := by
  have hcent := noncomp_core h.core hnc
  have hQne : CFSG.pCore 3 G ≠ ⊥ := pCore_ne_bot_of_centralizer_le h hcent
  obtain ⟨D, hDQ, hDnorm, hexp, hcop⟩ := exists_exp3_normal_coprime hQne
  have hCD : Subgroup.centralizer (D : Set G) ≤ CFSG.pCore 3 G :=
    centralizer_le_pCore_of_coprime hDnorm hcop hcent
  have hnab : ¬ IsMulCommutative D := noncomp_D_nonabelian h hDnorm hDQ hexp hCD hA
  have hn1 : n = 1 := noncomp_n_eq_one h hDnorm hDQ hexp hnab
  obtain ⟨hQcard, hDQeq⟩ := noncomp_core_card h hn1 hDQ hnab hA
  have hnabQ : ¬ IsMulCommutative (CFSG.pCore 3 G) := by rwa [← hDQeq]
  have hQexp : ∀ x ∈ CFSG.pCore 3 G, x ^ 3 = 1 := by
    intro x hx
    rw [← hDQeq] at hx
    exact hexp x hx
  refine ⟨hn1, ?_⟩
  unfold NoCompStruct
  exact ⟨hQcard, hnabQ, hQexp, hcent,
    noncomp_card_oPrimeResidual h hn1 hQcard hnabQ hcent,
    (pCore_le_sylow h.sylow).trans (le_oPrimeResidual_of_sylow h.sylow)⟩

@[expose] def K326CompCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → CFSG.pPrimeCore 3 G = ⊥ →
    ∀ n : ℕ, 1 ≤ n → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
    Nonempty (↥P ≃* ZWr n) → OmegaCentral P →
    ∀ (M : Subgroup G) (a : G), a ∈ jOf P → a ∉ z2Of P →
      Subgroup.normalizer (jOf P : Set G) ⊔ Subgroup.centralizer ({a} : Set G) ≤ M →
      (∃ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤) → M = ⊤

theorem K326P2S_of_noComp (hcomp : K326CompCase) : K326P2S := by
  intro G _ _ hK hc n hn P hP e hz M a ha ha2 hM
  by_cases hMtop : M = ⊤
  · exact Or.inl hMtop
  · by_cases hex : ∃ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤
    · exact Or.inl (hcomp G hK hc n hn P hP e hz M a ha ha2 hM hex)
    · push Not at hex
      have h : Hyp326 G n P := ⟨hK, hc, hn, hP, e, hz⟩
      have hA : ¬ jOf P ≤ CFSG.pCore 3 G :=
        not_jOf_le_pCore h (le_sup_left.trans hM) hMtop
      obtain ⟨hn1, hQ27, -, -, -, hX648, hQX⟩ := noncomp_case h hex hA
      exact Or.inr ⟨hn1, hQ27, hX648, hQX⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
