module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

private theorem w16l_odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.Open.fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold CFSG.Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem w16l_le_fusionOddCore {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ CFSG.Open.fusionOddCore X :=
  le_sSup ⟨inferInstance, hN⟩

private theorem w16l_odd_card_center_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) :=
  CFSG.CGT.Timmesfeld75.odd_card_center fun N hN hN2 => by
    rw [eq_bot_iff, ← h]
    exact le_sSup ⟨hN, hN2⟩

private theorem w16l_exists_normal_card_three_of_card_six {Y : Type*} [Group Y] [Finite Y]
    (hY : Nat.card Y = 6) :
    ∃ T : Subgroup Y, T.Normal ∧ Nat.card T = 3 ∧ T.index = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3dvd : 3 ∣ Nat.card Y := by rw [hY]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 h3dvd
  have hTcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact hx
  have hTindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).index_mul_card
    rw [hTcard, hY] at h
    omega
  exact ⟨Subgroup.zpowers x, Subgroup.normal_of_index_eq_two hTindex, hTcard, hTindex⟩

private theorem w16l_eq_top_of_le_of_index_eq_two {G : Type*} [Group G] {N H : Subgroup G}
    (hN : N.index = 2) (hle : N ≤ H) (hne : H ≠ N) : H = ⊤ := by
  have hrel : N.relIndex H * H.index = 2 := by
    rw [Subgroup.relIndex_mul_index hle, hN]
  have hrel_ne : N.relIndex H ≠ 1 := by
    intro h
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hle)
  obtain h1 | h2 := (Nat.dvd_prime Nat.prime_two).mp ⟨H.index, hrel.symm⟩
  · exact absurd h1 hrel_ne
  · have hidx : H.index = 1 := by
      rw [h2] at hrel
      omega
    exact Subgroup.index_eq_one.mp hidx

private theorem w16l_card_comap_of_index_two_card_six {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) (hY : Nat.card Y = 6) {T : Subgroup Y}
    (hT : T.index = 2) :
    Nat.card (T.comap f) = 3 * Nat.card f.ker := by
  have hNidx : (T.comap f).index = 2 := by
    rw [Subgroup.index_comap_of_surjective T (f := f) hf, hT]
  have h1 : Nat.card (T.comap f) * 2 = Nat.card X := by
    rw [← hNidx]
    exact Subgroup.card_mul_index (T.comap f)
  have h2 : Nat.card X = Nat.card f.ker * Nat.card Y :=
    (Subgroup.card_ker_mul_card_of_surjective hf).symm
  rw [h2, hY] at h1
  have h3 : Nat.card (T.comap f) * 2 = (3 * Nat.card f.ker) * 2 := by
    rw [h1]
    ring
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) h3

private theorem w16l_false_of_fusionOddCore_index_one {X : Type} [Group X] [Finite X]
    {B : Subgroup X} (hB2 : Nat.card B = 2)
    (hQ : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = 1) : False := by
  have hOodd := w16l_odd_card_fusionOddCore X
  have hOtop : CFSG.Open.fusionOddCore X = ⊤ := by
    refine Subgroup.index_eq_one.mp ?_
    rw [Subgroup.index_eq_card]
    exact hQ
  have hdvd : Nat.card B ∣ Nat.card (CFSG.Open.fusionOddCore X) :=
    Subgroup.card_dvd_of_le (by rw [hOtop]; exact le_top)
  rw [hB2] at hdvd
  exact hOodd.not_two_dvd_nat hdvd

theorem w16l_sym_small {X : Type} [Group X] [Finite X] {B : Subgroup X} {k : ℕ}
    (hB2 : Nat.card B = 2) (hk : IsSymGp (X ⧸ CFSG.Open.fusionOddCore X) k) (hk4 : k < 4) :
    k = 2 ∧ B ⊔ CFSG.Open.fusionOddCore X = ⊤ := by
  obtain ⟨e⟩ := hk
  have hQcard : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = k.factorial := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  interval_cases k
  · exfalso
    exact w16l_false_of_fusionOddCore_index_one hB2 (by rw [hQcard]; norm_num)
  · exfalso
    exact w16l_false_of_fusionOddCore_index_one hB2 (by rw [hQcard]; norm_num)
  · refine ⟨rfl, ?_⟩
    have hQ2 : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = 2 := by
      rw [hQcard]
      norm_num
    have hOodd := w16l_odd_card_fusionOddCore X
    have hOidx : (CFSG.Open.fusionOddCore X).index = 2 := by
      rw [Subgroup.index_eq_card]
      exact hQ2
    have hBnotO : ¬ B ≤ CFSG.Open.fusionOddCore X := by
      intro hBO
      have hdvd : Nat.card B ∣ Nat.card (CFSG.Open.fusionOddCore X) :=
        Subgroup.card_dvd_of_le hBO
      rw [hB2] at hdvd
      exact hOodd.not_two_dvd_nat hdvd
    have hne : B ⊔ CFSG.Open.fusionOddCore X ≠ CFSG.Open.fusionOddCore X := by
      intro h
      exact hBnotO (le_sup_left.trans (le_of_eq h))
    exact w16l_eq_top_of_le_of_index_eq_two hOidx le_sup_right hne
  · exfalso
    have hQ6 : Nat.card (X ⧸ CFSG.Open.fusionOddCore X) = 6 := by
      rw [hQcard]
      norm_num
    have hOodd := w16l_odd_card_fusionOddCore X
    obtain ⟨T, hTnormal, _, hTindex⟩ :=
      w16l_exists_normal_card_three_of_card_six hQ6
    have hf : Function.Surjective (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)) :=
      QuotientGroup.mk'_surjective _
    have hNcard : Nat.card (T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))) =
        3 * Nat.card (CFSG.Open.fusionOddCore X) := by
      have h := w16l_card_comap_of_index_two_card_six
        (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)) hf hQ6 hTindex
      rwa [QuotientGroup.ker_mk' (CFSG.Open.fusionOddCore X)] at h
    have hNodd : Odd (Nat.card (T.comap
        (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)))) := by
      rw [hNcard]
      exact Odd.mul (by decide : Odd 3) hOodd
    haveI : (T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))).Normal :=
      hTnormal.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))
    have hNle : T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X)) ≤
        CFSG.Open.fusionOddCore X := w16l_le_fusionOddCore hNodd
    have hle_card : Nat.card (T.comap (QuotientGroup.mk' (CFSG.Open.fusionOddCore X))) ≤
        Nat.card (CFSG.Open.fusionOddCore X) := Subgroup.card_le_of_le hNle
    rw [hNcard] at hle_card
    have hOpos : 0 < Nat.card (CFSG.Open.fusionOddCore X) := hOodd.pos
    omega

theorem w16l_sp_two_one {X : Type} [Group X] [Finite X] {B : Subgroup X}
    (hB2 : Nat.card B = 2) (hcore : CFSG.pCore 2 X = ⊥)
    (hSp : IsSpGp (X ⧸ Subgroup.center X) 2 1) : B ⊔ CFSG.Open.fusionOddCore X = ⊤ := by
  have hZodd : Odd (Nat.card (Subgroup.center X)) :=
    w16l_odd_card_center_of_pCore_eq_bot hcore
  obtain ⟨k, _, F, _, _, hFcard, ⟨e⟩⟩ := hSp
  obtain rfl : k = 1 := by omega
  have hYcard : Nat.card (X ⧸ Subgroup.center X) = 6 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := F) 1,
      show Finset.Icc 1 1 = {1} by decide,
      Finset.prod_singleton, hFcard]
    norm_num
  obtain ⟨T, hTnormal, _, hTindex⟩ :=
    w16l_exists_normal_card_three_of_card_six hYcard
  have hf : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  have hNindex : (T.comap (QuotientGroup.mk' (Subgroup.center X))).index = 2 := by
    rw [Subgroup.index_comap_of_surjective T
      (f := QuotientGroup.mk' (Subgroup.center X)) hf, hTindex]
  have hNcard : Nat.card (T.comap (QuotientGroup.mk' (Subgroup.center X))) =
      3 * Nat.card (Subgroup.center X) := by
    have h := w16l_card_comap_of_index_two_card_six
      (QuotientGroup.mk' (Subgroup.center X)) hf hYcard hTindex
    rwa [QuotientGroup.ker_mk' (Subgroup.center X)] at h
  have hNodd : Odd (Nat.card (T.comap (QuotientGroup.mk' (Subgroup.center X)))) := by
    rw [hNcard]
    exact Odd.mul (by decide : Odd 3) hZodd
  haveI : (T.comap (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    hTnormal.comap (QuotientGroup.mk' (Subgroup.center X))
  have hNle : T.comap (QuotientGroup.mk' (Subgroup.center X)) ≤
      CFSG.Open.fusionOddCore X := w16l_le_fusionOddCore hNodd
  have hBnotN : ¬ B ≤ T.comap (QuotientGroup.mk' (Subgroup.center X)) := by
    intro hBN
    have hdvd : Nat.card B ∣
        Nat.card (T.comap (QuotientGroup.mk' (Subgroup.center X))) :=
      Subgroup.card_dvd_of_le hBN
    rw [hB2] at hdvd
    exact hNodd.not_two_dvd_nat hdvd
  have hsup_ne : B ⊔ T.comap (QuotientGroup.mk' (Subgroup.center X)) ≠
      T.comap (QuotientGroup.mk' (Subgroup.center X)) := by
    intro h
    exact hBnotN (le_sup_left.trans (le_of_eq h))
  have hsup : B ⊔ T.comap (QuotientGroup.mk' (Subgroup.center X)) = ⊤ :=
    w16l_eq_top_of_le_of_index_eq_two hNindex le_sup_right hsup_ne
  refine le_antisymm le_top ?_
  rw [← hsup]
  exact sup_le_sup_left hNle B

end CFSG.LocalAnalysis.WeakClosure81

end
