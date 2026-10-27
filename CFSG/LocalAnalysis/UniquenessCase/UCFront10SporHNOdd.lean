module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Radical
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Plus
import CFSG.Sporadic.HNOddCore.FusB
import CFSG.LargeExtraspecial.S4EightRes
import CFSG.GH74.GLS.LU.Local.Core
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S4EightOdd
import CFSG.LargeExtraspecial.S4SevenC
import CFSG.LargeExtraspecial.S4SevenCases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.EvenSporadicStandard.HNRecog.SideF4 Equiv

section HN

private theorem card_eq_of_isSylowTwoOf_jh
    {T : Subgroup JH}
    (hT : IsSylowTwoOf T ⊤) : Nat.card T = 16384 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hTidx⟩ := hT
  have hidx : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  rw [hidx] at hTidx
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hmul := Subgroup.card_mul_index T
  rw [hk, card_JH] at hmul
  have hk15 : k < 15 := by
    by_contra hc
    have h : 2 ^ 15 ∣ 273030912000000 :=
      (pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ hmul)
    norm_num at h
  rw [hk]
  interval_cases k <;> omega

private theorem card_inf_centralizer_le
    {A : Subgroup JH} (hA : CFSG.Open.IsElemAbelian 5 A) {g : JH} (hg : IsConj t4J g) :
    Nat.card ↥(A ⊓ centralizer {g}) ≤ 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (centralizer {g}) = 3686400 :=
    (card_centralizer_of_isConj hg).symm.trans card_CJ_t4
  obtain ⟨k, hk⟩ := (hA.isPGroup.to_le inf_le_left :
    IsPGroup 5 ↥(A ⊓ centralizer {g})).exists_card_eq
  have hdvd : 5 ^ k ∣ 3686400 := by
    rw [← hk, ← hc]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : 5 ^ 3 ∣ 3686400 := (pow_dvd_pow 5 (by omega)).trans hdvd
    norm_num at h3
  rw [hk]
  calc 5 ^ k ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 25 := by norm_num

private theorem isConj_t4J_of_thetaJ
    {x : HJ} {σ : Perm (Fin 12)}
    (hσ : σ ∈ alternatingGroup (Fin 12)) (h : (thetaJ x : Perm (Fin 12)) = σ * sig4 * σ⁻¹) :
    IsConj t4J (x : JH) := by
  have hx : thetaJ.symm ⟨σ, hσ⟩ * t4H * (thetaJ.symm ⟨σ, hσ⟩)⁻¹ = x := by
    apply thetaJ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, thetaJ_t4H, h]
  refine isConj_iff.2 ⟨((thetaJ.symm ⟨σ, hσ⟩ : HJ) : JH), ?_⟩
  have := congrArg (fun y : HJ => (y : JH)) hx
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this


theorem hn_qJ_le_subgroupOf {T : Subgroup JH} (hT : IsSylowTwoOf T ⊤)
    (hTC : T ≤ centralizer {t4J}) : QJ ≤ T.subgroupOf (centralizer {t4J}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : Nat.card (T.subgroupOf (centralizer {t4J})) = 16384 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv).trans
      (card_eq_of_isSylowTwoOf_jh hT)
  have hp : IsPGroup 2 (T.subgroupOf (centralizer {t4J})) :=
    IsPGroup.of_card (n := 14) (by rw [hT']; norm_num)
  have hidx : ¬ 2 ∣ (T.subgroupOf (centralizer {t4J})).index := by
    have h := Subgroup.card_mul_index (T.subgroupOf (centralizer {t4J}))
    rw [hT', card_CJ_t4] at h
    omega
  have hQ : IsPGroup 2 QJ := IsPGroup.of_card (n := 9) (by rw [card_QJ]; norm_num)
  exact hQ.le_sylow_of_normal (hp.toSylow hidx)

private theorem eq_one_or_eq_t4J_of_central {T : Subgroup JH} (hT : IsSylowTwoOf T ⊤)
    (hTC : T ≤ centralizer {t4J}) {t : JH} (ht : t ∈ T) (hts : ∀ s ∈ T, s * t = t * s) :
    t = 1 ∨ t = t4J := by
  have hQT := hn_qJ_le_subgroupOf hT hTC
  have hcent : (⟨t, hTC ht⟩ : centralizer {t4J}) ∈ Subgroup.centralizer (QJ : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subtype.ext (hts q (Subgroup.mem_subgroupOf.1 (hQT hq)))
  have hz := centre_QJ_le exists_noncomm_QJ _ (centralizer_QJ_le hcent) fun y hy =>
    Subtype.ext (hts y (Subgroup.mem_subgroupOf.1 (hQT hy))).symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hk2 : t4G ^ (k % (orderOf t4G : ℤ)) = t4G ^ k := zpow_mod_orderOf t4G k
  rw [orderOf_t4G, Nat.cast_ofNat, hk] at hk2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero] at hk2
    exact congrArg Subtype.val hk2.symm
  · right
    rw [h, zpow_one] at hk2
    exact congrArg Subtype.val hk2.symm

private theorem thetaK_c4K_eq {s : ℕ} (hs : s < 9) {σ : Perm (Fin 12)}
    (h : PRep 12 (natArr InvData.c4Nat[s]!) σ) : thetaK (c4K s) = σ := by
  rw [thetaK_c4K hs]
  exact (nat_c4G hs).unique h

private theorem thetaK_eK_three : thetaK (eK 3) = swap 4 5 * swap 6 7 := by
  have h1 : thetaK (c4K 1) = swap 0 1 * swap 4 5 :=
    thetaK_c4K_eq (by norm_num) (by unfold PRep; decide)
  have h2 : thetaK (c4K 2) = swap 0 1 * swap 6 7 :=
    thetaK_c4K_eq (by norm_num) (by unfold PRep; decide)
  have he : eK 3 = c4K 2 * c4K 1 := by
    have hw : eWords[3]! = [3, 2] := by decide
    rw [eK, hw, CFSG.Sporadic.LySchreier.evalWord_cons, CFSG.Sporadic.LySchreier.evalWord_cons,
      CFSG.Sporadic.LySchreier.evalWord_nil, mul_one]
    rfl
  rw [he, map_mul, h2, h1]
  decide

private theorem thetaK_eK_two : thetaK (eK 2) = swap 8 11 * swap 9 10 := by
  have h6 : thetaK (c4K 6) = swap 8 10 * swap 8 9 :=
    thetaK_c4K_eq (by norm_num) (by unfold PRep; decide)
  have h7 : thetaK (c4K 7) = swap 8 11 * swap 8 9 :=
    thetaK_c4K_eq (by norm_num) (by unfold PRep; decide)
  have he : eK 2 = c4K 7 * c4K 6 := by
    have hw : eWords[2]! = [8, 7] := by decide
    rw [eK, hw, CFSG.Sporadic.LySchreier.evalWord_cons, CFSG.Sporadic.LySchreier.evalWord_cons,
      CFSG.Sporadic.LySchreier.evalWord_nil, mul_one]
    rfl
  rw [he, map_mul, h7, h6]
  decide

private theorem thetaJ_eH :
    (thetaJ (Subgroup.inclusion K4_le_HJ (eK 3 * eK 2)) : Perm (Fin 12)) =
      swap 4 5 * swap 6 7 * (swap 8 11 * swap 9 10) := by
  rw [← thetaK_apply, map_mul, thetaK_eK_three, thetaK_eK_two]

private theorem exists_e :
    ∃ e : JH, (∀ T : Subgroup JH, IsSylowTwoOf T ⊤ → T ≤ centralizer {t4J} → e ∈ T) ∧ e * e = 1 ∧
      IsConj t4J e ∧ IsConj t4J (e * t4J) := by
  have hc : swap 0 8 * swap 1 11 * swap 2 9 * swap 3 10 ∈ alternatingGroup (Fin 12) := by
    rw [Perm.mem_alternatingGroup]
    decide
  have hd : swap 4 8 * swap 5 11 * swap 6 9 * swap 7 10 ∈ alternatingGroup (Fin 12) := by
    rw [Perm.mem_alternatingGroup]
    decide
  have he : IsConj t4J ((Subgroup.inclusion K4_le_HJ (eK 3 * eK 2) : HJ) : JH) :=
    isConj_t4J_of_thetaJ hc (by rw [thetaJ_eH, sig4]; decide)
  have hez : IsConj t4J ((Subgroup.inclusion K4_le_HJ (eK 3 * eK 2) * t4H : HJ) : JH) :=
    isConj_t4J_of_thetaJ hd
      (by rw [map_mul, Subgroup.coe_mul, thetaJ_eH, thetaJ_t4H, sig4]; decide)
  rw [Subgroup.coe_inclusion] at he
  rw [Subgroup.coe_mul, Subgroup.coe_inclusion] at hez
  refine ⟨((eK 3 * eK 2 : K4) : JH), fun T hT hTC => ?_, ?_, he, hez⟩
  · have hmem : Subgroup.inclusion K4_le_CJ (eK 3 * eK 2) ∈ QJ := by
      rw [map_mul]
      exact QJ.mul_mem (eK_mem_QJ (by norm_num)) (eK_mem_QJ (by norm_num))
    have h := Subgroup.mem_subgroupOf.1 (hn_qJ_le_subgroupOf hT hTC hmem)
    rwa [Subgroup.coe_inclusion] at h
  · obtain ⟨c, hc⟩ := isConj_iff.1 he
    rw [← hc]
    calc c * t4J * c⁻¹ * (c * t4J * c⁻¹) = c * (t4J * t4J) * c⁻¹ := by group
      _ = 1 := by rw [t4J_sq, mul_one, mul_inv_cancel]

theorem hn_oddLocal {T : Subgroup JH} (hT : IsSylowTwoOf T ⊤) (hTC : T ≤ centralizer {t4J})
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : Subgroup JH) (hA : CFSG.Open.IsElemAbelian p A)
    (hA1 : A ≠ ⊥) (hTA : T ≤ normalizer (A : Set JH)) : A ⊓ centralizer {t4J} ≠ ⊥ := by
  intro hAz
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hA.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hzT : t4J ∈ T := Subgroup.mem_subgroupOf.1 (hn_qJ_le_subgroupOf hT hTC t4G_mem_QJ)
  have hdvd := card_dvd_card_GL_of_inf_centralizer_eq_bot hp (by omega) hT.2.1 hzT t4J_sq
    (fun t ht hts => eq_one_or_eq_t4J_of_central hT hTC ht hts) hA hn hA1 hTA hAz
  rw [card_eq_of_isSylowTwoOf_jh hT] at hdvd
  rcases Nat.lt_or_ge p 7 with hp7 | hp7
  ·
    obtain rfl : p = 5 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
      have h := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
      exact h
    have hinv : ∀ a ∈ A, t4J * a * t4J⁻¹ = a⁻¹ :=
      CFSG.GH74.GLS.LU.Local.inverts_of_fixed_eq_bot t4J_sq hAcomm
        (fun a ha => (Subgroup.mem_normalizer_iff.1 (hTA hzT) a).1 ha) fun a ha h => by
          have hm : a ∈ A ⊓ centralizer {t4J} := by
            refine Subgroup.mem_inf.2 ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
            calc a * t4J = t4J * a * t4J⁻¹ * t4J := by rw [h]
              _ = t4J * a := by group
          rw [hAz] at hm
          exact Subgroup.mem_bot.1 hm
    obtain ⟨e, heT, hee, he, hez⟩ := exists_e
    have hodd : Odd (Nat.card A) := by
      rw [hn]
      exact Odd.pow (by decide)
    have hle := CFSG.LargeExtraspecial.S4.card_le_mul_of_conj_eq_inv hodd hee
      (hTA (heT T hT hTC)) hinv
    have hA625 : Nat.card A ≤ 5 ^ 4 :=
      hle.trans ((Nat.mul_le_mul (card_inf_centralizer_le hA he)
        (card_inf_centralizer_le hA hez)).trans (by norm_num))
    have hn4 : n ≤ 4 := by
      rw [hn] at hA625
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hA625
    interval_cases n <;> rw [Matrix.card_GL_field] at hdvd <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at hdvd
  ·
    have hfac : (273030912000000 : ℕ) = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by norm_num
    have hdvdJ : p ^ n ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by
      rw [← hfac, ← card_JH, ← hn]
      exact Subgroup.card_subgroup_dvd_card A
    have hpJ := (dvd_pow_self p hn0).trans hdvdJ
    have hpq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
      (Nat.prime_dvd_prime_iff_eq hp hq).1 h
    have hp' : p = 7 ∨ p = 11 ∨ p = 19 := by
      rcases (Nat.Prime.dvd_mul hp).1 hpJ with h | h19
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h11
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
            · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
              · have := hpq 2 Nat.prime_two (hp.dvd_of_dvd_pow h2)
                omega
              · have := hpq 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)
                omega
            · have := hpq 5 (by norm_num) (hp.dvd_of_dvd_pow h5)
              omega
          · exact Or.inl (hpq 7 (by norm_num) h7)
        · exact Or.inr (Or.inl (hpq 11 (by norm_num) h11))
      · exact Or.inr (Or.inr (hpq 19 (by norm_num) h19))
    have hn1 : n = 1 := by
      by_contra hn1
      have h2 : p ^ 2 ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 :=
        (pow_dvd_pow p (by omega)).trans hdvdJ
      rcases hp' with rfl | rfl | rfl <;> norm_num at h2
    subst hn1
    rcases hp' with rfl | rfl | rfl <;> rw [Matrix.card_GL_field] at hdvd <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at hdvd

end HN

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
