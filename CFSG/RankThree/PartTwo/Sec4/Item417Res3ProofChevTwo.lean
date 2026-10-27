module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL3
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofOutData
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

open scoped MatrixGroups

namespace Res417Three

theorem two_pow_mod_three (n : ℕ) : (Even n → 2 ^ n % 3 = 1) ∧ (Odd n → 2 ^ n % 3 = 2) := by
  refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ?_⟩
  · subst hk
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  · subst hk
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem pRank_three_projSL_two_two {n : ℕ} (hn : 1 ≤ n) :
    CFSG.pRank 3 (projSL 2 (GaloisField 2 n)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hcard := Sec21.card_projSL_two n hn
    have : Finite (projSL 2 (GaloisField 2 n)) := Nat.finite_of_card_ne_zero (by
      rw [hcard]
      have : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
      have : 0 < (2 ^ n) ^ 2 - 1 := by omega
      positivity)
    refine pRank_le_one_of_not_dvd ?_
    rw [hcard]
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl <;> norm_num
  · have e := projSLEquivPSL (GaloisField 2 n)
    have : Finite (PSL(2, GaloisField 2 n)) := inferInstance
    have : Finite (projSL 2 (GaloisField 2 n)) := Finite.of_equiv _ e.symm.toEquiv
    have h := pRank_le_one_of_isCyclic_sylow (X := PSL(2, GaloisField 2 n)) (p := 3) fun R =>
      CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField 2 n) hK
        (by rw [hK]; exact (Nat.pow_le_pow_right (by norm_num) hn3).trans' (by norm_num)) 3
        (by norm_num) (by rw [hK]; exact Nat.Coprime.pow_right n (by norm_num)) R
    exact (CFSG.RankThree.OddKernel.pRank_le_of_injective (by norm_num) e.toMonoidHom
      e.injective).trans h

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK, Nat.cast_pow] at h
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (eq_zero_of_pow_eq_zero h)

theorem pRank_three_statedSL_two {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Odd n)
    (hK : Nat.card K = 2 ^ n) : CFSG.pRank 3 (StatedSL 3 K) ≤ 1 := by
  have : CharP K 2 := charP_two_of_card hK
  have hq : Nat.card K % 3 = 2 := by rw [hK]; exact (two_pow_mod_three n).2 hn
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have hE : CFSG.Open.IsElemAbelian 3 (B.map (StatedSL 3 K).subtype) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x', hx', hxe⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : GL (Fin 3) K) * y = y * x
      rw [← hxe, ← hye, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hB.toIsMulCommutative.is_comm.comm ⟨x', hx'⟩
        ⟨y', hy'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩
      have h' : x ^ 3 = 1 := by simpa using congrArg Subtype.val h
      rw [← map_pow, h', map_one]
  have h3 := Sec20.card_le_three_of_isElemAbelian hq (Subgroup.map_subtype_le _) hE
  rw [Subgroup.card_map_of_injective (StatedSL 3 K).subtype_injective, hr] at h3
  by_contra hr1
  have : 3 ^ 2 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem eq_of_card_datum {m k : ℕ} (hm : 3 ≤ m) {n : ℕ} (h1 : n = 3 ^ (m - 1))
    (h2 : n = 3 ^ k) : m = k + 1 := by
  rw [h1] at h2
  have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
  omega

end Res417Three

open Res417Three

section Certs


@[expose] def K417CenterChevTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
    ((∃ n : ℕ, 1 ≤ n ∧ (Nonempty (Y ⧸ Subgroup.center Y ≃* projSp 2 (GaloisField 2 n)) ∨
        Nonempty (Y ⧸ Subgroup.center Y ≃* projSU 4 2 n))) ∨
      ∃ f : ℕ, ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .G2 2 f ∨
        ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .trialityD4 2 f ∨
        ReeTitsModel (Y ⧸ Subgroup.center Y) .twistedF4 2 f ∨
        ReeTitsModel (Y ⧸ Subgroup.center Y) .Tits 2 f) →
    ∀ r : ℕ, r.Prime → 3 < r → ¬ r ∣ Nat.card (Subgroup.center Y)

@[expose] def K417DatumChevTwo : Prop :=
  (∀ (n : ℕ), 1 ≤ n → ∀ D : Subgroup (projSp 2 (GaloisField 2 n)),
    IsDatum417 (projSp 2 (GaloisField 2 n)) D →
      Even n ∧ Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)) ∧
  (∀ (n : ℕ), 1 ≤ n → ∀ D : Subgroup (projSU 4 2 n), IsDatum417 (projSU 4 2 n) D →
      (Even n ∧ Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)) ∨
        (Odd n ∧ Nat.card D = 27 ∧ Nonempty (autIn ⊤ D ≃* Equiv.Perm (Fin 4)))) ∧
  (∀ (X : Type) [Group X] (f : ℕ),
    (ChevalleyExceptionalModel X .G2 2 f ∨ ChevalleyExceptionalModel X .trialityD4 2 f) →
      ∀ D : Subgroup X, IsDatum417 X D →
        Even f ∧ Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 6)) ∧
  (∀ (X : Type) [Group X] (f : ℕ),
    (ReeTitsModel X .twistedF4 2 f ∨ ReeTitsModel X .Tits 2 f) →
      ∀ D : Subgroup X, ¬ IsDatum417 X D)

variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.false_of_pRank_mulAut (h : IsInnerOutConf417 L A E c m)
    (hS : CFSG.pRank 3 (MulAut (L ⧸ aschbacherSolvableCore 3 L)) ≤ 1) : False := by
  have hLq := h.2.2.1.1
  have hAN := h.2.2.2.2.2.1
  obtain ⟨hAmax, hcard, hAc, hc3, -⟩ := h.2.2.2.2.1
  have h1 := card_range_thetaAct_mul hLq hAN
  rw [hAc, Nat.card_zpowers, hc3, hcard] at h1
  have hm := three_le_of_isQuad h.2.2.2.2.1
  have hR : Nat.card (thetaAct hAN).range = 3 ^ (m - 1) := by
    have : 3 ^ m = 3 ^ (m - 1) * 3 := by rw [← pow_succ]; congr 1; omega
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have h2 := le_pRank_mulAut (MulEquiv.refl _) (isElemAbelian_range_thetaAct hAN hAmax.prop) hR
  omega

theorem IsInnerOutConf417.alt417_of_chevTwo (hC : K417CenterChevTwo) (hD : K417DatumChevTwo)
    (h : IsInnerOutConf417 L A E c m)
    (hX : (∃ n : ℕ, 1 ≤ n ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 n))) ∨
        ∃ f : ℕ, ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 f ∨
          ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 f ∨
          ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 f ∨
          ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .Tits 2 f) : Alt417 L A m := by
  have eC := h.centerEquiv
  have hm3 := three_le_of_isQuad h.2.2.2.2.1
  have hθ : aschbacherSolvableCore 3 L = ⊥ := by
    refine theta_eq_bot_of_two_three h.2.1 h.2.2.1 fun r hr hr3 => hC L h.2.2.1.1 ?_ r hr hr3
    rcases hX with ⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨f, hG2 | hD4 | hF4 | hT⟩
    · exact Or.inl ⟨n, hn, Or.inl ⟨eC.trans φ⟩⟩
    · exact Or.inl ⟨n, hn, Or.inr ⟨eC.trans φ⟩⟩
    · exact Or.inr ⟨f, Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eC hG2)⟩
    · exact Or.inr ⟨f, Or.inr (Or.inl
        (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eC hD4))⟩
    · exact Or.inr ⟨f, Or.inr (Or.inr (Or.inl (CFSG.SectionRank.reeTitsModel_of_mulEquiv eC hF4)))⟩
    · exact Or.inr ⟨f, Or.inr (Or.inr (Or.inr (CFSG.SectionRank.reeTitsModel_of_mulEquiv eC hT)))⟩
  set eL : L ≃* L ⧸ aschbacherSolvableCore 3 L := (Res417.thetaQuotEquivOfEqBot hθ).symm
  rcases hX with ⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨f, hG2 | hD4 | hF4 | hT⟩
  · obtain ⟨hdat, hcD, ⟨eA⟩⟩ := h.datum (eL.trans φ)
    obtain ⟨hev, h9, ⟨q⟩⟩ := hD.1 n hn _ hdat
    have hm := eq_of_card_datum (k := 2) hm3 hcD (h9.trans (by norm_num))
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hm, Or.inl ⟨n, by omega, hev, Or.inl ⟨eL.trans φ⟩⟩, ⟨eA.trans q⟩⟩))))))))))
  · obtain ⟨hdat, hcD, ⟨eA⟩⟩ := h.datum (eL.trans φ)
    rcases hD.2.1 n hn _ hdat with ⟨hev, h9, ⟨q⟩⟩ | ⟨hodd, h27, ⟨q⟩⟩
    · have hm := eq_of_card_datum (k := 2) hm3 hcD (h9.trans (by norm_num))
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hm, Or.inl ⟨n, by omega, hev, Or.inr ⟨eL.trans φ⟩⟩, ⟨eA.trans q⟩⟩))))))))))
    · have hm := eq_of_card_datum (k := 3) hm3 hcD (h27.trans (by norm_num))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨hm, ⟨n, hodd, ⟨eL.trans φ⟩⟩, ⟨eA.trans q⟩⟩)))))))))))
  · have hG2' := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL hG2
    obtain ⟨hdat, hcD, ⟨eA⟩⟩ := h.datum (MulEquiv.refl L)
    obtain ⟨hev, h9, ⟨q⟩⟩ := hD.2.2.1 L f (Or.inl hG2') _ hdat
    have hm := eq_of_card_datum (k := 2) hm3 hcD (h9.trans (by norm_num))
    have hf : 0 < f := hG2.1.2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hm, ⟨f, hf, hev, Or.inl hG2'⟩, ⟨eA.trans q⟩⟩)))))))))
  · have hD4' := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eL hD4
    obtain ⟨hdat, hcD, ⟨eA⟩⟩ := h.datum (MulEquiv.refl L)
    obtain ⟨hev, h9, ⟨q⟩⟩ := hD.2.2.1 L f (Or.inr hD4') _ hdat
    have hm := eq_of_card_datum (k := 2) hm3 hcD (h9.trans (by norm_num))
    have hf : 0 < f := hD4.1.2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hm, ⟨f, hf, hev, Or.inr hD4'⟩, ⟨eA.trans q⟩⟩)))))))))
  · obtain ⟨hdat, -, -⟩ := h.datum (MulEquiv.refl L)
    exact (hD.2.2.2 L f (Or.inl (CFSG.SectionRank.reeTitsModel_of_mulEquiv eL hF4)) _ hdat).elim
  · obtain ⟨hdat, -, -⟩ := h.datum (MulEquiv.refl L)
    exact (hD.2.2.2 L f (Or.inr (CFSG.SectionRank.reeTitsModel_of_mulEquiv eL hT)) _ hdat).elim

theorem item417OutChevTwo_of (hU3 : K417RankOneU3) (hC : K417CenterChevTwo)
    (hD : K417DatumChevTwo) : Item417OutChevTwo := by
  intro G _ _ L A E c m hconf hX
  have hSL : ¬ IsSLThreePiTheta L := hconf.2.2.2.2.2.2.2.1
  rcases hX with (⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | hSp | hU4⟩ |
      ⟨f, hG2 | hD4 | hSz | hF4 | hT⟩) | ⟨n, hn, hSL3⟩
  ·
    exact (hconf.false_of_theta_pRank φ (pRank_three_projSL_two_two hn)).elim
  ·
    rcases Nat.even_or_odd n with hev | hodd
    · exact (hSL ⟨2, n, inferInstance, hn,
        Or.inr (Or.inl ⟨(two_pow_mod_three n).1 hev, ⟨φ⟩⟩)⟩).elim
    · have h1 := Sec20.kFactL3OddThreeRank n hodd (L ⧸ aschbacherSolvableCore 3 L) ⟨φ⟩
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
      exact (hconf.false_of_theta_pRank (MulEquiv.refl _) h1).elim
  ·
    rcases Nat.even_or_odd n with hev | hodd
    · exact (hconf.false_of_theta_pRank φ
        (hU3 2 n (by norm_num) hn ((two_pow_mod_three n).1 hev)).1).elim
    · exact (hSL ⟨2, n, inferInstance, hn,
        Or.inr (Or.inr ⟨(two_pow_mod_three n).2 hodd, ⟨φ⟩⟩)⟩).elim
  · exact hconf.alt417_of_chevTwo hC hD (Or.inl ⟨n, hn, Or.inl hSp⟩)
  · exact hconf.alt417_of_chevTwo hC hD (Or.inl ⟨n, hn, Or.inr hU4⟩)
  · exact hconf.alt417_of_chevTwo hC hD (Or.inr ⟨f, Or.inl hG2⟩)
  · exact hconf.alt417_of_chevTwo hC hD (Or.inr ⟨f, Or.inr (Or.inl hD4)⟩)
  ·
    exact (hconf.false_of_pRank_mulAut (KFacts.KP7.pRank_three_mulAut_le_one hSz)).elim
  · exact hconf.alt417_of_chevTwo hC hD (Or.inr ⟨f, Or.inr (Or.inr (Or.inl hF4))⟩)
  · exact hconf.alt417_of_chevTwo hC hD (Or.inr ⟨f, Or.inr (Or.inr (Or.inr hT))⟩)
  ·
    obtain ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := hSL3
    · rcases Nat.even_or_odd n with hev | hodd
      · exact (hSL ⟨2, n, inferInstance, hn, Or.inl ⟨K, inferInstance, inferInstance,
          Or.inl ⟨hK, (two_pow_mod_three n).1 hev, ⟨φ⟩⟩⟩⟩).elim
      · exact (hconf.false_of_theta_pRank φ (pRank_three_statedSL_two hodd hK)).elim
    · rcases Nat.even_or_odd n with hev | hodd
      · exact (hconf.false_of_theta_pRank φ
          ((hU3 2 n (by norm_num) hn ((two_pow_mod_three n).1 hev)).2 K hK)).elim
      · exact (hSL ⟨2, n, inferInstance, hn, Or.inl ⟨K, inferInstance, inferInstance,
          Or.inr ⟨hK, (two_pow_mod_three n).2 hodd, ⟨φ⟩⟩⟩⟩).elim

end Certs

end CFSG.RankThree.PartTwo.Sec4
