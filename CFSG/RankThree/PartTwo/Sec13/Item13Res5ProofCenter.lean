module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofCensus
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
import CFSG.LieType.Simplicity.Classical
import CFSG.LieType.Simplicity.ExceptionalConverse
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherEasy
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Res5Proof

variable {X : Type} [Group X]

theorem prod_ne_of_ne {a b c : ℕ} (h : b ≠ c) : (a, b) ≠ (a, c) := fun e =>
  h (congrArg Prod.snd e)

theorem prod_ne_of_fst_ne {a b c d : ℕ} (h : a ≠ c) : (a, b) ≠ (c, d) := fun e =>
  h (congrArg Prod.fst e)

theorem le_pow_of_one_le {p e : ℕ} (he : 1 ≤ e) : p ≤ p ^ e := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact Nat.le_self_pow (by omega) p

theorem center_eq_bot_of_projSL {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSL n p e)
    (hq : IsQuasisimple X) (φ : X ≃* projSL n (GaloisField p e)) : Subgroup.center X = ⊥ := by
  obtain ⟨-, hc | ⟨hn, -⟩⟩ := KFacts.KS21Mult.lieModel_projSL h
  · have := (LieType.Simplicity.fam_PSL_simplicity _ n p e hc).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have h2 : 2 ≤ n := h.2.2.1
    omega

theorem center_eq_bot_of_projSU {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSU n p e)
    (hq : IsQuasisimple X) (φ : X ≃* projSU n p e) : Subgroup.center X = ⊥ := by
  obtain ⟨-, hc | ⟨hn, -⟩⟩ := KFacts.KS21Mult.lieModel_projSU h
  · have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n p e hc).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have h3 : 3 ≤ n := h.2.2.1
    omega

theorem center_eq_bot_of_projSp {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSp n p e)
    (hq : IsQuasisimple X) (φ : X ≃* projSp n (GaloisField p e)) : Subgroup.center X = ⊥ := by
  obtain ⟨-, hc | ⟨hn, -⟩⟩ := KFacts.KS21Mult.lieModel_projSp h
  · have := ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ n p e hc
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have h2 : 2 ≤ n := h.2.2.1
    omega

theorem false_of_projSL_two_small {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ∨ Nat.card K = 3) (hq : IsQuasisimple X) (φ : X ≃* projSL 2 K) :
    False := by
  have := ComponentClassification.CatalogueBGeneralLinear.projectiveGeneralLinear_two_small_solvable
    K hK
  have hs : Group.IsSolvable (projSL 2 K) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  exact Sec4.false_of_isQuasisimple_of_isSolvable hq
    (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)

theorem false_of_projSp_two_two (hq : IsQuasisimple X)
    (φ : X ≃* projSp 2 (GaloisField 2 1)) : False := by
  let ψ : StatedProj (StatedSp 2 (GaloisField 2 1)) ≃* StatedSp 2 (GaloisField 2 1) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSp_eq_bot 2)).trans
      QuotientGroup.quotientBot
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  obtain ⟨ω⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := GaloisField 2 1)
    (by rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero, pow_one])
  let θ := ((φ.trans (Sec4.projSpEquivStatedProj 2 (GaloisField 2 1))).trans ψ).trans ω
  have := hq.1
  exact Sec4.Item434SmallTwoOther.not_isPerfect_perm_six
    (Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective)

theorem center_eq_bot_of_sporadic
    (hq : IsQuasisimple X) {s : TauCeti.SporadicName} (hs : s ∈ Sec4.sporadics46)
    (φ : X ≃* Blueprint.NativeSporadic.Carrier s) : Subgroup.center X = ⊥ := by
  simp only [Sec4.sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M11) :=
      CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M12) :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M22) :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M23) :=
      CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M24) :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J1) :=
      CFSG.Sporadic.J1.isSimpleGroup_J1
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J2) :=
      CFSG.Sporadic.J2.isSimpleGroup_J2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J3) :=
      CFSG.Sporadic.J3.isSimpleGroup_J3
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J4) :=
      CFSG.Sporadic.J4.isSimpleGroup_J4
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .McL) :=
      CFSG.Sporadic.McL.isSimpleGroup_McL
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .HS) :=
      CFSG.Sporadic.HS.isSimpleGroup_HS
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .He) :=
      CFSG.Sporadic.He.isSimpleGroup_He
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  · have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .Ru) :=
      CFSG.Sporadic.Ru.isSimpleGroup_Ru
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ

theorem mem_range_conj_of_not_three_dvd_outer {Y : Type*} [Group Y] (hXp : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* Y) (hY : ¬ 3 ∣ Nat.card (Outer Y)) {σ : MulAut X}
    (hσ : σ ^ 3 = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  apply Sec12.KS128NotHJTC.mem_range_conj_of_congr_mem hXp e
  set τ := MulAut.congr e (KFacts.centerDescend X σ) with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, ← map_pow, hσ, map_one, map_one]
  have hne : Nat.card (Outer Y) ≠ 0 := fun h0 => hY (h0 ▸ dvd_zero 3)
  have : Finite (Outer Y) := Nat.finite_of_card_ne_zero hne
  set t : Outer Y := (τ : Outer Y) with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← QuotientGroup.mk_pow, hτ3, QuotientGroup.mk_one]
  have hcop : Nat.Coprime 3 (Nat.card (Outer Y)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY
  have hord : orderOf t ∣ Nat.gcd 3 (Nat.card (Outer Y)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht3) (orderOf_dvd_natCard t)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact (QuotientGroup.eq_one_iff τ).mp hord

theorem not_three_dvd_of_card_le_two {Y : Type*} [Group Y] [Finite (Outer Y)]
    (h : Nat.card (Outer Y) ≤ 2) : ¬ 3 ∣ Nat.card (Outer Y) := by
  have h1 : 0 < Nat.card (Outer Y) := Nat.card_pos
  intro h3
  obtain ⟨k, hk⟩ := h3
  omega

theorem finite_outer (Y : Type*) [Group Y] [Finite Y] : Finite (Outer Y) := by
  have : Finite (MulAut Y) := Finite.of_injective (fun α : MulAut Y => (α : Y → Y))
    fun _ _ h => MulEquiv.ext (congrFun h)
  infer_instance

theorem cover_facts_sporadic
    (hq : IsQuasisimple X) {s : TauCeti.SporadicName}
    (hs : s ∈ Sec4.sporadicCovers46)
    (hext : Sec4.IsExtOf X (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) :
    Nat.card (Subgroup.center X) = 3 ∧
      ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range := by
  have htc := (Sec4.isTripleCover_iff_isExtOf hq (Sec4.center_carrier_eq_bot_of_cover hs)).mpr
    hext
  obtain ⟨hc3, ⟨e⟩⟩ := htc
  refine ⟨hc3, fun σ hσ => ?_⟩
  simp only [Sec4.sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hq.1
      (Or.inr (Or.inr ⟨hc3, ⟨e⟩⟩)) hσ
  · have : Finite Blueprint.NativeSporadic.J3 := CFSG.Sporadic.J3.fam_j3_simplicity.1
    have : Finite (Outer Blueprint.NativeSporadic.J3) := finite_outer _
    exact mem_range_conj_of_not_three_dvd_outer (Y := Blueprint.NativeSporadic.J3) hq.1 e
      (not_three_dvd_of_card_le_two Sec4.card_outer_J3) hσ
  · have : Finite Blueprint.NativeSporadic.McL :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
    have : Finite (Outer Blueprint.NativeSporadic.McL) := finite_outer _
    exact mem_range_conj_of_not_three_dvd_outer (Y := Blueprint.NativeSporadic.McL) hq.1 e
      (not_three_dvd_of_card_le_two Sec4.card_outer_McL) hσ
  · exact mem_range_conj_of_not_three_dvd_outer hq.1 e Sec4.inputs47Core_outON hσ

theorem card_center_of_isSLThreePiAt {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hX : Sec4.IsSLThreePiAt X (p ^ e)) : Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨φ⟩⟩ | ⟨hK, hq, ⟨φ⟩⟩⟩ := hX
  · have hK' : Sec4.PiField true p e K := ⟨hp, he, hK⟩
    rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
    exact KFacts.card_center_slPi (π := true) hK' hq
  · have hK' : Sec4.PiField false p e K := ⟨hp, he, hK⟩
    rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
    exact KFacts.card_center_slPi (π := false) hK' hq

theorem card_center_of_isSLThreeEpsAt {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hp3 : p ≠ 3)
    (hX : Sec4.IsSLThreeEpsAt X (p ^ e)) (h3 : 3 ∣ Nat.card (Subgroup.center X)) :
    Nat.card (Subgroup.center X) = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
    have h0 : p ^ e % 3 ≠ 0 := fun h0 => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))).symm
    omega
  have hZ : Subgroup.center X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  exact card_center_of_isSLThreePiAt hp he (KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hX hq hZ)

theorem center_cases
    [Finite X] (hl : Sec4.IsList46 X) (hq : IsQuasisimple X) :
    Subgroup.center X = ⊥ ∨
      (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ (p = 2 ∨ (3 < p ∧ e ≤ 2)) ∧
        Sec4.IsSLThreeEpsAt X (p ^ e)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hl with ⟨p, e, hp, hp2, he, ⟨φ⟩⟩ | ⟨p, e, hp, hp3, he1, he2, hSL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ |
      ⟨p, hp, hp3, hG2 | ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩⟩ |
      (⟨n, hn, ⟨φ⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩) |
      ((⟨e, he1, -, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩) | ⟨⟨φ⟩⟩ | ⟨hZ3, hG23 | ⟨⟨φ⟩⟩⟩)
  ·
    left
    by_cases hq3 : p ^ e = 3
    · exact (false_of_projSL_two_small (Or.inr (by rw [GaloisField.card p e (by omega), hq3]))
        hq φ).elim
    · refine center_eq_bot_of_projSL ⟨hp.out, he, le_rfl, prod_ne_of_ne ?_, prod_ne_of_ne hq3⟩
        hq φ
      intro h
      have h2' : 2 ∣ p ^ e := ⟨1, by omega⟩
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp
        (Nat.prime_two.dvd_of_dvd_pow h2')).symm
  ·
    exact Or.inr (Or.inl ⟨p, e, hp.out, he1, Or.inr ⟨hp3, he2⟩, hSL⟩)
  ·
    exact Or.inl (center_eq_bot_of_projSL (n := 3) ⟨hp.out, he1, by norm_num,
      prod_ne_of_fst_ne (by norm_num), prod_ne_of_fst_ne (by norm_num)⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSU (n := 3) ⟨hp.out, he1, le_rfl, fun h => by
      have := le_pow_of_one_le (p := p) he1
      have h' := congrArg Prod.snd h
      simp only at h'
      omega⟩ hq φ)
  ·
    have := (LieType.Simplicity.fam_chevalley_exceptional_simplicity X _ p 1 hG2).2
    exact Or.inl (Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X))
  ·
    exact Or.inl (center_eq_bot_of_projSp ⟨hp.out, le_rfl, le_rfl, prod_ne_of_ne (by
      rw [pow_one]; omega)⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSU (n := 4) ⟨hp.out, le_rfl, by norm_num, fun h => by
      have h' := congrArg Prod.fst h
      simp only at h'
      omega⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSL (n := 4) ⟨hp.out, le_rfl, by norm_num, fun h => by
      have h' := congrArg Prod.fst h
      simp only at h'
      omega, fun h => by
      have h' := congrArg Prod.fst h
      simp only at h'
      omega⟩ hq φ)
  ·
    left
    by_cases h4 : n ≤ 4
    · have hs := alternatingGroup.isSolvable (α := Fin n) (by rwa [Nat.card_fin])
      exact (Sec4.false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)).elim
    · have : IsSimpleGroup (alternatingGroup (Fin n)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
      exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ
  ·
    have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    have htc := (Sec4.isTripleCover_iff_isExtOf hq hZ6).mpr hA6
    exact Or.inr (Or.inr ⟨htc.1.le, fun σ hσ =>
      Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hq.1 (Or.inl htc) hσ⟩)
  ·
    have hZ7 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
    have htc := (Sec4.isTripleCover_iff_isExtOf hq hZ7).mpr hA7
    exact Or.inr (Or.inr ⟨htc.1.le, fun σ hσ =>
      Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hq.1 (Or.inr (Or.inl htc)) hσ⟩)
  ·
    exact Or.inl (center_eq_bot_of_sporadic hq hs φ)
  ·
    obtain ⟨h1, h2⟩ := cover_facts_sporadic hq hs hext
    exact Or.inr (Or.inr ⟨h1.le, h2⟩)
  ·
    left
    rcases hchev with ⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ |
        ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
    · by_cases hn1 : n = 1
      · subst hn1
        exact (false_of_projSL_two_small (Or.inl (by rw [GaloisField.card 2 1 one_ne_zero]; rfl))
          hq φ).elim
      · have h4 : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact center_eq_bot_of_projSL ⟨Nat.prime_two, hn, le_rfl, prod_ne_of_ne (by omega),
          prod_ne_of_ne (by omega)⟩ hq φ
    · have h2n := le_pow_of_one_le (p := 2) hn
      exact center_eq_bot_of_projSL (n := 3) ⟨Nat.prime_two, hn, by norm_num, fun h => by
        have h' := congrArg Prod.fst h
        simp only at h'
        omega, fun h => by
        have h' := congrArg Prod.fst h
        simp only at h'
        omega⟩ hq φ
    · by_cases hn1 : n = 1
      · subst hn1
        exact (Sec4.false_of_mulEquiv_projSU_three_two hq φ).elim
      · have h4 : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact center_eq_bot_of_projSU ⟨Nat.prime_two, hn, le_rfl, prod_ne_of_ne (by omega)⟩ hq φ
    · by_cases hn1 : n = 1
      · subst hn1
        exact (false_of_projSp_two_two hq φ).elim
      · have h4 : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact center_eq_bot_of_projSp ⟨Nat.prime_two, hn, le_rfl, prod_ne_of_ne (by omega)⟩ hq φ
    · exact center_eq_bot_of_projSU (n := 4) ⟨Nat.prime_two, hn, by norm_num, fun h => by
        have h' := congrArg Prod.fst h
        simp only at h'
        omega⟩ hq φ
    · have := (LieType.Simplicity.fam_chevalley_exceptional_simplicity X _ 2 f hG2).2
      exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
    · have := (LieType.Simplicity.fam_chevalley_exceptional_simplicity X _ 2 f hD4).2
      exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
    · have := (LieType.Simplicity.fam_2b2_simplicity X 2 f hSz).2
      exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
    · have := (LieType.Simplicity.fam_ree_tits_simplicity X _ 2 f hF4).2
      exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
    · have := (LieType.Simplicity.fam_ree_tits_simplicity X _ 2 f hTits).2
      exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
  ·
    exact Or.inr (Or.inl ⟨2, n, Nat.prime_two, hn, Or.inl rfl, hSL⟩)
  ·
    exact Or.inl (center_eq_bot_of_projSL (n := 5) ⟨Nat.prime_two, le_rfl, by norm_num, by decide,
      by decide⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSp (n := 3) ⟨Nat.prime_two, le_rfl, by norm_num,
      by decide⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSU (n := 5) ⟨Nat.prime_two, by norm_num, by norm_num,
      by decide⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSL (n := 3) ⟨Nat.prime_three, he1, by norm_num, fun h => by
      have h' := congrArg Prod.fst h
      simp only at h'
      omega, fun h => by
      have h' := congrArg Prod.fst h
      simp only at h'
      omega⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSU (n := 3) ⟨Nat.prime_three, he1, le_rfl, fun h => by
      have := le_pow_of_one_le (p := 3) he1
      have h' := congrArg Prod.snd h
      simp only at h'
      omega⟩ hq φ)
  ·
    exact Or.inl (center_eq_bot_of_projSL (n := 4) ⟨Nat.prime_three, le_rfl, by norm_num, by decide,
      by decide⟩ hq φ)
  ·
    refine Or.inr (Or.inr ⟨hZ3, fun σ hσ => ?_⟩)
    refine mem_range_conj_of_not_three_dvd_outer hq.1 (MulEquiv.refl _) ?_ hσ
    rw [KFacts.OutFixCentralThree.card_outer_G2_three _ hG23]
    norm_num
  ·
    exact Or.inr (Or.inr ⟨hZ3, fun σ hσ =>
      mem_range_conj_of_not_three_dvd_outer hq.1 φ Sec4.outU43_holds hσ⟩)

end Res5Proof

open Res5Proof

theorem ks131CenterList46 :
    KS131CenterList46 := by
  intro X _ _ hl hq h3
  rcases center_cases hl hq with hZ | ⟨p, e, hp, he, hpe, hSL⟩ | ⟨hle, -⟩
  · rw [hZ, Subgroup.card_bot] at h3
    norm_num at h3
  · refine card_center_of_isSLThreeEpsAt hp he ?_ hSL h3
    rcases hpe with rfl | ⟨hp3, -⟩ <;> omega
  · obtain ⟨k, hk⟩ := h3
    have h0 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
    omega

end CFSG.RankThree.PartTwo.Sec13
