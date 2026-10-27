module

public import CFSG.RankThree.PartTwo.Sec4.Item413Inputs
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Transport

variable {X : Type} [Group X]

theorem map_center_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) :
    (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e w * e x = e x * e w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx w]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro z
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hy (e z)]

@[expose] noncomputable def quotientCenterCongr {Y : Type*} [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr _ _ e (map_center_mulEquiv e)

theorem card_center_congr {Y : Type*} [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) := by
  rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective]

@[expose] noncomputable def quotientCenterEquivOfBot {Y : Type*} [Group Y]
    (hZ : Subgroup.center Y = ⊥) : Y ⧸ Subgroup.center Y ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem IsExtOf.of_mulEquiv {Y S B : Type*} [Group Y] [Group S] [Group B] (e : X ≃* Y)
    (h : IsExtOf X S B) : IsExtOf Y S B := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have hK' : (K.map (e : X →* Y)).Normal := hK.map _ e.surjective
  exact ⟨K.map (e : X →* Y), hK',
    ⟨((K.equivMapOfInjective _ e.injective).symm.trans eK)⟩,
    ⟨(QuotientGroup.congr K (K.map (e : X →* Y)) e rfl).symm.trans eQ⟩⟩

theorem card_quotient_center_dvd {K : Subgroup X} (hK : K ≤ Subgroup.center X) :
    Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card (X ⧸ K) := by
  rw [← Subgroup.index, ← Subgroup.index]
  exact Subgroup.index_dvd_of_le hK

theorem false_of_mulEquiv_projSU_three_two (hq : CFSG.IsQuasisimple X)
    (e : X ≃* projSU 3 2 1) : False := by
  have := Sec13.isSolvable_projSU_two
  exact false_of_isQuasisimple_of_isSolvable hq
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem false_of_mulEquiv_statedSU_three_two (hq : CFSG.IsQuasisimple X) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) : False := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
      (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  exact false_of_isQuasisimple_of_isSolvable hq
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

end Transport

section Bounds

variable {X : Type} [Group X] [Finite X]

theorem false_of_rankAut {M : Type} [Group M] (e : X ≃* M)
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B) {k : ℕ}
    (hk : Nat.card B = 3 ^ k) (hk4 : 4 ≤ k) (hM : CFSG.pRank 3 (MulAut M) ≤ 3) : False := by
  have : Finite M := Finite.of_equiv X e.toEquiv
  have := le_pRank_mulAut e hB hk
  omega

theorem false_of_rankInner {S : Type} [Group S]
    (e : X ⧸ Subgroup.center X ≃* S) {B : Subgroup (MulAut X)}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBi : B ≤ (MulAut.conj : X →* MulAut X).range)
    {k : ℕ} (hk : Nat.card B = 3 ^ k) (hk4 : 4 ≤ k) (hS : CFSG.pRank 3 S ≤ 3) : False := by
  have : Finite S := Finite.of_equiv _ e.toEquiv
  have := le_pRank_of_le_inner e hB hBi hk
  omega

theorem false_of_rankInnerModel {M : Type} [Group M] (e : X ≃* M)
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBi : B ≤ (MulAut.conj : X →* MulAut X).range) {k : ℕ} (hk : Nat.card B = 3 ^ k)
    (hk4 : 4 ≤ k) (hM : CFSG.pRank 3 (M ⧸ Subgroup.center M) ≤ 3) : False :=
  false_of_rankInner (quotientCenterCongr e) hB hBi hk hk4 hM

theorem false_of_rankInnerCard {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBi : B ≤ (MulAut.conj : X →* MulAut X).range) {k : ℕ} (hk : Nat.card B = 3 ^ k)
    (hk4 : 4 ≤ k) (h : ¬ 3 ^ 4 ∣ Nat.card (X ⧸ Subgroup.center X)) : False :=
  false_of_rankInner (MulEquiv.refl _) hB hBi hk hk4 (pRank_three_le_of_not_dvd h)

end Bounds

section CaseA

theorem exists_psl2_three_of_alt47 (hin : Inputs413) {H : Type} [Group H] [Finite H]
    {L : Subgroup H} {a : H} (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (h : Alt47 L a) {B : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) {k : ℕ} (hk : Nat.card B = 3 ^ k) (hk4 : 4 ≤ k) :
    ∃ e : ℕ, 1 ≤ e ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 e)) := by
  have h2 : 2 ^ 2 = 4 := by norm_num
  rcases h with ⟨p, e, _, -, he, ⟨e₁⟩, -⟩ | ⟨p, e, _, hp3, he1, -, hX, -⟩ | ⟨hX, -⟩ |
      ⟨n, hn, hX, -⟩ | ⟨n, hn, hD4, -, -⟩
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨3 * e, by omega, ⟨e₁⟩⟩
    · exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 p (3 * e) hp3 (by omega))).elim
  ·
    exfalso
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    rcases hX with ⟨K, _, _, ⟨hK, -, ⟨e₁⟩⟩ | ⟨hK, -, ⟨e₁⟩⟩⟩ | ⟨-, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 p e K (by omega) hK)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 p e K (by omega) hK hq2)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 p e (by omega) he1)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 p e (by omega) he1 hq2)
  ·
    exfalso
    rcases hX with ⟨m, hm, ⟨⟨e₁⟩⟩ | ⟨K, _, _, hK, ⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨K, _, _, hK, ⟨e₁⟩⟩⟩ |
        ⟨n, hn, hSz | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | hG2 | hF4⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 2 m (by norm_num) hm)
    · rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        exact false_of_mulEquiv_statedSU_three_two hq hK e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 2 m K (by norm_num) hK
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)))
    · rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        exact false_of_mulEquiv_projSU_three_two hq e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 2 m (by norm_num) hm
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 2 (2 * m) K (by norm_num) hK)
    · have := CFSG.RankThree.PartTwo.KFacts.KP7.pRank_three_mulAut_le_one hSz
      exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (this.trans (by norm_num))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 2 n (by norm_num) hn.pos)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSp4 n hn.pos)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutG2 _ n hG2)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutF4 _ n hF4)
  ·
    exfalso
    rcases hX with ⟨K, _, _, ⟨hK, -, ⟨e₁⟩⟩ | ⟨hK, -, ⟨e₁⟩⟩⟩ | ⟨-, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 2 n K (by norm_num) hK)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_statedSU_three_two hq hK e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 2 n K (by norm_num) hK
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 2 n (by norm_num) hn)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_projSU_three_two hq e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 2 n (by norm_num) hn
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
  ·
    exact (false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutD4 _ n hD4)).elim

end CaseA

section CaseB

variable {X : Type} [Group X] [Finite X]

theorem card_alternatingGroup_dvd (n : ℕ) :
    Nat.card (alternatingGroup (Fin n)) ∣ n.factorial := by
  have h := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
  rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h

theorem not_dvd_card_alternatingGroup {n : ℕ} (hn : n ≤ 8) :
    ¬ 3 ^ 4 ∣ Nat.card (alternatingGroup (Fin n) ⧸ Subgroup.center (alternatingGroup (Fin n))) := by
  intro h
  have h1 := h.trans ((Subgroup.index_dvd_card _).trans (card_alternatingGroup_dvd n))
  have h2 : n.factorial ∣ Nat.factorial 8 := Nat.factorial_dvd_factorial hn
  have := h1.trans h2
  revert this
  decide

omit [Finite X] in
theorem le_center_of_normal_mulEquiv_zmod3 (hq : CFSG.IsQuasisimple X) {K : Subgroup X}
    (hK : K.Normal) (eK : K ≃* Multiplicative (ZMod 3)) : K ≤ Subgroup.center X := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hK with h | h
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hK3 : Nat.card K = 3 := by
      rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]
    have hX3 : Nat.card X = 3 := by
      rw [← Subgroup.card_top (G := X), ← h, hK3]
    have hcyc : IsCyclic X := isCyclic_of_prime_card hX3
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hcomm : ∀ x y : X, x * y = y * x := fun x y => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
      exact zpow_mul_comm g m n
    obtain ⟨a, b, hab⟩ := hq.2.2
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y => exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm])
  · exact h

theorem false_of_isExtOf_card {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple X)
    (h : IsExtOf X S (Multiplicative (ZMod 3))) (hS : ¬ 3 ^ 4 ∣ Nat.card S)
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBi : B ≤ (MulAut.conj : X →* MulAut X).range) {k : ℕ} (hk : Nat.card B = 3 ^ k)
    (hk4 : 4 ≤ k) : False := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  refine false_of_rankInnerCard hB hBi hk hk4 fun h3 => hS ?_
  rw [← Nat.card_congr eQ.toEquiv]
  exact h3.trans (card_quotient_center_dvd (le_center_of_normal_mulEquiv_zmod3 hq hK eK))

theorem isSpecial413_of_le_inner (hin : Inputs413)
    (hZspor : ∀ s ∈ sporadicCovers46,
      Subgroup.center (Blueprint.NativeSporadic.Carrier s) = ⊥)
    (hX : IsList46 X) (hq : CFSG.IsQuasisimple X) (hZodd : Odd (Nat.card (Subgroup.center X)))
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBi : B ≤ (MulAut.conj : X →* MulAut X).range) {k : ℕ} (hk : Nat.card B = 3 ^ k)
    (hk4 : 4 ≤ k) : IsSpecial413 X := by
  have hZ13 : Nat.card (Subgroup.center X) ≤ 3 → Nat.card (Subgroup.center X) = 1 ∨
      Nat.card (Subgroup.center X) = 3 := fun h => by
    obtain ⟨t, ht⟩ := hZodd
    omega
  rcases hX with ⟨p, e, _, -, he, ⟨e₁⟩⟩ | ⟨p, e, _, hp3, he1, -, hSL | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩⟩ |
      ⟨p, _, hp3, hG2 | ⟨⟨e₁⟩⟩ | ⟨hp1, ⟨e₁⟩⟩ | ⟨hp2, ⟨e₁⟩⟩⟩ |
      (⟨n, hn, ⟨e₁⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨e₁⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩) |
      ((⟨e, he1, he2, ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩⟩) | ⟨⟨e₁⟩⟩ | ⟨hZ3, hG23 | ⟨⟨e₁⟩⟩⟩)
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl ⟨e, he, ⟨e₁⟩⟩
    · exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 p e hp3 he)).elim
  ·
    exfalso
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := hSL
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 p e K (by omega) hK)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 p e K (by omega) hK hq2)
  ·
    exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 p e (by omega) he1)).elim
  ·
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    exact (false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 p e (by omega) he1 hq2)).elim
  ·
    exact (false_of_rankInner (MulEquiv.refl _) hB hBi hk hk4 (hin.rankG2 X p hp3 hG2)).elim
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankSp4 p hp3)).elim
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankU4 p hp3 hp1)).elim
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankL4 p hp3 hp2)).elim
  ·
    exfalso
    rcases Nat.lt_or_ge n 9 with hn8 | hn9
    · exact false_of_rankInnerModel e₁ hB hBi hk hk4
        (pRank_three_le_of_not_dvd (not_dvd_card_alternatingGroup (by omega)))
    · obtain rfl : n = 9 := by omega
      exact false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankA9
  ·
    refine (false_of_isExtOf_card hq hA6 ?_ hB hBi hk hk4).elim
    intro h
    have := h.trans (card_alternatingGroup_dvd 6)
    revert this
    decide
  ·
    refine (false_of_isExtOf_card hq hA7 ?_ hB hBi hk hk4).elim
    intro h
    have := h.trans (card_alternatingGroup_dvd 7)
    revert this
    decide
  ·
    by_cases hsM : s = .McL
    · subst hsM
      have hZ : Subgroup.center X = ⊥ :=
        center_eq_bot_of_mulEquiv e₁ (hZspor .McL (by simp [sporadicCovers46]))
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inr (Or.inl ⟨e₁⟩)⟩)))
    · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankSporadic s hs hsM)).elim
  ·
    have hs' := hs
    simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl
    · obtain ⟨-, ⟨eQ⟩⟩ := (isTripleCover_iff_isExtOf hq (hZspor _ hs)).mpr hext
      exact (false_of_rankInner (eQ.trans (quotientCenterEquivOfBot (hZspor _ hs)).symm) hB hBi
        hk hk4 (hin.rankSporadic .M22 (by simp [sporadics46]) (by decide))).elim
    · obtain ⟨-, ⟨eQ⟩⟩ := (isTripleCover_iff_isExtOf hq (hZspor _ hs)).mpr hext
      exact (false_of_rankInner (eQ.trans (quotientCenterEquivOfBot (hZspor _ hs)).symm) hB hBi
        hk hk4 (hin.rankSporadic .J3 (by simp [sporadics46]) (by decide))).elim
    · exact Or.inr (Or.inr (Or.inl (Or.inr hext)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hext))))
  ·
    exfalso
    rcases hchev with ⟨n, hn, ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩⟩ |
        ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL2 2 n (by norm_num) hn)
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutL3 2 n (by norm_num) hn)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_projSU_three_two hq e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutU3 2 n (by norm_num) hn
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSp4 n hn)
    · exact false_of_rankInnerModel e₁ hB hBi hk hk4 (hin.rankU4Even n hn)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutG2 _ f hG2)
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutD4 _ f hD4)
    · have := CFSG.RankThree.PartTwo.KFacts.KP7.pRank_three_mulAut_le_one hSz
      exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (this.trans (by norm_num))
    · exact false_of_rankAut (MulEquiv.refl _) hB hk hk4 (hin.rankAutF4 _ f hF4)
    · exact false_of_rankInner (MulEquiv.refl _) hB hBi hk hk4 (hin.rankTits _ f hTits)
  ·
    exfalso
    obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := hSL
    · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSL3 2 n K (by norm_num) hK)
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact false_of_mulEquiv_statedSU_three_two hq hK e₁
      · exact false_of_rankAut e₁ hB hk hk4 (hin.rankAutSU3 2 n K (by norm_num) hK
          (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)))
  ·
    exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankSeven.1).elim
  · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankSeven.2.1).elim
  · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankSeven.2.2).elim
  ·
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankEight.1).elim
    · exact Or.inr (Or.inl (Or.inl ⟨e₁⟩))
  ·
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · exact (false_of_rankInnerModel e₁ hB hBi hk hk4 hin.rankEight.2).elim
    · exact Or.inr (Or.inl (Or.inr ⟨e₁⟩))
  ·
    have := (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 3 1) (n := 4)
      (by norm_num) (Or.inl (by norm_num))).2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨center_eq_bot_of_mulEquiv_isSimpleGroup hq
      (e₁.trans (projSLEquivPSLn 4 _)), Or.inr (Or.inr (Or.inl ⟨e₁⟩))⟩)))
  ·
    rcases hZ13 hZ3 with h1 | h3
    · have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inl
        (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
          (quotientCenterEquivOfBot hZ).symm hG23)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨h3, hG23⟩))))
  ·
    rcases hZ13 hZ3 with h1 | h3
    · have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, Or.inr (Or.inr (Or.inr
        ⟨(quotientCenterEquivOfBot hZ).symm.trans e₁⟩))⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h3, ⟨e₁⟩⟩)))

end CaseB

end CFSG.RankThree.PartTwo.Sec4
