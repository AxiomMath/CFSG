module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGExcFiveFour
public import CFSG.LocalAnalysis.StandardType.GGExcPRankBound
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.LieType.SeitzGeneration.ExcTorusE7One
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8One
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Six
public import CFSG.LieType.SeitzGeneration.ExcTorusF4One
public import CFSG.LieType.SeitzGeneration.ExcTorusF4Two
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.ExcMaxToral
open CFSG.Open (IsElemAbelian)

private theorem ggPA1_isElemAbelian_torusPow
    (τ : Tag) (K : Type) [Field K] (p : ℕ) :
    IsElemAbelian p (TableBExc.torusPow τ K p) :=
  ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (mul_comm_of_mem_diagonalGroup
    (torusGroup_le_diagonalGroup a.2.1) (torusGroup_le_diagonalGroup b.2.1)))⟩⟩,
    fun _ hx => hx.2⟩

private theorem ggPA1_three_dvd_card_sub_one
    (K : Type) (hq : ∃ e, Nat.card K = 4 ^ e) :
    3 ∣ Nat.card K - 1 := by
  obtain ⟨e, he⟩ := hq
  rw [he]
  have hone : 1 ≤ 4 ^ e := Nat.succ_le_of_lt (pow_pos (by norm_num) e)
  have h0 : (((4 ^ e - 1 : ℕ)) : ZMod 3) = 0 := by
    rw [Nat.cast_sub hone, Nat.cast_one]
    have h4 : (((4 : ℕ) : ZMod 3)) = 1 := by decide
    rw [Nat.cast_pow, h4, one_pow, sub_self]
  exact (ZMod.natCast_eq_zero_iff (4 ^ e - 1) 3).mp h0

private theorem ggPA1_le_card_of_exists_elemAbelian
    {G : Type*} [Group G] {p : ℕ} (E : Subgroup G)
    (hmax : ∀ A : Subgroup G, IsElemAbelian p A → Nat.card A ≤ Nat.card E)
    (A : Subgroup G) (hA : IsElemAbelian p A) {k : ℕ} (hAcard : Nat.card A = p ^ k) :
    p ^ k ≤ Nat.card E := by
  rw [← hAcard]
  exact hmax A hA

private theorem ggPA1_four_le_excDegCount
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E) :
    4 ≤ excDegCount τ (orderOf (Nat.card K : ZMod p)) := by
  by_contra h
  have h3 : excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ 3 := by omega
  have hle := excPRankBound hτ K hp hp2 h3 E hE
  have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  exact not_lt_of_ge hle (lt_of_lt_of_le hlt h4)

private theorem ggPA1_three_pow_rank_le_card
    {τ : Tag} (K : Type) [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (adjointGroup τ K))
    (hmax : ∀ A : Subgroup (adjointGroup τ K), IsElemAbelian 3 A → Nat.card A ≤ Nat.card E)
    (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hq : ∃ e, Nat.card K = 4 ^ e) :
    3 ^ τ.rank ≤ Nat.card E := by
  have hpq3 : 3 ∣ Nat.card K - 1 := ggPA1_three_dvd_card_sub_one K hq
  rcases hτ with rfl | rfl | rfl
  · exact ggPA1_le_card_of_exists_elemAbelian E hmax (TableBExc.torusPow .E7 K 3)
      (ggPA1_isElemAbelian_torusPow .E7 K 3)
      (TableBExc.card_torusPow_E7 (p := 3) Nat.prime_three hpq3)
  · exact ggPA1_le_card_of_exists_elemAbelian E hmax (TableBExc.torusPow .E8 K 3)
      (ggPA1_isElemAbelian_torusPow .E8 K 3)
      (TableBExc.card_torusPow_E8 (p := 3) Nat.prime_three hpq3)
  · exact ggPA1_le_card_of_exists_elemAbelian E hmax (TableBF4.torusPow K 3)
      (show IsElemAbelian 3 (TableBF4.torusPow K 3) from
        ggPA1_isElemAbelian_torusPow .F4 K 3)
      (TableBF4.card_torusPow (K := K) (p := 3) Nat.prime_three hpq3)

private theorem ggPA1_pow_excDegCount_le_card
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hq : ∃ e, Nat.card K = 4 ^ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hmax : ∀ A : Subgroup (adjointGroup τ K), IsElemAbelian p A → Nat.card A ≤ Nat.card E) :
    p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ Nat.card E := by
  have hdeg := ggPA1_four_le_excDegCount hτ K hp hp2 E hE h4
  rcases excDegCount_ge_four (τ := τ) (d := orderOf (Nat.card K : ZMod p)) hdeg with
    ⟨hτ', hd, ha⟩ | ⟨hE8, hd, ha⟩
  · rw [ha]
    by_cases hp3 : p = 3
    · subst hp3
      exact ggPA1_three_pow_rank_le_card K E hmax hτ' hq
    · have hp3' : 3 < p := by
        have h2 : 2 ≤ p := hp.two_le
        omega
      rcases hτ' with rfl | rfl | rfl
      · rcases hd with hd1 | hd2
        · obtain ⟨A, hA, hAc⟩ :=
            CFSG.LieType.SeitzGeneration.exists_elemAbelian_E7_one K hp hp3' hd1
          exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
        · obtain ⟨A, hA, hAc⟩ :=
            CFSG.LieType.SeitzGeneration.exists_elemAbelian_E7_two K hp hp3' hd2
          exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
      · rcases hd with hd1 | hd2
        · obtain ⟨A, hA, hAc⟩ :=
            CFSG.LieType.SeitzGeneration.exists_elemAbelian_E8_one K hp hp3' hd1
          exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
        · obtain ⟨A, hA, hAc⟩ :=
            CFSG.LieType.SeitzGeneration.exists_elemAbelian_E8_two K hp hp3' hd2
          exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
      · rcases hd with hd1 | hd2
        · obtain ⟨A, hA, hAc⟩ :=
            CFSG.LieType.SeitzGeneration.exists_elemAbelian_F4_one K hp hp3' hd1
          exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
        · obtain ⟨A, hA, hAc⟩ :=
            CFSG.LieType.SeitzGeneration.exists_elemAbelian_F4_two K hp hp3' hd2
          exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
  · subst hE8
    rw [ha]
    rcases hd with hd3 | hd4 | hd6
    · obtain ⟨A, hA, hAc⟩ :=
        CFSG.LieType.SeitzGeneration.exists_elemAbelian_E8_three K hp hd3
      exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
    · obtain ⟨A, hA, hAc⟩ :=
        CFSG.LieType.SeitzGeneration.exists_elemAbelian_E8_four K hp hd4
      exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc
    · obtain ⟨A, hA, hAc⟩ :=
        CFSG.LieType.SeitzGeneration.exists_elemAbelian_E8_six K hp hd6
      exact ggPA1_le_card_of_exists_elemAbelian E hmax A hA hAc

theorem exists_langDatum_of_maxElem
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hq : ∃ e, Nat.card K = 4 ^ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hmax : ∀ A : Subgroup (adjointGroup τ K), IsElemAbelian p A → Nat.card A ≤ Nat.card E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (w : WeylGroup τ) (g0 : ModGL τ (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w),
      ∀ x ∈ E, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 ∈
        (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).torus := by
  have hdeg := ggPA1_four_le_excDegCount hτ K hp hp2 E hE h4
  have hcard := ggPA1_pow_excDegCount_le_card hτ K hq hp hp2 E hE h4 hmax
  obtain ⟨Fr, hFr, D, hΦ, _hqK, ⟨w, hwn, _hshape⟩, hmem, _hiff⟩ :=
    adjointMaxElemToral τ K p (inferInstance : Finite K) (inferInstance : CharP K 2)
      hp hp2 hdeg E hE hcard
  have hg0 : Units.map (entrywiseHom Fr) D.g0 =
      D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
    rw [← hΦ, ← hwn]
    exact D.lang
  have htorus : (LangDatum.ofFrobenius Fr (Nat.card K) hFr w D.g0_mem hg0).torus = D.torus := by
    change CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr)) = CFSG.RankThree.PartOne.KE.twistedTorusOf D.n D.Φ
    rw [hwn, hΦ]
  refine ⟨Fr, hFr, w, D.g0, D.g0_mem, hg0, ?_⟩
  intro x hx
  rw [htorus]
  exact hmem x hx

end CFSG.StandardType
