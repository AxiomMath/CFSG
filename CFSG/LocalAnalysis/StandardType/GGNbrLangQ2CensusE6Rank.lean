module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar
import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


private theorem q2cE6_card_le_pow_six_of_le_inner {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hA : IsElemAbelian p A)
    (hAinn : A ≤ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range) :
    Nat.card A ≤ p ^ 6 := by
  have hZ : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hconj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) :=
    CFSG.ComponentClassification.SmallLocal.mulAut_conj_injective hZ
  let A₀ : Subgroup (adjointGroup Tag.E6 K) := A.comap (MulAut.conj)
  have hA₀ : IsElemAbelian p A₀ := hA.comap hconj
  have hcard : Nat.card A₀ = Nat.card A := by
    have hmap : A₀.map (MulAut.conj) = A := Subgroup.map_comap_eq_self hAinn
    calc Nat.card A₀ = Nat.card (A₀.map (MulAut.conj)) :=
          (Subgroup.card_map_of_injective hconj).symm
      _ = Nat.card A := congrArg (fun H : Subgroup _ => Nat.card ↥H) hmap
  have hle : Nat.card A₀ ≤ p ^ 6 := by
    have hlen : (CFSG.LieType.SeitzGeneration.degreesW Tag.E6).length ≤ 6 := by decide
    have hdeg : CFSG.LieType.SeitzGeneration.degCount Tag.E6
        (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 6 := by
      unfold CFSG.LieType.SeitzGeneration.degCount
      exact (List.length_filter_le _ _).trans hlen
    have hb : Nat.card A₀ ≤ p ^ CFSG.LieType.SeitzGeneration.degCount Tag.E6
        (orderOf ((Nat.card K : ℕ) : ZMod p)) :=
      rankLE_E6 (K := K) (p := p) (e := orderOf ((Nat.card K : ℕ) : ZMod p)) hp hp2 rfl
        A₀ hA₀
    exact hb.trans (Nat.pow_le_pow_right hp.pos hdeg)
  rwa [← hcard]

private theorem q2cE6_card_le_pow_six_of_le_hatAut_of_ne_three
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    {A : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hA : IsElemAbelian p A)
    (hAI : A ≤ (TableBExc.E6Three.hatAut .E6 K).range) :
    Nat.card A ≤ p ^ 6 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAinn : A ≤
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range := by
    obtain ⟨Φ, -, hker, hdvd⟩ :=
      CFSG.LieType.Chevalley.exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
    let N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K)
    haveI : N.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    haveI : ((MulAut.conj : adjointGroup Tag.E6 K →*
        MulAut (adjointGroup Tag.E6 K)).range).Normal :=
      CFSG.StandardType.AutSt.normal_range_conj
    have hdet : Nat.card Φ.ker ∣ 3 := by
      have h := hdvd
      rwa [show Tag.E6.cartan.det.natAbs = 3 by
        rw [CFSG.LieType.Chevalley.det_cartan_E6]; rfl] at h
    have hmaple : A.map (QuotientGroup.mk' N) ≤ Φ.ker := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      have haz : a ∈ (TableBExc.E6Three.hatAut .E6 K).range := hAI ha
      rw [NoOffE6Three.hatAut_range_eq_sup] at haz
      obtain ⟨i, hi, d, ⟨p, rfl⟩, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := (MulAut.conj :
          adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range)).1 haz
      rw [hker]
      refine ⟨p, ?_⟩
      show QuotientGroup.mk' N (rootDiagAutHom .E6 K p) =
        QuotientGroup.mk' N (i * rootDiagAutHom .E6 K p)
      rw [map_mul]
      have hqi : (QuotientGroup.mk' N) i = 1 := (QuotientGroup.eq_one_iff i).2 hi
      rw [hqi, one_mul]
    have hcarddvd : Nat.card (A.map (QuotientGroup.mk' N)) ∣ 3 :=
      (Subgroup.card_dvd_of_le hmaple).trans hdet
    have hpt : IsPGroup p (A.map (QuotientGroup.mk' N)) := hA.isPGroup.map _
    have hbot : A.map (QuotientGroup.mk' N) = ⊥ := by
      refine Subgroup.card_eq_one.mp ?_
      obtain ⟨k, hk⟩ := hpt.exists_card_eq
      have hkdvd : p ^ k ∣ 3 := hk ▸ hcarddvd
      have hk0 : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact h
        · exfalso
          have hpk : p ^ k ≤ 3 := Nat.le_of_dvd (by norm_num) hkdvd
          have hp_le : p ≤ 3 := by
            calc p = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos h
              _ ≤ 3 := hpk
          have hp2le : 2 ≤ p := hp.two_le
          interval_cases p
          · exact absurd rfl hp2
          · exact absurd rfl hp3
      rw [hk, hk0]
      norm_num
    intro a ha
    have hmem : QuotientGroup.mk' N a ∈ A.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ ha
    rw [hbot] at hmem
    exact (QuotientGroup.eq_one_iff a).1 (Subgroup.mem_bot.1 hmem)
  exact q2cE6_card_le_pow_six_of_le_inner hp hp2 hA hAinn

private theorem q2cE6_card_le_pow_six_of_le_hatAut_of_not_dvd
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnd : ¬ 3 ∣ Nat.card K - 1)
    {A : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hA : IsElemAbelian p A)
    (hAI : A ≤ (TableBExc.E6Three.hatAut .E6 K).range) :
    Nat.card A ≤ p ^ 6 := by
  have hAinn : A ≤
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range := by
    have h1 : A ≤ (MulAut.conj :
        adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ⊔
        (rootDiagAutHom .E6 K).range := by
      rw [← NoOffE6Three.hatAut_range_eq_sup]
      exact hAI
    refine h1.trans (sup_le le_rfl ?_)
    rintro _ ⟨a, rfl⟩
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagAut_mem_innerAut_of_not_dvd
      K hnd a
  exact q2cE6_card_le_pow_six_of_le_inner hp hp2 hA hAinn

theorem q2c_E6_rank {p d : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .E6) (hp : p.Prime)
    (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d → (p = 3 ∧ d = 6) ∨ (p = 7 ∧ d = 7)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  haveI : Fact p.Prime := ⟨hp⟩
  intro Q hQ
  obtain ⟨K, hF, hFin, hKcard, hQ'⟩ := hQ
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, hF, hFin, hKcard, hQ', ?_⟩
  intro A hA hAI hbig hlo hup
  let e := TableBExc.recipeEquiv .E6 K
  let A' : Subgroup (MulAut (adjointGroup Tag.E6 K)) := A.map (MulAut.congr e).toMonoidHom
  have hA' : IsElemAbelian p A' :=
    CFSG.SectionRank.isElemAbelian_map hA (MulAut.congr e).toMonoidHom
  have hcardA' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hA'I : A' ≤ (TableBExc.E6Three.hatAut .E6 K).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact (E6ThreeModel.recipeID_iff_hatAut a).1 (hAI a ha)
  have hupper : Nat.card A ≤ p ^ 6 := by
    by_cases hd3 : 3 ∣ Nat.card K - 1
    · by_cases hp3 : p = 3
      · subst hp3
        exact (TableBExc.E6Three.card_le_and_normalizes_E6_three (K := K) hd3 hA hAI).1
      · have h6 := q2cE6_card_le_pow_six_of_le_hatAut_of_ne_three hp hp2 hp3 hA' hA'I
        rw [hcardA'] at h6
        exact h6
    · have h6 := q2cE6_card_le_pow_six_of_le_hatAut_of_not_dvd hp hp2 hd3 hA' hA'I
      rw [hcardA'] at h6
      exact h6
  have hsplt : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) :=
    (largeEvenSplit_E_iff (lab := (⟨.E6, l, n⟩ : LargeEvenLabel)) (Or.inl rfl)).mp hsplit
  rcases hsplt with hpq | ⟨hn1, hp3eq⟩
  · by_cases hp3 : p = 3
    · subst hp3
      have h3 : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
      have hlower : 3 ^ 5 ≤ Nat.card A :=
        hbig 5 (TableBExc.ggTorusLift_E6_three (K := K) h3)
      have hd_ge : 5 ≤ d :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlower.trans hup)
      have hd_le : d - 1 ≤ 6 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlo.trans hupper)
      have hd7 : d ≤ 7 := by omega
      left
      have hd_cases : d = 5 ∨ d = 6 ∨ d = 7 := by omega
      rcases hd_cases with rfl | rfl | rfl
      · exfalso; exact (by norm_num : ¬ (3 ∣ 5)) hpd
      · exact ⟨rfl, rfl⟩
      · exfalso; exact (by norm_num : ¬ (3 ∣ 7)) hpd
    · have hlower : p ^ 6 ≤ Nat.card A :=
        hbig 6 (TableBExc.ggTorusLift_E6 (K := K) hp hp2 hp3
          (by rw [hKcard]; exact hpq))
      have hd_ge : 6 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
      have hd_le : d - 1 ≤ 6 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hupper)
      have hd7 : d ≤ 7 := by omega
      right
      have hd_cases : d = 6 ∨ d = 7 := by omega
      rcases hd_cases with rfl | rfl
      · exfalso
        have h23 : p ∣ 2 * 3 := by
          rwa [show (6 : ℕ) = 2 * 3 by norm_num] at hpd
        rcases (Nat.Prime.dvd_mul hp).1 h23 with h | h
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
      · exact ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp hpd, rfl⟩
  · subst hn1
    subst hp3eq
    have hlower : 3 ^ 4 ≤ Nat.card A :=
      hbig 4 (TableBExc.E6Three.ggTorusLift_E6_two (K := K))
    have hd_ge : 4 ≤ d :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlower.trans hup)
    have hd_le : d - 1 ≤ 6 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlo.trans hupper)
    have hd7 : d ≤ 7 := by omega
    left
    have hd_cases : d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
    rcases hd_cases with rfl | rfl | rfl | rfl
    · exfalso; exact (by norm_num : ¬ (3 ∣ 4)) hpd
    · exfalso; exact (by norm_num : ¬ (3 ∣ 5)) hpd
    · exact ⟨rfl, rfl⟩
    · exfalso; exact (by norm_num : ¬ (3 ∣ 7)) hpd

end CFSG.StandardType
