module

public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.Quasithin.H13.NQCatG24X3

public section

namespace CFSG.Quasithin.H13.NQCat.G2Rad

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.LieType.BorelTits

section Transport

variable {Y X : Type*} [Group Y] [Group X] {ι : Y →* X}

theorem centerOf_eq_map_center (A : Subgroup Y) :
    centerOf A = (Subgroup.center ↥A).map A.subtype := by
  ext z
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 hc g g.2
  · rintro ⟨z', hz', rfl⟩
    refine ⟨z'.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨y, hy⟩)

theorem map_centerOf (hι : Function.Injective ι) (A : Subgroup Y) :
    (centerOf A).map ι = centerOf (A.map ι) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyC⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem ι hyA, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hyC a ha]
  · rintro ⟨⟨y, hyA, rfl⟩, hxC⟩
    refine ⟨y, ⟨hyA, Subgroup.mem_centralizer_iff.2 fun a ha => hι ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hxC _ (Subgroup.mem_map_of_mem ι ha)

theorem le_centralizer_of_map (hι : Function.Injective ι) {A B : Subgroup Y}
    (h : A.map ι ≤ Subgroup.centralizer (B.map ι : Set X)) :
    A ≤ Subgroup.centralizer (B : Set Y) := fun y hy =>
  Subgroup.mem_centralizer_iff.2 fun b hb => hι (by
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_map_of_mem ι hy)) _
      (Subgroup.mem_map_of_mem ι hb))

theorem map_le_normalizer_map {A W : Subgroup Y}
    (h : A ≤ Subgroup.normalizer (W : Set Y)) :
    A.map ι ≤ Subgroup.normalizer (W.map ι : Set X) :=
  (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map ι)

theorem card_center_eq (hι : Function.Injective ι) (A : Subgroup Y) :
    Nat.card (Subgroup.center ↥A) = Nat.card (centerOf (A.map ι)) := by
  rw [centerOf_eq_map_center, Subgroup.card_map_of_injective (A.map ι).subtype_injective]
  exact Nat.card_congr (Subgroup.centerCongr (A.equivMapOfInjective ι hι)).toEquiv

end Transport

section Amalgam

theorem exists_model
    {Y : Type} [Group Y] {n : ℕ} (hY : IsLieOverTwo .G2 0 n Y) {T M₁ M : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M)
    (hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 (perfectCore M))) = 2 ^ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ ι : Y →* ModGL Tag.G2 K, Function.Injective ι ∧
        (perfectCore M).map ι = perfectCore (parabolicSubgroup Tag.G2 K {i1}) ∧
        (pCoreOf 2 (perfectCore M)).map ι = parabolicRadical Tag.G2 K {i1} := by
  have hYm : ChevalleyExceptionalModel Y .G2 2 n := by
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  have hn : 2 ≤ n := (exists_mulEquiv_G2_model hYm).1
  obtain ⟨K, _, _, _, hK, θ, i, rfl⟩ := G24X3.exists_eq_parabolic_g2 hYm hpair
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : Finite Y := Finite.of_equiv _ θ.toEquiv
  let ι : Y →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp θ.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (adjointGroup Tag.G2 K).subtype_injective.comp θ.symm.injective
  have hM : (((parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)).map
      θ.toMonoidHom).map ι = parabolicSubgroup Tag.G2 K {i} := by
    rw [Subgroup.map_map]
    have e : ι.comp θ.toMonoidHom = (adjointGroup Tag.G2 K).subtype := by
      ext x
      simp [ι]
    rw [e, Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup _ _ _)]
  have hK' : (perfectCore (((parabolicSubgroup Tag.G2 K {i}).subgroupOf
      (adjointGroup Tag.G2 K)).map θ.toMonoidHom)).map ι =
      perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
    rw [map_perfectCore, hM]
  have hO : (pCoreOf 2 (perfectCore (((parabolicSubgroup Tag.G2 K {i}).subgroupOf
      (adjointGroup Tag.G2 K)).map θ.toMonoidHom))).map ι = parabolicRadical Tag.G2 K {i} := by
    rw [← G24X3.pCoreOf_map_of_inj ι hι, hK', pCoreOf_perfectCore_parabolic hK hn i]
  have hi : i = i1 := by
    rcases G2.fin_two_cases i with rfl | rfl
    · exfalso
      have h1 := card_center_eq hι (pCoreOf 2 (perfectCore (((parabolicSubgroup Tag.G2 K
        {i0}).subgroupOf (adjointGroup Tag.G2 K)).map θ.toMonoidHom)))
      rw [hO, hZ] at h1
      have h2 := card_le_card_centerOf_zero (K := K)
      rw [← h1, hK] at h2
      have h3 : 2 ^ n < 2 ^ n * 2 ^ n := by
        have : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
      omega
    · rfl
  subst hi
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, ι, hι, hK', hO⟩

theorem factG24ParabolicCenter_holds :
    FactG24ParabolicCenter := by
  intro Y _ T M₁ M hY hpair hsp
  obtain ⟨K, _, _, _, hK, ι, hι, hK', hO⟩ := exists_model hY hpair hsp.2.2
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hZ : (centerOf (pCoreOf 2 (perfectCore M))).map ι = N1 := by
    rw [map_centerOf hι, hO, centerOf_parabolicRadical_one]
  refine ⟨le_centralizer_of_map hι ?_, fun R hRQ hKR _ => ?_⟩
  · rw [hK', hZ]
    exact perfectCore_le_centralizer
  · rw [← Subgroup.map_le_map_iff_of_injective hι, map_centerOf hι, hZ]
    refine centerOf_le_of_le_normalizer hK4 ?_ ?_
    · rw [← hO]
      exact Subgroup.map_mono hRQ
    · rw [← hK']
      exact map_le_normalizer_map hKR

theorem g2ParabolicIrred
    {Y : Type} [Group Y] {n : ℕ} {T M₁ M : Subgroup Y} (hn : 3 ≤ n)
    (hY : IsLieOverTwo .G2 0 n Y) (hsp : IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 (perfectCore M)))
    (hpair : IsYAmalgamPair T M₁ M) :
    perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y) ∧
      ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
        W ≤ pCoreOf 2 (perfectCore M) → perfectCore M ≤ Subgroup.normalizer (W : Set Y) →
          W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M) := by
  obtain ⟨K, _, _, _, hK, ι, hι, hK', hO⟩ := exists_model hY hpair hsp.2.2
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZ : (centerOf (pCoreOf 2 (perfectCore M))).map ι = N1 := by
    rw [map_centerOf hι, hO, centerOf_parabolicRadical_one]
  refine ⟨le_centralizer_of_map hι ?_, fun W hZW hWQ hKW => ?_⟩
  · rw [hK', hZ]
    exact perfectCore_le_centralizer
  · have h := eq_or_eq_of_le_normalizer h8 (W := W.map ι) (hZ ▸ Subgroup.map_mono hZW)
      (hO ▸ Subgroup.map_mono hWQ) (hK' ▸ map_le_normalizer_map hKW)
    rcases h with h | h
    · exact Or.inl (Subgroup.map_injective hι (h.trans hZ.symm))
    · exact Or.inr (Subgroup.map_injective hι (h.trans hO.symm))

end Amalgam

end CFSG.Quasithin.H13.NQCat.G2Rad
