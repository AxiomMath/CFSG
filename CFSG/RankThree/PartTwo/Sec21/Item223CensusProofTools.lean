module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofInner
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

structure Config223 (Y : Type) [Group Y] (E D : Subgroup (MulAut Y)) (Kb : Subgroup Y) (m : ℕ) :
    Prop where
  elemAbelian : CFSG.Assembly.IsElemAbelian 3 E
  card_E : Nat.card E = 3 ^ 3
  le_inner : E ≤ (MulAut.conj : Y →* MulAut Y).range
  le_E : D ≤ E
  card_D : 3 ^ 2 ≤ Nat.card D
  fix : ∀ d ∈ D, ∀ k ∈ Kb, d k = k
  normalizes : ∀ y : Y, (∀ d ∈ D, d y = y) → ∀ k ∈ Kb, y * k * y⁻¹ ∈ Kb
  equiv : Nonempty (Kb ≃* projSL 2 (GaloisField 2 m))
  one_lt : 1 < m
  odd : Odd m

@[expose] def NoL2Inner223 (S : Type) [Group S] : Prop :=
  ∀ (Kb : Subgroup S) (m : ℕ) (a : S), Nonempty (Kb ≃* projSL 2 (GaloisField 2 m)) → 1 < m →
    Odd m → a ∉ Subgroup.center S → a ^ 3 ∈ Subgroup.center S → ¬ ∀ k ∈ Kb, a * k = k * a

theorem innerCensus223_of_config
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (E D : Subgroup (MulAut Y)) (Kb : Subgroup Y)
      (m : ℕ), Sec4.IsList46 Y → Config223 Y E D Kb m →
        ∃ k : ℕ, Odd k ∧ Nonempty (Y ≃* projSU 4 2 k)) : InnerCensus223 := by
  intro Y _ _ E D Kb m hL hE hE27 hEi hDE hD9 hfix hnorm hK hm1 hmo
  exact h Y E D Kb m hL ⟨hE, hE27, hEi, hDE, hD9, hfix, hnorm, hK, hm1, hmo⟩

namespace Item223CensusProof

theorem isElemAbelian_of_isElementaryAbelian {X : Type*} [Group X] {B : Subgroup X}
    (hB : CFSG.IsElementaryAbelian 3 B) : CFSG.Assembly.IsElemAbelian 3 B := by
  refine ⟨hB.toIsMulCommutative, fun x hx => ?_⟩
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩
  simpa using congrArg Subtype.val h

theorem pRank_le_two_of_card_le_nine {S : Type*} [Group S]
    (hS : ∀ F : Subgroup S, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9) :
    CFSG.pRank 3 S ≤ 2 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  have h9 := hS B (isElemAbelian_of_isElementaryAbelian hB)
  rw [hr] at h9
  by_contra hr2
  have : 3 ^ 3 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Item223CensusProof

open Item223CensusProof

namespace Config223

variable {Y : Type} [Group Y] {E D : Subgroup (MulAut Y)} {Kb : Subgroup Y} {m : ℕ}

theorem false_of_hom (h : Config223 Y E D Kb m) {M : Type*} [Group M]
    (φ : MulAut Y →* MulAut M) (hφ : Function.Injective φ)
    (hinn : ∀ y : Y, φ (MulAut.conj y) ∈ (MulAut.conj : M →* MulAut M).range)
    (hM : ∀ F : Subgroup (MulAut M), CFSG.Assembly.IsElemAbelian 3 F →
      F ≤ (MulAut.conj : M →* MulAut M).range → Nat.card F ≤ 9) : False := by
  have h1 := hM (E.map φ) (Sec4.isElemAbelian_map φ h.elemAbelian) (by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨y, rfl⟩ := h.le_inner hσ
    exact hinn y)
  rw [Subgroup.card_map_of_injective hφ, h.card_E] at h1
  norm_num at h1

theorem false_of_mulEquiv (h : Config223 Y E D Kb m) {M : Type*} [Group M]
    (e : Y ≃* M)
    (hM : ∀ F : Subgroup (MulAut M), CFSG.Assembly.IsElemAbelian 3 F →
      F ≤ (MulAut.conj : M →* MulAut M).range → Nat.card F ≤ 9) : False :=
  h.false_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    (fun y => ⟨e y, (KFacts.congr_mulAutConj e y).symm⟩) hM

theorem false_of_pRank (h : Config223 Y E D Kb m) {S : Type*} [Group S] [Finite S]
    (e : Y ⧸ Subgroup.center Y ≃* S) (hS : CFSG.pRank 3 S ≤ 2) : False := by
  have := Sec4.le_pRank_of_le_inner e h.elemAbelian h.le_inner h.card_E
  omega

theorem false_of_not_dvd (h : Config223 Y E D Kb m)
    (hY : ¬ 3 ^ 3 ∣ Nat.card (Y ⧸ Subgroup.center Y)) : False := by
  apply hY
  rw [← h.card_E, Nat.card_congr (Sec4.innerEquivQuotientCenter Y).toEquiv]
  exact Subgroup.card_dvd_of_le h.le_inner

theorem false_of_not_dvd_card [Finite Y] (h : Config223 Y E D Kb m) {S : Type*}
    [Group S] (e : Y ≃* S) (hS : ¬ 3 ^ 3 ∣ Nat.card S) : False := by
  refine h.false_of_not_dvd fun h3 => hS ?_
  rw [← Nat.card_congr e.toEquiv]
  exact h3.trans (Subgroup.index_dvd_card _)

theorem two_pow_sub_one_dvd [Finite Y] (h : Config223 Y E D Kb m) :
    2 ^ m - 1 ∣ Nat.card Y := by
  obtain ⟨eK⟩ := h.equiv
  have hcard : Nat.card Kb = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two m (by have := h.one_lt; omega)]
  have h1 : 2 ^ m - 1 ∣ (2 ^ m) ^ 2 - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (x := 2 ^ m) (y := 1) (n := 2)
  exact (h1.trans (Dvd.intro_left _ hcard.symm)).trans (Subgroup.card_subgroup_dvd_card Kb)

theorem false_of_card_dvd [Finite Y] (h : Config223 Y E D Kb m) {N b : ℕ}
    (hN : Nat.card Y ∣ N) (hN0 : 0 < N) (hb : N < 2 ^ b - 1)
    (hcheck : ∀ m < b, 1 < m → Odd m → ¬ 2 ^ m - 1 ∣ N) : False := by
  have hdvd := h.two_pow_sub_one_dvd.trans hN
  by_cases hmb : m < b
  · exact hcheck m hmb h.one_lt h.odd hdvd
  · have h1 : 2 ^ b ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.le_of_dvd hN0 hdvd
    omega

theorem exists_inner_three (h : Config223 Y E D Kb m) :
    ∃ a : Y, a ∉ Subgroup.center Y ∧ a ^ 3 ∈ Subgroup.center Y ∧ ∀ k ∈ Kb, a * k = k * a := by
  have hD1 : D ≠ ⊥ := fun hD => by
    have := h.card_D
    rw [hD, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨⟨d, hdD⟩, hd1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
  have hd1 : d ≠ 1 := fun h1 => hd1' (Subtype.ext h1)
  obtain ⟨a, rfl⟩ := h.le_inner (h.le_E hdD)
  refine ⟨a, fun ha => hd1 ?_, ?_, fun k hk => ?_⟩
  · rw [← Sec4.ker_conj_eq_center, MonoidHom.mem_ker] at ha
    exact ha
  · rw [← Sec4.ker_conj_eq_center, MonoidHom.mem_ker, map_pow]
    exact h.elemAbelian.2 _ (h.le_E hdD)
  · have h1 : a * k * a⁻¹ = k := h.fix _ hdD k hk
    calc a * k = a * k * a⁻¹ * a := by group
      _ = k * a := by rw [h1]

theorem false_of_noL2Inner (h : Config223 Y E D Kb m) {S : Type} [Group S] (e : Y ≃* S)
    (hS : NoL2Inner223 S) : False := by
  obtain ⟨a, haZ, ha3, hak⟩ := h.exists_inner_three
  obtain ⟨eK⟩ := h.equiv
  have hZ := Sec4.map_center_mulEquiv e
  have hmemZ : ∀ y : Y, e y ∈ Subgroup.center S ↔ y ∈ Subgroup.center Y := fun y => by
    rw [← hZ]
    exact ⟨fun ⟨z, hz, hzy⟩ => (e.injective hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩
  refine hS (Kb.map e.toMonoidHom) m (e a)
    ⟨(Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK⟩ h.one_lt h.odd
    (fun h1 => haZ ((hmemZ a).mp h1)) (by rw [← map_pow]; exact (hmemZ _).mpr ha3) ?_
  rintro _ ⟨k, hk, rfl⟩
  change e a * e k = e k * e a
  rw [← map_mul, ← map_mul, hak k hk]

end Config223

end CFSG.RankThree.PartTwo.Sec21
