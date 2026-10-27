module

public import CFSG.Quasithin.Vol2.Ch11SecA02Recog2
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

structure RecogCtx (X Y : Type) [Group X] [Group Y] (n : ℕ) (f : X →* Y) : Prop where
  shape : ShapeData X n
  two_le : 2 ≤ n
  surj : Function.Surjective f
  ker_le : f.ker ≤ Subgroup.center X
  odd : Odd (Nat.card f.ker)

theorem card_eq_of_simple_quot {S Y : Type*} [Group S] [Group Y] [IsSimpleGroup S]
    (π : S →* Y) (hπ : Function.Surjective π) (hY : ∃ y : Y, y ≠ 1) :
    Nat.card Y = Nat.card S :=
  (Nat.card_congr (Equiv.ofBijective π ⟨injective_of_isSimpleGroup π hπ hY, hπ⟩)).symm

namespace RecogCtx

variable {X Y : Type} [Group X] [Group Y] {n : ℕ} {f : X →* Y}

theorem false_of_dvd (hc : RecogCtx X Y n f) {E O : ℕ} (hO : Odd O) (hE : E ≤ 5)
    (hY : Nat.card Y ∣ 2 ^ E * O) : False := by
  obtain ⟨e, o, he, ho, hYe⟩ := exists_two_pow_mul_odd_of_dvd hO hY
  exact recog_small hc.shape hc.two_le hc.surj hc.odd ho (he.trans hE) hYe

theorem exists_ne_one (hc : RecogCtx X Y n f) : ∃ y : Y, y ≠ 1 := by
  by_contra hne
  push Not at hne
  have h1 : Nat.card Y = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
  exact hc.false_of_dvd (E := 0) (O := 1) odd_one (by norm_num) (by rw [h1]; norm_num)

theorem false_of_ten (hc : RecogCtx X Y n f) {o : ℕ} (ho : Odd o)
    (hY : Nat.card Y = 2 ^ 10 * o) : False :=
  recog_ten hc.shape hc.two_le hc.surj hc.odd ho hY

theorem false_of_SL2 (hc : RecogCtx X Y n f) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (π : ↥(StatedSL 2 K) →* Y) (hπ : Function.Surjective π) :
    False := by
  have hcard : Nat.card ↥(StatedSL 2 K) = 2 ^ m * oSL2 m := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv, card_SL_two hK]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hdvd : Nat.card Y ∣ Nat.card ↥(StatedSL 2 K) := Subgroup.card_dvd_of_surjective hπ
    rw [hcard] at hdvd
    interval_cases m
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact hc.false_of_dvd (E := 1) (O := 3) (by decide) (by norm_num) hdvd
  · have := isSimpleGroup_statedSL (isSimpleGroup_SL_two hK hm)
    have hY := card_eq_of_simple_quot π hπ hc.exists_ne_one
    rw [hcard] at hY
    exact recog_SL2 hc.shape hc.two_le hc.surj hc.odd (by omega) hY

theorem false_of_SL_zmod_two (hc : RecogCtx X Y n f) (hL34 : FactL34) {d : ℕ}
    (hd : d = 4 ∨ d = 5) (π : ↥(StatedSL d (ZMod 2)) →* Y) (hπ : Function.Surjective π) :
    False := by
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :=
    isSimpleGroup_SL_zmod_two (by omega)
  set π' := π.comp (specialLinearGroupEquivStatedSL d (ZMod 2)).toMonoidHom
  have hπ' : Function.Surjective π' :=
    hπ.comp (specialLinearGroupEquivStatedSL d (ZMod 2)).surjective
  have hinj := injective_of_isSimpleGroup π' hπ' hc.exists_ne_one
  rcases hd with rfl | rfl
  · exact recog_SL42 hL34 hc.shape hc.two_le hc.surj hc.odd
      (MulEquiv.ofBijective π' ⟨hinj, hπ'⟩).symm
  · have hY := card_eq_of_simple_quot π' hπ' hc.exists_ne_one
    rw [card_SL_five_two] at hY
    exact hc.false_of_ten (by decide) hY

theorem false_of_alt (hc : RecogCtx X Y n f) {k : ℕ} (hk : k = 5 ∨ k = 6 ∨ k = 7)
    (e : Y ≃* alternatingGroup (Fin k)) : False := by
  have hY : Nat.card Y = (Nat.card (Fin k)).factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
    exact nat_card_alternatingGroup
  rw [Nat.card_fin] at hY
  rcases hk with rfl | rfl | rfl
  · exact hc.false_of_dvd (E := 2) (O := 15) (by decide) (by norm_num) (by rw [hY]; decide)
  · exact hc.false_of_dvd (E := 3) (O := 45) (by decide) (by norm_num) (by rw [hY]; decide)
  · exact hc.false_of_dvd (E := 3) (O := 315) (by decide) (by norm_num) (by rw [hY]; decide)

end RecogCtx

end CFSG.Quasithin.Vol2.Ch11.SecA
