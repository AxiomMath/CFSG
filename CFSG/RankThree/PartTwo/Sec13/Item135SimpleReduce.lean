module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (isoLThreePi_of_mulEquiv)
open scoped MatrixGroups

@[expose] def KS135TwoRank : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsPGroup 2 (Subgroup.center J) →
    (Nonempty (J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      ∃ f : ℕ, 1 ≤ f ∧ Sec4.IsoLThreePi (J ⧸ Subgroup.center J) 2 f) →
    3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup J)

section TypeFacts

variable {Y : Type} [Group Y]

theorem isSimpleGroup_of_isQuasisimple_center_eq_bot (hq : IsQuasisimple Y)
    (hZ : Subgroup.center Y = ⊥) : IsSimpleGroup Y := by
  have := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem exponent_dvd_three_of_isElemAbelian {E : Subgroup Y}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : Monoid.exponent E ∣ 3 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 x x.2)

theorem exists_exponent_dvd_three_card_nine_of_isHeisThree [Finite Y] {P : Subgroup Y}
    (hP : Sec4.IsHeisThree P) : ∃ E : Subgroup Y, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  obtain ⟨-, hcard, hexp⟩ := hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 3 (n := 2)
    (by rw [hcard]; norm_num)
  refine ⟨H.map P.subtype, ?_, ?_⟩
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, ⟨h, -, rfl⟩⟩
    apply Subtype.ext
    change (P.subtype h) ^ 3 = 1
    rw [← map_pow, ← hexp, Monoid.pow_exponent_eq_one, map_one]
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hH]
    norm_num

theorem le_mul_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    64 * (15 * 63) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h1 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 16 ≤ q ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))

theorem le_card_of_isoLThreePi {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi Y p e) (hq2 : 2 < p ^ e) : 20160 ≤ Nat.card Y := by
  have hq4 : 4 ≤ p ^ e := by
    rcases h with ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega
  have key := le_mul_of_four_le hq4
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hle : Nat.card Y * Nat.gcd 3 (p ^ e - 1) ≤ Nat.card Y * 3 := Nat.mul_le_mul_left _ hg
    omega
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hle : Nat.card Y * Nat.gcd 3 (p ^ e + 1) ≤ Nat.card Y * 3 := Nat.mul_le_mul_left _ hg
    have hmono : (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ≤
        (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    omega

theorem typeFacts135_isoLThreePi [Finite Y] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hq : IsQuasisimple Y) (h : Sec4.IsoLThreePi Y p e) :
    IsSimpleGroup Y ∧ Subgroup.center Y = ⊥ ∧ 20160 ≤ Nat.card Y ∧
      ∃ E : Subgroup Y, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 < p ^ e := by
    by_contra hle
    have h2 : p ^ e = 2 := by
      have : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp h2
    rcases h with ⟨h3, -⟩ | ⟨-, ⟨φ⟩⟩
    · norm_num at h3
    · have hs := isSolvable_projSU_two
      have hsY : Group.IsSolvable Y :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect Y := hq.1
      exact Group.IsPerfect.not_isSolvable Y hsY
  have hZ : Subgroup.center Y = ⊥ := by
    rcases h with ⟨h3, ⟨φ⟩⟩ | ⟨h3, ⟨φ⟩⟩
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he h3).2
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he h3 hq2).2
  refine ⟨isSimpleGroup_of_isQuasisimple_center_eq_bot hq hZ, hZ,
    le_card_of_isoLThreePi he h hq2, ?_⟩
  rcases h with ⟨h3, ⟨φ⟩⟩ | ⟨h3, ⟨φ⟩⟩
  · obtain ⟨D, hD, hD9⟩ := exists_elemAbelian_nine_projImage_slPi (piField_galoisField p e he)
      (show Sec4.ModThree true (p ^ e) from h3)
    let ψ : Y ≃* projImage (Sec4.slPi true 3 (p ^ e) (GaloisField p e)) :=
      φ.trans (MulEquiv.subgroupCongr (projSL_eq p e))
    exact ⟨D.map ψ.symm.toMonoidHom,
      exponent_dvd_three_of_isElemAbelian (isElemAbelian_map hD ψ.symm.toMonoidHom),
      by rw [Subgroup.card_map_of_injective ψ.symm.injective, hD9]⟩
  · obtain ⟨D, hD, hD9⟩ := exists_elemAbelian_nine_projImage_slPi
      (piField_galoisField_two p e he) (show Sec4.ModThree false (p ^ e) from h3)
    let ψ : Y ≃* projImage (Sec4.slPi false 3 (p ^ e) (GaloisField p (2 * e))) :=
      φ.trans (MulEquiv.subgroupCongr (projSU_eq p e))
    exact ⟨D.map ψ.symm.toMonoidHom,
      exponent_dvd_three_of_isElemAbelian (isElemAbelian_map hD ψ.symm.toMonoidHom),
      by rw [Subgroup.card_map_of_injective ψ.symm.injective, hD9]⟩

theorem typeFacts135 [Finite Y] (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    (h415 : Sec4.Item4_15) (hq : IsQuasisimple Y)
    (htype : IsLThreePi Y ∨ Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    IsSimpleGroup Y ∧ Subgroup.center Y = ⊥ ∧ 20160 ≤ Nat.card Y ∧
      ∃ E : Subgroup Y, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Y) := inferInstance
  rcases htype with ⟨p, e, hp, he, h⟩ | hM | hJ
  · exact typeFacts135_isoLThreePi he hq h
  · obtain ⟨φ⟩ := hM
    have hZ := center_eq_bot_of_mulEquiv φ hspor.2.1.2
    refine ⟨isSimpleGroup_of_isQuasisimple_center_eq_bot hq hZ, hZ, ?_,
      exists_exponent_dvd_three_card_nine_of_isHeisThree (h414 Y ⟨φ⟩ P).1⟩
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num
  · obtain ⟨φ⟩ := hJ
    have hZ := center_eq_bot_of_mulEquiv φ hspor.2.2.2
    refine ⟨isSimpleGroup_of_isQuasisimple_center_eq_bot hq hZ, hZ, ?_,
      exists_exponent_dvd_three_card_nine_of_isHeisThree (h415 Y ⟨φ⟩ P _ rfl _ rfl).1.1⟩
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num

end TypeFacts

section General

variable {X : Type} [Group X] [Finite X]

theorem false_of_surjective_of_card_lt [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K) {Y : Type*} [Group Y] (φ : X →* Y)
    (hφ : Function.Surjective φ) (hY1 : 1 < Nat.card Y) (hY : Nat.card Y < Nat.card (X ⧸ K)) :
    False := by
  have : Finite Y := Finite.of_surjective φ hφ
  by_cases hle : φ.ker ≤ K
  · have hdvd : K.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hle
    have hker : φ.ker.index = Nat.card Y := by
      rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    rw [hker] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    change Nat.card (X ⧸ K) ≤ Nat.card Y at this
    omega
  · have htop := Sec4.Census.eq_top_of_not_le hK hle
    have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp hY1
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨x, rfl⟩ := hφ y
    have hx : x ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hy (MonoidHom.mem_ker.mp hx)

theorem false_of_isExtOf_of_card_lt [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K) {M : Subgroup X} [M.Normal]
    {Y B : Type*} [Group Y] [Group B] (h : Sec4.IsExtOf (X ⧸ M) Y B) (hY1 : 1 < Nat.card Y)
    (hY : Nat.card Y < Nat.card (X ⧸ K)) : False := by
  obtain ⟨M', hM', -, ⟨e⟩⟩ := h
  exact false_of_surjective_of_card_lt hK
    (e.toMonoidHom.comp ((QuotientGroup.mk' M').comp (QuotientGroup.mk' M)))
    (e.surjective.comp ((QuotientGroup.mk'_surjective M').comp (QuotientGroup.mk'_surjective M)))
    hY1 hY

theorem false_of_oTwoP_equiv_SL2 [Group.IsPerfect X]
    {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (e3 : X ⧸ Sec4.oTwoP p X ≃* SL(2, ZMod p)) {E : Subgroup (X ⧸ K)}
    (hE : Monoid.exponent E ∣ 3) (hE9 : Nat.card E = 9) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : Sec4.oTwoP p X ≤ K :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance (Sec4.isSolvable_oTwoP p)
  set F : SL(2, ZMod p) →* X ⧸ K :=
    (QuotientGroup.map (Sec4.oTwoP p X) K (MonoidHom.id X) hle).comp e3.symm.toMonoidHom with hF
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    refine ⟨e3 (x : X ⧸ Sec4.oTwoP p X), ?_⟩
    rw [hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Sec4.false_of_surjective_of_isCyclic_sylow F hFs
    (Sec4.Census.isCyclic_sylow_SL2 (p := p) (by norm_num) (by omega)) hE hE9

omit [Finite X] in
theorem oddCore_le_of_isQuasisimple [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K)
    (hO : IsQuasisimple (X ⧸ CFSG.oddCore X)) : CFSG.oddCore X ≤ K := by
  by_contra h
  have htop := Sec4.Census.eq_top_of_not_le hK h
  exact (QuotientGroup.nontrivial_iff.mp (CFSG.LocalCores.isQuasisimple_nontrivial hO)) htop

omit [Finite X] in
theorem center_quotient_oddCore_eq_map {K : Subgroup X} [K.Normal] (hK : Group.IsSolvable K)
    (hZK : Subgroup.center (X ⧸ K) = ⊥) (hO : IsQuasisimple (X ⧸ CFSG.oddCore X))
    (hOK : CFSG.oddCore X ≤ K) :
    Subgroup.center (X ⧸ CFSG.oddCore X) = K.map (QuotientGroup.mk' (CFSG.oddCore X)) := by
  have hN : (K.map (QuotientGroup.mk' (CFSG.oddCore X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) z
    have hxc : QuotientGroup.mk' K x ∈ Subgroup.center (X ⧸ K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K y
      have h1 := Subgroup.mem_center_iff.mp hz (QuotientGroup.mk' (CFSG.oddCore X) y)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      exact hOK h1
    rw [hZK, Subgroup.mem_bot] at hxc
    exact ⟨x, (QuotientGroup.eq_one_iff x).mp hxc, rfl⟩
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hO hN with h | h
    · exfalso
      have hs : Group.IsSolvable (K.map (QuotientGroup.mk' (CFSG.oddCore X))) :=
        Group.isSolvable_of_surjective
          ((QuotientGroup.mk' (CFSG.oddCore X)).subgroupMap_surjective K)
      rw [h] at hs
      have hsol : Group.IsSolvable (X ⧸ CFSG.oddCore X) :=
        Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup (X ⧸ CFSG.oddCore X)) ≃* (X ⧸ CFSG.oddCore X)) :
            (⊤ : Subgroup (X ⧸ CFSG.oddCore X)) →* (X ⧸ CFSG.oddCore X)))
          Subgroup.topEquiv.surjective
      have : Nontrivial (X ⧸ CFSG.oddCore X) := CFSG.LocalCores.isQuasisimple_nontrivial hO
      have : Group.IsPerfect (X ⧸ CFSG.oddCore X) := hO.1
      exact Group.IsPerfect.not_isSolvable (X ⧸ CFSG.oddCore X) hsol
    · exact h

end General

end CFSG.RankThree.PartTwo.Sec13
