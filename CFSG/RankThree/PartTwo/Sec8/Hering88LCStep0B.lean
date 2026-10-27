module

public import CFSG.RankThree.PartTwo.Sec8.Hering88LCStep0A
public import CFSG.RankThree.PartTwo.Sec8.Hering88LCInner
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp projSU projImage)
open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open Hering88N
open Matrix
open scoped MatrixGroups

section General

variable {Q M : Type*} [Group Q] [Group M]

@[expose] def CentExp (Q : Type*) [Group Q] (j : ℕ) : Prop :=
  ∀ g : Q, g ^ 3 = 1 → g ≠ 1 → ∀ P : Subgroup Q, Group.IsPerfect P →
    P ≤ Subgroup.centralizer ({g} : Set Q) → ∀ t ∈ P, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ j = 1

@[expose] def CentFive (Q : Type*) [Group Q] : Prop :=
  ∀ g : Q, g ^ 3 = 1 → g ≠ 1 → ∀ P : Subgroup Q, Group.IsPerfect P →
    P ≤ Subgroup.centralizer ({g} : Set Q) → ¬ 5 ∣ Nat.card P

theorem map_le_centralizer (e : Q ≃* M) {g : Q} {P : Subgroup Q}
    (hP : P ≤ Subgroup.centralizer ({g} : Set Q)) :
    P.map e.toMonoidHom ≤ Subgroup.centralizer ({e g} : Set M) := by
  rintro _ ⟨p, hp, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  change e p * e g = e g * e p
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hP hp)]

theorem CentExp.of_mulEquiv (e : Q ≃* M) {j : ℕ} (h : CentExp M j) : CentExp Q j := by
  intro g hg3 hg1 P hP hPg t ht ht2
  obtain ⟨k, hk⟩ := ht2
  have h1 := h (e g) (by rw [← map_pow, hg3, map_one])
    (fun h1 => hg1 (e.injective (h1.trans (map_one e).symm))) (P.map e.toMonoidHom)
    (Hering88N.isPerfect_map _ hP) (map_le_centralizer e hPg) (e t) ⟨t, ht, rfl⟩
    ⟨k, by rw [← map_pow, hk, map_one]⟩
  exact e.injective (by rw [map_pow, h1, map_one])

theorem CentFive.of_mulEquiv (e : Q ≃* M) (h : CentFive M) : CentFive Q := by
  intro g hg3 hg1 P hP hPg h5
  apply h (e g) (by rw [← map_pow, hg3, map_one])
    (fun h1 => hg1 (e.injective (h1.trans (map_one e).symm))) (P.map e.toMonoidHom)
    (Hering88N.isPerfect_map _ hP) (map_le_centralizer e hPg)
  rwa [Subgroup.card_map_of_injective e.injective]

theorem centFive_of_not_dvd [Finite Q] (h5 : ¬ 5 ∣ Nat.card Q) : CentFive Q :=
  fun _ _ _ P _ _ hP5 => h5 (hP5.trans (Subgroup.card_subgroup_dvd_card P))

end General

section Sp4

variable {F : Type} [Field F] [Finite F] [CharP F 2]


theorem exists_sl2_of_perfect_le_centralizer (hF4 : 4 ≤ Nat.card F)
    {g : StatedProj (StatedSp 2 F)} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {P : Subgroup (StatedProj (StatedSp 2 F))} (hP : Group.IsPerfect P)
    (hPg : P ≤ Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 F)))) :
    P ≤ inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 F)))) ∧
      Nonempty (inSubgroup perfectResidual
        (Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 F)))) ≃* SL(2, F)) :=
  ⟨Sec18.le_inSubgroup_perfectResidual (Subgroup.isPerfect_iff.mp hP) hPg,
    Item84KFacts4.kF84Sp4ThreeCent_holds F hF4 g (orderOf_eq_prime hg3 hg1)⟩

theorem centExp_sp4 (hF4 : 4 ≤ Nat.card F) : CentExp (StatedProj (StatedSp 2 F)) 1 := by
  intro g hg3 hg1 P hP hPg t ht ht2
  obtain ⟨hPR, ⟨ι⟩⟩ := exists_sl2_of_perfect_le_centralizer hF4 hg3 hg1 hP hPg
  obtain ⟨k, hk⟩ := ht2
  set t' : inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set _)) := ⟨t, hPR ht⟩
  have hk' : t' ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  have h2 : ι t' ^ 2 = 1 :=
    Hering88N.sl2_pow_two_eq_one _ ⟨k, by rw [← map_pow, hk', map_one]⟩
  have h2' : t' ^ 2 = 1 := ι.injective (by rw [map_pow, h2, map_one])
  have := congrArg Subtype.val h2'
  rw [Subgroup.coe_pow] at this
  rwa [pow_one]

theorem centFive_sp4 {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : Odd f) (hF4 : 4 ≤ Nat.card F) :
    CentFive (StatedProj (StatedSp 2 F)) := by
  intro g hg3 hg1 P hP hPg h5
  obtain ⟨hPR, ⟨ι⟩⟩ := exists_sl2_of_perfect_le_centralizer hF4 hg3 hg1 hP hPg
  have hdvd : Nat.card P ∣ Nat.card SL(2, F) := by
    rw [← Nat.card_congr ι.toEquiv]
    exact Subgroup.card_dvd_of_le hPR
  exact five_not_dvd_card_sl2 hF hf (h5.trans hdvd)

end Sp4

section Ree


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem centExp_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CentExp (ReeTag.F4.reeGamma K a) 2 := by
  intro g hg3 hg1 P _ hPg t ht ht2
  obtain ⟨e⟩ := Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK g (orderOf_eq_prime hg3 hg1)
  obtain ⟨k, hk⟩ := ht2
  set t' : Subgroup.centralizer ({g} : Set (ReeTag.F4.reeGamma K a)) := ⟨t, hPg ht⟩
  have hk' : t' ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  have h4 : ((e t' : _) : GL (Fin 3) (GaloisField 2 (2 * (2 * a + 1)))) ^ 4 = 1 :=
    Hering88N.gl3_pow_four_eq_one _ ⟨k, by rw [← Subgroup.coe_pow, ← map_pow, hk', map_one]; rfl⟩
  have h4' : t' ^ 4 = 1 := e.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4))
  have := congrArg Subtype.val h4'
  rw [Subgroup.coe_pow] at this
  simpa using this

theorem centFive_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CentFive (ReeTag.F4.reeGamma K a) := by
  intro g hg3 hg1 P _ hPg h5
  obtain ⟨e⟩ := Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK g (orderOf_eq_prime hg3 hg1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (2 * a + 1)
      (GaloisField 2 (2 * (2 * a + 1))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  have hC : Nat.card (Subgroup.centralizer ({g} : Set (ReeTag.F4.reeGamma K a))) =
      (2 ^ (2 * a + 1)) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2 - 1) * ((2 ^ (2 * a + 1)) ^ 3 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.card_unitarySU_three hU
  apply five_not_dvd_su3 (f := 2 * a + 1) (by exact odd_two_mul_add_one a)
  rw [← hC]
  exact h5.trans (Subgroup.card_dvd_of_le hPg)

end Ree

section Case1


theorem centExp_case1 {Q : Type} [Group Q] [Finite Q] {m : ℕ} (hodd : Odd m)
    (hQ : IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) : CentExp Q 2 :=
  fun _ hg3 hg1 _ hP hPg _ ht ht2 => by
    simpa using Hering88N.lemmaB hodd hQ hg3 hg1 hP hPg ht ht2

theorem centFive_case1 {Q : Type} [Group Q] [Finite Q] {m : ℕ} (hodd : Odd m)
    (hQ : IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) : CentFive Q :=
  centFive_of_not_dvd (Hering88N.five_not_dvd_card_of_case1 hodd hQ)

end Case1

section Exclusion

variable {G : Type} [Group G] [Finite G]

theorem exists_inner_setup {Y W : Subgroup G} {w : G}
    (hZ : ∀ z : Y ⧸ aschbacherSolvableCore 3 Y, (∀ y, z * y = y * z) → z = 1)
    (hwN : w ∈ Subgroup.normalizer (Y : Set G)) (hw3 : w ^ 3 = 1) (hWY : W ≤ Y)
    (hWw : W ≤ Subgroup.centralizer ({w} : Set G)) (hWp : Group.IsPerfect W)
    (hin : KFacts.IsInnerAut (barAut Y w hwN)) (hne : barAut Y w hwN ≠ 1) :
    ∃ g : Y ⧸ aschbacherSolvableCore 3 Y, g ^ 3 = 1 ∧ g ≠ 1 ∧
      imageModTheta Y W ≤ Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) ∧
      Group.IsPerfect (imageModTheta Y W) := by
  obtain ⟨g, hg⟩ := hin
  have hg3 : g ^ 3 = 1 := eq_of_conj_eq hZ (by rw [map_pow, hg, barAut_pow_three hwN hw3, map_one])
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hne
    rw [← hg]
    exact map_one _
  have hπ : imageModTheta Y W ≤ barCentralizer (Subgroup.zpowers w) Y := by
    rw [← KFacts.imageModTheta_centralizer_eq hwN ⟨1, by simpa using hw3⟩]
    exact Hering88F.imageModTheta_mono' (le_inf hWY hWw)
  refine ⟨g, hg3, hg1, ?_, hWp.ofSurjective (f := Item87Proof.modThetaOnto hWY)
    (Item87Proof.modThetaOnto_surjective hWY)⟩
  rw [← barCentralizer_eq_centralizer hwN hg.symm]
  exact hπ

theorem barAut_eq_one_of_centExp {Y W : Subgroup G} {w : G} {j : ℕ}
    (hZ : ∀ z : Y ⧸ aschbacherSolvableCore 3 Y, (∀ y, z * y = y * z) → z = 1)
    (hexp : CentExp (Y ⧸ aschbacherSolvableCore 3 Y) j)
    (hwN : w ∈ Subgroup.normalizer (Y : Set G)) (hw3 : w ^ 3 = 1) (hWY : W ≤ Y)
    (hWw : W ≤ Subgroup.centralizer ({w} : Set G)) (hWp : Group.IsPerfect W)
    (hs : ∃ s : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 2 ^ j ≠ 1)
    (hin : KFacts.IsInnerAut (barAut Y w hwN)) : barAut Y w hwN = 1 := by
  by_contra hne
  obtain ⟨g, hg3, hg1, hπg, hWbar⟩ := exists_inner_setup hZ hwN hw3 hWY hWw hWp hin hne
  have hB : ∀ t : imageModTheta Y W, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ j = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := ht
    have h := hexp g hg3 hg1 _ hWbar hπg t t.2 ⟨k, by rw [← Subgroup.coe_pow, hk]; rfl⟩
    exact Subtype.ext (by rw [Subgroup.coe_pow]; simpa using h)
  obtain ⟨f, hf⟩ := exists_surjective_imageModTheta_quot hWY
  obtain ⟨s, hs2, hsj⟩ := hs
  have hmem : s ∈ f.range := by
    rw [MonoidHom.range_eq_top.mpr hf]
    exact Subgroup.mem_top s
  exact hsj (pow_two_pow_eq_one_of_mem_range f hB hmem hs2)

theorem barAut_eq_one_of_centFive {Y W : Subgroup G} {w : G}
    (hZ : ∀ z : Y ⧸ aschbacherSolvableCore 3 Y, (∀ y, z * y = y * z) → z = 1)
    (hfive : CentFive (Y ⧸ aschbacherSolvableCore 3 Y))
    (hwN : w ∈ Subgroup.normalizer (Y : Set G)) (hw3 : w ^ 3 = 1) (hWY : W ≤ Y)
    (hWw : W ≤ Subgroup.centralizer ({w} : Set G)) (hWp : Group.IsPerfect W)
    (h5 : 5 ∣ Nat.card (W ⧸ aschbacherSolvableCore 3 W))
    (hin : KFacts.IsInnerAut (barAut Y w hwN)) : barAut Y w hwN = 1 := by
  by_contra hne
  obtain ⟨g, hg3, hg1, hπg, hWbar⟩ := exists_inner_setup hZ hwN hw3 hWY hWw hWp hin hne
  exact hfive g hg3 hg1 _ hWbar hπg (h5.trans (card_quot_theta_dvd_card_imageModTheta hWY))

theorem false_of_exp_four_of_not_five {Y W : Subgroup G} (hWY : W ≤ Y)
    (hexp : ∀ t : Y ⧸ aschbacherSolvableCore 3 Y, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ 2 = 1)
    (h5 : ¬ 5 ∣ Nat.card (Y ⧸ aschbacherSolvableCore 3 Y))
    (hS : (∃ s : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) ∨
      5 ∣ Nat.card (W ⧸ aschbacherSolvableCore 3 W)) : False := by
  rcases hS with ⟨s, hs2, hs4⟩ | hs5
  · have hB : ∀ t : imageModTheta Y W, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ 2 = 1 := by
      intro t ht
      obtain ⟨k, hk⟩ := ht
      have h := hexp t ⟨k, by rw [← Subgroup.coe_pow, hk]; rfl⟩
      exact Subtype.ext (by rw [Subgroup.coe_pow]; simpa using h)
    obtain ⟨f, hf⟩ := exists_surjective_imageModTheta_quot hWY
    have hmem : s ∈ f.range := by
      rw [MonoidHom.range_eq_top.mpr hf]
      exact Subgroup.mem_top s
    exact hs4 (by simpa using pow_two_pow_eq_one_of_mem_range f hB hmem hs2)
  · exact h5 ((hs5.trans (card_quot_theta_dvd_card_imageModTheta hWY)).trans
      (Subgroup.card_subgroup_dvd_card _))

end Exclusion

section SU3


theorem gl3_sub_pow_four {F : Type} [Field F] [CharP F 2] (H : Subgroup (GL (Fin 3) F))
    (t : H) (ht : ∃ k : ℕ, t ^ 2 ^ k = 1) : t ^ 2 ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := ht
  have h := Hering88N.gl3_pow_four_eq_one (t : GL (Fin 3) F)
    ⟨k, by rw [← Subgroup.coe_pow, hk]; rfl⟩
  exact Subtype.ext (by rw [Subgroup.coe_pow]; simpa using h)

theorem su3_facts {K : Type} [Field K] [Finite K] {m : ℕ} (hodd : Odd m)
    (hK : Nat.card K = (2 ^ (3 * m)) ^ 2) :
    (∀ t : StatedSU 3 (2 ^ (3 * m)) K, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ^ 2 ^ 2 = 1) ∧
      ¬ 5 ∣ Nat.card (StatedSU 3 (2 ^ (3 * m)) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3 * m * 2) (by have := hodd.pos; omega) (by rw [hK, ← pow_mul])
  refine ⟨gl3_sub_pow_four _, ?_⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * m) K :=
    ⟨Nat.prime_two, by have := hodd.pos; omega, by rw [hK, ← pow_mul, mul_comm]⟩
  rw [show StatedSU 3 (2 ^ (3 * m)) K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (3 * m) K 3
    from rfl,
    KFacts.card_unitarySU_three hU]
  exact five_not_dvd_su3 (f := 3 * m) (Odd.mul (by decide) hodd)

theorem false_of_su3 {G : Type} [Group G] [Finite G] {Y W : Subgroup G} (hWY : W ≤ Y) {m : ℕ}
    (hodd : Odd m) (hY : IsoSUThree (Y ⧸ aschbacherSolvableCore 3 Y) (2 ^ (3 * m)))
    (hS : (∃ s : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) ∨
      5 ∣ Nat.card (W ⧸ aschbacherSolvableCore 3 W)) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hY
  obtain ⟨hexp, h5⟩ := su3_facts hodd hK
  refine false_of_exp_four_of_not_five hWY (fun t ht => ?_) (by rwa [Nat.card_congr e.toEquiv]) hS
  obtain ⟨k, hk⟩ := ht
  exact e.injective (by
    rw [map_pow, map_one]
    exact hexp (e t) ⟨k, by rw [← map_pow, hk, map_one]⟩)

theorem false_of_psu3 {G : Type} [Group G] [Finite G] {Y W : Subgroup G} (hWY : W ≤ Y) {m : ℕ}
    (hodd : Odd m) (hY : Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSU 3 2 (3 * m)))
    (hS : (∃ s : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) ∨
      5 ∣ Nat.card (W ⧸ aschbacherSolvableCore 3 W)) : False := by
  obtain ⟨e⟩ := hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 (2 * (3 * m)) with hF
  have hFc : Nat.card F = (2 ^ (3 * m)) ^ 2 := by
    rw [hF, GaloisField.card 2 _ (by have := hodd.pos; omega), ← pow_mul, mul_comm]
  set H : Subgroup (GL (Fin 3) F) := Subgroup.closure {A : GL (Fin 3) F |
    Matrix.GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ (3 * m))))ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1}
    with hH
  have hHSU : H = StatedSU 3 (2 ^ (3 * m)) F := by
    rw [hH]
    change _ = Subgroup.closure _
    congr 1
    ext A
    simp only [Set.mem_setOf_eq, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_one]
  have hproj : projSU 3 2 (3 * m) = H.map Matrix.ProjGenLinGroup.mk := rfl
  obtain ⟨hexpH, h5H⟩ := su3_facts hodd hFc
  refine false_of_exp_four_of_not_five hWY (fun t ht => ?_) ?_ hS
  ·
    obtain ⟨k, hk⟩ := ht
    have hmem : ((e t : projSU 3 2 (3 * m)) : Matrix.ProjGenLinGroup (Fin 3) F) ∈
        (Matrix.ProjGenLinGroup.mk.comp H.subtype).range := by
      obtain ⟨h, hh, hhe⟩ := (show ((e t : projSU 3 2 (3 * m)) :
          Matrix.ProjGenLinGroup (Fin 3) F) ∈ H.map Matrix.ProjGenLinGroup.mk from (e t).2)
      exact ⟨⟨h, hh⟩, hhe⟩
    have h4 := pow_two_pow_eq_one_of_mem_range (Matrix.ProjGenLinGroup.mk.comp H.subtype) (j := 2)
      (fun s hs => by
        have hs' : (⟨s, hHSU ▸ s.2⟩ : StatedSU 3 (2 ^ (3 * m)) F) ^ 2 ^ 2 = 1 := hexpH _ (by
          obtain ⟨k', hk'⟩ := hs
          exact ⟨k', Subtype.ext (by
            have := congrArg Subtype.val hk'
            rw [Subgroup.coe_pow] at this ⊢
            exact this)⟩)
        exact Subtype.ext (by
          have := congrArg Subtype.val hs'
          rw [Subgroup.coe_pow] at this ⊢
          exact this))
      hmem ⟨k, by rw [← Subgroup.coe_pow, ← map_pow, hk, map_one, Subgroup.coe_one]⟩
    exact e.injective (by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4))
  ·
    rw [Nat.card_congr e.toEquiv]
    intro h5
    apply h5H
    rw [← hHSU]
    exact h5.trans (by rw [hproj]; exact Subgroup.card_map_dvd H _)

end SU3

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
