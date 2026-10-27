module

public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.Sporadic.J3
import CFSG.LieType.Simplicity.Classical
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Models.PGLSimple
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

variable {G : Type} [Group G]

theorem isSimpleGroup_projSL_three (F : Type) [Field F] : IsSimpleGroup (projSL 3 F) :=
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le F (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem false_of_isSimpleGroup_of_mulEquiv_SL3 {X : Type*} [Group X] [IsSimpleGroup X] {n : ℕ}
    (hn : 0 < n) (he : Even n) (e : X ≃* SL3 n) : False :=
  not_isSimpleGroup_SL3 hn he e.symm.isSimpleGroup

theorem false_of_statedClassicalModel_PSL_of_mulEquiv_SL3 {X : Type} [Group X] {m n : ℕ}
    (hX : StatedClassicalModel X .PSL m 2 1) (hn : 0 < n) (he : Even n) (e : X ≃* SL3 n) :
    False := by
  have := (CFSG.LieType.Simplicity.fam_PSL_simplicity X m 2 1 hX).2
  exact false_of_isSimpleGroup_of_mulEquiv_SL3 hn he e

theorem not_mem_of_isSimpleGroup {L : Subgroup G} [IsSimpleGroup L]
    (hab : ∃ a b : L, a * b ≠ b * a) {c : G} (hc1 : c ≠ 1)
    (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) : c ∉ L := by
  intro hcL
  have hZ : Subgroup.center L = ⊥ := by
    obtain ⟨a, b, hab⟩ := hab
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a) hab
  have hmem : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC g.2))
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hc1 (congrArg Subtype.val hmem)

theorem card_center_SL3 {n : ℕ} (hn : 0 < n) (he : Even n) :
    Nat.card (Subgroup.center (SL3 n)) = 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd,
    GaloisField.card 2 n hn.ne']
  exact Nat.gcd_eq_right (three_dvd_two_pow_sub_one he)

theorem inSubgroup_theta_eq_bot_of_mulEquiv_SL3 [Finite G] {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (he : Even n) (e : L ≃* SL3 n) : inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  obtain ⟨hTs, hTc, hT3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hTdef
  have : T.Normal := by
    have := hTc
    infer_instance
  set T' : Subgroup (SL3 n) := T.map e.toMonoidHom with hT'def
  have hT'n : T'.Normal := Subgroup.Normal.map this _ e.surjective
  have eT : T ≃* T' := T.equivMapOfInjective _ e.injective
  have hT's : Group.IsSolvable T' :=
    Group.isSolvable_of_surjective (f := eT.toMonoidHom) eT.surjective
  have hT'3 : ¬ 3 ∣ Nat.card T' := by rwa [← Nat.card_congr eT.toEquiv]
  set π := QuotientGroup.mk' (Subgroup.center (SL3 n)) with hπ
  have hsimp : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 n) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n)) :=
    CFSG.LinearGroups.linear_projective_perfect (by norm_num) (Or.inl le_rfl)
  have hnt : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 n) (n := 3) (by norm_num)
      (Or.inl le_rfl)).1
  have hmn : (T'.map π).Normal := Subgroup.Normal.map hT'n _ (QuotientGroup.mk'_surjective _)
  have hcen : T' ≤ Subgroup.center (SL3 n) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T'.map π) with hb | ht
    · intro x hx
      have hmem : π x ∈ T'.map π := ⟨x, hx, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    · exfalso
      have hsolv : Group.IsSolvable (T'.map π) :=
        Group.isSolvable_of_surjective (π.subgroupMap_surjective T')
      rw [ht] at hsolv
      have hs : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n)) :=
        Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
          (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≃*
            _).toMonoidHom) (MulEquiv.surjective _)
      have := subsingleton_of_isPerfect_of_isSolvable hperf hs
      exact not_subsingleton _ this
  have hdvd : Nat.card T' ∣ 3 :=
    calc Nat.card T' ∣ Nat.card (Subgroup.center (SL3 n)) := Subgroup.card_dvd_of_le hcen
      _ = 3 := card_center_SL3 hn he
  have hT'1 : Nat.card T' = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exact absurd (by rw [h]) hT'3
  have hTb : T = ⊥ := by
    have h1 : Nat.card T = 1 := by rw [Nat.card_congr eT.toEquiv, hT'1]
    exact Subgroup.card_eq_one.mp h1
  rw [inSubgroup, ← hTdef, hTb, Subgroup.map_bot]

theorem nonempty_lBar_mulEquiv_SL3 [Finite G] {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (he : Even n) (e : L ≃* SL3 n) : Nonempty (lBar L ≃* SL3 n) :=
  ⟨(mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot_of_mulEquiv_SL3 hn he e)).symm.trans e⟩

theorem padicValNat_card_projSU_four {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 2 (Nat.card (projSU 4 2 n)) = n * 6 := by
  rw [card_projSU le_rfl hn, ordTwistedA_three_eq hn,
    padicValNat_pow_two_pow_mul_odd (odd_ordTwistedA_three_part hn)]

theorem false_of_mulEquiv_projSU_four_of_J3 {X : Type*} [Group X]
    {n : ℕ} (hn : 1 ≤ n) (e₁ : X ≃* projSU 4 2 n) (e₂ : X ≃* NativeSporadic.J3) : False := by
  have h := (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr e₂.toEquiv)
  rw [CFSG.Sporadic.J3.card_J3, show (50232960 : ℕ) = 2 ^ 7 * 392445 by norm_num] at h
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat_card_projSU_four hn, padicValNat_two_pow_mul_odd (by decide)] at hv
  omega

theorem false_of_projSU_four_of_PSp_three {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* projSU 4 2 n) (hX : StatedClassicalModel X .PSp 3 2 1) : False := by
  have h := (Nat.card_congr e.toEquiv).symm.trans
    ((CFSG.Timmesfeld.card_statedClassicalModel_two hX).2.2.1 rfl)
  rw [show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide] at h
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat_card_projSU_four hn, padicValNat_two_pow_mul_odd (by decide)] at hv
  omega

theorem not_isTripleCover_of_isSimpleGroup {X Y : Type*} [Group X] [Group Y] [IsSimpleGroup X]
    (hab : ∃ a b : X, a * b ≠ b * a) : ¬ Sec4.IsTripleCover X Y := by
  rintro ⟨hcard, -⟩
  have hZ : Subgroup.center X = ⊥ := by
    obtain ⟨a, b, hab⟩ := hab
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a) hab
  rw [hZ, Subgroup.card_bot] at hcard
  omega

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
