module

import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Proof1514

theorem ker_toQuotTwo_le {L Y : Subgroup G} (hLY : L ≤ Y) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY)).ker ≤
      aschbacherSolvableCore 3 ↥L := by
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY) with hf
  have hK : IsPGroup 2 f.ker := by
    intro x
    have hx : Subgroup.inclusion hLY (x : ↥L) ∈ CFSG.pCore 2 ↥Y := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hLY (x : ↥L)) = 1 := x.2
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (⟨_, hx⟩ : CFSG.pCore 2 ↥Y)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : CFSG.pCore 2 ↥Y => ((z : ↥Y) : G)) hk
    simpa using this
  have hKle : f.ker ≤ CFSG.pCore 2 ↥L := le_sSup ⟨MonoidHom.normal_ker f, hK⟩
  obtain ⟨-, -, -, -, -, -, hcore⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  exact hKle.trans (hcore 2 Nat.prime_two (by norm_num))

theorem card_thetaQuot_dvd {L Y : Subgroup G} (hLY : L ≤ Y) :
    Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY) with hf
  have hker := ker_toQuotTwo_le hLY
  rw [← hf] at hker
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have h1 : Nat.card (↥L ⧸ θ) ∣ Nat.card (↥L ⧸ f.ker) := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hker
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    refine ⟨k, ?_⟩
    have : Nat.card (↥L ⧸ f.ker) * Nat.card f.ker =
        Nat.card (↥L ⧸ θ) * k * Nat.card f.ker := by
      rw [← e2, e1, hk]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have h2 : Nat.card (↥L ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  exact h1.trans (h2 ▸ Subgroup.card_subgroup_dvd_card f.range)

theorem card_thetaQuot_eq {L Y : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hp : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY) with hf
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hker : f.ker ≤ θ := ker_toQuotTwo_le hLY
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) q
    have hy : (y : G) ∈ ((L ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hY]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hy
    obtain ⟨l, hl, n, hn, hln⟩ := Set.mem_mul.mp hy
    obtain ⟨n', hn', rfl⟩ := hn
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hyn : (Subgroup.inclusion hLY ⟨l, hl⟩)⁻¹ * y = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hln, Subgroup.coe_subtype]
      group
    rw [hyn]
    exact hn'
  have hθc : θ.Characteristic := (solvable_prime_complement_core_characterization (H := ↥L)
    Nat.prime_three).2.1
  have hθn : θ.Normal := Subgroup.normal_of_characteristic θ
  have hθs : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have himg : θ.map f = ⊥ := by
    have hnorm : (θ.map f).Normal := hθn.map f hsurj
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hs' : Group.IsSolvable (θ.map f) :=
        Group.isSolvable_of_surjective (f.subgroupMap_surjective θ)
      have htop : Group.IsSolvable (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
        rw [h] at hs'
        exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).subtype)
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      have := hs.toNontrivial
      exact Group.IsPerfect.not_isSolvable _ htop
  have hθker : θ ≤ f.ker := (Subgroup.map_eq_bot_iff θ).mp himg
  have heq : f.ker = θ := le_antisymm hker hθker
  calc Nat.card (↥L ⧸ θ) = Nat.card (↥L ⧸ f.ker) := by rw [heq]
    _ = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv

theorem checkSL_a7 : ∀ q < 14, 2 ≤ q → q ^ 3 ∣ 2520 →
    2520 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_a7 : ∀ q < 14, 2 ≤ q → q ^ 3 ∣ 2520 →
    2520 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem not_isoLThreePi_of_card_2520 {X : Type} [Group X] (hX : Nat.card X = 2520) (p e : ℕ)
    [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e :=
  KFacts.KS14.not_isoLThreePi_of_card hX
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_a7)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_a7) p e

end Proof1514

end CFSG.RankThree.PartTwo.Sec15
