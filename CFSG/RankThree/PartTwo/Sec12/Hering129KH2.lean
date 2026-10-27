module

import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec12.Hering129KE1
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)


namespace Hering129KH2

theorem isSimpleGroup_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (hns : ¬ Group.IsSolvable X) (h : Sec4.IsoLThreePi X p e) : IsSimpleGroup X := by
  rcases h with ⟨-, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  ·
    haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p e)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact f.isSimpleGroup
  · by_cases hpe : p ^ e = 2
    ·
      exfalso
      obtain ⟨hp2, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hpe
      subst hp2 he1
      haveI : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
      exact hns (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
    ·
      have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 p e := by
        refine ⟨Fact.out, ?_, le_rfl, ?_⟩
        · rcases Nat.eq_zero_or_pos e with h0 | h0
          · subst h0
            simp at h2
          · exact h0
        · intro hh
          exact hpe (by simpa using congrArg Prod.snd hh)
      haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm
      exact f.isSimpleGroup

theorem not_isSolvable_of_hessData {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P}
    {xh bh ch : P} (hD : HessData Yh Bh xh bh ch) : ¬ Group.IsSolvable ↥Yh := by
  intro hsol
  obtain ⟨Xh, hXY, -, hperf, -, -, p, n, hp, h4, φ, hφ⟩ := hD.comp
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at h4
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn0
  have hsimp : IsSimpleGroup (projSL 2 (GaloisField p n)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 2) (GaloisField p n) le_rfl
      (Or.inr (by rw [hcard]; omega)) (Or.inr (by rw [hcard]; omega))
  haveI : Nontrivial ↥Xh := hφ.nontrivial
  haveI : Group.IsPerfect ↥Xh := hperf
  exact Group.IsPerfect.not_isSolvable ↥Xh
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXY)
      (Subgroup.inclusion_injective hXY))

theorem isQuasisimple_of_isSimpleGroup_not_isSolvable {X : Type} [Group X] [IsSimpleGroup X]
    (hns : ¬ Group.IsSolvable X) : CFSG.IsQuasisimple X := by
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  exact hns (IsSimpleGroup.comm_iff_isSolvable.mp fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩)

theorem hess_model {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}
    (hD : HessData Yh Bh xh bh ch) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi ↥Yh p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), Sec4.PiField π p e K ∧ Sec4.ModThree π (p ^ e) ∧
      Nonempty (↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ e) K)) := by
  have hns := not_isSolvable_of_hessData hD
  haveI := isSimpleGroup_of_isoLThreePi hns hiso
  obtain ⟨π, K, hK, hPi, hMod, -, hiso'⟩ :=
    Sec4.exists_pslPi_model he hiso (isQuasisimple_of_isSimpleGroup_not_isSolvable hns)
  exact ⟨π, K, hK, hPi, hMod, hiso'⟩

end Hering129KH2

end CFSG.RankThree.PartTwo.Sec12
