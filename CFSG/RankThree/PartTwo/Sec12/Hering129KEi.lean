module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd
import CFSG.Models.PGLSimple
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec12.Hering129KModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)


variable {G : Type} [Group G] [Finite G]

theorem theta_eq_pCore_of_typ129IIIcType {L Y : Subgroup G}
    (hYq : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) (h3 : Typ129IIIcType L Y) :
    aschbacherSolvableCore 3 Y = CFSG.pCore 2 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 3 Y with hθ
  set Q := CFSG.pCore 2 Y with hQ
  obtain ⟨hθsol, hθn, -, -, -, -, hpc⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  have hQθ : Q ≤ θ := hpc 2 Nat.prime_two (by norm_num)
  refine le_antisymm ?_ hQθ
  haveI : Group.IsPerfect (Y ⧸ θ) := hYq.1
  haveI : Nontrivial (Y ⧸ θ) := CFSG.LocalCores.isQuasisimple_nontrivial hYq
  have hnsY : ¬ Group.IsSolvable (Y ⧸ Q) := by
    intro hs
    haveI := hs
    have hsur : Function.Surjective
        (QuotientGroup.map Q θ (MonoidHom.id Y) (by simpa using hQθ)) := by
      intro z
      induction z using QuotientGroup.induction_on with
      | H y => exact ⟨(y : Y ⧸ Q), rfl⟩
    exact Group.IsPerfect.not_isSolvable (Y ⧸ θ) (Group.isSolvable_of_surjective hsur)
  have hsimp : IsSimpleGroup (Y ⧸ Q) := by
    obtain ⟨-, hty, -⟩ := h3
    rcases hty with ⟨p, e, hp, hiso⟩ | ⟨q₀, hq, ⟨ee⟩⟩
    · haveI := hp
      rcases hiso with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
      · haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p e)
          (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
        exact f.isSimpleGroup
      · by_cases hpe : p ^ e = 2
        · exfalso
          obtain ⟨hp2, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hpe
          subst hp2 he1
          haveI : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
          haveI : Group.IsSolvable (Y ⧸ Q) :=
            solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
          exact hnsY this
        · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 p e := by
            refine ⟨Fact.out, ?_, le_rfl, ?_⟩
            · rcases Nat.eq_zero_or_pos e with h0 | h0
              · subst h0
                simp at h2
              · exact h0
            · intro hh
              exact hpe (by simpa using congrArg Prod.snd hh)
          haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm
          exact f.isSimpleGroup
    · exact Hering129KModels.isSimpleGroup_of_isG2D4
        (Or.inr ⟨rfl, hq, ⟨ee⟩⟩ : IsG2D4 (Y ⧸ Q) q₀ 3)
  set π := QuotientGroup.mk' Q with hπ
  haveI hnorm : (θ.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Q)
  rcases hsimp.eq_bot_or_eq_top_of_normal (θ.map π) with h | h
  · intro y hy
    have : π y ∈ θ.map π := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff y).mp this
  · exfalso
    haveI : Group.IsSolvable θ := hθsol
    refine hnsY (Group.isSolvable_of_surjective (f := π.comp θ.subtype) ?_)
    intro z
    have hz : z ∈ θ.map π := h ▸ Subgroup.mem_top z
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨⟨y, hy⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec12
