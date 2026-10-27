module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# A proper characteristic subgroup of odd `PGL₂`

For a finite field of odd cardinality, the commutator subgroup of `PGL₂` is
nontrivial and proper.  Nontriviality follows from the trivial center.  For
properness, the commutator is contained in the embedded `PSL₂`: lift a
commutator to `GL₂`, whose determinant is one, and then descend through
`PSL₂`.  The embedded `PSL₂` is proper because its surjectivity would say
that every unit of the field is a square.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- Over a finite field of odd prime-power cardinality, the characteristic
commutator subgroup of `PGL₂` is neither trivial nor the whole group. -/
public theorem pgl2_commutator_ne_bot_ne_top
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    commutator (PGL2 K) ≠ ⊥ ∧ commutator (PGL2 K) ≠ ⊤ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, n, _hp, hpOdd, _hn, hcard⟩
    rw [hcard]
    exact hpOdd.pow
  have hchar : ringChar K ≠ 2 := by
    intro hchar
    have heven : Fintype.card K % 2 = 0 :=
      FiniteField.even_card_of_char_two hchar
    have hqOdd' : Odd (Fintype.card K) := by
      simpa [Nat.card_eq_fintype_card] using hqOdd
    rcases hqOdd' with ⟨m, hm⟩
    omega
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    exact ha IsSquare.zero
  let u : Kˣ := Units.mk0 a ha0
  have hu : ¬ IsSquare u := by
    rintro ⟨v, hv⟩
    apply ha
    refine ⟨(v : K), ?_⟩
    simpa [u] using congrArg Units.val hv
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL_not_surj : ¬ Function.Surjective toPGL := by
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_iff]
    intro hall
    have hall' : ∀ r : Kˣ, ∃ k : Kˣ, k ^ 2 = r := by
      simpa using hall
    obtain ⟨k, hk⟩ := hall' u
    exact hu ⟨k, by simpa [pow_two] using hk.symm⟩
  have htoPGL_range_ne_top : toPGL.range ≠ ⊤ := by
    intro hrange
    exact htoPGL_not_surj (MonoidHom.range_eq_top.mp hrange)
  let mkPGL : Matrix.GeneralLinearGroup (Fin 2) K →* PGL2 K :=
    Matrix.ProjGenLinGroup.mk
  have hmkRange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hmapComm :
      (commutator (Matrix.GeneralLinearGroup (Fin 2) K)).map mkPGL =
        commutator (PGL2 K) := by
    rw [map_commutator_eq, hmkRange]
    rfl
  have hcomm_le : commutator (PGL2 K) ≤ toPGL.range := by
    rw [← hmapComm]
    rintro _ ⟨g, hg, rfl⟩
    have hgdetUnit : Matrix.GeneralLinearGroup.det g = 1 :=
      MonoidHom.mem_ker.mp
        (Abelianization.commutator_subset_ker Matrix.GeneralLinearGroup.det hg)
    have hgdet : Matrix.det g.1 = 1 := by
      simpa using congrArg Units.val hgdetUnit
    let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨g.1, hgdet⟩
    have hsGL : Matrix.SpecialLinearGroup.toGL s = g := by
      ext i j
      rfl
    refine ⟨QuotientGroup.mk s, ?_⟩
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hsGL]
  have hcomm_ne_top : commutator (PGL2 K) ≠ ⊤ := by
    intro hcomm
    apply htoPGL_range_ne_top
    apply top_unique
    rw [← hcomm]
    exact hcomm_le
  have hq3 : 3 ≤ Nat.card K := by
    have hq1 : 1 < Nat.card K := Finite.one_lt_card
    rcases hqOdd with ⟨m, hm⟩
    omega
  have hqSq : 9 ≤ Nat.card K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hq3 hq3
  have hqDiff : 8 ≤ Nat.card K ^ 2 - 1 := by omega
  have hpglLower : 24 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
    simpa using Nat.mul_le_mul hq3 hqDiff
  have hpglCard : 1 < Nat.card (PGL2 K) := by
    rw [pgl2_card_formula]
    omega
  let : Nontrivial (PGL2 K) :=
    Finite.one_lt_card_iff_nontrivial.mp hpglCard
  have hcomm_ne_bot : commutator (PGL2 K) ≠ ⊥ := by
    intro hcomm
    have hcenter : Subgroup.center (PGL2 K) = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top (PGL2 K)).mp hcomm
    rw [pgl2_center_eq_bot K] at hcenter
    exact bot_ne_top hcenter
  exact ⟨hcomm_ne_bot, hcomm_ne_top⟩

/-- Properness and nontriviality of the odd-`PGL₂` commutator transport
across a group equivalence. -/
public theorem commutator_ne_bot_ne_top_of_mulEquiv_pgl2_odd
    {Q : Type u} [Group Q] [Finite Q]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : Q ≃* PGL2 K) :
    commutator Q ≠ ⊥ ∧ commutator Q ≠ ⊤ := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hPGL := pgl2_commutator_ne_bot_ne_top K hK
  have hErange : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr e.surjective
  have hmap : (commutator Q).map e.toMonoidHom = commutator (PGL2 K) := by
    rw [map_commutator_eq, hErange]
    rfl
  constructor
  · intro hbot
    apply hPGL.1
    calc
      commutator (PGL2 K) = (commutator Q).map e.toMonoidHom := hmap.symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  · intro htop
    apply hPGL.2
    calc
      commutator (PGL2 K) = (commutator Q).map e.toMonoidHom := hmap.symm
      _ = ⊤ := by
        rw [htop]
        exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

end CFSG.GorensteinWalter
