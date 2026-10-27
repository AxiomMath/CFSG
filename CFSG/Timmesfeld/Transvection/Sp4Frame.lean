module

public import CFSG.Timmesfeld.Transvection.TriangleCrux
public import CFSG.Timmesfeld.Transvection.ModelRankBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

structure Sp4Frame (Δ : Set (Subgroup G)) (A E D E' B : Subgroup G) : Prop where
  memA : A ∈ Δ
  memE : E ∈ Δ
  memD : D ∈ Δ
  memE' : E' ∈ Δ
  oppA : Opposite E A
  oppD : Opposite E' D
  comm : Commuting (A ⊔ E) (D ⊔ E')
  memB : B ∈ lineOf Δ A D
  neA : B ≠ A
  neD : B ≠ D

namespace Sp4Frame

variable {A E D E' B : Subgroup G} (F : Sp4Frame Δ A E D E' B)
include F

theorem commuting_AD : Commuting A D := F.comm.mono le_sup_left le_sup_left

theorem commuting_AE' : Commuting A E' := F.comm.mono le_sup_left le_sup_right

theorem commuting_ED : Commuting E D := F.comm.mono le_sup_right le_sup_left

theorem ne_AD : A ≠ D := fun e =>
  ModelRank.not_commuting_of_opposite F.oppA (by rw [e]; exact F.commuting_ED)

theorem swap : Sp4Frame Δ D E' A E B :=
  ⟨F.memD, F.memE', F.memA, F.memE, F.oppD, F.oppA, F.comm.symm,
    lineOf_comm (Δ := Δ) A D ▸ F.memB, F.neD, F.neA⟩

variable [Finite G] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
include hΔ hpts

omit [Finite G] hpts in
theorem commuting_AB : Commuting A B :=
  (commuting_of_mem_lineOf' hΔ F.memA F.memD F.commuting_AD F.memB).1

theorem lineOf_eq : lineOf Δ A B = lineOf Δ A D :=
  lineOf_eq_of_mem_of_ne hΔ hpts F.memA F.memD F.ne_AD F.commuting_AD F.memB F.neA

theorem mem_lineOf : D ∈ lineOf Δ A B := F.lineOf_eq hΔ hpts ▸ right_mem_lineOf F.memD

theorem opp_EB : Opposite E B := by
  have hEB : E ≠ B := by
    rintro rfl
    exact ModelRank.not_commuting_of_opposite F.oppA (F.commuting_AB hΔ).symm
  rcases hΔ.commuting_or_opposite F.memE F.memB.1 hEB with hc | ho
  · exfalso
    have := commuting_of_commuting_of_mem_lineOf hΔ hpts F.memA F.memD F.ne_AD F.commuting_AD
      F.memB (right_mem_lineOf F.memD) F.neD (left_mem_lineOf F.memA) F.memE hc F.commuting_ED
    exact ModelRank.not_commuting_of_opposite F.oppA this
  · exact ho

theorem isTriangle : IsTriangle Δ A E B :=
  ⟨F.memA, F.memE, F.memB.1, F.neA.symm, F.commuting_AB hΔ, F.oppA, F.opp_EB hΔ hpts⟩

theorem le_corrL {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (hq : 4 ≤ Nat.card A) : D ≤ corrL A E t :=
  S.le_corrL_of_mem_lineOf htY hq hpts (F.mem_lineOf hΔ hpts) F.commuting_ED.symm

theorem corrL_eq_sup {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (hq : 4 ≤ Nat.card A) : corrL A E t = A ⊔ D ⊔ B := by
  have hAD := F.ne_AD
  refine (S.sup_sup_eq_corrL htY hq hpts F.memA F.memD F.memB.1 ?_ (F.le_corrL hΔ hpts S htY hq)
    ?_ hAD F.neA.symm F.neD.symm).symm
  · exact le_iSup₂_of_le A mem_corrLSet_self le_rfl
  · exact S.le_corrL_right

end Sp4Frame

structure PairFrame (Δ : Set (Subgroup G)) (A E D E' : Subgroup G) : Prop where
  memA : A ∈ Δ
  memE : E ∈ Δ
  memD : D ∈ Δ
  memE' : E' ∈ Δ
  oppA : Opposite E A
  oppD : Opposite E' D
  comm : Commuting (A ⊔ E) (D ⊔ E')

theorem Sp4Frame.toPairFrame {A E D E' B : Subgroup G} (F : Sp4Frame Δ A E D E' B) :
    PairFrame Δ A E D E' :=
  ⟨F.memA, F.memE, F.memD, F.memE', F.oppA, F.oppD, F.comm⟩

namespace PairFrame

variable {A E D E' : Subgroup G} (P : PairFrame Δ A E D E')
include P

theorem toSp4Frame {B : Subgroup G} (hB : B ∈ lineOf Δ A D) (hBA : B ≠ A) (hBD : B ≠ D) :
    Sp4Frame Δ A E D E' B :=
  ⟨P.memA, P.memE, P.memD, P.memE', P.oppA, P.oppD, P.comm, hB, hBA, hBD⟩

theorem swap : PairFrame Δ D E' A E :=
  ⟨P.memD, P.memE', P.memA, P.memE, P.oppD, P.oppA, P.comm.symm⟩

theorem flip : PairFrame Δ E A D E' :=
  ⟨P.memE, P.memA, P.memD, P.memE', P.oppA.symm, P.oppD, sup_comm A E ▸ P.comm⟩

theorem flip' : PairFrame Δ A E E' D :=
  ⟨P.memA, P.memE, P.memE', P.memD, P.oppA, P.oppD.symm, sup_comm D E' ▸ P.comm⟩

theorem commuting_AD : Commuting A D := P.comm.mono le_sup_left le_sup_left

theorem commuting_AE' : Commuting A E' := P.comm.mono le_sup_left le_sup_right

theorem commuting_ED : Commuting E D := P.comm.mono le_sup_right le_sup_left

theorem commuting_EE' : Commuting E E' := P.comm.mono le_sup_right le_sup_right

theorem ne_AD : A ≠ D := fun e =>
  ModelRank.not_commuting_of_opposite P.oppA (by rw [e]; exact P.commuting_ED)

theorem conj (hΔ : IsRootClass Δ) (g : G) :
    PairFrame Δ (conjSub A g) (conjSub E g) (conjSub D g) (conjSub E' g) := by
  refine ⟨hΔ.conjSub_mem P.memA g, hΔ.conjSub_mem P.memE g, hΔ.conjSub_mem P.memD g,
    hΔ.conjSub_mem P.memE' g, P.oppA.conj g, P.oppD.conj g, ?_⟩
  have := P.comm.conjSub g
  simpa only [conjSub, Subgroup.map_sup] using this

end PairFrame

end CFSG.Timmesfeld.Transvection
