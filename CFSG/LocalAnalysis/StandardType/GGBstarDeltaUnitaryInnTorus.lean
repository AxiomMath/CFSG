module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInnFrame
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter

public section

namespace CFSG.StandardType

namespace TableBUI

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] [Finite K] {d n p : ℕ}

theorem exists_frame_torus (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    {E₀ : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hE₀ : IsElemAbelian p E₀)
    (hE₀D : E₀ ≤ inndiagU (TableBU.unitaryFieldData_of_card hK hn) (by omega)) :
    ∃ (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary (TableBU.unitaryFieldData_of_card hK hn)
      (idGram K d)) (W : Subgroup (Fin d → Kˣ)),
      Nat.card W = Nat.card E₀ ∧ (∀ σ ∈ W, (∀ k, σ k ^ p = 1) ∧ ∏ k, σ k = 1) ∧
      (∀ σ ∈ W, ∃ x : ↥(unitarySU 2 n K d),
        (TableBUE.conjSU (TableBU.unitaryFieldData_of_card hK hn) P hP x : GL (Fin d) K) =
          diagHom d σ ∧ MulAut.conj (projU n d K x) ∈ E₀) ∧
      ∀ e ∈ E₀, ∃ σ ∈ W, ∃ x : ↥(unitarySU 2 n K d),
        (TableBUE.conjSU (TableBU.unitaryFieldData_of_card hK hn) P hP x : GL (Fin d) K) =
          diagHom d σ ∧ e = MulAut.conj (projU n d K x) := by
  classical
  set h := TableBU.unitaryFieldData_of_card hK hn with hh
  have := Fact.mk hp
  set R := LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))
  have hR := TableBUE.center_proj_eq_bot hK hd hdq
  have hcinj := mulAut_conj_injective hR
  have hinner : ∀ e ∈ E₀, ∃ r : R, MulAut.conj r = e := by
    intro e he
    have heI := mem_conjImage_of_mem_inndiagU h (hE₀D he)
    exact ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd e heI (hE₀.2 e he)
  set Ab : Subgroup R := E₀.comap MulAut.conj with hAb
  have hAbmap : Ab.map MulAut.conj = E₀ := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr
    · intro e he
      obtain ⟨r, rfl⟩ := hinner e he
      exact ⟨r, he, rfl⟩
  have hAbcard : Nat.card Ab = Nat.card E₀ := by
    rw [← hAbmap, Subgroup.card_map_of_injective hcinj]
  have hAbab : IsElemAbelian p Ab := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcinj ?_)⟩⟩, fun a ha => hcinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE₀ a.2 b.2
    · rw [map_pow, hE₀.2 _ ha, map_one]
  have hnp : ∀ z ∈ (projU n d K).ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    TableBUE.eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hAmap, -, hA, hAcard⟩ :=
    TableBUE.exists_lift_of_noTorsion (projU n d K) projU_surjective hp hnp hAbab
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA
  set A' := A.map (TableBUE.conjSU h P hP).toMonoidHom with hA'
  have hA'ab : IsElemAbelian p A' := TableB.isElemAbelian_map hA _
  have hA'd : ∀ y ∈ A', ∃ σ : Fin d → Kˣ, (y : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPd x hx
  set W := TableBUE.diagVec A' with hW
  refine ⟨P, hP, W, ?_, fun σ hσ => ?_, fun σ hσ => ?_, fun e he => ?_⟩
  · rw [hW, TableBUE.card_diagVec hA'd, hA',
      Subgroup.card_map_of_injective (TableBUE.conjSU h P hP).injective, hAcard, hAbcard]
  · obtain ⟨hσp, hσprod⟩ := TableBUE.diagVec_props h hA'ab hσ
    refine ⟨hσp, Units.ext ?_⟩
    rw [Units.coe_prod, hσprod, Units.val_one]
  · obtain ⟨y, hy, hyσ⟩ := TableBUE.mem_diagVec.mp hσ
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, hyσ, ?_⟩
    have hxAb : projU n d K x ∈ Ab := by
      rw [← hAmap]
      exact ⟨x, hx, rfl⟩
    exact hxAb
  · obtain ⟨r, rfl⟩ := hinner e he
    have hrAb : r ∈ Ab := he
    rw [← hAmap] at hrAb
    obtain ⟨x, hx, rfl⟩ := hrAb
    obtain ⟨σ, hσ⟩ := hPd x hx
    exact ⟨σ, TableBUE.mem_diagVec.mpr ⟨_, ⟨x, hx, rfl⟩, hσ⟩, x, hσ, rfl⟩

end TableBUI

end CFSG.StandardType
