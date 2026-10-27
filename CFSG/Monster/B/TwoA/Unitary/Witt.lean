
module

public import CFSG.Monster.B.TwoA.Unitary.WittBase
import all CFSG.Monster.B.TwoA.Unitary.WittBase

public import CFSG.Monster.B.TwoA.Unitary.Planes
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix CFSG.Monster.B.Classical.UnitarySix CFSG.LieType.Universal.Unitary

theorem exists_SUh_plane0 {P : Submodule F4 V6} (hP : IsMaxIso P) :
    ∃ g : SUh, subMul (plane 0) ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = P := by
  classical
  let b := Module.finBasisOfFinrankEq F4 P hP.1
  let v : Fin 3 → V6 := fun a => (b a : V6)
  have hli : LinearIndependent F4 v := b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hvP : ∀ a, v a ∈ P := fun a => (b a).2
  have hiso : ∀ a c, herm (swV (v a)) (swV (v c)) = 0 := fun a c => by
    rw [herm_swV]
    exact hP.2 _ (hvP a) _ (hvP c)
  have hli' : LinearIndependent F4 ![swV (v 0), swV (v 1), swV (v 2)] := by
    have h1 : LinearIndependent F4 (fun a => swLin (v a)) := hli.map' swLin.toLinearMap
      (LinearMap.ker_eq_bot.2 swLin.injective)
    have h2 : ![swV (v 0), swV (v 1), swV (v 2)] = fun a => swLin (v a) := by
      funext a
      fin_cases a <;> rfl
    rw [h2]
    exact h1
  obtain ⟨e, he, e0, e1, e2⟩ := exists_frame_of_triple hli' (hiso 0 0) (hiso 0 1) (hiso 0 2)
    (hiso 1 1) (hiso 1 2) (hiso 2 2)
  obtain ⟨g, hg⟩ := exists_SU_lines_of_frame he
  set G : Matrix (Fin 6) (Fin 6) F4 := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hdet : (rowConj G).det = 1 := by rw [det_rowConj]; exact det_of_mem g
  have hA : GeneralLinearGroup.mkOfDetNeZero (rowConj G) (by rw [hdet]; exact one_ne_zero) ∈
      SUh := by
    refine ⟨hdet, fun s t => ?_⟩
    change hU (s ᵥ* rowConj G) (t ᵥ* rowConj G) = hU s t
    rw [vecMul_rowConj, vecMul_rowConj, hU_swV, isIsometry_of_mem g, herm_swV]
  refine ⟨⟨_, hA⟩, ?_⟩
  change subMul (plane 0) (rowConj G) = P
  have himg : ∀ a : Fin 3, planeRow 0 a ᵥ* rowConj G ∈ P := by
    intro a
    obtain ⟨c, -, hc⟩ := hg (lo a)
    have hea : e (lo a) = swV (v a) := by
      fin_cases a
      · exact e0
      · exact e1
      · exact e2
    rw [vecMul_rowConj, planeRow_zero, swV_single_lo, hc, hea]
    change c • swV (swV (v a)) ∈ P
    rw [swV_swV]
    exact P.smul_mem c (hvP a)
  have hspan : subMul (plane 0) (rowConj G) =
      Submodule.span F4 (Set.range fun a => planeRow 0 a ᵥ* rowConj G) := by
    rw [plane, subMul_span, ← Set.range_comp]
    rfl
  rw [hspan]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact himg a
  · rw [finrank_span_eq_card (linearIndependent_vecMul (linearIndependent_planeRow 0)
      (by rw [hdet]; exact one_ne_zero)), Fintype.card_fin, hP.1]

end CFSG.Monster.B.TwoA.Unitary
