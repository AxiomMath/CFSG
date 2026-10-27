module

public import Certificates.Data.FischerMarkedReflection
public import CFSG.Fischer.Classification.PartIII.Beta.Points

public section

namespace CFSG.OddTranspositions.FischerMarked

open CFSG.Fischer.Classification

theorem point_norm : ∀ i : Fin 351, dot (point i) (point i) = 1 := by
  decide +kernel

theorem pointIndex_point : ∀ i : Fin 351, pointIndex (point i) = i ∧ pointIndex (-point i) = i := by
  decide +kernel

theorem point_pointIndex : ∀ a b c d e f g : ZMod 3,
    dot ![a, b, c, d, e, f, g] ![a, b, c, d, e, f, g] = 1 →
      point (pointIndex ![a, b, c, d, e, f, g]) = ![a, b, c, d, e, f, g] ∨
        point (pointIndex ![a, b, c, d, e, f, g]) = -![a, b, c, d, e, f, g] := by
  decide +kernel

theorem diagF3_seven_one_apply (v w : Fin 7 → ZMod 3) : diagF3 7 1 v w = dot v w := by
  rw [diagF3_apply, Fin.sum_univ_seven, dot]
  simp only [diagF3Entry, ite_self, one_mul]

private theorem vector_eq (v : Fin 7 → ZMod 3) :
    v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] := by
  ext i
  fin_cases i <;> rfl

@[expose] noncomputable def reflPoint (i : Fin 351) : D3 (diagF3 7 1) :=
  ⟨reflBar (diagF3 7 1) (point i), reflBar_mem_D3 (by
    rw [diagF3_seven_one_apply]
    exact point_norm i)⟩

theorem reflPoint_bijective : Function.Bijective reflPoint :=
  Beta.bijective_reflBar_of_reps (isF3Form_diagF3 (by decide)) (by decide) point pointIndex
    (fun i => by rw [diagF3_seven_one_apply]; exact point_norm i) pointIndex_point fun w hw => by
      rw [diagF3_seven_one_apply, vector_eq w] at hw
      rw [vector_eq w]
      exact point_pointIndex _ _ _ _ _ _ _ hw

@[expose] noncomputable def reflPointEquiv : Fin 351 ≃ D3 (diagF3 7 1) :=
  Equiv.ofBijective reflPoint reflPoint_bijective

theorem reflPointEquiv_apply (i : Fin 351) : reflPointEquiv i = reflPoint i := rfl

theorem reflPoint_conj (i j k : Fin 351)
    (h : point k = reflectPoint (point i) (point j) ∨
      point k = -reflectPoint (point i) (point j)) :
    (reflPoint k : R3 (diagF3 7 1)) = reflPoint i * reflPoint j * reflPoint i := by
  change reflBar _ (point k) = reflBar _ (point i) * reflBar _ (point j) * reflBar _ (point i)
  rw [reflBar_conj (isF3Form_diagF3 (by decide))]
  have hact : F3.act (F3.refl (diagF3 7 1) (point i)) (point j) =
      reflectPoint (point i) (point j) := by
    rw [F3.act_refl (by rw [diagF3_seven_one_apply]; exact point_norm i),
      diagF3_seven_one_apply]
    rfl
  rw [hact]
  rcases h with h | h <;> rw [h]
  exact reflBar_neg _

theorem reflectPoint_norm {v w : Fin 7 → ZMod 3} (hv : dot v v = 1) (hw : dot w w = 1) :
    dot (reflectPoint v w) (reflectPoint v w) = 1 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have e : dot (reflectPoint v w) (reflectPoint v w) =
      dot w w + 3 * dot w v ^ 2 + dot w v ^ 2 * (dot v v - 1) := by
    unfold reflectPoint dot
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, hv, hw, h3]
  ring

theorem point_reflect (i j : Fin 351) :
    point (pointIndex (reflectPoint (point i) (point j))) = reflectPoint (point i) (point j) ∨
      point (pointIndex (reflectPoint (point i) (point j))) =
        -reflectPoint (point i) (point j) := by
  have hn := reflectPoint_norm (point_norm i) (point_norm j)
  generalize reflectPoint (point i) (point j) = w at hn ⊢
  rw [vector_eq w] at hn ⊢
  exact point_pointIndex _ _ _ _ _ _ _ hn

theorem reflPoint_reflect (i j : Fin 351) :
    (reflPoint (pointIndex (reflectPoint (point i) (point j))) : R3 (diagF3 7 1)) =
      reflPoint i * reflPoint j * reflPoint i :=
  reflPoint_conj i j _ (point_reflect i j)

end CFSG.OddTranspositions.FischerMarked
