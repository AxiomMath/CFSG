module

public import CFSG.Quasithin.Background.Harris.R1.J2VertIso

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Quasithin CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.F2 CFSG.Quasithin.J2Cz.QM

variable {G : Type} [Group G]

structure VertRel (z : G) (x : Fin 5 → G) (a b : G) : Prop where
  z_sq : z * z = 1
  zx : ∀ i, z * x i = x i * z
  x_sq : ∀ i, x i * x i = 1
  xx : ∀ i j, i ≠ j → x i * x j * (x i * x j) = z
  x0 : x 0 = x 1 * x 2 * x 3 * x 4
  a_sq : a * a = 1
  b_cube : b * b * b = 1
  ab_five : (a * b) ^ 5 = 1
  za : z * a = a * z
  zb : z * b = b * z
  ax : ∀ i, a * x i * a⁻¹ = x (pa i)
  bx : ∀ i, b * x i * b⁻¹ = x (pb i)

namespace VertRel

variable {z : G} {x : Fin 5 → G} {a b : G} (h : VertRel z x a b) {X : Subgroup G}
  (hz : z ∈ X) (hx : ∀ i, x i ∈ X)

include h in
theorem anti {i j : Fin 5} (hij : i ≠ j) : x j * x i = z * (x i * x j) := by
  calc x j * x i = (x i * x i) * (x j * x i) * (x j * x j) := by
        rw [h.x_sq i, h.x_sq j]; group
    _ = x i * (x i * x j * (x i * x j)) * x j := by group
    _ = z * (x i * x j) := by rw [h.xx i j hij, ← h.zx i]; group

include h in
theorem liftRel : LiftRel (⟨z, hz⟩ : X) (fun j => ⟨x j.succ, hx _⟩) where
  w_sq := Subtype.ext h.z_sq
  w_comm _ := Subtype.ext (h.zx _)
  y_sq _ := Subtype.ext (h.x_sq _)
  anti _ _ hij := Subtype.ext (h.anti ((Fin.succ_injective _).ne hij.ne))

theorem liftHom_x (j : Fin 5) : ((h.liftRel hz hx).liftHom (QM.x j) : G) = x j := by
  rw [LiftRel.liftHom_apply]
  fin_cases j
  · simp [liftT, QM.x, h.x0, mul_assoc]
  all_goals simp [liftT, QM.x]

@[expose] def toVertGens (ha : a ∈ X) (hb : b ∈ X) : VertGens ↥X where
  z := ⟨z, hz⟩
  y j := ⟨x j.succ, hx _⟩
  a := ⟨a, ha⟩
  b := ⟨b, hb⟩
  lift := h.liftRel hz hx
  a_sq := Subtype.ext h.a_sq
  b_cube := Subtype.ext h.b_cube
  ab_five := Subtype.ext (by simpa using h.ab_five)
  za := Subtype.ext h.za
  zb := Subtype.ext h.zb
  ax j := Subtype.ext (by
    show a * ((h.liftRel hz hx).liftHom (QM.x j) : G) * a⁻¹ =
      ((h.liftRel hz hx).liftHom (QM.x (pa j)) : G)
    rw [h.liftHom_x, h.liftHom_x, h.ax])
  bx j := Subtype.ext (by
    show b * ((h.liftRel hz hx).liftHom (QM.x j) : G) * b⁻¹ =
      ((h.liftRel hz hx).liftHom (QM.x (pb j)) : G)
    rw [h.liftHom_x, h.liftHom_x, h.bx])

variable (ha : a ∈ X) (hb : b ∈ X)

theorem chi_x (j : Fin 5) : ((h.toVertGens hz hx ha hb).chi (QM.x j) : G) = x j :=
  h.liftHom_x hz hx j

theorem chi_z' : ((h.toVertGens hz hx ha hb).chi QM.z : G) = z := by
  rw [VertGens.chi_z]
  rfl

theorem map_Q : (h.toVertGens hz hx ha hb).Q.map X.subtype =
    Subgroup.closure {z, x 1, x 2, x 3, x 4} := by
  set g := h.toVertGens hz hx ha hb
  apply le_antisymm
  · rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    have e : (X.subtype (g.chi p) : G) = liftT z (fun j => x j.succ) p 1 := by
      have := map_liftT X.subtype (⟨z, hz⟩ : X) (fun j => ⟨x j.succ, hx _⟩) p 1
      rw [map_one] at this
      exact this
    rw [e]
    refine VertGens.liftT_mem' (Subgroup.subset_closure (by simp)) (fun j => ?_) p
    apply Subgroup.subset_closure
    fin_cases j <;> simp
  · rw [Subgroup.closure_le]
    have hmem : ∀ q : QM, (g.chi q : G) ∈ g.Q.map X.subtype := fun q =>
      Subgroup.mem_map.mpr ⟨g.chi q, ⟨q, rfl⟩, rfl⟩
    rintro _ (rfl | rfl | rfl | rfl | rfl)
    · rw [← h.chi_z' hz hx ha hb]; exact hmem _
    · rw [← h.chi_x hz hx ha hb 1]; exact hmem _
    · rw [← h.chi_x hz hx ha hb 2]; exact hmem _
    · rw [← h.chi_x hz hx ha hb 3]; exact hmem _
    · rw [← h.chi_x hz hx ha hb 4]; exact hmem _

theorem map_L : (h.toVertGens hz hx ha hb).L.map X.subtype = Subgroup.closure {a, b} := by
  rw [VertGens.L, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem chi_injective (hz1 : z ≠ 1) : Function.Injective (h.toVertGens hz hx ha hb).chi :=
  VertGens.chi_injective _ fun e => hz1 (congrArg Subtype.val e)

end VertRel

end CFSG.Quasithin.Background.Harris.R1.J2Vert
