module

public import CFSG.GH74.BNPair.Geometry
public import CFSG.Quasithin.Background.F3Paths

public section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.Quasithin

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

abbrev V : Type _ := D.Vertex

instance : MulAction X (V D) where
  smul g u := D.action g u
  one_smul u := by
    show D.action 1 u = u
    rw [map_one]
    rfl
  mul_smul g h u := by
    show D.action (g * h) u = D.action g (D.action h u)
    rw [map_mul]
    rfl

abbrev Γ : SimpleGraph (V D) := D.graph

@[expose] def v (i : Bool) : V D :=
  cond i D.vertex₁ D.vertex₂

variable {D}

@[expose] def vt (D : RankTwoSystem X n) (i : Bool) (x : X) : V D :=
  vtx D.B D.N D.w₁ D.w₂ i x

theorem smul_vt (g : X) (i : Bool) (x : X) : g • vt D i x = vt D i (x * g⁻¹) :=
  rankTwoAction_vtx g i x

theorem v_eq_vt (i : Bool) : v D i = vt D i 1 := by
  cases i <;> rfl

theorem vt_eq_vt_iff (i : Bool) (x z : X) :
    vt D i z = vt D i x ↔ z * x⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i := by
  refine ⟨fun h => ?_, vtx_eq_vtx⟩
  have : z ∈ ((vtx D.B D.N D.w₁ D.w₂ i x : rankTwoVertices D.B D.N D.w₁ D.w₂) : Set X) := by
    rw [← show vtx D.B D.N D.w₁ D.w₂ i z = vtx D.B D.N D.w₁ D.w₂ i x from h]
    exact mem_self_vtx
  exact mem_vtx.1 this

theorem vt_ne_of_ne (i j : Bool) (hij : i ≠ j) (x z : X) : vt D i x ≠ vt D j z :=
  fun h => hij (D.rank2.vtx_type_eq h)

theorem pgen_true : pgen D.B D.N D.w₁ D.w₂ true = D.P₁ := rfl

theorem pgen_false : pgen D.B D.N D.w₁ D.w₂ false = D.P₂ := rfl

theorem smul_v_true_eq_iff (y : X) : y • v D true = v D true ↔ y ∈ D.P₁ := by
  rw [v_eq_vt, smul_vt, vt_eq_vt_iff, one_mul, inv_one, mul_one, pgen_true]
  exact ⟨fun h => by simpa using D.P₁.inv_mem h, fun h => D.P₁.inv_mem h⟩

theorem smul_v_false_eq_iff (y : X) : y • v D false = v D false ↔ y ∈ D.P₂ := by
  rw [v_eq_vt, smul_vt, vt_eq_vt_iff, one_mul, inv_one, mul_one, pgen_false]
  exact ⟨fun h => by simpa using D.P₂.inv_mem h, fun h => D.P₂.inv_mem h⟩

variable (D)

theorem stab_v : (∀ y : X, y • v D true = v D true ↔ y ∈ D.P₁) ∧
    (∀ y : X, y • v D false = v D false ↔ y ∈ D.P₂) :=
  ⟨smul_v_true_eq_iff, smul_v_false_eq_iff⟩

theorem stabilizer_v_true : MulAction.stabilizer X (v D true) = D.P₁ :=
  Subgroup.ext fun y => smul_v_true_eq_iff y

theorem stabilizer_v_false : MulAction.stabilizer X (v D false) = D.P₂ :=
  Subgroup.ext fun y => smul_v_false_eq_iff y

theorem disj : ∀ y z : X, y • v D true ≠ z • v D false := by
  intro y z
  rw [v_eq_vt, v_eq_vt, smul_vt, smul_vt]
  exact vt_ne_of_ne true false (by simp) _ _

theorem adj_iff_vtype (a b : V D) :
    (Γ D).Adj a b → vtype D.B D.N D.w₁ D.w₂ a ≠ vtype D.B D.N D.w₁ D.w₂ b :=
  D.rank2.vtype_ne_of_adj

instance : GraphAction X (Γ D) where
  adj_smul g a b := rankTwoAction_adj g a b

theorem noadj_true : ∀ y z : X, ¬ (Γ D).Adj (y • v D true) (z • v D true) := by
  intro y z h
  rw [v_eq_vt, smul_vt, smul_vt] at h
  exact (adj_iff_vtype D _ _ h) (by
    show vtype D.B D.N D.w₁ D.w₂ (vtx D.B D.N D.w₁ D.w₂ true _) =
      vtype D.B D.N D.w₁ D.w₂ (vtx D.B D.N D.w₁ D.w₂ true _)
    rw [D.rank2.vtype_vtx, D.rank2.vtype_vtx])

theorem noadj_false : ∀ y z : X, ¬ (Γ D).Adj (y • v D false) (z • v D false) := by
  intro y z h
  rw [v_eq_vt, smul_vt, smul_vt] at h
  exact (adj_iff_vtype D _ _ h) (by
    show vtype D.B D.N D.w₁ D.w₂ (vtx D.B D.N D.w₁ D.w₂ false _) =
      vtype D.B D.N D.w₁ D.w₂ (vtx D.B D.N D.w₁ D.w₂ false _)
    rw [D.rank2.vtype_vtx, D.rank2.vtype_vtx])

theorem adj_v : (Γ D).Adj (v D true) (v D false) := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    have := disj D 1 1
    rw [one_smul, one_smul] at this
    exact this h
  · exact ⟨1, (D.P₁).one_mem, 1, rfl, one_mul 1⟩
  · exact ⟨1, (D.P₂).one_mem, 1, rfl, one_mul 1⟩

theorem mem_vt_iff {i : Bool} {x z : X} :
    z ∈ ((vt D i x : V D) : Set X) ↔ z * x⁻¹ ∈ pgen D.B D.N D.w₁ D.w₂ i :=
  mem_vtx

theorem vtype_vt (i : Bool) (x : X) : vtype D.B D.N D.w₁ D.w₂ (vt D i x) = i :=
  D.rank2.vtype_vtx i x

theorem flag_true : ∀ b, (Γ D).Adj (v D true) b → ∃ p ∈ D.P₁, p • v D false = b := by
  intro b h
  obtain ⟨-, z, hz1, hz2⟩ := id h
  have hz : z ∈ D.P₁ := by
    rw [v_eq_vt] at hz1
    simpa [mem_vt_iff, pgen_true] using hz1
  refine ⟨z⁻¹, D.P₁.inv_mem hz, ?_⟩
  have ht : vtype D.B D.N D.w₁ D.w₂ (v D true) = true := by rw [v_eq_vt, vtype_vt]
  have e := D.rank2.eq_vtx_not_of_adj h hz2
  rw [ht] at e
  rw [v_eq_vt false, smul_vt, e]
  simp [vt]

theorem flag_false : ∀ b, (Γ D).Adj (v D false) b → ∃ p ∈ D.P₂, p • v D true = b := by
  intro b h
  obtain ⟨-, z, hz1, hz2⟩ := id h
  have hz : z ∈ D.P₂ := by
    rw [v_eq_vt] at hz1
    simpa [mem_vt_iff, pgen_false] using hz1
  refine ⟨z⁻¹, D.P₂.inv_mem hz, ?_⟩
  have ht : vtype D.B D.N D.w₁ D.w₂ (v D false) = false := by rw [v_eq_vt, vtype_vt]
  have e := D.rank2.eq_vtx_not_of_adj h hz2
  rw [ht] at e
  rw [v_eq_vt true, smul_vt, e]
  simp [vt]

theorem adj_v_true_iff {b : V D} : (Γ D).Adj (v D true) b ↔ ∃ p ∈ D.P₁, p • v D false = b := by
  refine ⟨flag_true D b, ?_⟩
  rintro ⟨p, hp, rfl⟩
  have h := (GraphAction.adj_smul (Γ := Γ D) p (v D true) (v D false)).2 (adj_v D)
  rwa [(smul_v_true_eq_iff p).2 hp] at h

end CFSG.Quasithin.H13.F431.BN
