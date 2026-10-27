module

public import CFSG.LocalAnalysis.StandardType.GGForkAffineFalse
public import CFSG.LocalAnalysis.StandardType.GGForkNullPos

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Cells

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}

theorem ggAffineE6_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan (CartanMatrix.E 6) 1)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![1, 2, 2, 3, 2, 1] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 1, some 3, some 2, some 0, some 4, some 3, some 1, some 2, some 3, some 4])
    (by decide) (j₁ := some 5) (by decide) (by decide +kernel)

theorem ggAffineE7_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan (CartanMatrix.E 7) 0)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![2, 2, 3, 4, 3, 2, 1] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 0, some 2, some 3, some 1, some 4, some 3, some 2, some 0, some 5, some 4, some 3,
        some 1, some 2, some 3, some 4, some 5])
    (by decide) (j₁ := some 6) (by decide) (by decide +kernel)

theorem ggAffineE8_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan (CartanMatrix.E 8) 7)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![2, 3, 4, 6, 5, 4, 3, 2] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 7, some 6, some 5, some 4, some 3, some 1, some 2, some 0, some 3, some 2, some 4,
        some 3, some 1, some 5, some 4, some 3, some 2, some 0, some 6, some 5, some 4, some 3,
        some 1, some 2, some 3, some 4, some 5, some 6])
    (by decide) (j₁ := some 7) (by decide) (by decide +kernel)

theorem ggAffineD8_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan (CartanMatrix.D 8) 7)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 2 | some i => ![1, 2, 3, 4, 5, 6, 3, 4] i)
    (by decide +kernel) (j₀ := some 0) (by decide)
    (w := [some 1, some 2, some 3, some 4, some 5, some 6, some 7, none, some 5, some 4, some 3,
        some 2, some 1, some 7, some 5, some 4, some 3, some 2, some 6, some 5, some 4, some 3,
        some 7, none, some 5, some 4, some 6, some 5])
    (by decide) (j₁ := some 7) (by decide) (by decide +kernel)

theorem ggAffineF4a_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan CartanMatrix.F₄ 0)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![2, 3, 4, 2] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 0, some 1, some 2, some 1, some 0, some 3, some 2])
    (by decide) (j₁ := some 1) (by decide) (by decide +kernel)

theorem ggAffineF4b_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan CartanMatrix.F₄ 3)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![1, 2, 3, 2] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 3, some 2, some 1, some 0, some 2, some 1, some 2])
    (by decide) (j₁ := some 3) (by decide) (by decide +kernel)

theorem ggAffineF4Ta_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan (Matrix.transpose CartanMatrix.F₄) 0)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![2, 3, 2, 1] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 0, some 1, some 2, some 1, some 0, some 3, some 2])
    (by decide) (j₁ := some 1) (by decide) (by decide +kernel)

theorem ggAffineF4Tb_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (D : GGReflDatum p ι (ggAttachCartan (Matrix.transpose CartanMatrix.F₄) 3)) : False :=
  ggAffine_false hp2 hNT D (n := fun | none => 1 | some i => ![2, 4, 3, 2] i)
    (by decide +kernel) (j₀ := none) (by decide)
    (w := [some 3, some 2, some 1, some 0, some 2, some 1, some 2])
    (by decide) (j₁ := some 3) (by decide) (by decide +kernel)

private def ggReflDatum_transport {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ} {b : Λ} (D : GGReflDatum p ι (ggAttachCartan C b))
    {m : ℕ} {C₀ : Matrix (Fin m) (Fin m) ℤ} {k : Fin m}
    (e : Fin m ≃ Λ) (hC : ∀ i j, C (e i) (e j) = C₀ i j) (hb : b = e k) :
    GGReflDatum p ι (ggAttachCartan C₀ k) :=
  (ggAttachCartan_submatrix_optionCongr e hC hb) ▸ D.comap (Equiv.optionCongr e)

theorem ggForkAffineCell_false (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b : Λ}
    (D : GGReflDatum p ι (ggAttachCartan C b)) (h : GGForkAffineCell C b) : False := by
  rcases h with ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ |
    ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩ | ⟨e, hC, hb⟩
  · exact ggAffineE6_false hp2 hNT (ggReflDatum_transport D e hC hb)
  · exact ggAffineE7_false hp2 hNT (ggReflDatum_transport D e hC hb)
  · exact ggAffineE8_false hp2 hNT (ggReflDatum_transport D e hC hb)
  · exact ggAffineD8_false hp2 hNT (ggReflDatum_transport D e hC hb)
  · exact ggAffineF4a_false hp2 hNT (ggReflDatum_transport D e hC hb)
  · exact ggAffineF4b_false hp2 hNT (ggReflDatum_transport D e hC hb)
  · have hC' : ∀ i j, C (e i) (e j) = (Matrix.transpose CartanMatrix.F₄) i j :=
      fun i j => hC i j
    exact ggAffineF4Ta_false hp2 hNT (ggReflDatum_transport D e hC' hb)
  · have hC' : ∀ i j, C (e i) (e j) = (Matrix.transpose CartanMatrix.F₄) i j :=
      fun i j => hC i j
    exact ggAffineF4Tb_false hp2 hNT (ggReflDatum_transport D e hC' hb)

end Cells

end CFSG.StandardType
