module

public import CFSG.Quasithin.Background.F918W8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.D35ValChk

open Matrix

private def mat (g : G0) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))

private theorem mat_inj {g h : G0} (e : mat g = mat h) : g = h :=
  Subtype.ext (Units.ext e)

private theorem conj_cancel {A B X Y : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : B * A = 1)
    (e : A * X * B = A * Y * B) : X = Y := by
  calc X = (B * A) * X * (B * A) := by rw [h, Matrix.one_mul, Matrix.mul_one]
    _ = B * (A * X * B) * A := by simp only [Matrix.mul_assoc]
    _ = B * (A * Y * B) * A := by rw [e]
    _ = (B * A) * Y * (B * A) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [h, Matrix.one_mul, Matrix.mul_one]

private theorem closure_gens_eq_top (r1 r2 r3 : G0)
    (h1 : mat r1 = toM (expand u0)) (h2 : mat r2 = toM (expand a0)) (h3 : mat r3 = toM (expand b0)) :
    Subgroup.closure ({r1, r2, r3} : Set G0) = ⊤ := by
  have hle : Subgroup.closure (((↑) : G0 → Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) ⁻¹'
      {g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) | ∃ i, i < 3 ∧
        ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
          toM (expand (genK i))}) ≤ Subgroup.closure ({r1, r2, r3} : Set G0) := by
    apply Subgroup.closure_mono
    rintro g ⟨i, hi, hg⟩
    have hg' : mat g = toM (expand (genK i)) := hg
    interval_cases i
    · exact Or.inl (mat_inj (hg'.trans h1.symm))
    · exact Or.inr (Or.inl (mat_inj (hg'.trans h2.symm)))
    · exact Or.inr (Or.inr (mat_inj (hg'.trans h3.symm)))
  have := Subgroup.closure_closure_coe_preimage (k := {g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) |
    ∃ i, i < 3 ∧ ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      toM (expand (genK i))})
  rw [eq_top_iff]
  intro g _
  exact hle (this ▸ Subgroup.mem_top g)

theorem core0_ref (hF : D35Facts)
    (α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)) (E F : Subgroup G0)
    (hE : ∀ h : G0, h ∈ E ↔ h ∈ V4set e1 e2) (hF' : OffF2 F)
    (hα : (E.map (QuotientGroup.mk' (Subgroup.center G0))).map α.toMonoidHom =
      F.map (QuotientGroup.mk' (Subgroup.center G0))) :
    ∃ (β : G0 ≃* G0) (P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)), P * Q = 1 ∧ Q * P = 1 ∧
      (∀ g : G0, QuotientGroup.mk' (Subgroup.center G0) (β g) = α (QuotientGroup.mk' (Subgroup.center G0) g)) ∧
      ∀ g : G0,
        P * (((g : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
          (((β g : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * P := by
  obtain ⟨r1, h1⟩ := exists_G0 hF hF.gl_mem.2.1
  obtain ⟨r2, h2⟩ := exists_G0 hF hF.gl_mem.2.2.1
  obtain ⟨r3, h3⟩ := exists_G0 hF hF.gl_mem.2.2.2
  obtain ⟨x1, x2, x3, P, Q, hPQ, hQP, hm1, hm2, hm3, c1, c2, c3⟩ :=
    exists_triple_data hF r1 r2 r3 h1 h2 h3 α E F hE hF' hα
  have htop := closure_gens_eq_top r1 r2 r3 h1 h2 h3
  let Pu : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) := ⟨P, Q, hPQ, hQP⟩
  let cj : G0 →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) :=
    (MulAut.conj Pu).toMonoidHom.comp G0.subtype
  have hcj : ∀ g : G0, ((cj g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      P * mat g * Q := fun g => rfl
  have hgen : ∀ (r x : G0), P * mat r = mat x * P → cj r = (x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :=
    fun r x h => Units.ext (by
      rw [hcj, h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
      rfl)
  have hgen1 := hgen r1 x1 c1
  have hgen2 := hgen r2 x2 c2
  have hgen3 := hgen r3 x3 c3
  have hT : ∀ g : G0, cj g ∈ G0 := by
    have : Subgroup.comap cj G0 = ⊤ := by
      rw [eq_top_iff, ← htop, Subgroup.closure_le]
      rintro g (rfl | rfl | rfl)
      · show cj g ∈ G0
        rw [hgen1]
        exact x1.2
      · show cj g ∈ G0
        rw [hgen2]
        exact x2.2
      · show cj g ∈ G0
        rw [hgen3]
        exact x3.2
    intro g
    have hg : g ∈ Subgroup.comap cj G0 := by
      rw [this]
      trivial
    exact hg
  let β0 : G0 →* G0 := cj.codRestrict G0 hT
  have hβmat : ∀ g, mat (β0 g) = P * mat g * Q := fun g => rfl
  have hinj : Function.Injective β0 := by
    intro g h e
    apply mat_inj
    have := congrArg mat e
    rw [hβmat, hβmat] at this
    exact conj_cancel hQP this
  have hbij : Function.Bijective β0 := Finite.injective_iff_bijective.mp hinj
  refine ⟨MulEquiv.ofBijective β0 hbij, P, Q, hPQ, hQP, ?_, ?_⟩
  · have hgens : Set.EqOn ((QuotientGroup.mk' (Subgroup.center G0)).comp β0)
        (α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G0))) ({r1, r2, r3} : Set G0) := by
      rintro g (rfl | rfl | rfl)
      · show QuotientGroup.mk (β0 g) = α (QuotientGroup.mk g)
        rw [show β0 g = x1 from Subtype.ext hgen1]
        exact hm1
      · show QuotientGroup.mk (β0 g) = α (QuotientGroup.mk g)
        rw [show β0 g = x2 from Subtype.ext hgen2]
        exact hm2
      · show QuotientGroup.mk (β0 g) = α (QuotientGroup.mk g)
        rw [show β0 g = x3 from Subtype.ext hgen3]
        exact hm3
    have := MonoidHom.eqOn_closure hgens
    rw [htop] at this
    exact fun g => this (Subgroup.mem_top g)
  · intro g
    show P * mat g = mat (β0 g) * P
    rw [hβmat, Matrix.mul_assoc, hQP, Matrix.mul_one]

end CFSG.Quasithin.D35ValChk
