module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Family
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private def s16e_d5_pfixSub (S : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ z ∈ S, g z = z}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh z hz
    rw [MulAut.mul_apply, hh z hz, hg z hz]
  inv_mem' := by
    intro g hg z hz
    refine g.injective ?_
    simpa [hg z hz]

theorem s16e_d5_conj_zpowers (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W))) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) {i j : Fin 4} {g : MulAut W} (hgA : g ∈ A)
    (hgj : (Z i).map g.toMonoidHom = Z j) :
    (Subgroup.zpowers (a i)).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (a j) := by
  obtain ⟨hyA, hyC, hy1, hyoff⟩ :=
    s16e_d5_axis_conj hfr hLn (hfam.mem_A i) (hfam.mem_cent i) (hfam.ne_one i)
      (hfam.off i) hgA hgj
  have hle : Subgroup.zpowers (g * a i * g⁻¹) ≤ Subgroup.zpowers (a j) :=
    Subgroup.zpowers_le.mpr
      (s16e_d5_line (i := j) hfr (hfam.mem_cent j) hyC (hfam.off j) hyoff (hfam.ne_one j))
  have hge : Subgroup.zpowers (a j) ≤ Subgroup.zpowers (g * a i * g⁻¹) :=
    Subgroup.zpowers_le.mpr
      (s16e_d5_line (i := j) hfr hyC (hfam.mem_cent j) hyoff (hfam.off j) hy1)
  have heq : Subgroup.zpowers (g * a i * g⁻¹) = Subgroup.zpowers (a j) :=
    le_antisymm hle hge
  rw [MonoidHom.map_zpowers]
  have hy : (MulAut.conj g).toMonoidHom (a i) = g * a i * g⁻¹ := rfl
  rw [hy, heq]

theorem s16e_d5_zpowers_inj (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    {a : Fin 4 → MulAut W} (hfam : s16e_d5_CoordFam A L Z a) :
    Function.Injective fun j => Subgroup.zpowers (a j) := by
  intro j k hjk
  by_contra hne
  have hjk' : Subgroup.zpowers (a j) = Subgroup.zpowers (a k) := by simpa using hjk
  have hoff : ∀ z ∈ Z j, a k z = z := hfam.off k j hne
  have hle : Subgroup.zpowers (a k) ≤ s16e_d5_pfixSub (Z j) :=
    Subgroup.zpowers_le.mpr hoff
  have haj : a j ∈ Subgroup.zpowers (a k) := by
    rw [← hjk']
    exact Subgroup.mem_zpowers (a j)
  have hfixj : ∀ z ∈ Z j, a j z = z := hle haj
  refine hfr.Z_ne_bot j ?_
  rw [eq_bot_iff]
  intro z hz
  exact s16e_d5_cent_fix hfr (hfam.mem_cent j) (hfam.off j) (hfam.ne_one j) hz (hfixj z hz)

theorem s16e_d5_conj_blocks (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) (i : Fin 4) :
    conjSubs A (commSub ⊤ (Subgroup.zpowers (a i))) = Set.range Z := by
  rw [s16e_d5_commSub_zpowers hfr (hfam.mem_cent i) (hfam.off i) (hfam.ne_one i)]
  ext X
  constructor
  · rintro ⟨g, hgA, rfl⟩
    obtain ⟨j, hj⟩ := hfr.perm (hLn g hgA) i
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨g, hgA, hg⟩ := htr i j
    exact ⟨g, hgA, hg.symm⟩

theorem s16e_d5_conj_set (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) (i : Fin 4) :
    {X : Subgroup (MulAut W) |
      ∃ φ ∈ A, X = (Subgroup.zpowers (a i)).map (MulAut.conj φ).toMonoidHom} =
        Set.range fun j => Subgroup.zpowers (a j) := by
  ext X
  constructor
  · rintro ⟨g, hgA, rfl⟩
    obtain ⟨j, hj⟩ := hfr.perm (hLn g hgA) i
    exact ⟨j, (s16e_d5_conj_zpowers hfr hLn hfam hgA hj).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨g, hgA, hg⟩ := htr i j
    exact ⟨g, hgA, (s16e_d5_conj_zpowers hfr hLn hfam hgA hg).symm⟩

theorem s16e_d5_conj_card (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) (i : Fin 4) :
    Set.ncard {X : Subgroup (MulAut W) |
      ∃ φ ∈ A, X = (Subgroup.zpowers (a i)).map (MulAut.conj φ).toMonoidHom} = 4 := by
  rw [s16e_d5_conj_set hfr hLn htr hfam i,
    Set.ncard_range_of_injective (s16e_d5_zpowers_inj hfr hfam)]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
