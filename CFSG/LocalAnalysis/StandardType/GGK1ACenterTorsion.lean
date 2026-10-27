module

public import CFSG.LocalAnalysis.StandardType.GGK1AGlEnd
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraCenter
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary

noncomputable def commutantCenterEquivPi {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hx : Squarefree (minpoly K x)) :
    Subring.center (commutant x) ≃+* ((a : primaryFactors x) → AdjoinRoot (a : K[X])) :=
  (Subring.centerCongr (commutantEquivMatrix hx)).trans
    ((_root_.CFSG.RankThree.PartOne.scalarCenterEquiv
      (fun a : primaryFactors x => AdjoinRoot (a : K[X]))
      (fun a : primaryFactors x => primaryMultiplicity x (a : K[X]))
      (KCUnitaryModel.primaryMultiplicity_pos hx)).symm)

noncomputable def commutantCenterUnitsEquivPi {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hx : Squarefree (minpoly K x)) :
    (Subring.center (commutant x))ˣ ≃* ((a : primaryFactors x) → (AdjoinRoot (a : K[X]))ˣ) :=
  (Units.mapEquiv (commutantCenterEquivPi hx).toMulEquiv).trans MulEquiv.piUnits

noncomputable def commutantCenterTorsion {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (x : Module.End K V) (p : ℕ) :
    Subgroup ((Subring.center (commutant x))ˣ) where
  carrier := {z | z ^ p = 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    rw [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

theorem mem_commutantCenterTorsion {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} {p : ℕ}
    {z : (Subring.center (commutant x))ˣ} :
    z ∈ commutantCenterTorsion x p ↔ z ^ p = 1 := Iff.rfl

theorem commutantCenterTorsion_map_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} (hx : Squarefree (minpoly K x)) (p : ℕ) :
    (commutantCenterTorsion x p).map (commutantCenterUnitsEquivPi hx).toMonoidHom =
      Subgroup.pi Set.univ (fun a : primaryFactors x =>
        rootsOfUnity p (AdjoinRoot (a : K[X]))) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_pi]
    intro a
    rw [mem_rootsOfUnity]
    have h1 : ((commutantCenterUnitsEquivPi hx) z) ^ p = 1 := by
      rw [← map_pow, mem_commutantCenterTorsion.mp hz, map_one]
    simpa using congrFun h1 a
  · intro hy
    refine ⟨(commutantCenterUnitsEquivPi hx).symm y, ?_, by simp⟩
    rw [mem_commutantCenterTorsion]
    apply (commutantCenterUnitsEquivPi hx).injective
    rw [map_pow, map_one, (commutantCenterUnitsEquivPi hx).apply_symm_apply]
    rw [Subgroup.mem_pi] at hy
    funext a
    simpa using (mem_rootsOfUnity p _).mp (hy a (Set.mem_univ a))

private theorem card_subgroup_pi {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V}
    (H : (a : primaryFactors x) → Subgroup ((AdjoinRoot (a : K[X]))ˣ)) :
    Nat.card (Subgroup.pi Set.univ H) = ∏ a : primaryFactors x, Nat.card (H a) := by
  let e : ↥(Subgroup.pi Set.univ H) ≃ ((a : primaryFactors x) → ↥(H a)) :=
    { toFun := fun f a => ⟨f.1 a, (Subgroup.mem_pi Set.univ).mp f.2 a (Set.mem_univ a)⟩
      invFun := fun g => ⟨fun a => (g a : _), by
        rw [Subgroup.mem_pi]
        intro a _
        exact (g a).2⟩
      left_inv := fun f => by ext a; rfl
      right_inv := fun g => by ext a; rfl }
  rw [Nat.card_congr e, Nat.card_pi]

theorem card_commutantCenterTorsion {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} (hx : Squarefree (minpoly K x)) (p : ℕ) :
    Nat.card (commutantCenterTorsion x p) =
      ∏ a : primaryFactors x, Nat.card (rootsOfUnity p (AdjoinRoot (a : K[X]))) := by
  rw [← Subgroup.card_map_of_injective (f := (commutantCenterUnitsEquivPi hx).toMonoidHom)
    (commutantCenterUnitsEquivPi hx).injective, commutantCenterTorsion_map_eq hx p]
  exact card_subgroup_pi _

theorem card_commutantCenterTorsion_eq_prod_gcd {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} [Finite K]
    (hx : Squarefree (minpoly K x)) {p : ℕ} (hp : 0 < p) :
    Nat.card (commutantCenterTorsion x p) =
      ∏ a : primaryFactors x, Nat.gcd p (Nat.card (AdjoinRoot (a : K[X])) - 1) := by
  rw [card_commutantCenterTorsion hx p]
  refine Finset.prod_congr rfl fun a _ => ?_
  have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  have : Module.Finite K (AdjoinRoot (a : K[X])) :=
    (monic_of_mem_primaryFactors a.2).finite_adjoinRoot
  have : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  exact _root_.CFSG.RankThree.PartOne.card_rootsOfUnity_finite_field hp


@[expose] noncomputable def ggK1A_torsGL {N : ℕ} {K : Type} [Field K] (g : GL (Fin N) K)
    (p : ℕ) : Subgroup (GL (Fin N) K) :=
  (commutantCenterTorsion (ggK1A_glEnd g) p).map
    (KCLinComm.centerUnitsToGL (ggK1A_glEnd g))

theorem ggK1A_glEnd_commutantUnitsToGL {N : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin N → K)) (u : (commutant x)ˣ) :
    ggK1A_glEnd (KCLinComm.commutantUnitsToGL x u) = (u : commutant x) := by
  rw [ggK1A_glEnd, KCLinComm.coe_commutantUnitsToGL,
    ← KCLinComm.toLinAlgEquiv'_eq_toLin']
  simp [KCLinComm.commutantToMat]

theorem ggK1A_glEnd_centerUnitsToGL {N : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin N → K)) (z : (Subring.center (commutant x))ˣ) :
    ggK1A_glEnd (KCLinComm.centerUnitsToGL x z) =
      (((z : Subring.center (commutant x)) : commutant x) : Module.End K (Fin N → K)) := by
  rw [KCLinComm.centerUnitsToGL, MonoidHom.comp_apply]
  rw [ggK1A_glEnd_commutantUnitsToGL, KCLinComm.coe_centerUnitsToUnits]

private theorem cenT_mem_ggK1A_torsGL_of_central {N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {p : ℕ} {t : GL (Fin N) K} (htp : t ^ p = 1)
    (hcomm : ∀ y : Module.End K (Fin N → K), Commute y (ggK1A_glEnd g) →
      Commute y (ggK1A_glEnd t)) :
    t ∈ ggK1A_torsGL g p := by
  let x := ggK1A_glEnd g
  let T := ggK1A_glEnd t
  let T' := ggK1A_glEnd t⁻¹
  have hcomm' : ∀ y : Module.End K (Fin N → K), Commute y x → Commute y T := hcomm
  have hTx : Commute T x := (hcomm' x (Commute.refl x)).symm
  have hT'_mul : T * T' = 1 := by
    show ggK1A_glEnd t * ggK1A_glEnd t⁻¹ = 1
    rw [← ggK1A_glEnd_mul, mul_inv_cancel, ggK1A_glEnd_one]
  have hT'_mul' : T' * T = 1 := by
    show ggK1A_glEnd t⁻¹ * ggK1A_glEnd t = 1
    rw [← ggK1A_glEnd_mul, inv_mul_cancel, ggK1A_glEnd_one]
  let Tu : (Module.End K (Fin N → K))ˣ := ⟨T, T', hT'_mul, hT'_mul'⟩
  have hTx' : Commute T' x :=
    (Commute.units_inv_right (u := Tu) (hcomm' x (Commute.refl x))).symm
  let a : commutant x := ⟨T, (mem_commutant x).mpr hTx⟩
  let b : commutant x := ⟨T', (mem_commutant x).mpr hTx'⟩
  have ha : a ∈ Subring.center (commutant x) := by
    rw [Subring.mem_center_iff]
    intro u
    apply Subtype.ext
    exact (hcomm' (u : Module.End K (Fin N → K)) ((mem_commutant x).mp u.2)).eq
  have hb : b ∈ Subring.center (commutant x) := by
    rw [Subring.mem_center_iff]
    intro u
    apply Subtype.ext
    exact (Commute.units_inv_right (u := Tu)
      (hcomm' (u : Module.End K (Fin N → K)) ((mem_commutant x).mp u.2))).eq
  let z : (Subring.center (commutant x))ˣ :=
    ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      apply Subtype.ext
      apply Subtype.ext
      show T * T' = 1
      exact hT'_mul, by
      apply Subtype.ext
      apply Subtype.ext
      show T' * T = 1
      exact hT'_mul'⟩
  have hz_eq : KCLinComm.centerUnitsToGL x z = t := by
    refine ggK1A_glEnd_injective ?_
    rw [ggK1A_glEnd_centerUnitsToGL]
  have hzp : z ^ p = 1 := by
    refine KCLinComm.centerUnitsToGL_injective x ?_
    rw [map_pow, hz_eq, htp, map_one]
  rw [ggK1A_torsGL, Subgroup.mem_map]
  exact ⟨z, mem_commutantCenterTorsion.mpr hzp, hz_eq⟩

private theorem cenT_center_commute {N : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin N → K)) (z : (Subring.center (commutant x))ˣ)
    (y : commutant x) :
    Commute (y : Module.End K (Fin N → K))
      (((z : Subring.center (commutant x)) : commutant x) :
        Module.End K (Fin N → K)) := by
  have h := Subring.mem_center_iff.mp (z : Subring.center (commutant x)).2 y
  exact congrArg Subtype.val h

theorem squarefree_minpoly_ggK1A_glEnd {p N : ℕ} {K : Type} [Field K] (hpK : (p : K) ≠ 0)
    {x : GL (Fin N) K} (hxp : x ^ p = 1) : Squarefree (minpoly K (ggK1A_glEnd x)) := by
  refine CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one hpK ?_
  rw [← ggK1A_glEnd_pow, hxp, ggK1A_glEnd_one]

theorem mem_ggK1A_torsGL_iff {N : ℕ} {K : Type} [Field K] {g : GL (Fin N) K} {p : ℕ}
    {t : GL (Fin N) K} :
    t ∈ ggK1A_torsGL g p ↔ t ^ p = 1 ∧
      ∀ y : Module.End K (Fin N → K), Commute y (ggK1A_glEnd g) →
        Commute y (ggK1A_glEnd t) := by
  constructor
  · intro ht
    rw [ggK1A_torsGL, Subgroup.mem_map] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    refine ⟨?_, ?_⟩
    · rw [← map_pow, mem_commutantCenterTorsion.mp hz, map_one]
    · intro y hy
      rw [ggK1A_glEnd_centerUnitsToGL]
      exact cenT_center_commute (ggK1A_glEnd g) z
        ⟨y, (mem_commutant (ggK1A_glEnd g)).mpr hy⟩
  · rintro ⟨htp, hcomm⟩
    exact cenT_mem_ggK1A_torsGL_of_central htp hcomm

private theorem cenT_commute_of_mem_ggK1A_torsGL {N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {p : ℕ} {t : GL (Fin N) K} (ht : t ∈ ggK1A_torsGL g p) :
    Commute t g := by
  have h := (mem_ggK1A_torsGL_iff.mp ht).2 (ggK1A_glEnd g) (Commute.refl _)
  apply ggK1A_glEnd_injective
  show ggK1A_glEnd (t * g) = ggK1A_glEnd (g * t)
  rw [ggK1A_glEnd_mul, ggK1A_glEnd_mul]
  exact h.eq.symm

theorem commute_of_mem_ggK1A_torsGL {N : ℕ} {K : Type} [Field K] {g : GL (Fin N) K} {p : ℕ}
    {t : GL (Fin N) K} (ht : t ∈ ggK1A_torsGL g p) {A : GL (Fin N) K} (hA : Commute A g) :
    Commute A t := by
  have hAy : Commute (ggK1A_glEnd A) (ggK1A_glEnd g) := by
    show ggK1A_glEnd A * ggK1A_glEnd g = ggK1A_glEnd g * ggK1A_glEnd A
    rw [← ggK1A_glEnd_mul, ← ggK1A_glEnd_mul, hA.eq]
  have hAt := (mem_ggK1A_torsGL_iff.mp ht).2 (ggK1A_glEnd A) hAy
  apply ggK1A_glEnd_injective
  show ggK1A_glEnd (A * t) = ggK1A_glEnd (t * A)
  rw [ggK1A_glEnd_mul, ggK1A_glEnd_mul]
  exact hAt.eq

theorem isElemAbelian_of_le_ggK1A_torsGL {N : ℕ} {K : Type} [Field K] {g : GL (Fin N) K}
    {p : ℕ} {T : Subgroup (GL (Fin N) K)} (hT : T ≤ ggK1A_torsGL g p) : IsElemAbelian p T := by
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => ?_
    have hcomm : Commute (b : GL (Fin N) K) g :=
      cenT_commute_of_mem_ggK1A_torsGL (hT b.2)
    have hba : Commute (b : GL (Fin N) K) (a : GL (Fin N) K) :=
      commute_of_mem_ggK1A_torsGL (hT a.2) hcomm
    exact Subtype.ext hba.eq.symm
  · intro x hx
    exact (mem_ggK1A_torsGL_iff.mp (hT hx)).1

theorem scalar_mem_ggK1A_torsGL {N : ℕ} {K : Type} [Field K] (g : GL (Fin N) K) {p : ℕ}
    {c : Kˣ} (hc : c ^ p = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin N) c ∈ ggK1A_torsGL g p := by
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
    (KCLinComm.scalar_mem_range_centerUnitsToGL (ggK1A_glEnd g) c)
  have hzp : z ^ p = 1 := by
    refine KCLinComm.centerUnitsToGL_injective (ggK1A_glEnd g) ?_
    rw [map_pow, hz, ← map_pow, hc]
    simp
  rw [ggK1A_torsGL]
  exact Subgroup.mem_map.mpr ⟨z, mem_commutantCenterTorsion.mpr hzp, hz⟩

theorem card_ggK1A_torsGL {N : ℕ} {K : Type} [Field K] [Finite K] {g : GL (Fin N) K} {p : ℕ}
    (hp : 0 < p) (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    Nat.card (ggK1A_torsGL g p) =
      ∏ a : primaryFactors (ggK1A_glEnd g), Nat.gcd p (Nat.card (AdjoinRoot (a : K[X])) - 1) := by
  rw [ggK1A_torsGL,
    Subgroup.card_map_of_injective (f := KCLinComm.centerUnitsToGL (ggK1A_glEnd g))
      (KCLinComm.centerUnitsToGL_injective (ggK1A_glEnd g))]
  exact card_commutantCenterTorsion_eq_prod_gcd hsq hp

end CFSG.StandardType

end
