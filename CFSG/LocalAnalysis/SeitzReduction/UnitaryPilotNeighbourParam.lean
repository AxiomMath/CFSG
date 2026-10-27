module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFactSwap
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)

section GraphField

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def barRingEquiv : K ≃+* K :=
  RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)

theorem barRingEquiv_apply (c : K) : barRingEquiv h c = h.bar c :=
  rfl

theorem barRingEquiv_mul_self : barRingEquiv h * barRingEquiv h = 1 :=
  RingEquiv.ext fun c => h.bar_bar c

theorem commute_barRingEquiv (φ : K ≃+* K) : Commute (barRingEquiv h) φ :=
  RingEquiv.ext fun c => by
    change h.bar (φ c) = φ (h.bar c)
    rw [h.bar_apply, h.bar_apply, map_pow]

variable (n : ℕ)

@[expose] noncomputable def barSL : MulAut (SpecialLinearGroup (Fin n) K) :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map (barRingEquiv h).toRingHom)
    (SpecialLinearGroup.map (barRingEquiv h).symm.toRingHom) (by ext x i j; simp)
    (by ext x i j; simp)

@[expose] noncomputable def graphFieldSL : MulAut (SpecialLinearGroup (Fin n) K) :=
  barSL h n * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n K

theorem graphFieldSL_apply (x : SpecialLinearGroup (Fin n) K) :
    graphFieldSL h n x = SpecialLinearGroup.map (barRingEquiv h).toRingHom (x⁻¹).transpose :=
  rfl

theorem coe_graphFieldSL (x : SpecialLinearGroup (Fin n) K) :
    ((graphFieldSL h n x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map h.bar :=
  rfl

variable {n}

theorem graphFieldSL_graphFieldSL (x : SpecialLinearGroup (Fin n) K) :
    graphFieldSL h n (graphFieldSL h n x) = x := by
  have hinv : (graphFieldSL h n x)⁻¹ = graphFieldSL h n x⁻¹ := (map_inv _ x).symm
  rw [graphFieldSL_apply h n (graphFieldSL h n x), hinv, graphFieldSL_apply, inv_inv]
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    SpecialLinearGroup.coe_transpose, transpose_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, barRingEquiv_apply, h.bar_bar]

theorem graphFieldSL_toSL (A : unitarySU p f K n) : graphFieldSL h n (toSL h n A) = toSL h n A := by
  have hu : ((((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := unitary_toSL h A
  have hinv : (((toSL h n A)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((((toSL h n A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ := by
    rw [← map_inv, coe_toSL, coe_toSL, Subgroup.coe_inv, Matrix.coe_units_inv,
      Matrix.inv_eq_left_inv hu]
  ext i j
  rw [coe_graphFieldSL, hinv, transpose_transpose, Matrix.map_map]
  simp [h.bar_bar]

theorem graphFieldSL_mem_blockSpecialLinear {N : Finset (Fin n)}
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ blockSpecialLinear N) :
    graphFieldSL h n x ∈ blockSpecialLinear N := by
  intro i j hij
  have h1 : ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) j i =
      (1 : Matrix (Fin n) (Fin n) K) j i := inv_mem hx j i hij.symm
  rw [coe_graphFieldSL, Matrix.map_apply, transpose_apply, h1, Matrix.one_apply,
    Matrix.one_apply]
  by_cases hji : j = i
  · subst hji
    simp [h.bar_apply]
  · simp [hji, Ne.symm hji]

@[expose] noncomputable def graphFieldBlock (N : Finset (Fin n)) :
    MulAut (blockSpecialLinear (K := K) N) where
  toFun x := ⟨graphFieldSL h n x, graphFieldSL_mem_blockSpecialLinear h x.2⟩
  invFun x := ⟨graphFieldSL h n x, graphFieldSL_mem_blockSpecialLinear h x.2⟩
  left_inv x := Subtype.ext (graphFieldSL_graphFieldSL h (x : SpecialLinearGroup (Fin n) K))
  right_inv x := Subtype.ext (graphFieldSL_graphFieldSL h (x : SpecialLinearGroup (Fin n) K))
  map_mul' x y := Subtype.ext (map_mul (graphFieldSL h n) (x : SpecialLinearGroup (Fin n) K) y)

theorem coe_graphFieldBlock_apply (N : Finset (Fin n)) (x : blockSpecialLinear (K := K) N) :
    ((graphFieldBlock h N x : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) =
      graphFieldSL h n x :=
  rfl

variable (n) in
@[expose] noncomputable def graphFieldAut : MulAut (LinearFlag.projectiveSL n K) :=
  LinearFlag.fieldAut n K (barRingEquiv h) * LinearFlag.dualAut n K

theorem graphFieldAut_proj (x : SpecialLinearGroup (Fin n) K) :
    graphFieldAut h n (LinearFlag.proj n K x) = LinearFlag.proj n K (graphFieldSL h n x) := by
  rw [graphFieldAut, MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.fieldAut_proj]
  rfl

theorem graphFieldAut_mul_self : graphFieldAut h n * graphFieldAut h n = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective n K y
  rw [MulAut.mul_apply, graphFieldAut_proj, graphFieldAut_proj, graphFieldSL_graphFieldSL,
    MulAut.one_apply]

theorem graphFieldAut_toPSL (x : unitaryPSU h n) : graphFieldAut h n (toPSL h n x) = toPSL h n x := by
  obtain ⟨A, rfl⟩ := unitaryProj_surjective h n x
  rw [toPSL_unitaryProj, graphFieldAut_proj, graphFieldSL_toSL]

end GraphField

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem TorusEquivariantProd.mono {e : L ≃* unitaryPSU h n} {N I I' : Finset (Fin n)}
    (hII' : I ⊆ I') {Ψ : unitaryBlock h N × unitaryBlock h N →* G}
    (hΨ : TorusEquivariantProd e N I Ψ) : TorusEquivariantProd e N I' Ψ :=
  fun c hc x => hΨ c (unitaryTorusParam_anti h hII' hc) x

structure GraphFieldNeighbourParam (e : L ≃* unitaryPSU h n) (t : G) (X : Subgroup G)
    (N : Finset (Fin n)) where
  Φ : blockSpecialLinear (K := K) N →* G
  range_eq : Φ.range = centralizerPerfectCore X
  ker_le : Φ.ker ≤ center (blockSpecialLinear (K := K) N)
  N1 : ∀ x : unitaryBlock h N,
    Φ ⟨toSL h n x, (mem_unitaryBlock_iff_toSL h).1 x.2⟩ = ((e.symm (unitaryProj h n x) : L) : G)
  N2 : TorusEquivariant e N ∅ Φ
  N3 : ∀ x : blockSpecialLinear (K := K) N, t * Φ x * t⁻¹ = Φ (graphFieldBlock h N x)

structure SwapNeighbourParam (e : L ≃* unitaryPSU h n) (t : G) (X : Subgroup G)
    (N : Finset (Fin n)) where
  Ψ : unitaryBlock h N × unitaryBlock h N →* G
  range_eq : Ψ.range = centralizerPerfectCore X
  ker_le : Ψ.ker ≤ center (unitaryBlock h N × unitaryBlock h N)
  diag : ∀ x : unitaryBlock h N, Ψ (x, x) = ((e.symm (unitaryProj h n x) : L) : G)
  N2 : TorusEquivariantProd e N ∅ Ψ
  swap : ∀ x y : unitaryBlock h N, t * Ψ (x, y) * t⁻¹ = Ψ (y, x)

variable {e : L ≃* unitaryPSU h n} {t : G} {X : Subgroup G} {N : Finset (Fin n)}

theorem GraphFieldNeighbourParam.pieceCore_eq_map [Finite G]
    (P : GraphFieldNeighbourParam e t X N) {I : Finset (Fin n)} (hIN : I ⊆ N)
    (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card) (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map P.Φ :=
  pieceCore_eq_map_of_conjTorus e hIN hI2 hIc hXI P.Φ P.ker_le P.range_eq
    (TorusEquivariant.mono e (Finset.empty_subset I) P.N2)

theorem GraphFieldNeighbourParam.pieceCore_eq_map_rootTorus [Finite G] {a b : Fin n}
    (hab : a ≠ b)
    (P : GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab)) {a, b}ᶜ)
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) (hI2 : 2 ≤ I.card) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map P.Φ :=
  P.pieceCore_eq_map hI hI2 (two_le_card_compl_of_subset_compl_pair hab hI)
    (modelToG_unitaryRootTorus_le e hab hI)

theorem SwapNeighbourParam.pieceCore_eq_map [Finite G] (P : SwapNeighbourParam e t X N)
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) :
    pieceCore e I = (((unitaryBlock h I).subgroupOf (unitaryBlock h N)).prod
      ((unitaryBlock h I).subgroupOf (unitaryBlock h N))).map P.Ψ :=
  pieceCore_eq_map_of_conjTorusSU_prod e hIN hI2 hIc hperf hXI P.Ψ P.ker_le P.range_eq
    (P.N2.mono (Finset.empty_subset I))

theorem SwapNeighbourParam.pieceCore_eq_map_rootTorus [Finite G] {a b : Fin n} (hab : a ≠ b)
    (P : SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab)) {a, b}ᶜ)
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) (hI2 : 2 ≤ I.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I) :
    pieceCore e I = (((unitaryBlock h I).subgroupOf (unitaryBlock h {a, b}ᶜ)).prod
      ((unitaryBlock h I).subgroupOf (unitaryBlock h {a, b}ᶜ))).map P.Ψ :=
  P.pieceCore_eq_map hI hI2 (two_le_card_compl_of_subset_compl_pair hab hI) hperf
    (modelToG_unitaryRootTorus_le e hab hI)

theorem SwapNeighbourParam.conj_inl (P : SwapNeighbourParam e t X N) (x : unitaryBlock h N) :
    t * P.Ψ (x, 1) * t⁻¹ = P.Ψ (1, x) :=
  P.swap x 1

theorem SwapNeighbourParam.commute_inl_inr (P : SwapNeighbourParam e t X N)
    (x y : unitaryBlock h N) : Commute (P.Ψ (x, 1)) (P.Ψ (1, y)) := by
  have hxy : ((x, 1) : unitaryBlock h N × unitaryBlock h N) * (1, y) = (1, y) * (x, 1) := by
    ext <;> simp
  change P.Ψ (x, 1) * P.Ψ (1, y) = P.Ψ (1, y) * P.Ψ (x, 1)
  rw [← map_mul, hxy, map_mul]

theorem SwapNeighbourParam.mul_conj_inl (P : SwapNeighbourParam e t X N) (x : unitaryBlock h N) :
    P.Ψ (x, 1) * (t * P.Ψ (x, 1) * t⁻¹) = ((e.symm (unitaryProj h n x) : L) : G) := by
  rw [P.conj_inl, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, P.diag]

end Param

end CFSG.SeitzReduction.UnitaryPilot
