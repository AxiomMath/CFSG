module

public import CFSG.RankThree.PartOne.KA5L.Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement Pointwise

theorem commutatorElement_mul_mul_of_mem_center {G : Type*} [Group G] {a b : G}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G) (x y : G) :
    ⁅a * x, b * y⁆ = ⁅x, y⁆ := by
  have ha' : ∀ g : G, a * g * a⁻¹ = g := fun g => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 ha g).symm
  have hb' : ∀ g : G, b * g * b⁻¹ = g := fun g => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 hb g).symm
  have h1 : ⁅a, b * y⁆ = 1 :=
    Commute.commutator_eq (Subgroup.mem_center_iff.1 ha (b * y)).symm
  have h2 : ⁅x, b⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.1 hb x)
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj, h1, h2,
    one_mul, hb', ha', mul_one]

section Core

variable {L : Type} [Field L]

@[expose] def fixRho (Φ' : SL(6, L) ≃* SL(6, L)) : Subgroup SL(6, L) :=
  ((a5Frame L).comp Φ'.toMonoidHom).eqLocus (a5Frame L)

theorem mem_fixRho {Φ' : SL(6, L) ≃* SL(6, L)} {X : SL(6, L)} :
    X ∈ fixRho Φ' ↔ a5Frame L (Φ' X) = a5Frame L X := Iff.rfl

theorem fixSubgroup_le_fixRho (Φ' : SL(6, L) ≃* SL(6, L)) : fixSubgroup Φ' ≤ fixRho Φ' := by
  intro X hX
  rw [mem_fixRho, (mem_fixSubgroup Φ').1 hX]

theorem fixRho_central {Φ' : SL(6, L) ≃* SL(6, L)} {X : SL(6, L)} (hX : X ∈ fixRho Φ') :
    Φ' X * X⁻¹ ∈ Subgroup.center SL(6, L) :=
  ker_a5Frame_le_center (MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, mem_fixRho.1 hX,
    mul_inv_cancel]))

theorem commutator_fixRho (Φ' : SL(6, L) ≃* SL(6, L)) (hq : CFSG.IsQuasisimple (fixSubgroup Φ')) :
    ⁅fixRho Φ', fixRho Φ'⁆ = fixSubgroup Φ' := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro X hX Y hY
    rw [mem_fixSubgroup, map_commutatorElement]
    calc ⁅Φ' X, Φ' Y⁆ = ⁅(Φ' X * X⁻¹) * X, (Φ' Y * Y⁻¹) * Y⁆ := by simp
      _ = ⁅X, Y⁆ := commutatorElement_mul_mul_of_mem_center (fixRho_central hX)
          (fixRho_central hY) X Y
  · calc fixSubgroup Φ' = ⁅fixSubgroup Φ', fixSubgroup Φ'⁆ :=
          (Subgroup.isPerfect_iff.1 hq.1).symm
      _ ≤ ⁅fixRho Φ', fixRho Φ'⁆ := Subgroup.commutator_mono (fixSubgroup_le_fixRho Φ')
          (fixSubgroup_le_fixRho Φ')

theorem Gamma_eq_map (Fr : L →+* L) (n : ModGL Tag.E7 L) (Φ' : SL(6, L) ≃* SL(6, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X)) :
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) = (fixRho Φ').map (a5Frame L) := by
  have hR : rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) = (a5Frame L).range := by
    rw [← subsystemGroup_eq_rootSpan, range_a5Frame]
  rw [hR]
  ext g
  constructor
  · rintro ⟨⟨X, rfl⟩, hg⟩
    refine ⟨X, ?_, rfl⟩
    have hg' : n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L X := hg
    show a5Frame L (Φ' X) = a5Frame L X
    rw [← hΦ' X]
    exact hg'
  · rintro ⟨X, hX, rfl⟩
    refine ⟨⟨X, rfl⟩, ?_⟩
    have hX' : a5Frame L (Φ' X) = a5Frame L X := hX
    show n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L X
    rw [hΦ' X]
    exact hX'

theorem commutator_Gamma (Fr : L →+* L) (n : ModGL Tag.E7 L) (Φ' : SL(6, L) ≃* SL(6, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X))
    (hq : CFSG.IsQuasisimple (fixSubgroup Φ')) :
    ⁅rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)),
      rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr))⁆ = (fixSubgroup Φ').map (a5Frame L) := by
  rw [Gamma_eq_map Fr n Φ' hΦ', ← Subgroup.map_commutator, commutator_fixRho Φ' hq]

theorem finite_quasisimple_map (Φ' : SL(6, L) ≃* SL(6, L)) [Finite (fixSubgroup Φ')]
    (hq : CFSG.IsQuasisimple (fixSubgroup Φ')) :
    Finite ((fixSubgroup Φ').map (a5Frame L)) ∧
      CFSG.IsQuasisimple ((fixSubgroup Φ').map (a5Frame L)) := by
  have hsurj : Function.Surjective ((a5Frame L).subgroupMap (fixSubgroup Φ')) :=
    MonoidHom.subgroupMap_surjective _ _
  refine ⟨Finite.of_surjective _ hsurj, ?_⟩
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hsurj ?_
  by_contra hcon
  have hcon' : ∀ k, (a5Frame L).subgroupMap (fixSubgroup Φ') k = 1 := fun k =>
    by_contra fun h => hcon ⟨k, h⟩
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  apply hab
  have ha : (a' : SL(6, L)) ∈ Subgroup.center SL(6, L) :=
    ker_a5Frame_le_center (MonoidHom.mem_ker.2 (congrArg Subtype.val (hcon' a')))
  have hcomm : a' * b' = b' * a' := Subtype.ext (Subgroup.mem_center_iff.1 ha b').symm
  change QuotientGroup.mk a' * QuotientGroup.mk b' = QuotientGroup.mk b' * QuotientGroup.mk a'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]

theorem toGL_commute_of_mem_center {z : SL(6, L)} (hz : z ∈ Subgroup.center SL(6, L))
    (g : GL (Fin 6) L) :
    Matrix.SpecialLinearGroup.toGL z * g = g * Matrix.SpecialLinearGroup.toGL z := by
  obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 6) (R := L)).1 hz
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← hr]
  exact (Matrix.scalar_commute r (fun x => Commute.all _ x) (g : Matrix (Fin 6) (Fin 6) L)).eq

theorem a5_commutant (Φ' : SL(6, L) ≃* SL(6, L)) (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hz : Subgroup.centralizer (((fixSubgroup Φ').map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 6) L)) : Set (GL (Fin 6) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 6)).range) :
    ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      (∀ u ∈ (fixSubgroup Φ').map (a5Frame L), y * u = u * y) →
      y ∈ torusGroup Tag.E7 L ∧
        y ∈ Subgroup.centralizer
          (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L)) := by
  intro y hy hcomm
  set S3 := parabolicRoots Tag.E7 (a5Nodes Tag.E7) with hS3def
  have hS3' : ∀ r ∈ S3, IsRoot Tag.E7 r := fun r hr => hr.1
  have hR : rootSpan Tag.E7 L S3 = (a5Frame L).range := by
    rw [hS3def, ← subsystemGroup_eq_rootSpan, range_a5Frame]
  set S := fixSubgroup Φ' with hS
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup Tag.E7 L)
    (rootSpan Tag.E7 L S3) (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS3')
  have hy' : y ∈ ((torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L S3 : Subgroup (ModGL Tag.E7 L)) :
    Set (ModGL Tag.E7 L)) := hy
  rw [e] at hy'
  obtain ⟨t, ht, q, hq', rfl⟩ := hy'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [SetLike.mem_coe, hR] at hq'
  obtain ⟨A, rfl⟩ := hq'
  obtain ⟨d, hd⟩ := a5Frame_torus (L := L) b
  set M : GL (Fin 6) L := diagGLn d * Matrix.SpecialLinearGroup.toGL A with hM
  have hconj : ∀ X ∈ S, ∃ z ∈ Subgroup.center SL(6, L), conjDiagn d (A * X * A⁻¹) = z * X := by
    intro X hX
    have hXP : a5Frame L X ∈ S.map (a5Frame L) := ⟨X, hX, rfl⟩
    have h := hcomm _ hXP
    have h2 : a5Frame L (conjDiagn d (A * X * A⁻¹)) = a5Frame L X := by
      rw [← hd]
      calc rootDiagUnit Tag.E7 b * a5Frame L (A * X * A⁻¹) * (rootDiagUnit Tag.E7 b)⁻¹
          = (rootDiagUnit Tag.E7 b * a5Frame L A) * a5Frame L X *
              (rootDiagUnit Tag.E7 b * a5Frame L A)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = a5Frame L X := by rw [h, mul_inv_cancel_right]
    refine ⟨conjDiagn d (A * X * A⁻¹) * X⁻¹,
      ker_a5Frame_le_center (MonoidHom.mem_ker.2 ?_), by group⟩
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have hMconj : ∀ X ∈ S, ∃ z ∈ Subgroup.center SL(6, L),
      M * Matrix.SpecialLinearGroup.toGL X * M⁻¹ =
        Matrix.SpecialLinearGroup.toGL z * Matrix.SpecialLinearGroup.toGL X := by
    intro X hX
    obtain ⟨z, hz', hzX⟩ := hconj X hX
    refine ⟨z, hz', ?_⟩
    have h := congrArg Matrix.SpecialLinearGroup.toGL hzX
    rw [toGL_conjDiagn, map_mul, map_mul, map_inv, map_mul] at h
    calc M * Matrix.SpecialLinearGroup.toGL X * M⁻¹
        = diagGLn d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X *
          (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGLn d)⁻¹ := by rw [hM]; group
      _ = _ := h
  let Cm : Subgroup SL(6, L) :=
    (Subgroup.centralizer ({M} : Set (GL (Fin 6) L))).comap Matrix.SpecialLinearGroup.toGL
  have hcommCm : ⁅S, S⁆ ≤ Cm := by
    rw [Subgroup.commutator_le]
    intro Y hY Z hZ
    obtain ⟨zY, hzY, hY'⟩ := hMconj Y hY
    obtain ⟨zZ, hzZ, hZ'⟩ := hMconj Z hZ
    have hc : M * Matrix.SpecialLinearGroup.toGL ⁅Y, Z⁆ * M⁻¹ =
        Matrix.SpecialLinearGroup.toGL ⁅Y, Z⁆ := by
      have hcg : ∀ z ∈ Subgroup.center SL(6, L),
          Matrix.SpecialLinearGroup.toGL z ∈ Subgroup.center (GL (Fin 6) L) := fun z hz =>
        Subgroup.mem_center_iff.2 fun g => (toGL_commute_of_mem_center hz g).symm
      have h1 : M * Matrix.SpecialLinearGroup.toGL ⁅Y, Z⁆ * M⁻¹ =
          ⁅M * Matrix.SpecialLinearGroup.toGL Y * M⁻¹,
            M * Matrix.SpecialLinearGroup.toGL Z * M⁻¹⁆ := by
        rw [map_commutatorElement, conjugate_commutatorElement]
      rw [h1, hY', hZ', commutatorElement_mul_mul_of_mem_center (hcg zY hzY) (hcg zZ hzZ),
        map_commutatorElement]
    show Matrix.SpecialLinearGroup.toGL ⁅Y, Z⁆ ∈ Subgroup.centralizer ({M} : Set (GL (Fin 6) L))
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff.1 hm]
    exact mul_inv_eq_iff_eq_mul.1 hc
  have hSCm : S ≤ Cm := by
    have h := Subgroup.isPerfect_iff.1 hq.1
    rw [← h]
    exact hcommCm
  have hMs : M ∈ (Matrix.GeneralLinearGroup.scalar (Fin 6)).range := by
    rw [← hz, Subgroup.mem_centralizer_iff]
    rintro _ ⟨X, hX, rfl⟩
    have := hSCm hX
    have h2 : Matrix.SpecialLinearGroup.toGL X ∈ Subgroup.centralizer ({M} : Set (GL (Fin 6) L)) :=
      this
    rw [Subgroup.mem_centralizer_iff] at h2
    exact (h2 M rfl).symm
  obtain ⟨c, hc⟩ := hMs
  have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin 6) (Fin 6) L) i j = 0 := by
    intro i j hij
    have h := congrArg (fun G : GL (Fin 6) L => (G : Matrix (Fin 6) (Fin 6) L) i j) hc
    simp only [hM, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, diagGLn,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.diagonal_mul, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij] at h
    have hdi : ((d i : Lˣ) : L) ≠ 0 := (d i).ne_zero
    exact (mul_eq_zero.1 h.symm).resolve_left hdi
  have hρA : a5Frame L A ∈ torusGroup Tag.E7 L := a5Frame_diag_mem_torusGroup A hoff
  have hyH : rootDiagUnit Tag.E7 b * a5Frame L A ∈ torusGroup Tag.E7 L := mul_mem ht hρA
  refine ⟨hyH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, hR] at hg
  obtain ⟨X', rfl⟩ := hg
  have hsc : M * Matrix.SpecialLinearGroup.toGL X' = Matrix.SpecialLinearGroup.toGL X' * M := by
    rw [← hc]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (c : L) (fun r => Commute.all _ r) _).eq
  have hinj : Function.Injective
      (Matrix.SpecialLinearGroup.toGL : SL(6, L) →* GL (Fin 6) L) := fun B B' h =>
    Subtype.ext (congrArg (fun G : GL (Fin 6) L => (G : Matrix (Fin 6) (Fin 6) L)) h)
  have hc' : conjDiagn d (A * X' * A⁻¹) = X' := by
    apply hinj
    rw [toGL_conjDiagn, map_mul, map_mul, map_inv]
    calc diagGLn d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X' *
          (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGLn d)⁻¹
        = M * Matrix.SpecialLinearGroup.toGL X' * M⁻¹ := by rw [hM]; group
      _ = Matrix.SpecialLinearGroup.toGL X' := by rw [hsc, mul_inv_cancel_right]
  have h4 : (rootDiagUnit Tag.E7 b * a5Frame L A) * a5Frame L X' *
      (rootDiagUnit Tag.E7 b * a5Frame L A)⁻¹ = a5Frame L X' := by
    calc (rootDiagUnit Tag.E7 b * a5Frame L A) * a5Frame L X' *
        (rootDiagUnit Tag.E7 b * a5Frame L A)⁻¹
        = rootDiagUnit Tag.E7 b * a5Frame L (A * X' * A⁻¹) * (rootDiagUnit Tag.E7 b)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          group
      _ = a5Frame L (conjDiagn d (A * X' * A⁻¹)) := hd _
      _ = a5Frame L X' := by rw [hc']
  exact (mul_inv_eq_iff_eq_mul.1 h4).symm

end Core

end CFSG.RankThree.PartOne.KA5L
