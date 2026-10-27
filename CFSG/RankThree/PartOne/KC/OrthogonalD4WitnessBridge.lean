module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalDescent

section Bridge

variable {K : Type} [Field K] {d : ℕ}

theorem map_matrixScalars_eq_scalars (hd : 0 < d) :
    (matrixScalars d K).map matrixLinearIso.toMonoidHom = scalars K (Fin d → K) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_scalars]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ : ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin d) c = matrixLinearIso.symm x := hx
    refine ⟨c, fun v => ?_⟩
    have h : matrixLinearIso (GeneralLinearGroup.scalar (Fin d) c) = x := by
      rw [hc, MulEquiv.apply_symm_apply]
    rw [← h]
    exact matrixLinearEquiv_scalar c v
  · rintro ⟨c, hc⟩
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 : x (Pi.single ⟨0, hd⟩ 1) = x 0 := by
        rw [hc, h0, zero_smul, map_zero]
      have h2 := x.injective h1
      have h3 := congrFun h2 ⟨0, hd⟩
      simp at h3
    refine ⟨Units.mk0 c hc0, ?_⟩
    have h : matrixLinearIso (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) = x := by
      refine LinearEquiv.ext fun v => ?_
      change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) v = x v
      rw [matrixLinearEquiv_scalar, hc]
      rfl
    rw [← h, MulEquiv.symm_apply_apply]

@[expose] noncomputable def bridgeEquiv (Q : QuadraticForm K (Fin d → K)) (hd : 0 < d) :
    matrixProjectiveDerived Q ≃* ProjOrthDerived Q :=
  quotientSubgroupOfEquiv matrixLinearIso (matrixDerived_map Q)
    (map_matrixScalars_eq_scalars hd)

theorem bridgeEquiv_mk (Q : QuadraticForm K (Fin d → K)) (hd : 0 < d) (A : matrixDerived Q)
    (B : orthDerived Q) (hB : (B : (Fin d → K) ≃ₗ[K] (Fin d → K)) = matrixLinearIso A.val) :
    bridgeEquiv Q hd (matrixProjectiveProjection Q A) = QuotientGroup.mk B :=
  quotientSubgroupOfEquiv_mk _ _ _ A B hB

@[expose] noncomputable def derivedEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≃* orthDerived Q :=
  (matrixLinearIso.subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (matrixDerived_map Q))

theorem derivedEquiv_val (Q : QuadraticForm K (Fin d → K)) (A : matrixDerived Q) :
    ((derivedEquiv Q A : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearIso A.val :=
  rfl

theorem bridgeEquiv_projection (Q : QuadraticForm K (Fin d → K)) (hd : 0 < d)
    (A : matrixDerived Q) :
    bridgeEquiv Q hd (matrixProjectiveProjection Q A) = QuotientGroup.mk (derivedEquiv Q A) :=
  bridgeEquiv_mk Q hd A _ rfl

theorem mem_matrixDerived_iff_linear (Q : QuadraticForm K (Fin d → K)) (A : GL (Fin d) K) :
    A ∈ matrixDerived Q ↔ matrixLinearIso A ∈ orthDerived Q := by
  have h : (matrixDerived Q).map matrixLinearIso.toMonoidHom = orthDerived Q :=
    matrixDerived_map Q
  rw [← h, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end Bridge

section MulAut

variable {G H : Type*} [Group G] [Group H]

theorem mulAut_conj_conj (β : MulAut G) (y : G) :
    β * MulAut.conj y * β⁻¹ = MulAut.conj (β y) := by
  refine MulEquiv.ext fun z => ?_
  change β (y * β⁻¹ z * y⁻¹) = β y * z * (β y)⁻¹
  rw [map_mul, map_mul, map_inv]
  congr 3
  simp

theorem conj_injective_of_trivial_center (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g g' e
  have hc : g'⁻¹ * g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut G => α x) e
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  rw [h, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

end MulAut

section Layer

variable {T : Type*} [Group T]

abbrev layerCentralizer (D : Subgroup (MulAut T)) (α : MulAut T) : Subgroup (MulAut T) :=
  (CFSG.layer ↥(D ⊓ Subgroup.centralizer ({α} : Set (MulAut T)))).map
    (D ⊓ Subgroup.centralizer ({α} : Set (MulAut T))).subtype

theorem le_layerCentralizer_of_isComponent {D : Subgroup (MulAut T)} {α : MulAut T}
    {L : Subgroup (MulAut T)}
    (hL : L ≤ D ⊓ Subgroup.centralizer ({α} : Set (MulAut T)))
    (hc : CFSG.IsComponent
      (L.subgroupOf (D ⊓ Subgroup.centralizer ({α} : Set (MulAut T))))) :
    L ≤ layerCentralizer D α := fun z hz =>
  Subgroup.mem_map.mpr ⟨⟨z, hL hz⟩,
    CFSG.LocalCores.component_le_layer hc (Subgroup.mem_subgroupOf.mpr hz), rfl⟩

theorem map_inf_centralizer_singleton {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (D : Subgroup G) (α : G) :
    (D ⊓ Subgroup.centralizer ({α} : Set G)).map φ.toMonoidHom =
      D.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ α} : Set G') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_map_equiv,
    Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ?_
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h1 := congrArg φ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  · intro h
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

@[expose] def equivOfMap {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {S : Subgroup X}
    {S' : Subgroup Y} (h : S.map φ.toMonoidHom = S') : ↥S ≃* ↥S' :=
  (φ.subgroupMap S).trans (MulEquiv.subgroupCongr h)

theorem equivOfMap_val {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {S : Subgroup X}
    {S' : Subgroup Y} (h : S.map φ.toMonoidHom = S') (s : ↥S) : (equivOfMap φ h s : Y) = φ s :=
  rfl

theorem isComponent_map_iff {T' : Type*} [Group T'] (e : T ≃* T') (D : Subgroup (MulAut T))
    (α : MulAut T) (L : Subgroup (MulAut T)) :
    CFSG.IsComponent (L.subgroupOf (D ⊓ Subgroup.centralizer ({α} : Set (MulAut T)))) ↔
      CFSG.IsComponent ((L.map (MulAut.congr e).toMonoidHom).subgroupOf
        (D.map (MulAut.congr e).toMonoidHom ⊓
          Subgroup.centralizer ({MulAut.congr e α} : Set (MulAut T')))) := by
  set φ : MulAut T ≃* MulAut T' := MulAut.congr e with hφ
  set S : Subgroup (MulAut T) := D ⊓ Subgroup.centralizer ({α} : Set (MulAut T)) with hS
  set S' : Subgroup (MulAut T') := D.map φ.toMonoidHom ⊓
    Subgroup.centralizer ({φ α} : Set (MulAut T')) with hS'
  have hmap : S.map φ.toMonoidHom = S' := map_inf_centralizer_singleton φ D α
  set ψ : ↥S ≃* ↥S' := equivOfMap φ hmap with hψ
  have hval : ∀ y : ↥S', ((ψ.symm y : ↥S) : MulAut T) = φ.symm (y : MulAut T') := by
    intro y
    apply φ.injective
    rw [MulEquiv.apply_symm_apply]
    have := equivOfMap_val φ hmap (ψ.symm y)
    rw [hψ] at this ⊢
    rw [← this, MulEquiv.apply_symm_apply]
  have hL : (L.subgroupOf S).map ψ.toMonoidHom = (L.map φ.toMonoidHom).subgroupOf S' := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_map_equiv, hval]
  rw [← hL]
  constructor
  · exact CFSG.LocalCores.isComponent_map_mulEquiv ψ
  · intro h
    have := CFSG.LocalCores.isComponent_map_mulEquiv ψ.symm h
    rwa [CFSG.LocalCores.map_map_symm] at this

end Layer

end CFSG.RankThree.PartOne.KCOrthogonalD4
