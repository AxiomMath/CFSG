module

public import CFSG.RankThree.PartOne.KC.OrthogonalPlanePermutations
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedMaps
public import CFSG.LocalAnalysis.StandardType.GGTBJOmCoordinates
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Perm.Fin
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.GroupTheory.WeirSylow.OrthogonalTori

public section

open Module QuadraticMap
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

namespace CFSG.RankThree.PartOne.KCOrthogonal

namespace CoordinateDeletion

variable {K R E Vo : Type} [Field K] [AddCommGroup R] [Module K R]
  [AddCommGroup E] [Module K E] [AddCommGroup Vo] [Module K Vo]
  {QR : QuadraticForm K R} {QE : QuadraticForm K E} {Qo : QuadraticForm K Vo}

abbrev Vm (R E : Type) (m : ℕ) : Type _ := R × (Fin m → E)

abbrev Qm (QR : QuadraticForm K R) (QE : QuadraticForm K E) (m : ℕ) :
    QuadraticForm K (Vm R E m) :=
  QR.prod (QuadraticMap.pi (fun _ : Fin m => QE))

@[expose] noncomputable def splitZeroLinear (m : ℕ) :
    (Vm R E m × E) ≃ₗ[K] Vm R E m.succ :=
  (LinearEquiv.prodAssoc K R (Fin m → E) E).trans
    ((LinearEquiv.refl K R).prodCongr
      ((LinearEquiv.prodComm K (Fin m → E) E).trans
        (Fin.consLinearEquiv K (fun _ : Fin m.succ => E))))

@[simp] theorem splitZeroLinear_apply (m : ℕ) (w : R) (x : Fin m → E) (z : E) :
    splitZeroLinear (K := K) (R := R) (E := E) m ((w, x), z) = (w, Fin.cons z x) := by
  rfl

@[expose] noncomputable def splitZero (m : ℕ) :
    ((Qm QR QE m).prod QE).IsometryEquiv (Qm QR QE m.succ) where
  toLinearEquiv := splitZeroLinear m
  map_app' p := by
    rcases p with ⟨⟨w, x⟩, z⟩
    change Qm QR QE m.succ (splitZeroLinear m ((w, x), z)) =
      ((Qm QR QE m).prod QE) ((w, x), z)
    rw [splitZeroLinear_apply]
    simp only [Qm, QuadraticMap.prod_apply, QuadraticMap.pi_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    abel

@[simp] theorem splitZero_apply (m : ℕ) (w : R) (x : Fin m → E) (z : E) :
    splitZero (QR := QR) (QE := QE) m ((w, x), z) = (w, Fin.cons z x) := by
  change splitZeroLinear (K := K) (R := R) (E := E) m ((w, x), z) = (w, Fin.cons z x)
  rw [splitZeroLinear_apply]

@[expose] noncomputable def insertZero (m : ℕ) :
    Qm QR QE m →qᵢ Qm QR QE m.succ :=
  (splitZero (QR := QR) (QE := QE) m).toIsometry.comp
    (QuadraticMap.Isometry.inl (Qm QR QE m) QE)

@[simp] theorem insertZero_apply (m : ℕ) (w : R) (x : Fin m → E) :
    insertZero (QR := QR) (QE := QE) m (w, x) = (w, Fin.cons 0 x) := by
  rw [insertZero, QuadraticMap.Isometry.comp_apply]
  simp

@[expose] noncomputable def zeroDeletionSupport (m : ℕ) : Submodule K (Vm R E m.succ) :=
  coordSupport (K := K) (V := Vm R E m.succ) (R := R) (E := E)
    (LinearEquiv.refl K (Vm R E m.succ)) (Finset.univ.erase (0 : Fin m.succ))

theorem mem_zeroDeletionSupport {m : ℕ} {v : Vm R E m.succ} :
    v ∈ zeroDeletionSupport (K := K) (R := R) (E := E) m ↔ v.2 0 = 0 := by
  classical
  rw [zeroDeletionSupport, coordSupport, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have ha2 : a.2 = 0 := by
      obtain ⟨r, rfl⟩ := mem_coordAnchor.mp ha
      rfl
    have hb2 : b.2 0 = 0 := by
      let T : Submodule K (Vm R E m.succ) :=
        LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : Fin m.succ => E)
          (0 : Fin m.succ)).comp (LinearMap.snd K R (Fin m.succ → E)))
      have hle : (Finset.univ.erase (0 : Fin m.succ)).sup
          (coordPlane (LinearEquiv.refl K (Vm R E m.succ))) ≤ T := by
        refine Finset.sup_le_iff.mpr ?_
        intro i hi b hb
        obtain ⟨e, rfl⟩ := mem_coordPlane.mp hb
        have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
        rw [LinearMap.mem_ker]
        simp [T, hi0]
      have hbT : b ∈ T := hle hb
      simpa [T] using hbT
    simp [ha2, hb2]
  · intro hv
    let S := Finset.univ.erase (0 : Fin m.succ)
    refine ⟨(v.1, 0), mem_coordAnchor.mpr ⟨v.1, rfl⟩,
      ∑ i ∈ S, ((0 : R), Pi.single i (v.2 i)), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun i hi => ?_
      exact Finset.le_sup (f := fun i => coordPlane (LinearEquiv.refl K (Vm R E m.succ)) i)
        hi (mem_coordPlane.mpr ⟨v.2 i, rfl⟩)
    · apply Prod.ext
      · change (LinearMap.fst K R (Fin m.succ → E))
          ((v.1, (0 : Fin m.succ → E)) + ∑ i ∈ S, ((0 : R), Pi.single i (v.2 i))) = v.1
        rw [map_add, map_sum (LinearMap.fst K R (Fin m.succ → E))]
        simp
      · have hsnd : (∑ i ∈ S, ((0 : R), Pi.single i (v.2 i))).2 =
            ∑ i ∈ S, Pi.single i (v.2 i) := by
          change (LinearMap.snd K R (Fin m.succ → E))
            (∑ i ∈ S, ((0 : R), Pi.single i (v.2 i))) = _
          rw [map_sum (LinearMap.snd K R (Fin m.succ → E))]
          rfl
        have hsum_point : ∀ j : Fin m.succ,
            (∑ i ∈ S, Pi.single i (v.2 i)) j = v.2 j := by
          intro j
          rw [Finset.sum_apply]
          by_cases hj : j = 0
          · subst hj
            simp [S, hv]
          · rw [Finset.sum_eq_single j]
            · simp [hj]
            · intro k hk hkj
              rw [Pi.single_eq_of_ne (Ne.symm hkj)]
            · intro hnot
              exact (hnot (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)).elim
        simp only [Prod.snd_add, Pi.zero_apply, zero_add]
        rw [hsnd]
        exact funext hsum_point

theorem insertZero_injective (m : ℕ) :
    Function.Injective (insertZero (QR := QR) (QE := QE) m) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  have h1 : a1 = b1 := by
    have := congrArg Prod.fst h
    simpa [insertZero_apply] using this
  have h2 : a2 = b2 := by
    funext i
    have := congrFun (congrArg (fun v : Vm R E m.succ => fun i : Fin m => v.2 i.succ) h) i
    simpa [insertZero_apply] using this
  rw [h1, h2]

theorem range_insertZero (m : ℕ) :
    LinearMap.range (insertZero (QR := QR) (QE := QE) m).toLinearMap =
      zeroDeletionSupport (K := K) (R := R) (E := E) m := by
  ext v
  constructor
  · rintro ⟨⟨w, x⟩, rfl⟩
    rw [mem_zeroDeletionSupport]
    simp [insertZero_apply]
  · intro hv
    rw [mem_zeroDeletionSupport] at hv
    refine ⟨(v.1, fun i => v.2 i.succ), ?_⟩
    change insertZero (QR := QR) (QE := QE) m (v.1, fun i => v.2 i.succ) = v
    rw [insertZero_apply]
    apply Prod.ext
    · rfl
    · have h := Fin.cons_self_tail v.2
      have htail : Fin.tail v.2 = (fun i : Fin m => v.2 i.succ) := by
        funext i; rfl
      rw [htail] at h
      simpa [hv] using h

@[expose] noncomputable def deletionIsometry (m : ℕ) :
    (Qm QR QE m).IsometryEquiv
      ((Qm QR QE m.succ).comp (zeroDeletionSupport (K := K) (R := R) (E := E) m).subtype) where
  toLinearEquiv :=
    (LinearEquiv.ofInjective (insertZero (QR := QR) (QE := QE) m).toLinearMap
        (insertZero_injective m)).trans
      (LinearEquiv.ofEq _ _ (range_insertZero (QR := QR) (QE := QE) m))
  map_app' v := by
    simpa using (insertZero (QR := QR) (QE := QE) m).map_app v

theorem deletionIsometry_apply (m : ℕ) (v : Vm R E m) :
    (((deletionIsometry (QR := QR) (QE := QE) m) v :
        zeroDeletionSupport (K := K) (R := R) (E := E) m) : Vm R E m.succ) =
      insertZero (QR := QR) (QE := QE) m v := by
  rw [deletionIsometry]
  change (((LinearEquiv.ofEq (LinearMap.range (insertZero (QR := QR) (QE := QE) m).toLinearMap)
      (zeroDeletionSupport (K := K) (R := R) (E := E) m)
      (range_insertZero (QR := QR) (QE := QE) m))
    ((LinearEquiv.ofInjective (insertZero (QR := QR) (QE := QE) m).toLinearMap
      (insertZero_injective (QR := QR) (QE := QE) m)) v) :
        zeroDeletionSupport (K := K) (R := R) (E := E) m) : Vm R E m.succ) =
    insertZero (QR := QR) (QE := QE) m v
  simp only [LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, Submodule.coe_subtype]
  rfl

theorem deletionSource_nondegenerate (m : ℕ)
    (hQR : (polarBilin QR).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    (polarBilin (Qm QR QE m)).Nondegenerate :=
  CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_prod hQR
    (CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_pi (fun _ : Fin m => hQE))

theorem deletionTarget_nondegenerate (m : ℕ)
    (hQR : (polarBilin QR).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    (polarBilin (Qm QR QE m.succ)).Nondegenerate :=
  deletionSource_nondegenerate (QR := QR) (QE := QE) m.succ hQR hQE

theorem deletionSupport_nondegenerate (m : ℕ)
    (hQR : (polarBilin QR).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    (polarBilin ((Qm QR QE m.succ).comp
      (zeroDeletionSupport (K := K) (R := R) (E := E) m).subtype)).Nondegenerate :=
  CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv
    (deletionIsometry (QR := QR) (QE := QE) m)
    (deletionSource_nondegenerate (QR := QR) (QE := QE) m hQR hQE)

@[expose] noncomputable def deletionEmbeddingEquiv (m : ℕ)
    [FiniteDimensional K R] [FiniteDimensional K E]
    (hD : (polarBilin ((Qm QR QE m.succ).comp
      (zeroDeletionSupport (K := K) (R := R) (E := E) m).subtype)).Nondegenerate) :
    orthDerived ((Qm QR QE m.succ).comp
      (zeroDeletionSupport (K := K) (R := R) (E := E) m).subtype) ≃*
      supportedDerived (Qm QR QE m.succ)
        (zeroDeletionSupport (K := K) (R := R) (E := E) m) :=
  orthDerivedSupportedEquiv hD

@[expose] noncomputable def deletionGroupEquiv (m : ℕ)
    [FiniteDimensional K R] [FiniteDimensional K E]
    (hQR : (polarBilin QR).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    orthDerived (Qm QR QE m) ≃*
      (supportedDerived (Qm QR QE m.succ)
        (zeroDeletionSupport (K := K) (R := R) (E := E) m)).subgroupOf
        (orthDerived (Qm QR QE m.succ)) :=
  let hD := deletionSupport_nondegenerate (QR := QR) (QE := QE) m hQR hQE
  (commutatorOrthogonalGroupCongr (deletionIsometry (QR := QR) (QE := QE) m)).trans
    ((deletionEmbeddingEquiv (QR := QR) (QE := QE) m hD).trans
      (Subgroup.subgroupOfEquivOfLe
        (supportedDerived_le_orthDerived_of_regular hD)).symm)

theorem refl_coordinate_quadratic (m : ℕ) :
    ∀ v : Vm R E m, Qm QR QE m v = QR v.1 + ∑ i, QE (v.2 i) := by
  intro v
  simp [Qm, QuadraticMap.prod_apply, QuadraticMap.pi_apply]

theorem refl_coordinate_quadratic_apply (m : ℕ) :
    ∀ v : Vm R E m, Qm QR QE m v =
      QR ((LinearEquiv.refl K (Vm R E m)) v).1 +
        ∑ i, QE (((LinearEquiv.refl K (Vm R E m)) v).2 i) := by
  intro v
  simpa only [LinearEquiv.refl_apply] using
    refl_coordinate_quadratic (QR := QR) (QE := QE) m v

@[expose] noncomputable def originalCoordinateIsometry (m : ℕ)
    (ψ : Vo ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v, Qo v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i)) :
    Qo.IsometryEquiv (Qm QR QE m) :=
  coordChangeIsometry ψ (LinearEquiv.refl K (Vm R E m))
    (QuadraticMap.IsometryEquiv.refl QR) (QuadraticMap.IsometryEquiv.refl QE)
    hψ (refl_coordinate_quadratic_apply (QR := QR) (QE := QE) m)

@[expose] noncomputable def originalDeletionGroupEquiv (m : ℕ)
    [FiniteDimensional K R] [FiniteDimensional K E]
    (ψ : Vo ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v, Qo v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (hQR : (polarBilin QR).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    orthDerived Qo ≃*
      (supportedDerived (Qm QR QE m.succ)
        (zeroDeletionSupport (K := K) (R := R) (E := E) m)).subgroupOf
        (orthDerived (Qm QR QE m.succ)) :=
  (commutatorOrthogonalGroupCongr
    (originalCoordinateIsometry (Qo := Qo) (QR := QR) (QE := QE) m ψ hψ)).trans
    (deletionGroupEquiv (QR := QR) (QE := QE) m hQR hQE)

private theorem map_subgroupOf_commutatorOrthogonalGroupCongr
    {F : Type*} [Field F] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (e : Q₁.IsometryEquiv Q₂) (H : Subgroup (V₁ ≃ₗ[F] V₁)) :
    (H.subgroupOf (orthDerived Q₁)).map (commutatorOrthogonalGroupCongr e).toMonoidHom =
      (H.map (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom).subgroupOf
        (orthDerived Q₂) := by
  let ee := LinearEquiv.autCongr e.toLinearEquiv
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxH : (x : V₁ ≃ₗ[F] V₁) ∈ H := Subgroup.mem_subgroupOf.mp hx
    have hcoe : ((commutatorOrthogonalGroupCongr e x : orthDerived Q₂) :
        V₂ ≃ₗ[F] V₂) = ee (x : V₁ ≃ₗ[F] V₁) := by
      simpa [ee, coe_commutatorOrthogonalGroupCongr_apply] using
        (LinearEquiv.autCongr_apply e.toLinearEquiv (x : V₁ ≃ₗ[F] V₁)).symm
    rw [Subgroup.mem_subgroupOf]
    rw [show (y : V₂ ≃ₗ[F] V₂) = ee (x : V₁ ≃ₗ[F] V₁) from by
      rw [← hcoe]
      exact (congrArg (fun z : orthDerived Q₂ => (z : V₂ ≃ₗ[F] V₂)) hxy).symm]
    exact Subgroup.mem_map_of_mem ee.toMonoidHom hxH
  · intro hy
    have hyH : (y : V₂ ≃ₗ[F] V₂) ∈ H.map ee.toMonoidHom :=
      Subgroup.mem_subgroupOf.mp hy
    obtain ⟨z, hzH, hzy⟩ := hyH
    have hzK : z ∈ orthDerived Q₁ := by
      have hyK : (y : V₂ ≃ₗ[F] V₂) ∈
          (orthDerived Q₁).map ee.toMonoidHom := by
        rw [map_autCongr_commutator_orthogonalGroup e]
        exact y.2
      obtain ⟨w, hwK, hwy⟩ := hyK
      exact (ee.injective (hzy.trans hwy.symm)) ▸ hwK
    refine ⟨⟨z, hzK⟩, Subgroup.mem_subgroupOf.mpr hzH, ?_⟩
    apply Subtype.ext
    have hcoe : ((commutatorOrthogonalGroupCongr e ⟨z, hzK⟩ : orthDerived Q₂) :
        V₂ ≃ₗ[F] V₂) = ee z := by
      simpa [ee, coe_commutatorOrthogonalGroupCongr_apply] using
        (LinearEquiv.autCongr_apply e.toLinearEquiv z).symm
    rw [show ((commutatorOrthogonalGroupCongr e).toMonoidHom ⟨z, hzK⟩ :
        V₂ ≃ₗ[F] V₂) = ee z from hcoe]
    simpa only [MulEquiv.coe_toMonoidHom] using hzy

private theorem map_subgroupOf_subgroupOfEquivOfLe_symm
    {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) (L : Subgroup G) :
    (L.subgroupOf H).map (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom =
      (L.subgroupOf K).subgroupOf (H.subgroupOf K) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
    simpa using hxL
  · intro hy
    have hyL : (y : G) ∈ L := by
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)
    have hyH : (y : G) ∈ H := by
      exact Subgroup.mem_subgroupOf.mp y.2
    refine ⟨⟨(y : G), hyH⟩, Subgroup.mem_subgroupOf.mpr hyL, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using (Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe h
      (⟨(y : G), hyH⟩ : H))

private theorem map_subgroupOf_congrOfMapEq
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {B : Subgroup G} {B' : Subgroup H} (hB : B.map (e : G →* H) = B')
    (L : Subgroup G) :
    (L.subgroupOf B).map (TauCeti.Subgroup.congrOfMapEq e hB).toMonoidHom =
      (L.map e.toMonoidHom).subgroupOf B' := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf]
    have hcoe : (TauCeti.Subgroup.congrOfMapEq e hB x : H) = e (x : G) :=
      TauCeti.Subgroup.coe_congrOfMapEq_apply e hB x
    have hxy' : (y : H) = e (x : G) := by
      rw [← hcoe]
      exact (congrArg (fun z : B' => (z : H)) hxy).symm
    rw [hxy']
    exact Subgroup.mem_map_of_mem e.toMonoidHom (Subgroup.mem_subgroupOf.mp hx)
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨z, hzL, hzy⟩ := hy
    have hzB : z ∈ B := by
      have hyB' : (y : H) ∈ B.map (e : G →* H) := by
        rw [hB]
        exact y.2
      obtain ⟨w, hwB, hwy⟩ := hyB'
      exact (e.injective (hzy.trans hwy.symm)) ▸ hwB
    refine ⟨⟨z, hzB⟩, Subgroup.mem_subgroupOf.mpr hzL, ?_⟩
    apply Subtype.ext
    change (TauCeti.Subgroup.congrOfMapEq e hB ⟨z, hzB⟩ : H) = (y : H)
    rw [TauCeti.Subgroup.coe_congrOfMapEq_apply]
    exact hzy

private theorem mem_coordSupport_refl {m : ℕ} :
    ∀ (S : Finset (Fin m)) (v : Vm R E m),
      v ∈ coordSupport (LinearEquiv.refl K (Vm R E m)) S ↔
        ∀ i : Fin m, i ∉ S → v.2 i = 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro v
      rw [coordSupport_empty]
      constructor
      · intro hv i _
        obtain ⟨r, hr⟩ := mem_coordAnchor.mp hv
        have hvr : (r, (0 : Fin m → E)) = v := by simpa using hr
        rw [← hvr]
        simp
      · intro hv
        rw [mem_coordAnchor]
        refine ⟨v.1, ?_⟩
        apply Prod.ext
        · simp
        · funext i
          simp [hv i (by simp)]
  | insert i S hi ih =>
      intro v
      rw [coordSupport_insert (LinearEquiv.refl K (Vm R E m)) hi]
      constructor
      · intro hv
        rw [Submodule.mem_sup] at hv
        obtain ⟨a, ha, b, hb, rfl⟩ := hv
        have ha' : ∀ j : Fin m, j ∉ S → a.2 j = 0 := (ih a).mp ha
        obtain ⟨e, he⟩ := mem_coordPlane.mp hb
        have hb' : b = ((0 : R), Pi.single i e) := by simpa using he.symm
        rw [hb']
        intro j hj
        have hji : j ≠ i := by
          intro h
          exact hj (by simp [h])
        have hjs : j ∉ S := by
          intro h
          exact hj (Finset.mem_insert_of_mem h)
        simp [ha' j hjs, hji]
      · intro hv
        rw [Submodule.mem_sup]
        refine ⟨(v.1, fun j : Fin m => if j = i then 0 else v.2 j), ?_,
          ((0 : R), Pi.single i (v.2 i)), ?_, ?_⟩
        · apply (ih _).mpr
          intro j hj
          by_cases hji : j = i
          · simp [hji]
          · have hvj : v.2 j = 0 := hv j (by simp [hj, hji])
            simp [hji, hvj]
        · exact mem_coordPlane.mpr ⟨v.2 i, rfl⟩
        · apply Prod.ext
          · simp
          · funext j
            by_cases hji : j = i
            · simp [hji]
            · simp [hji]

private theorem map_insertZero_coordSupport {m : ℕ} (T : Finset (Fin m)) :
    (coordSupport (LinearEquiv.refl K (Vm R E m)) T).map
        (insertZero (QR := QR) (QE := QE) m).toLinearMap =
      coordSupport (LinearEquiv.refl K (Vm R E (m+1))) (T.image Fin.succ) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change insertZero (QR := QR) (QE := QE) m w ∈
      coordSupport (LinearEquiv.refl K (Vm R E (m+1))) (T.image Fin.succ)
    have hw' : ∀ j : Fin m, j ∉ T → w.2 j = 0 :=
      (mem_coordSupport_refl T w).mp hw
    rw [mem_coordSupport_refl]
    intro j hj
    rw [insertZero_apply]
    obtain rfl | ⟨i, rfl⟩ := j.eq_zero_or_eq_succ
    · simp
    · have hi : i ∉ T := by
        intro hit
        exact hj (Finset.mem_image.mpr ⟨i, hit, rfl⟩)
      simpa using hw' i hi
  · intro hv
    have hv' : ∀ j : Fin (m+1), j ∉ T.image Fin.succ → v.2 j = 0 :=
      (mem_coordSupport_refl (T.image Fin.succ) v).mp hv
    refine ⟨(v.1, fun i : Fin m => v.2 i.succ), ?_, ?_⟩
    · apply (mem_coordSupport_refl T _).mpr
      intro i hi
      have hsi : Fin.succ i ∉ T.image Fin.succ := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hmem
        exact hi (Fin.succ_injective _ hji ▸ hj)
      simpa using hv' (Fin.succ i) hsi
    · change insertZero (QR := QR) (QE := QE) m (v.1, fun i : Fin m => v.2 i.succ) = v
      rw [insertZero_apply]
      apply Prod.ext
      · rfl
      · have hv0 : v.2 0 = 0 := hv' 0 (by simp)
        have h := Fin.cons_self_tail v.2
        have htail : Fin.tail v.2 = (fun i : Fin m => v.2 i.succ) := by
          funext i
          rfl
        rw [htail] at h
        rw [hv0] at h
        exact h

private theorem map_deletionIsometry_coordSupport {m : ℕ} (T : Finset (Fin m)) :
    (coordSupport (LinearEquiv.refl K (Vm R E m)) T).map
        (deletionIsometry (QR := QR) (QE := QE) m).toLinearEquiv.toLinearMap =
      (coordSupport (LinearEquiv.refl K (Vm R E (m+1))) (T.image Fin.succ)).comap
        (zeroDeletionSupport (K := K) (R := R) (E := E) m).subtype := by
  let D := zeroDeletionSupport (K := K) (R := R) (E := E) m
  let U := coordSupport (LinearEquiv.refl K (Vm R E (m+1))) (T.image Fin.succ)
  have hUle : U ≤ D := by
    intro v hv
    rw [mem_zeroDeletionSupport]
    have hv' : ∀ i : Fin (m+1), i ∉ T.image Fin.succ → v.2 i = 0 :=
      (mem_coordSupport_refl (T.image Fin.succ) v).mp hv
    exact hv' 0 (by simp)
  apply Submodule.map_injective_of_injective D.subtype_injective
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUle]
  rw [← Submodule.map_comp]
  have hcomp : D.subtype.comp
        (deletionIsometry (QR := QR) (QE := QE) m).toLinearEquiv.toLinearMap =
      (insertZero (QR := QR) (QE := QE) m).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact deletionIsometry_apply (QR := QR) (QE := QE) m v
  rw [hcomp]
  exact map_insertZero_coordSupport (QR := QR) (QE := QE) (K := K) (R := R) (E := E) T

theorem originalDeletionGroupEquiv_map_supportedDerived (m : ℕ)
    [FiniteDimensional K Vo] [FiniteDimensional K R] [FiniteDimensional K E]
    (ψ : Vo ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : Vo, Qo v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (hQo : (polarBilin Qo).Nondegenerate)
    (hQR : (polarBilin QR).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (T : Finset (Fin m)) :
    ((supportedDerived Qo (coordSupport ψ T)).subgroupOf (orthDerived Qo)).map
        (originalDeletionGroupEquiv (Qo := Qo) (QR := QR) (QE := QE) m ψ hψ hQR hQE).toMonoidHom =
      ((supportedDerived (Qm QR QE (m+1))
          (coordSupport (LinearEquiv.refl K (Vm R E (m+1))) (T.image Fin.succ))).subgroupOf
          (orthDerived (Qm QR QE (m+1)))).subgroupOf
        ((supportedDerived (Qm QR QE (m+1))
          (zeroDeletionSupport (K := K) (R := R) (E := E) m)).subgroupOf
          (orthDerived (Qm QR QE (m+1)))) := by
  classical
  let D := zeroDeletionSupport (K := K) (R := R) (E := E) m
  let U := coordSupport (LinearEquiv.refl K (Vm R E (m+1))) (T.image Fin.succ)
  let Sm := coordSupport (LinearEquiv.refl K (Vm R E m)) T
  let Ωo := orthDerived Qo
  let Ωm := orthDerived (Qm QR QE m)
  let Ωt := orthDerived (Qm QR QE (m+1))
  let Ωd := orthDerived ((Qm QR QE (m+1)).comp D.subtype)
  let H := supportedDerived Qo (coordSupport ψ T)
  let Hm := supportedDerived (Qm QR QE m) Sm
  let HD := supportedDerived (Qm QR QE (m+1)) D
  let HU := supportedDerived (Qm QR QE (m+1)) U
  let edel := deletionIsometry (QR := QR) (QE := QE) m
  let eψ := originalCoordinateIsometry (Qo := Qo) (QR := QR) (QE := QE) m ψ hψ
  let Hd := supportedDerived ((Qm QR QE (m+1)).comp D.subtype)
    (Sm.map edel.toLinearEquiv.toLinearMap)
  have hreflR : (QuadraticMap.IsometryEquiv.refl QR).toLinearEquiv =
      LinearEquiv.refl K R := rfl
  have hreflE : (QuadraticMap.IsometryEquiv.refl QE).toLinearEquiv =
      LinearEquiv.refl K E := rfl
  have hsuppψ : (coordSupport ψ T).map eψ.toLinearEquiv.toLinearMap = Sm := by
    have h := map_coordSupport_coordChange (psi1 := ψ)
      (psi2 := LinearEquiv.refl K (Vm R E m)) (epsR := LinearEquiv.refl K R)
      (epsE := LinearEquiv.refl K E) T
    simpa [eψ, Sm, originalCoordinateIsometry, coordChangeIsometry_toLinearEquiv,
      hreflR, hreflE] using h
  have hsuppd : Sm.map edel.toLinearEquiv.toLinearMap = U.comap D.subtype := by
    simpa [Sm, U, D, edel] using
      (map_deletionIsometry_coordSupport (QR := QR) (QE := QE) (K := K) (R := R) (E := E) T)
  have hDreg : (polarBilin ((Qm QR QE (m+1)).comp D.subtype)).Nondegenerate := by
    simpa [D] using deletionSupport_nondegenerate (QR := QR) (QE := QE) m hQR hQE
  have hUle : U ≤ D := by
    intro v hv
    rw [mem_zeroDeletionSupport]
    have hv' : ∀ i : Fin (m+1), i ∉ T.image Fin.succ → v.2 i = 0 :=
      (mem_coordSupport_refl (T.image Fin.succ) v).mp hv
    exact hv' 0 (by simp)
  have hUreg : (polarBilin ((Qm QR QE (m+1)).comp U.subtype)).Nondegenerate := by
    simpa [U] using coordSupport_nondegenerate
      (LinearEquiv.refl K (Vm R E (m+1)))
      (refl_coordinate_quadratic_apply (QR := QR) (QE := QE) (m+1))
      (deletionTarget_nondegenerate (QR := QR) (QE := QE) m hQR hQE) hQE
      (T.image Fin.succ)
  have hHd : Hd = supportedDerived ((Qm QR QE (m+1)).comp D.subtype) (U.comap D.subtype) := by
    dsimp [Hd]
    rw [hsuppd]
  have hstep1 : (H.subgroupOf Ωo).map (commutatorOrthogonalGroupCongr eψ).toMonoidHom =
      Hm.subgroupOf Ωm := by
    rw [map_subgroupOf_commutatorOrthogonalGroupCongr]
    rw [map_supportedDerived_isometryEquiv eψ, hsuppψ]
  have hstep2a : (Hm.subgroupOf Ωm).map
      (commutatorOrthogonalGroupCongr edel).toMonoidHom = Hd.subgroupOf Ωd := by
    rw [map_subgroupOf_commutatorOrthogonalGroupCongr]
    rw [map_supportedDerived_isometryEquiv edel]
  have hstep2b : (Hd.subgroupOf Ωd).map
      (deletionEmbeddingEquiv (QR := QR) (QE := QE) m hDreg).toMonoidHom =
        HU.subgroupOf HD := by
    rw [hHd]
    exact orthDerivedSupportedEquiv_map_supportedDerived hUle hUreg hDreg
  have hstep3 : (HU.subgroupOf HD).map
      (Subgroup.subgroupOfEquivOfLe
        (supportedDerived_le_orthDerived_of_regular hDreg)).symm.toMonoidHom =
        (HU.subgroupOf Ωt).subgroupOf (HD.subgroupOf Ωt) :=
    map_subgroupOf_subgroupOfEquivOfLe_symm
      (supportedDerived_le_orthDerived_of_regular hDreg) HU
  have hdelEq : deletionGroupEquiv (QR := QR) (QE := QE) m hQR hQE =
      (commutatorOrthogonalGroupCongr edel).trans
        ((deletionEmbeddingEquiv (QR := QR) (QE := QE) m hDreg).trans
          (Subgroup.subgroupOfEquivOfLe
            (supportedDerived_le_orthDerived_of_regular hDreg)).symm) := by
    rfl
  have hdel : (Hm.subgroupOf Ωm).map
      (deletionGroupEquiv (QR := QR) (QE := QE) m hQR hQE).toMonoidHom =
        (HU.subgroupOf Ωt).subgroupOf (HD.subgroupOf Ωt) := by
    rw [hdelEq]
    change (Hm.subgroupOf Ωm).map
      ((Subgroup.subgroupOfEquivOfLe
        (supportedDerived_le_orthDerived_of_regular hDreg)).symm.toMonoidHom.comp
        ((deletionEmbeddingEquiv (QR := QR) (QE := QE) m hDreg).toMonoidHom.comp
          (commutatorOrthogonalGroupCongr edel).toMonoidHom)) =
        (HU.subgroupOf Ωt).subgroupOf (HD.subgroupOf Ωt)
    rw [← Subgroup.map_map, ← Subgroup.map_map]
    rw [hstep2a, hstep2b, hstep3]
  have hmain : (H.subgroupOf Ωo).map
      ((commutatorOrthogonalGroupCongr eψ).trans
        (deletionGroupEquiv (QR := QR) (QE := QE) m hQR hQE)).toMonoidHom =
        (HU.subgroupOf Ωt).subgroupOf (HD.subgroupOf Ωt) := by
    change (H.subgroupOf Ωo).map
      ((deletionGroupEquiv (QR := QR) (QE := QE) m hQR hQE).toMonoidHom.comp
        (commutatorOrthogonalGroupCongr eψ).toMonoidHom) =
        (HU.subgroupOf Ωt).subgroupOf (HD.subgroupOf Ωt)
    rw [← Subgroup.map_map, hstep1, hdel]
  simpa [originalDeletionGroupEquiv, eψ, H, HU, HD, Ωt, U, D] using hmain

private theorem map_supportedDerived_chart
    {F : Type} [Field F] [Finite F] [CharP F 2] {W E : Type} [AddCommGroup W]
    [Module F W] [AddCommGroup E] [Module F E] {QR : QuadraticForm F W}
    {QE : QuadraticForm F E} {r : ℕ} {b c : F}
    (N : (Qm QR QE (r + 1)).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadMinus (r + 2) F b c))
    (hN : ∀ S : Finset (Fin (r + 1)),
      (coordSupport (LinearEquiv.refl F (Vm W E (r + 1))) S).map
          N.toLinearEquiv.toLinearMap = anchoredSupport F (r + 2) S)
    (S : Finset (Fin (r + 1))) :
    ((supportedDerived (Qm QR QE (r + 1))
        (coordSupport (LinearEquiv.refl F (Vm W E (r + 1))) S)).subgroupOf
        (orthDerived (Qm QR QE (r + 1)))).map
          (commutatorOrthogonalGroupCongr N).toMonoidHom =
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S := by
  rw [map_subgroupOf_commutatorOrthogonalGroupCongr]
  rw [map_supportedDerived_isometryEquiv N, hN S]

section OriginalCanonicalZeroDeletion

open CFSG.StandardType.OrthTorus
open CFSG.Timmesfeld.ClassicalOrders
open CFSG.LieType.Universal.Spin
open CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] {p r : ℕ} {A : Subgroup (V ≃ₗ[F] V)}
  {Q : QuadraticForm F V}

private theorem hypPlane_isPlusType :
    IsPlusType (CFSG.Timmesfeld.ClassicalOrders.hypPlane F) := by
  have h : CFSG.Timmesfeld.ClassicalOrders.hypPlane F =
      CFSG.GroupTheory.WeirSylow.hypQuadForm (LinearMap.id : F →ₗ[F] F) := by
    ext v
    simp [CFSG.Timmesfeld.ClassicalOrders.hypPlane_apply,
      CFSG.GroupTheory.WeirSylow.hypQuadForm_apply]
  rw [h]
  exact CFSG.GroupTheory.WeirSylow.isPlusType_hypQuadForm (lam := LinearMap.id)

theorem exists_originalDeletion_chartSubgroup
    [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hr : 1 ≤ r) (hdim : finrank F V = 2 * (r + 1))
    (hminus : ¬ IsPlusType Q) (hsplit : p ∣ Nat.card F - 1)
    (b c : F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (o : Fin r) :
    ∃ e0 : orthDerived Q ≃*
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (Finset.univ.erase (0 : Fin (r + 1))),
      ∀ T : Finset (Fin r),
        ((supportedDerived Q (Δ.originalAnchor ⊔ T.sup Δ.F.U)).subgroupOf (orthDerived Q)).map
            e0.toMonoidHom =
          (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
            (T.image Fin.succ)).subgroupOf
            (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
              (Finset.univ.erase (0 : Fin (r + 1)))) := by
  classical
  let hrow : p ∣ Nat.card F - 1 ∨ Odd r ∧ p ∣ Nat.card F + 1 := Or.inl hsplit
  let W := Δ.originalAnchor
  let E := Δ.F.U o
  let QR : QuadraticForm F W := Q.comp W.subtype
  let QE : QuadraticForm F E := Q.comp E.subtype
  have hWS : IsCompl W Δ.originalActive := by
    simpa [W] using Δ.originalMinusAnchor_isCompl hp2 hQ hA hr hdim hminus hrow
  let ψ : V ≃ₗ[F] W × (Fin r → E) := Δ.originalCoordinates hQ o hWS
  have hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i) := by
    intro v
    simpa [ψ, QR, QE, W, E] using Δ.originalCoordinates_quadratic_apply hQ o hWS v
  have hQR : (polarBilin QR).Nondegenerate := by
    simpa [QR, W] using Δ.originalMinusAnchor_regular hp2 hQ hA hr hdim hminus hrow
  have hQE : (polarBilin QE).Nondegenerate := by
    simpa [QE, E] using Δ.originalPlaneForm_nondegenerate o
  have hdata := Δ.inactive_plane_of_minus hp2 hQ hA hr hdim hminus hrow
  have hQR_unfold : QR =
      Q.comp (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q
        (⨆ i, Δ.F.U i)).subtype := by
    simp [QR, W, TBJOmData.originalAnchor, TBJOmData.originalActive]
    rfl
  have hW_unfold : W = CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q
      (⨆ i, Δ.F.U i) := by
    simp [W, TBJOmData.originalAnchor, TBJOmData.originalActive]
  have hRminus : ¬ IsPlusType QR := by
    rw [hQR_unfold]
    have hpiece : IsPlusType QE := by
      simpa [QE, E] using (Δ.isPlusType_piece_iff_dvd_card_sub_one hp2 hA o).mpr hsplit
    exact fun hplus => (hdata.2.2.2.2 o).mp hplus (by simpa [QE, E] using hpiece)
  have hRdim : finrank F W = 2 := by
    rw [hW_unfold]
    exact hdata.2.1
  have hbindim : finrank F (Fin 2 → F) = 2 :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.finrank_fin_two_fun (K := F)
  have hbin : CFSG.LieType.Universal.Spin.binaryForm F b c =
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.minusTailForm F b c := by
    ext x
    rw [CFSG.LieType.Universal.Spin.binaryForm_apply,
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.minusTailForm_apply]
  have hbinnd : (polarBilin (CFSG.LieType.Universal.Spin.binaryForm F b c)).Nondegenerate := by
    rw [hbin]
    exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.nondegenerate_minusTailForm hirr
  have hbinminus : ¬ IsPlusType (CFSG.LieType.Universal.Spin.binaryForm F b c) := by
    rw [hbin]
    rintro ⟨U, hU, hUs⟩
    have hdim : finrank F U = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.finrank_fin_two_fun (K := F)] at hU
      omega
    have hUne : U ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim
      omega
    obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    exact hx0 (CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.anisotropic_minusTailForm
      (K := F) hirr x (hUs x hxU))
  have hR : Nonempty (QR.IsometryEquiv (CFSG.LieType.Universal.Spin.binaryForm F b c)) :=
    CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff (n := 1) hQR hbinnd hRdim hbindim
      (by
        refine ⟨?_, ?_⟩
        · intro h
          exact absurd h hRminus
        · intro h
          exact absurd h hbinminus)
  let epsR : QR.IsometryEquiv (CFSG.LieType.Universal.Spin.binaryForm F b c) :=
    Classical.choice hR
  have hEplus : IsPlusType QE := by
    simpa [QE, E] using (Δ.isPlusType_piece_iff_dvd_card_sub_one hp2 hA o).mpr hsplit
  have hE_dim : finrank F E = 2 := by simpa [E] using Δ.finrank_piece o
  have hHyp_dim : finrank F (F × F) = 2 := by simp
  have hE : Nonempty (QE.IsometryEquiv (CFSG.Timmesfeld.ClassicalOrders.hypPlane F)) :=
    CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff (n := 1) hQE
      hypPlane_polarBilin_nondegenerate hE_dim hHyp_dim
      (by
        refine ⟨?_, ?_⟩
        · intro _
          exact hypPlane_isPlusType
        · intro _
          exact hEplus)
  let epsE : QE.IsometryEquiv (CFSG.Timmesfeld.ClassicalOrders.hypPlane F) :=
    Classical.choice hE
  let N : (Qm QR QE (r + 1)).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadMinus (r + 2) F b c) :=
    coordChangeIsometry (K := F) (V := Vm W E (r + 1)) (R := W) (E := E)
      (Q1 := Qm QR QE (r + 1)) (QR1 := QR) (QE1 := QE)
      (Q2 := CFSG.LieType.Universal.Spin.quadMinus (r + 2) F b c)
      (QR2 := CFSG.LieType.Universal.Spin.binaryForm F b c)
      (QE2 := CFSG.Timmesfeld.ClassicalOrders.hypPlane F)
      (LinearEquiv.refl F (Vm W E (r + 1)))
      (minusPlaneCoordinates (n := r + 2) (F := F)) epsR epsE
      (refl_coordinate_quadratic_apply (QR := QR) (QE := QE) (r + 1))
      (quadMinus_eq_binaryForm_add_minusPlaneCoordinates (r := r) (F := F) (b := b) (c := c))
  have hN : ∀ S : Finset (Fin (r + 1)),
      (coordSupport (LinearEquiv.refl F (Vm W E (r + 1))) S).map
          N.toLinearEquiv.toLinearMap = anchoredSupport F (r + 2) S := by
    intro S
    have h := map_coordSupport_coordChange
      (psi1 := LinearEquiv.refl F (Vm W E (r + 1)))
      (psi2 := minusPlaneCoordinates (n := r + 2) (F := F))
      (epsR := epsR.toLinearEquiv) (epsE := epsE.toLinearEquiv) S
    have hNlin : N.toLinearEquiv.toLinearMap =
        (coordChange (LinearEquiv.refl F (Vm W E (r + 1)))
          (minusPlaneCoordinates (n := r + 2) (F := F))
          epsR.toLinearEquiv epsE.toLinearEquiv).toLinearMap := by
      simp [N, coordChangeIsometry_toLinearEquiv]
    rw [hNlin, h]
    exact coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := r + 2) (F := F) S
  let D0 : Finset (Fin (r + 1)) := Finset.univ.erase (0 : Fin (r + 1))
  have hD0 : ((supportedDerived (Qm QR QE (r + 1))
        (zeroDeletionSupport (K := F) (R := W) (E := E) r)).subgroupOf
        (orthDerived (Qm QR QE (r + 1)))).map
          (commutatorOrthogonalGroupCongr N).toMonoidHom =
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D0 := by
    simpa [D0, zeroDeletionSupport] using map_supportedDerived_chart N hN D0
  have hD0' : ((supportedDerived (Qm QR QE (r + 1))
        (zeroDeletionSupport (K := F) (R := W) (E := E) r)).subgroupOf
        (orthDerived (Qm QR QE (r + 1)))).map
          (commutatorOrthogonalGroupCongr N :
            orthDerived (Qm QR QE (r + 1)) →*
              orthDerived (CFSG.LieType.Universal.Spin.quadMinus (r + 2) F b c)) =
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D0 :=
    hD0
  let eN : ((supportedDerived (Qm QR QE (r + 1))
        (zeroDeletionSupport (K := F) (R := W) (E := E) r)).subgroupOf
        (orthDerived (Qm QR QE (r + 1)))) ≃*
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D0 :=
    TauCeti.Subgroup.congrOfMapEq (commutatorOrthogonalGroupCongr N) hD0'
  refine ⟨(originalDeletionGroupEquiv (Qo := Q) (QR := QR) (QE := QE) r ψ hψ hQR hQE).trans eN, ?_⟩
  intro T
  have hsuppT : coordSupport ψ T = Δ.originalAnchor ⊔ T.sup Δ.F.U := by
    simpa [ψ] using Δ.coordSupport_originalCoordinates hQ o hWS T
  have hgen := originalDeletionGroupEquiv_map_supportedDerived (Qo := Q) (QR := QR) (QE := QE)
    r ψ hψ hQ hQR hQE T
  rw [hsuppT] at hgen
  let L : Subgroup (orthDerived (Qm QR QE (r + 1))) :=
    (supportedDerived (Qm QR QE (r + 1))
      (coordSupport (LinearEquiv.refl F (Vm W E (r + 1))) (T.image Fin.succ))).subgroupOf
      (orthDerived (Qm QR QE (r + 1)))
  have hchartT : L.map (commutatorOrthogonalGroupCongr N).toMonoidHom =
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (T.image Fin.succ) :=
    map_supportedDerived_chart N hN (T.image Fin.succ)
  have hbase := map_subgroupOf_congrOfMapEq (commutatorOrthogonalGroupCongr N) hD0' L
  rw [hchartT] at hbase
  calc
    ((supportedDerived Q (Δ.originalAnchor ⊔ T.sup Δ.F.U)).subgroupOf (orthDerived Q)).map
        ((originalDeletionGroupEquiv (Qo := Q) (QR := QR) (QE := QE) r ψ hψ hQR hQE).trans
          eN).toMonoidHom
        = (((supportedDerived Q (Δ.originalAnchor ⊔ T.sup Δ.F.U)).subgroupOf
            (orthDerived Q)).map
            (originalDeletionGroupEquiv (Qo := Q) (QR := QR) (QE := QE) r ψ hψ hQR hQE).toMonoidHom).map
              eN.toMonoidHom := by
          rw [show ((originalDeletionGroupEquiv (Qo := Q) (QR := QR) (QE := QE) r ψ hψ hQR hQE).trans
              eN).toMonoidHom =
              eN.toMonoidHom.comp
                (originalDeletionGroupEquiv (Qo := Q) (QR := QR) (QE := QE) r ψ hψ hQR hQE).toMonoidHom
              from rfl, Subgroup.map_map]
    _ = (L.subgroupOf ((supportedDerived (Qm QR QE (r + 1))
          (zeroDeletionSupport (K := F) (R := W) (E := E) r)).subgroupOf
          (orthDerived (Qm QR QE (r + 1))))).map eN.toMonoidHom := by
          rw [hgen]
    _ = (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (T.image Fin.succ)).subgroupOf
          (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
            (Finset.univ.erase (0 : Fin (r + 1)))) := hbase

end OriginalCanonicalZeroDeletion

end CoordinateDeletion

end CFSG.RankThree.PartOne.KCOrthogonal

end
