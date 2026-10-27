module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

@[expose] noncomputable def s16h_sl24_statedSLMap {E E' : Type} [Field E] [Field E']
    (ρ : E →+* E') : ↥(StatedSL 2 E) →* ↥(StatedSL 2 E') where
  toFun γ := ⟨Matrix.GeneralLinearGroup.map ρ (γ : Matrix.GeneralLinearGroup (Fin 2) E), by
    apply Subgroup.subset_closure
    have hg : Matrix.GeneralLinearGroup.det (γ : Matrix.GeneralLinearGroup (Fin 2) E) = 1 :=
      Units.ext (StatedAPI.det_of_mem_statedSL γ.2)
    have hd : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map ρ (γ : Matrix.GeneralLinearGroup (Fin 2) E)) = 1 := by
      rw [Matrix.GeneralLinearGroup.map_det (n := Fin 2) (f := ρ)
        (g := (γ : Matrix.GeneralLinearGroup (Fin 2) E)), hg, map_one]
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hd⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Matrix.GeneralLinearGroup.map ρ)
  map_mul' := fun a b => by
    apply Subtype.ext
    exact map_mul (Matrix.GeneralLinearGroup.map ρ)
      (a : Matrix.GeneralLinearGroup (Fin 2) E) (b : Matrix.GeneralLinearGroup (Fin 2) E)

theorem s16h_sl24_statedSLMap_apply {E E' : Type} [Field E] [Field E'] (ρ : E →+* E')
    (γ : ↥(StatedSL 2 E)) (i j : Fin 2) :
    ((s16h_sl24_statedSLMap ρ γ : Matrix.GeneralLinearGroup (Fin 2) E') :
        Matrix (Fin 2) (Fin 2) E') i j =
      ρ (((γ : Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) i j) :=
  Matrix.GeneralLinearGroup.map_apply ρ i j (γ : Matrix.GeneralLinearGroup (Fin 2) E)

theorem s16h_sl24_statedSLMap_surjective {E E' : Type} [Field E] [Field E'] (ρ : E ≃+* E') :
    Function.Surjective (s16h_sl24_statedSLMap ρ.toRingHom) := by
  intro δ
  refine ⟨s16h_sl24_statedSLMap ρ.symm.toRingHom δ, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [s16h_sl24_statedSLMap_apply, s16h_sl24_statedSLMap_apply]
  simp

@[expose] noncomputable def s16h_sl24_natCoordEquiv {E E' : Type} [Field E] [Field E']
    (ρ : E ≃+* E') : StdMod (Fin 2) E ≃* StdMod (Fin 2) E' where
  toFun x := Multiplicative.ofAdd (fun i => ρ (Multiplicative.toAdd x i))
  invFun y := Multiplicative.ofAdd (fun i => ρ.symm (Multiplicative.toAdd y i))
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  right_inv y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [map_add]

@[simp] theorem s16h_sl24_natCoordEquiv_apply {E E' : Type} [Field E] [Field E']
    (ρ : E ≃+* E') (x : Fin 2 → E) :
    s16h_sl24_natCoordEquiv ρ (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (fun i => ρ (x i)) := rfl

@[simp] theorem s16h_sl24_toAdd_natCoordEquiv {E E' : Type} [Field E] [Field E']
    (ρ : E ≃+* E') (x : StdMod (Fin 2) E) :
    Multiplicative.toAdd (s16h_sl24_natCoordEquiv ρ x) =
      fun i => ρ (Multiplicative.toAdd x i) := rfl

theorem s16h_sl24_natAct_transport {E E' : Type} [Field E] [Field E'] (ρ : E ≃+* E')
    (γ : ↥(StatedSL 2 E')) (x : StdMod (Fin 2) E) :
    s16h_sl24_natCoordEquiv ρ
        (natAct (StatedSL 2 E) (s16h_sl24_statedSLMap ρ.symm.toRingHom γ) x) =
      natAct (StatedSL 2 E') γ (s16h_sl24_natCoordEquiv ρ x) := by
  set M : Matrix (Fin 2) (Fin 2) E' :=
    ((γ : Matrix.GeneralLinearGroup (Fin 2) E') : Matrix (Fin 2) (Fin 2) E') with hM
  have hcoe : (((s16h_sl24_statedSLMap ρ.symm.toRingHom γ : ↥(StatedSL 2 E)) :
      Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      M.map ρ.symm.toRingHom :=
    Matrix.ext fun i j => s16h_sl24_statedSLMap_apply ρ.symm.toRingHom γ i j
  apply Multiplicative.toAdd.injective
  funext i
  show ρ ((((s16h_sl24_statedSLMap ρ.symm.toRingHom γ : ↥(StatedSL 2 E)) :
      Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).mulVec
        (Multiplicative.toAdd x) i) =
    M.mulVec (fun j => ρ (Multiplicative.toAdd x j)) i
  rw [hcoe]
  refine (RingHom.map_mulVec ρ.toRingHom (M.map ρ.symm.toRingHom)
    (Multiplicative.toAdd x) i).trans ?_
  congr 1
  ext a b
  simp

theorem s16h_sl24_transport_coord {K F : Type} [Field K] [Field F] (ρ : K ≃+* F)
    {L : Subgroup (MulAut W)}
    {π : ↥(StatedSL 2 K) →* ↥L}
    {β : ↥(commSub ⊤ L) →* StdMod (Fin 2) K}
    (hπ : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : β.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L))
    (hβe : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commSub ⊤ L))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
      β ⟨_, hu⟩ = natAct (StatedSL 2 K) γ (β u)) :
    ∃ (π' : ↥(StatedSL 2 F) →* ↥L) (β' : ↥(commSub ⊤ L) →* StdMod (Fin 2) F),
      Function.Surjective π' ∧ Function.Surjective β' ∧
      β'.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) ∧
      (∀ (γ : ↥(StatedSL 2 F)) (u : ↥(commSub ⊤ L))
        (hu : ((π' γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
        β' ⟨_, hu⟩ = natAct (StatedSL 2 F) γ (β' u)) := by
  classical
  let σ : ↥(StatedSL 2 F) →* ↥(StatedSL 2 K) := s16h_sl24_statedSLMap ρ.symm.toRingHom
  let π' : ↥(StatedSL 2 F) →* ↥L := π.comp σ
  let β' : ↥(commSub ⊤ L) →* StdMod (Fin 2) F :=
    (s16h_sl24_natCoordEquiv ρ).toMonoidHom.comp β
  have hπ' : Function.Surjective π' := hπ.comp (s16h_sl24_statedSLMap_surjective ρ.symm)
  have hβ' : Function.Surjective β' :=
    (s16h_sl24_natCoordEquiv ρ).surjective.comp hβs
  have hβ'k : β'.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) := by
    ext u
    rw [MonoidHom.mem_ker]
    show (s16h_sl24_natCoordEquiv ρ) (β u) = 1 ↔ _
    rw [map_eq_one_iff _ (s16h_sl24_natCoordEquiv ρ).injective, ← MonoidHom.mem_ker, hβk]
  have hβ'e : ∀ (γ : ↥(StatedSL 2 F)) (u : ↥(commSub ⊤ L))
      (hu : ((π' γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
      β' ⟨_, hu⟩ = natAct (StatedSL 2 F) γ (β' u) := by
    intro γ u hu
    change (s16h_sl24_natCoordEquiv ρ)
        (β ⟨((π (σ γ) : ↥L) : MulAut W) (u : W), hu⟩) =
      natAct (StatedSL 2 F) γ ((s16h_sl24_natCoordEquiv ρ) (β u))
    rw [hβe (σ γ) u hu]
    exact s16h_sl24_natAct_transport ρ γ (β u)
  exact ⟨π', β', hπ', hβ', hβ'k, hβ'e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
