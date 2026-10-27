module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33b
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ThetaUMem

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {Y X Z : Subgroup G}

namespace Thm33Transport

theorem esetX_eq_iEset (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    esetX p A θ Y X = iEset A X Y := by
  have hD := cenIn_eq_dsub_of_mem_mtil hθ hX
  ext Z
  constructor
  · rintro ⟨⟨hZ, hZY⟩, hZX⟩
    exact ⟨(mem_mhat_iff_isDAIn hθ hX).mp ⟨hZX, hZ⟩, by rw [hD]; exact hZY⟩
  · rintro ⟨hZ, hZY⟩
    rw [hD] at hZY
    exact ⟨⟨((mem_mhat_iff_isDAIn hθ hX).mpr hZ).2, hZY⟩, hZ.1⟩

theorem thetaY_eq_iThetaY (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    thetaY p A θ Y X = iThetaY A X Y := by
  unfold thetaY iThetaY
  rw [esetX_eq_iEset hθ hX]

theorem thetaM_eq_iThetaM (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    thetaM p A θ Y X = iThetaM A X Y := by
  unfold thetaM iThetaM
  rw [pairsYX_eq_iPairsY hθ hX]

theorem thetaL_eq_iThetaL (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    thetaL p A θ Y X = iThetaL A X Y := by
  unfold thetaL iThetaL
  rw [pairsYX_eq_iPairsY hθ hX]

theorem nonempty_iPairsY (hθ : NearFunctor p A θ) (hX : X ∈ cset p A θ Y) :
    (iPairsY A X Y).Nonempty := by
  rw [← pairsYX_eq_iPairsY hθ hX.1]
  exact hX.2

omit [Finite G] in
theorem orbitClosure_mono {V W : Subgroup G} (h : V ≤ W) : orbitClosure Y V ≤ orbitClosure Y W :=
  orbitClosure_le fun _ ha => map_conj_le_orbitClosure Y (h ha)

omit [Finite G] in
theorem admits_dsub_sup (hX : X ∈ mtil p A θ) : Admits (dsub A θ ⊔ A) X :=
  sup_le (admits_dsub_of_le hX.2) hX.1.1

theorem iThetaU_inf_le
    (hθ : NearFunctor p A θ) (hX : X ∈ cset p A θ Y) (hZ : Z ∈ cset p A θ Y) :
    iThetaU A X Y ⊓ Z ≤ X ⊓ iThetaU A Z Y := by
  have hXm : X ∈ mtil p A θ := hX.1
  have hZm : Z ∈ mtil p A θ := hZ.1
  have hactX := Thm33a.nearAsolvAction_of_mem_mtil hθ hXm
  have hDZX : cenIn Z (A : Set G) = cenIn X (A : Set G) :=
    (cenIn_eq_dsub_of_mem_mtil hθ hZm).trans (cenIn_eq_dsub_of_mem_mtil hθ hXm).symm
  have hDZ : cenIn X (A : Set G) ≤ Z := by
    rw [cenIn_eq_dsub_of_mem_mtil hθ hXm]
    exact hZm.2
  have hZadm : Admits (cenIn X (A : Set G) ⊔ A) Z := by
    rw [cenIn_eq_dsub_of_mem_mtil hθ hXm]
    exact admits_dsub_sup hZm
  obtain ⟨⟨X₁, X₂⟩, hP⟩ := nonempty_iPairsY hθ hX
  have hmem := iThetaU_mem_iUset hactX ⟨_, hP⟩
  have hYD : Y ≤ cenIn X (A : Set G) := Thm33a.pair_Y_le hP
  have hVU : iThetaU A X Y ⊓ Z ∈ iUset A Z Y := by
    refine ⟨⟨inf_le_right, ?_⟩, ?_, ?_⟩
    · rw [hDZX]
      exact Admits.inf Thm33a.admits_iThetaU hZadm
    · rw [hDZX]
      exact le_inf (Thm33a.dsub_le_iThetaU hP) hDZ
    · rw [hDZX]
      refine le_antisymm ?_ (le_inf (le_orbitClosure _ _) hYD)
      calc orbitClosure Y (iThetaU A X Y ⊓ Z) ⊓ cenIn X (A : Set G)
          ≤ orbitClosure Y (iThetaU A X Y) ⊓ cenIn X (A : Set G) :=
            inf_le_inf_right _ (orbitClosure_mono inf_le_left)
        _ = Y := hmem.2.2
  exact le_inf (inf_le_left.trans Thm33a.iThetaU_le) (Thm33a.le_iThetaU hVU)

theorem iThetaY_inf_le
    (hθ : NearFunctor p A θ) (hX : X ∈ cset p A θ Y) (hZ : Z ∈ cset p A θ Y) :
    iThetaY A X Y ⊓ Z ≤ X ⊓ iThetaY A Z Y := by
  have hXm : X ∈ mtil p A θ := hX.1
  have hZm : Z ∈ mtil p A θ := hZ.1
  have hactX := Thm33a.nearAsolvAction_of_mem_mtil hθ hXm
  have hDZX : cenIn Z (A : Set G) = cenIn X (A : Set G) :=
    (cenIn_eq_dsub_of_mem_mtil hθ hZm).trans (cenIn_eq_dsub_of_mem_mtil hθ hXm).symm
  have hDZ : cenIn X (A : Set G) ≤ Z := by
    rw [cenIn_eq_dsub_of_mem_mtil hθ hXm]
    exact hZm.2
  have hZadm : Admits (cenIn X (A : Set G) ⊔ A) Z := by
    rw [cenIn_eq_dsub_of_mem_mtil hθ hXm]
    exact admits_dsub_sup hZm
  have hmem := iThetaY_mem_iEset hactX (nonempty_iPairsY hθ hX)
  have hVE : iThetaY A X Y ⊓ Z ∈ iEset A Z Y := by
    refine ⟨⟨inf_le_right, ?_⟩, ?_⟩
    · rw [hDZX]
      exact Admits.inf hmem.1.2 hZadm
    · rw [hDZX]
      refine le_antisymm ?_ ?_
      · intro x hx
        obtain ⟨⟨hxT, -⟩, hxD⟩ := Subgroup.mem_inf.mp hx
        rw [← hmem.2]
        exact Subgroup.mem_inf.mpr ⟨hxT, hxD⟩
      · intro y hy
        have hy' : y ∈ iThetaY A X Y ⊓ cenIn X (A : Set G) := by
          rw [hmem.2]
          exact hy
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hy'.1, hDZ hy'.2⟩, hy'.2⟩
  exact le_inf (inf_le_left.trans hmem.1.1) (le_iSup₂ (f := fun W (_ : W ∈ iEset A Z Y) => W) _ hVE)

end Thm33Transport

theorem thetaM_thetaL_mem_pairsYX'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) :
    (thetaM p A θ Y X, thetaL p A θ Y X) ∈ pairsYX p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  rw [Thm33Transport.thetaM_eq_iThetaM hθ hXm, Thm33Transport.thetaL_eq_iThetaL hθ hXm,
    pairsYX_eq_iPairsY hθ hXm]
  exact iThetaM_iThetaL_mem (Thm33a.nearAsolvAction_of_mem_mtil hθ hXm)
    (Thm33Transport.nonempty_iPairsY hθ hX)

theorem kOf_le_thetaM'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : kOf X ≤ thetaM p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  rw [Thm33Transport.thetaM_eq_iThetaM hθ hXm]
  exact kOf_le_iThetaM (Thm33a.nearAsolvAction_of_mem_mtil hθ hXm)
    (Thm33Transport.nonempty_iPairsY hθ hX)

theorem thetaY_mem_esetX'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaY p A θ Y X ∈ esetX p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  rw [Thm33Transport.thetaY_eq_iThetaY hθ hXm, Thm33Transport.esetX_eq_iEset hθ hXm]
  exact iThetaY_mem_iEset (Thm33a.nearAsolvAction_of_mem_mtil hθ hXm)
    (Thm33Transport.nonempty_iPairsY hθ hX)

theorem thetaL_le_thetaY' (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaL p A θ Y X ≤ thetaY p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  rw [Thm33Transport.thetaL_eq_iThetaL hθ hXm, Thm33Transport.thetaY_eq_iThetaY hθ hXm]
  exact iThetaL_le_iThetaY A X Y

theorem thetaY_le_thetaM'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaY p A θ Y X ≤ thetaM p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  rw [Thm33Transport.thetaY_eq_iThetaY hθ hXm, Thm33Transport.thetaM_eq_iThetaM hθ hXm]
  exact iThetaY_le_iThetaM (Thm33a.nearAsolvAction_of_mem_mtil hθ hXm)
    (Thm33Transport.nonempty_iPairsY hθ hX)

theorem thetaM_le_thetaU' (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaM p A θ Y X ≤ thetaU p A θ Y X := by
  have hXm : X ∈ mtil p A θ := hX.1
  rw [Thm33Transport.thetaM_eq_iThetaM hθ hXm, Thm33a.thetaU_eq_iThetaU hθ hXm]
  exact iThetaM_le_iThetaU A X Y

theorem thetaU_inf'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) (hZ : Z ∈ cset p A θ Y) :
    thetaU p A θ Y X ⊓ Z = X ⊓ thetaU p A θ Y Z := by
  rw [Thm33a.thetaU_eq_iThetaU hθ hX.1, Thm33a.thetaU_eq_iThetaU hθ hZ.1]
  refine le_antisymm (Thm33Transport.iThetaU_inf_le hθ hX hZ) ?_
  rw [inf_comm X, inf_comm (iThetaU A X Y)]
  exact Thm33Transport.iThetaU_inf_le hθ hZ hX

theorem thetaY_inf'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) (hZ : Z ∈ cset p A θ Y) :
    thetaY p A θ Y X ⊓ Z = X ⊓ thetaY p A θ Y Z := by
  rw [Thm33Transport.thetaY_eq_iThetaY hθ hX.1, Thm33Transport.thetaY_eq_iThetaY hθ hZ.1]
  refine le_antisymm (Thm33Transport.iThetaY_inf_le hθ hX hZ) ?_
  rw [inf_comm X, inf_comm (iThetaY A X Y)]
  exact Thm33Transport.iThetaY_inf_le hθ hZ hX

end CFSG.SignalizerFunctorTheorem.McBride.Near
