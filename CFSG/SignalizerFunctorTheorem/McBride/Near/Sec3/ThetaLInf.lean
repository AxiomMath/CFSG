module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm33Transport
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ThetaLInfAux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ThetaLInfAux3

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {Y X Z : Subgroup G}

namespace Thm33h

omit [Finite G] in
theorem iThetaL_le (A X Y : Subgroup G) : iThetaL A X Y ≤ X :=
  iSup₂_le fun P hP => (Thm33a.pair_le₂ (X₁ := P.1) (X₂ := P.2) hP).trans
    (Thm33a.pair_le (X₁ := P.1) (X₂ := P.2) hP)

omit [Finite G] in
theorem iThetaM_le (A X Y : Subgroup G) : iThetaM A X Y ≤ X :=
  iSup₂_le fun P hP => Thm33a.pair_le (X₁ := P.1) (X₂ := P.2) hP

omit [Finite G] in
theorem admits_iThetaL_left (A X Y : Subgroup G) : Admits A (iThetaL A X Y) :=
  Admits.iSup fun _ => Admits.iSup fun hP => hP.1.2.1.admits_left

theorem thetaL_inf_le
    (hθ : NearFunctor p A θ) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A)
    (hb1 : b ≠ 1) (hX : θ a ∈ cset p A θ Y) (hZ : θ b ∈ cset p A θ Y) :
    thetaL p A θ Y (θ a) ⊓ θ b ≤ thetaL p A θ Y (θ b) := by
  have hXm : θ a ∈ mtil p A θ := hX.1
  have hZm : θ b ∈ mtil p A θ := hZ.1
  have hactX := Thm33a.nearAsolvAction_of_mem_mtil hθ hXm
  have hactZ := Thm33a.nearAsolvAction_of_mem_mtil hθ hZm
  have hneX := Thm33Transport.nonempty_iPairsY hθ hX
  have hneZ := Thm33Transport.nonempty_iPairsY hθ hZ
  rw [Thm33Transport.thetaL_eq_iThetaL hθ hXm, Thm33Transport.thetaL_eq_iThetaL hθ hZm]
  have hPX := iThetaM_iThetaL_mem hactX hneX
  have hPZ := iThetaM_iThetaL_mem hactZ hneZ
  have hcen : cenIn (θ b) (A : Set G) = cenIn (θ a) (A : Set G) :=
    (cenIn_eq_dsub_of_mem_mtil hθ hZm).trans (cenIn_eq_dsub_of_mem_mtil hθ hXm).symm
  refine Thm33h.le_of_normalized hactZ hPZ ha ha1 ?_ ?_ ?_ ?_ ?_
  ·
    calc iThetaL A (θ a) Y ⊓ θ b ≤ iThetaY A (θ a) Y ⊓ θ b :=
          inf_le_inf_right _ (iThetaL_le_iThetaY A (θ a) Y)
      _ ≤ θ a ⊓ iThetaY A (θ b) Y := Thm33Transport.iThetaY_inf_le hθ hX hZ
      _ ≤ iThetaY A (θ b) Y := inf_le_right
      _ ≤ iThetaM A (θ b) Y := iThetaY_le_iThetaM hactZ hneZ
  · exact inf_le_left.trans ((Thm33h.iThetaL_le A (θ a) Y).trans
      (hθ.isFunctor.le_centralizer a ha ha1))
  · exact Admits.inf (Thm33h.admits_iThetaL_left A (θ a) Y) hZm.1.1
  · calc iThetaL A (θ a) Y ⊓ θ b ⊓ cenIn (θ b) (A : Set G)
        ≤ iThetaL A (θ a) Y ⊓ cenIn (θ a) (A : Set G) := by
          rw [hcen]
          exact inf_le_inf inf_le_left le_rfl
      _ = Y := Thm33a.pair_inf hPX
      _ ≤ iThetaL A (θ b) Y := Thm33a.pair_Y_le₂ hPZ
  · intro c hc
    obtain ⟨hcM, hca⟩ := Subgroup.mem_inf.1 hc
    have hcZ : c ∈ θ b := Thm33h.iThetaM_le A (θ b) Y hcM
    have hcX : c ∈ θ a := hθ.isFunctor.balance b hb hb1 a ha ha1 (Subgroup.mem_inf.2 ⟨hcZ, hca⟩)
    have hcU : c ∈ iThetaU A (θ b) Y := iThetaM_le_iThetaU A (θ b) Y hcM
    have hcU' : c ∈ iThetaU A (θ a) Y :=
      (Thm33Transport.iThetaU_inf_le hθ hZ hX (Subgroup.mem_inf.2 ⟨hcU, hcX⟩)).2
    have hcL : c ∈ Subgroup.normalizer ((iThetaL A (θ a) Y : Subgroup G) : Set G) :=
      Thm33h.admits_iThetaL hactX hneX hcU'
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hcL, Subgroup.le_normalizer hcZ⟩

end Thm33h

theorem thetaL_inf'
    (hθ : NearFunctor p A θ) (_hY : Y ∈ dset p A θ) {a b : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) (hX : θ a ∈ cset p A θ Y)
    (hZ : θ b ∈ cset p A θ Y) :
    thetaL p A θ Y (θ a) ⊓ θ b = θ a ⊓ thetaL p A θ Y (θ b) := by
  have hLX : thetaL p A θ Y (θ a) ≤ θ a := by
    rw [Thm33Transport.thetaL_eq_iThetaL hθ hX.1]
    exact Thm33h.iThetaL_le A (θ a) Y
  have hLZ : thetaL p A θ Y (θ b) ≤ θ b := by
    rw [Thm33Transport.thetaL_eq_iThetaL hθ hZ.1]
    exact Thm33h.iThetaL_le A (θ b) Y
  refine le_antisymm (le_inf (inf_le_left.trans hLX)
    (Thm33h.thetaL_inf_le hθ ha ha1 hb hb1 hX hZ)) ?_
  refine le_inf ?_ (inf_le_right.trans hLZ)
  rw [inf_comm]
  exact Thm33h.thetaL_inf_le hθ hb hb1 ha ha1 hZ hX

end CFSG.SignalizerFunctorTheorem.McBride.Near
