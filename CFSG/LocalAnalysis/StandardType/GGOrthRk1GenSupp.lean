module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

private theorem q2cO5s_isCompl_orthogonal {W : Submodule K V}
    (hW : ∀ w ∈ W, (∀ v ∈ W, polar Q v w = 0) → w = 0) :
    IsCompl W (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (B := QuadraticMap.polarBilin Q) (fun x y hxy => ?_)).mpr ?_
  · rw [QuadraticMap.polarBilin_apply_apply] at hxy ⊢
    rw [QuadraticMap.polar_comm]
    exact hxy
  · rw [Submodule.disjoint_def]
    intro w hw hw'
    exact hW w hw fun v hv => LinearMap.BilinForm.mem_orthogonal_iff.mp hw' v hv

theorem TBJOmData.component_eq_zero_of_orthogonal (Δ : TBJOmData Q p A r)
    {x : V} {j : Fin r} {v : Fin r → V} (hv : ∀ k, v k ∈ Δ.F.U k)
    (hx : x = ∑ k, v k) (horth : ∀ w ∈ Δ.F.U j, polar Q w x = 0) : v j = 0 := by
  refine Δ.F.nondeg j (v j) (hv j) (fun w hw => ?_)
  have h1 : polar Q w x = 0 := horth w hw
  rw [hx, ← QuadraticMap.polarBilin_apply_apply, map_sum] at h1
  simp only [QuadraticMap.polarBilin_apply_apply] at h1
  rw [Finset.sum_eq_single j] at h1
  · exact h1
  · intro k _ hkj
    exact Δ.F.orth j k (Ne.symm hkj) w hw (v k) (hv k)
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private theorem q2cO5s_iSup_pieces_nondegenerate (Δ : TBJOmData Q p A r) :
    ∀ w ∈ (⨆ k, Δ.F.U k : Submodule K V),
      (∀ v ∈ (⨆ k, Δ.F.U k), polar Q v w = 0) → w = 0 := by
  intro w hw horth
  classical
  obtain ⟨f, hf, hfw⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun k => Δ.F.U k) w).mp hw
  have hsum : f.sum (fun _ xi => xi) = ∑ k, f k :=
    Finsupp.sum_fintype f (fun _ xi => xi) (by simp)
  have hw' : w = ∑ k, f k := by
    rw [← hsum]
    exact hfw.symm
  rw [hw']
  refine Finset.sum_eq_zero (fun j _ => ?_)
  exact TBJOmData.component_eq_zero_of_orthogonal Δ hf hw'
    (fun u hu => horth u (Submodule.mem_iSup_of_mem j hu))

theorem TBJOmData.exists_sum_pieces (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (v : V) :
    ∃ u : Fin r → V, (∀ k, u k ∈ Δ.F.U k) ∧ ∑ k, u k = v := by
  classical
  have hnd := q2cO5s_iSup_pieces_nondegenerate (Q := Q) Δ
  have hcompl : IsCompl (⨆ k, Δ.F.U k)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (⨆ k, Δ.F.U k)) :=
    q2cO5s_isCompl_orthogonal hnd
  have hbot : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (⨆ k, Δ.F.U k) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    apply hfix z
    intro a ha
    rw [← Δ.F.range] at ha
    obtain ⟨s, rfl⟩ := ha
    rw [Δ.F.fix s z]
    intro j _ u hu
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz) u (Submodule.mem_iSup_of_mem j hu)
  have htop : (⨆ k, Δ.F.U k) = ⊤ := by
    have h := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at h
  have hv : v ∈ (⨆ k, Δ.F.U k) := htop ▸ Submodule.mem_top
  obtain ⟨f, hf, hfv⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun k => Δ.F.U k) v).mp hv
  refine ⟨f, hf, ?_⟩
  rw [Finsupp.sum_fintype f (fun _ xi => xi) (by simp)] at hfv
  exact hfv

private theorem q2cO5s_mapsTo_sup_of_fixes (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) {S : Finset (Fin r)} {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) (hgS : ∀ k, k ∉ S → ∀ u ∈ Δ.F.U k, g u = u) :
    ∀ k ∈ S, ∀ u ∈ Δ.F.U k, g u ∈ (⨆ l ∈ S, Δ.F.U l) := by
  intro k hkS u hu
  have hgO := CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q hg
  obtain ⟨v, hv, hgv⟩ := Δ.exists_sum_pieces hfix (g u)
  have hzero : ∀ l, l ∉ S → v l = 0 := by
    intro l hlS
    refine TBJOmData.component_eq_zero_of_orthogonal Δ hv hgv.symm (fun w hw => ?_)
    have hgw : g w = w := hgS l hlS w hw
    have hgwinv : g⁻¹ w = w := by
      calc g⁻¹ w = g⁻¹ (g w) := by rw [hgw]
        _ = w := CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' g w
    have hpolar : polar Q w (g u) = polar Q (g⁻¹ w) u := by
      rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO (g⁻¹ w) u]
      exact congrArg (fun z => polar Q z (g u))
        (CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply' g w).symm
    rw [hpolar, hgwinv]
    exact Δ.F.orth l k (by rintro rfl; exact hlS hkS) w hw u hu
  have hsumS : ∑ l ∈ S, v l = g u := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun l _ hlS => hzero l hlS)]
    exact hgv
  rw [← hsumS]
  exact Submodule.sum_mem (p := ⨆ l ∈ S, Δ.F.U l) (t := S) (f := v)
    (fun l hl => Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem hl (hv l)))

private theorem q2cO5s_fixes_sup (Δ : TBJOmData Q p A r) {S : Finset (Fin r)}
    {g : V ≃ₗ[K] V} (hg : ∀ k ∈ S, ∀ u ∈ Δ.F.U k, g u = u) :
    ∀ v ∈ (⨆ l ∈ S, Δ.F.U l), g v = v := by
  intro v hv
  refine Submodule.iSup_induction (motive := fun x => g x = x)
    (fun l => ⨆ (_ : l ∈ S), Δ.F.U l) hv ?_ ?_ ?_
  · intro l x hx
    refine Submodule.iSup_induction (motive := fun y => g y = y)
      (fun _ : l ∈ S => Δ.F.U l) hx ?_ ?_ ?_
    · intro hl y hy
      exact hg l hl y hy
    · rw [map_zero]
    · intro a b ha hb
      rw [map_add, ha, hb]
  · rw [map_zero]
  · intro a b ha hb
    rw [map_add, ha, hb]

theorem TBJOmData.commute_of_fixes_outside (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) {S S' : Finset (Fin r)} (hSS' : Disjoint S S')
    {g g' : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q) (hg' : g' ∈ orthDerived Q)
    (hgS : ∀ k, k ∉ S → ∀ u ∈ Δ.F.U k, g u = u)
    (hg'S' : ∀ k, k ∉ S' → ∀ u ∈ Δ.F.U k, g' u = u) : g * g' = g' * g := by
  classical
  have hA : ∀ k ∈ S, ∀ u ∈ Δ.F.U k, g u ∈ (⨆ l ∈ S, Δ.F.U l) :=
    q2cO5s_mapsTo_sup_of_fixes Δ hfix hg hgS
  have hA' : ∀ k ∈ S', ∀ u ∈ Δ.F.U k, g' u ∈ (⨆ l ∈ S', Δ.F.U l) :=
    q2cO5s_mapsTo_sup_of_fixes Δ hfix hg' hg'S'
  have hB : ∀ v ∈ (⨆ l ∈ S, Δ.F.U l), g' v = v :=
    q2cO5s_fixes_sup Δ (fun k hk => hg'S' k (Finset.disjoint_left.mp hSS' hk))
  have hB' : ∀ v ∈ (⨆ l ∈ S', Δ.F.U l), g v = v :=
    q2cO5s_fixes_sup Δ (fun k hk => hgS k (Finset.disjoint_right.mp hSS' hk))
  ext v
  obtain ⟨u, hu, rfl⟩ := Δ.exists_sum_pieces hfix v
  simp only [LinearEquiv.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkS : k ∈ S
  · have hkS' : k ∉ S' := Finset.disjoint_left.mp hSS' hkS
    have h1 : g' (u k) = u k := hg'S' k hkS' (u k) (hu k)
    have h2 : g' (g (u k)) = g (u k) := hB (g (u k)) (hA k hkS (u k) (hu k))
    simp only [h1, h2]
  · by_cases hkS' : k ∈ S'
    · have hkg : g (u k) = u k := hgS k hkS (u k) (hu k)
      have h2 : g (g' (u k)) = g' (u k) := hB' (g' (u k)) (hA' k hkS' (u k) (hu k))
      simp only [hkg, h2]
    · have h1 : g (u k) = u k := hgS k hkS (u k) (hu k)
      have h2 : g' (u k) = u k := hg'S' k hkS' (u k) (hu k)
      simp only [h1, h2]

theorem TBJOmData.reflFixed_comm_index (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Δ.reflFixed i j = Δ.reflFixed j i := by
  have h : reflFixedCoord p r i j = reflFixedCoord p r j i := by
    ext f
    simp [reflFixedCoord, MonoidHom.mem_ker, div_eq_one, eq_comm]
  exact congrArg (fun H => H.map Δ.τ) h

theorem TBJOmData.reflFixedPos_comm_index (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Δ.reflFixedPos i j = Δ.reflFixedPos j i := by
  have h : reflFixedCoordPos p r i j = reflFixedCoordPos p r j i := by
    ext f
    simp [reflFixedCoordPos, MonoidHom.mem_ker, mul_comm]
  exact congrArg (fun H => H.map Δ.τ) h

theorem TBJOmData.rankOne_comm_index (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Δ.rankOne i j = Δ.rankOne j i := by
  unfold TBJOmData.rankOne
  rw [Δ.reflFixed_comm_index i j]

theorem TBJOmData.rankOnePos_comm_index (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Δ.rankOnePos i j = Δ.rankOnePos j i := by
  unfold TBJOmData.rankOnePos
  rw [Δ.reflFixedPos_comm_index i j]

theorem TBJOmData.rankOne_le (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Δ.rankOne i j ≤ orthDerived Q := by
  exact (ggOTwoPrime_le _).trans inf_le_right

theorem TBJOmData.rankOnePos_le (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Δ.rankOnePos i j ≤ orthDerived Q := by
  exact (ggOTwoPrime_le _).trans inf_le_right

end OrthTorus

end CFSG.StandardType

end
