module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs

public section

namespace CFSG.StandardType

theorem GGResTwoNodeSideDatum.transport
    {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Bs' X' J' : Subgroup G'}
    (e : ↥Bs ≃* ↥Bs')
    (hX : ggAutomizer X' Bs' =
      (ggAutomizer X Bs).map (MulAut.congr e).toMonoidHom)
    (hJ : ggAutomizer J' Bs' =
      (ggAutomizer J Bs).map (MulAut.congr e).toMonoidHom)
    (hD : GGResTwoNodeSideDatum p Bs X J) :
    GGResTwoNodeSideDatum p Bs' X' J' := by
  classical
  obtain ⟨Λ, instF, instD, b1, b2, M, C, MJ, V, instA, instM, ι, φ, h, α,
    hb, hWM, hC, hWMJ, hMJ, hlin, hrefl, hpair, hXe, hXclos, hJe, hJclos, hJrefl⟩ := hD
  let g : MulAut ↥Bs →* MulAut ↥Bs' := (MulAut.congr e).toMonoidHom
  obtain ⟨fX, hXe⟩ := hXe
  obtain ⟨fJ, hJe⟩ := hJe
  have hg : Function.Injective g := (MulAut.congr e).injective
  let ι' : Additive ↥Bs' ≃+ V := (MulEquiv.toAdditive e.symm).trans ι
  let φ' : Λ → MulAut ↥Bs' := fun i => g (φ i)
  have hφ' : ∀ i, φ' i = MulAut.congr e (φ i) := fun _ => rfl
  have hlin' : ∀ i w, ggLin (p := p) ι' (φ' i) w = w - α i w • h i := by
    intro i w
    change ggLin (p := p) ((MulEquiv.toAdditive e.symm).trans ι)
      (MulAut.congr e (φ i)) w = w - α i w • h i
    rw [ggLin_mulEquiv_congr e ι (φ i)]
    exact hlin i w
  have hrefl' : ∀ i, GGIsReflection p (φ' i) := by
    intro i
    exact (F4AutRefl.ggIsReflection_congr_iff e (φ i)).mpr (hrefl i)
  let eXAut : ↥(ggAutomizer X Bs) ≃* ↥(ggAutomizer X' Bs') :=
    (Subgroup.equivMapOfInjective (ggAutomizer X Bs) g hg).trans
      (MulEquiv.subgroupCongr hX.symm)
  have hXe' : ∀ i, (eXAut (fX (M.simple i)) : MulAut ↥Bs') = φ' i := by
    intro i
    change MulAut.congr e ((fX (M.simple i) : MulAut ↥Bs)) = MulAut.congr e (φ i)
    rw [hXe i]
  let eJAut : ↥(ggAutomizer J Bs) ≃* ↥(ggAutomizer J' Bs') :=
    (Subgroup.equivMapOfInjective (ggAutomizer J Bs) g hg).trans
      (MulEquiv.subgroupCongr hJ.symm)
  have hJe' : ∀ j, (eJAut (fJ (MJ.simple j)) : MulAut ↥Bs') = φ' j := by
    intro j
    change MulAut.congr e ((fJ (MJ.simple j) : MulAut ↥Bs)) = MulAut.congr e (φ j)
    rw [hJe j]
  have hXclos' : ggAutomizer X' Bs' = Subgroup.closure (Set.range φ') := by
    calc
      ggAutomizer X' Bs' = (ggAutomizer X Bs).map g := hX
      _ = (Subgroup.closure (Set.range φ)).map g := by rw [hXclos]
      _ = Subgroup.closure (g '' Set.range φ) := by rw [MonoidHom.map_closure]
      _ = Subgroup.closure (Set.range φ') := by
            rw [← Set.range_comp' g φ]
  have hJclos' : ggAutomizer J' Bs' = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b1 ∧ j ≠ b2} => φ' j) := by
    calc
      ggAutomizer J' Bs' = (ggAutomizer J Bs).map g := hJ
      _ = (Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b1 ∧ j ≠ b2} => φ j)).map g := by
            rw [hJclos]
      _ = Subgroup.closure (g '' Set.range fun j : {j : Λ // j ≠ b1 ∧ j ≠ b2} => φ j) := by
            rw [MonoidHom.map_closure]
      _ = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b1 ∧ j ≠ b2} => φ' j) := by
            rw [← Set.range_comp' g (fun j : {j : Λ // j ≠ b1 ∧ j ≠ b2} => φ j)]
  have hJrefl' : GGReflConjSimple p (ggAutomizer J' Bs')
      (fun j : {j : Λ // j ≠ b1 ∧ j ≠ b2} => φ' j) := by
    intro t' htA' htR'
    rw [hJ] at htA'
    obtain ⟨t, htA, rfl⟩ := Subgroup.mem_map.mp htA'
    have htR : GGIsReflection p t :=
      (F4AutRefl.ggIsReflection_congr_iff e t).mp htR'
    obtain ⟨w, hwA, j, hwj⟩ := hJrefl t htA htR
    refine ⟨MulAut.congr e w, ?_, j, ?_⟩
    · rw [hJ]
      exact Subgroup.mem_map.mpr ⟨w, hwA, rfl⟩
    · rw [hwj]
      change g (w * φ j * w⁻¹) = g w * g (φ j) * (g w)⁻¹
      rw [map_mul, map_mul, map_inv]
  exact ⟨Λ, instF, instD, b1, b2, M, C, MJ, V, instA, instM, ι', φ', h, α,
    hb, hWM, hC, hWMJ, hMJ, hlin', hrefl', hpair, ⟨fX.trans eXAut, hXe'⟩,
    hXclos', ⟨fJ.trans eJAut, hJe'⟩, hJclos', hJrefl'⟩

theorem GGResTwoNodeSideDatum.transport_iff
    {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Bs' X' J' : Subgroup G'}
    (e : ↥Bs ≃* ↥Bs')
    (hX : ggAutomizer X' Bs' =
      (ggAutomizer X Bs).map (MulAut.congr e).toMonoidHom)
    (hJ : ggAutomizer J' Bs' =
      (ggAutomizer J Bs).map (MulAut.congr e).toMonoidHom) :
    GGResTwoNodeSideDatum p Bs X J ↔ GGResTwoNodeSideDatum p Bs' X' J' := by
  refine ⟨GGResTwoNodeSideDatum.transport e hX hJ, ?_⟩
  have hcompX : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id (MulAut ↥Bs) := by
    ext φ
    simp [MulAut.congr_apply]
  have hXsymm : ggAutomizer X Bs =
      (ggAutomizer X' Bs').map (MulAut.congr e.symm).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (MulAut.congr e.symm).toMonoidHom) hX
    rw [Subgroup.map_map] at h1
    rw [hcompX, Subgroup.map_id] at h1
    exact h1.symm
  have hJsymm : ggAutomizer J Bs =
      (ggAutomizer J' Bs').map (MulAut.congr e.symm).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (MulAut.congr e.symm).toMonoidHom) hJ
    rw [Subgroup.map_map] at h1
    rw [hcompX, Subgroup.map_id] at h1
    exact h1.symm
  exact GGResTwoNodeSideDatum.transport e.symm hXsymm hJsymm

end CFSG.StandardType

end
