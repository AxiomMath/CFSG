module

public import CFSG.Monster.B.Geometry.InitialIsometryTransport
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldMain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding
open CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4

variable {δ : Chamber → Chamber → WeylGroup .F4} (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
    chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i)
include hδ hadj

theorem native_eq_simple_iff
    (i : Fin Tag.F4.rank) (x y : Chamber) :
    δ x y = (coxeterSystem .F4).simple i ↔ x ≠ y ∧ chamberCS.adj i x y := by
  rw [hadj]
  constructor
  · intro h
    exact ⟨hδ.ne_of_eq_simple h, Or.inr h⟩
  · rintro ⟨hne, h | h⟩
    · exact absurd ((hδ.eq_one_iff x y).mp h) hne
    · exact h

theorem native_end_model
    {F : Type*} {Y : ChamberSystem (Fin Tag.F4.rank) F}
    {k : Fin Tag.F4.rank} (hYk : Y.adj k = Eq) (x : Chamber)
    (h : ∃ ψ : F → Chamber, Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ k} x) ∧
      ∀ a b (j : Fin Tag.F4.rank), j ≠ k → (chamberCS.adj j (ψ a) (ψ b) ↔ Y.adj j a b)) :
    ∃ f : residue (coxeterSystem .F4) δ {j | j ≠ k} x → F,
      IsChamberModel (coxeterSystem .F4) (resDist (coxeterSystem .F4) δ {j | j ≠ k} x) Y f := by
  obtain ⟨ψ, hψ, hψadj⟩ := h
  rw [ChamberSystem.residue_eq_of_adj_iff hδ hadj] at hψ
  refine exists_isChamberModel_of_bijOn hψ fun a b j => ?_
  by_cases hj : j = k
  · subst hj
    rw [hYk]
    constructor
    · intro e
      exact absurd e (dist_ne_simple_of_mem_residue hδ (hψ.mapsTo (Set.mem_univ a))
        (hψ.mapsTo (Set.mem_univ b)) (by simp))
    · rintro ⟨hne, rfl⟩
      exact absurd rfl hne
  · rw [native_eq_simple_iff hδ hadj, hψadj a b j hj,
      hψ.injOn.ne_iff (Set.mem_univ a) (Set.mem_univ b)]

omit hδ hadj in
theorem polarChamber_adj_of_ne {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {P : PolarSpace K V} {ι : Type*} {p l π k : ι} (hp : k ≠ p) (hl : k ≠ l) (hπ : k ≠ π) :
    (polarChamber P p l π).adj k = Eq := by
  unfold polarChamber ChamberSystem.ofThree
  dsimp only
  rw [ite_eq_right hp, ite_eq_right hl, ite_eq_right hπ]

theorem hasClassicalEnds_native :
    HasClassicalEnds δ where
  unit x := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hU, -⟩ := short_F4_chamber_system_local_buildings
    exact native_end_model hδ hadj (k := 0) (polarChamber_adj_of_ne (by decide) (by decide)
      (by decide)) x (hU x)
  orth x := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hO, -⟩ := short_F4_chamber_system_local_buildings
    exact native_end_model hδ hadj (k := 3) (polarChamber_adj_of_ne (by decide) (by decide)
      (by decide)) x (hO x)

end CFSG.Monster.B.TwoA.Amalgam
