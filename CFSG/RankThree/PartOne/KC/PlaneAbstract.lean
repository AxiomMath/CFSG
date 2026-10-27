module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory

theorem autThetaT_map_subtype {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) (hA : A ≠ ⊥) :
    autThetaT p B (A.map B.subtype) = (thetaT p A).map B.subtype := by
  apply le_antisymm _ (map_subtype_thetaT_le hp B A)
  obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  intro x hx
  have hx' := hx
  simp only [autThetaT, Subgroup.mem_iInf] at hx'
  have hxB : x ∈ B := by
    have h := hx' (a₀ : M) (Subgroup.mem_map_of_mem _ a₀.2) (fun h => ha₀ (Subtype.ext
      (Subtype.ext (by simpa using h))))
    exact (inf_le_left : B ⊓ centralizer ({(a₀ : M)} : Set M) ≤ B)
      (Subgroup.map_subtype_le _ h)
  refine Subgroup.mem_map.mpr ⟨⟨x, hxB⟩, ?_, rfl⟩
  simp only [thetaT, Subgroup.mem_iInf]
  intro b hb hb1
  have h := hx' (b : M) (Subgroup.mem_map_of_mem _ hb)
    (fun h => hb1 (Subtype.ext (by simpa using h)))
  rw [← map_subtype_theta_centralizer hp B b] at h
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
  have : y = ⟨x, hxB⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem autPlaneProduct_map_subtype {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) (hA : A ≠ ⊥) (t : B) :
    autPlaneProduct p B (A.map B.subtype) (t : M) =
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), A⁆ ⊔
        thetaT p A).map B.subtype := by
  rw [autPlaneProduct, autThetaT_map_subtype hp B A hA, Subgroup.map_sup,
    Subgroup.map_commutator, map_subtype_theta_centralizer hp B t]

theorem map_planeProduct_mulEquiv {B B' : Type*} [Group B] [Group B'] [Finite B] [Finite B']
    {p : ℕ} (hp : p.Prime) (Φ : B ≃* B') (A : Subgroup B) (t : B) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), A⁆ ⊔
        thetaT p A).map Φ.toMonoidHom =
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({Φ t} : Set B')),
        A.map Φ.toMonoidHom⁆ ⊔ thetaT p (A.map Φ.toMonoidHom) := by
  have h := map_inSubgroup_theta_centralizer_mulEquiv hp Φ (⊤ : Subgroup B) t
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ Φ.surjective, top_inf_eq] at h
  rw [Subgroup.map_sup, Subgroup.map_commutator, thetaT_map_equiv hp Φ A, h]

end CFSG.RankThree.PartOne
