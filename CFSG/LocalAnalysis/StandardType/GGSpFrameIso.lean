module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameIsoCoord
public import CFSG.LocalAnalysis.StandardType.GGSpFrameClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSpJoinWeylRank

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType CFSG.StandardType.SpJoin CFSG.LieType.Universal CFSG.LieType.RootSystem
  CoxeterSystem CFSG.LieType.Universal.Symplectic CFSG.Open

theorem exists_frame_iso {G : Type*} [Group G] {Bs : Subgroup G} [Finite Bs] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hm : 1 ≤ m)
    (hrank : Nat.card Bs = p ^ (m + 1)) {A : Subgroup (MulAut ↥Bs)}
    (e : (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group ≃* ↥A)
    (he : ∀ i : Fin (m + 1),
      ((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) : ↥A) :
          MulAut ↥Bs) ^ 2 = 1 ∧
        Nat.card {b : ↥Bs //
          ((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) : ↥A) :
            MulAut ↥Bs) b = b} * p = Nat.card Bs) :
    ∃ Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs,
      ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a) := by
  obtain ⟨Φ, hΦ⟩ := exists_frame_coords hp hp2 hBs hm hrank e he
  refine ⟨Φ, exists_induced_of_spSignedGroup Φ fun k =>
    ⟨((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k) : ↥A) :
        MulAut ↥Bs),
      (e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k)).2,
      hΦ k⟩⟩

theorem exists_frame_iso_of_weyl {G : Type} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hm : 1 ≤ m)
    (hrank : Nat.card Bs = p ^ (m + 1)) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A) :
    ∃ Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs,
      ∀ h ∈ spSignedGroup (m + 1) p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a) := by
  haveI : Finite Bs := Subtype.finite
  have hA' : GGWeylOfType p (coxeterMatrix (isFiniteType_cartanC (m + 1))) A := by
    rw [coxeterMatrix_cartanC_eq_B]
    exact hA
  obtain ⟨e, he⟩ := hA'
  exact exists_frame_iso hp hp2 hBs hm hrank e fun i => he i

end CFSG.StandardType.SpFrame
