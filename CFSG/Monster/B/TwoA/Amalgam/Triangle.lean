module

public import CFSG.Monster.B.TwoA.Amalgam.TriangleCore
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoInst

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_triangle_local_orbit_permutation_invariance :
    (∀ a : CVert, Nonempty (RootModel a)) ∧
    (∀ (a : CVert) (M : RootModel a) (b c : cgraph.neighborSet a),
      orbSize (M.pt b) (M.pt c) = triType a b c) ∧
    (∀ a b c : CVert, IsCTriangle a b c → triType a b c = 1782 ∨ triType a b c = 44352) ∧
    (∀ a b c : CVert, IsCTriangle a b c →
      triType a c b = triType a b c ∧ triType b a c = triType a b c ∧
        triType b c a = triType a b c ∧ triType c a b = triType a b c ∧
        triType c b a = triType a b c) ∧
    (∃ a b c : CVert, IsCTriangle a b c ∧ triType a b c = 1782) ∧
    ∃ a b c : CVert, IsCTriangle a b c ∧ triType a b c = 44352 := by
  have hM : ∀ a : CVert, Nonempty (RootModel a) := fun a =>
    let ⟨M, _⟩ := exists_rootModel a
    ⟨M⟩
  obtain ⟨M⟩ := hM cv0
  obtain ⟨b₁, c₁, h₁, e₁⟩ := M.exists_triangle 1 (Or.inl rfl)
  obtain ⟨b₂, c₂, h₂, e₂⟩ := M.exists_triangle 2 (Or.inr rfl)
  exact ⟨hM, fun _ M b c => (M.triType_eq_orbSize b c).symm,
    fun a _ _ h => triType_eq_or (Classical.choice (hM a)) h, fun _ _ _ h => triType_perm h,
    ⟨cv0, b₁, c₁, h₁, e₁⟩, cv0, b₂, c₂, h₂, e₂⟩

end CFSG.Monster.B.TwoA.Amalgam
