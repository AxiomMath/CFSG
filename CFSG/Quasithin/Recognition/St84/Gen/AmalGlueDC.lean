module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.GH74.QTGen4.DSGen4.L34

private def glueRestrict {G H : Type} [Group G] [Group H] {P : Subgroup G} {M : Subgroup H}
    (e : ↥P ≃* ↥M) {K : Subgroup G} (hK : K ≤ P) {K' : Subgroup H} (hK' : K' ≤ M)
    (h : ∀ x : ↥P, (x : G) ∈ K ↔ ((e x : ↥M) : H) ∈ K') : ↥K ≃* ↥K' where
  toFun x := ⟨((e ⟨x.1, hK x.2⟩ : ↥M) : H), (h ⟨x.1, hK x.2⟩).1 x.2⟩
  invFun y := ⟨(e.symm ⟨y.1, hK' y.2⟩ : G), (h (e.symm ⟨y.1, hK' y.2⟩)).2 (by simpa using y.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have h := congrArg Subtype.val (map_mul e ⟨x.1, hK x.2⟩ ⟨y.1, hK y.2⟩)
    exact h

theorem amalgam_iso_of_dcProp {G Y : Type} [Group G] [Group Y] {P1 P2 Q1 : Subgroup G}
    {M1 M2 : Subgroup Y} (hDC : DCProp M1 M2) (ψ₁ : ↥P1 ≃* ↥M1) (ψ₂ : ↥P2 ≃* ↥M2)
    (hB1 : ∀ x : ↥P1, (x : G) ∈ P2 ↔ ((ψ₁ x : ↥M1) : Y) ∈ M2)
    (hB2 : ∀ x : ↥P2, (x : G) ∈ P1 ↔ ((ψ₂ x : ↥M2) : Y) ∈ M1)
    (hQ1 : ∀ x : ↥P1, (x : G) ∈ Q1 ↔ ((ψ₁ x : ↥M1) : Y) ∈ pCoreOf 2 M1)
    (hQ1' : ∀ x : ↥P2, (x : G) ∈ Q1 ↔ ((ψ₂ x : ↥M2) : Y) ∈ pCoreOf 2 M1) :
    Nonempty ((RankTwoAmalgam.ofSubgroups P1 P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2)) := by
  classical
  have hψ₁B : ∀ x : ↥P1, (x : G) ∈ P1 ⊓ P2 ↔ ((ψ₁ x : ↥M1) : Y) ∈ M1 ⊓ M2 := by
    intro x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨(ψ₁ x).2, (hB1 x).1 h.2⟩, fun h => ⟨x.2, (hB1 x).2 h.2⟩⟩
  have hψ₂B : ∀ x : ↥P2, (x : G) ∈ P1 ⊓ P2 ↔ ((ψ₂ x : ↥M2) : Y) ∈ M1 ⊓ M2 := by
    intro x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨(hB2 x).1 h.1, (ψ₂ x).2⟩, fun h => ⟨(hB2 x).2 h.1, x.2⟩⟩
  let βψ₁ : ↥(P1 ⊓ P2) ≃* ↥(M1 ⊓ M2) :=
    glueRestrict ψ₁ (inf_le_left : P1 ⊓ P2 ≤ P1) (inf_le_left : M1 ⊓ M2 ≤ M1) hψ₁B
  let βψ₂ : ↥(P1 ⊓ P2) ≃* ↥(M1 ⊓ M2) :=
    glueRestrict ψ₂ (inf_le_right : P1 ⊓ P2 ≤ P2) (inf_le_right : M1 ⊓ M2 ≤ M2) hψ₂B
  let γ : ↥(M1 ⊓ M2) ≃* ↥(M1 ⊓ M2) := βψ₁.symm.trans βψ₂
  have hγz : ∀ z : ↥(P1 ⊓ P2), γ (βψ₁ z) = βψ₂ z := by
    intro z
    show βψ₂ (βψ₁.symm (βψ₁ z)) = βψ₂ z
    rw [MulEquiv.symm_apply_apply]
  have hσ : ∀ b : ↥(M1 ⊓ M2), (b : Y) ∈ pCoreOf 2 M1 ↔
      ((γ b : ↥(M1 ⊓ M2)) : Y) ∈ pCoreOf 2 M1 := by
    intro b
    obtain ⟨z, rfl⟩ := βψ₁.surjective b
    rw [hγz z]
    exact (hQ1 ⟨(z : G), z.2.1⟩).symm.trans (hQ1' ⟨(z : G), z.2.2⟩)
  obtain ⟨a₁, a₂, hA1, hA2, hA3⟩ := hDC γ hσ
  let A₁ : ↥(M1 ⊓ M2) ≃* ↥(M1 ⊓ M2) :=
    glueRestrict a₁ (inf_le_left : M1 ⊓ M2 ≤ M1) (inf_le_left : M1 ⊓ M2 ≤ M1)
      (by
        intro m
        simp only [Subgroup.mem_inf]
        exact ⟨fun h => ⟨(a₁ m).2, (hA1 m).1 h.2⟩, fun h => ⟨m.2, (hA1 m).2 h.2⟩⟩)
  let A₂ : ↥(M1 ⊓ M2) ≃* ↥(M1 ⊓ M2) :=
    glueRestrict a₂ (inf_le_right : M1 ⊓ M2 ≤ M2) (inf_le_right : M1 ⊓ M2 ≤ M2)
      (by
        intro m
        simp only [Subgroup.mem_inf]
        exact ⟨fun h => ⟨(hA2 m).1 h.1, (a₂ m).2⟩, fun h => ⟨(hA2 m).2 h.1, m.2⟩⟩)
  have hγ2 : ∀ c : ↥(M1 ⊓ M2), A₂ (A₁ c) = γ c := by
    intro c
    apply Subtype.ext
    exact hA3 c ⟨(c : Y), c.2.1⟩ ⟨((A₁ c : ↥(M1 ⊓ M2)) : Y), (A₁ c).2.2⟩ rfl rfl
  let φ1 : ↥P1 ≃* ↥M1 := ψ₁.trans a₁
  let φ2 : ↥P2 ≃* ↥M2 := ψ₂.trans (MulEquiv.symm a₂)
  let φ12 : ↥(P1 ⊓ P2) ≃* ↥(M1 ⊓ M2) := βψ₁.trans A₁
  refine ⟨⟨φ1, φ12, φ2, ?_, ?_⟩⟩
  · intro g
    apply Subtype.ext
    rfl
  · intro g
    have hm : a₂ ⟨(A₁ (βψ₁ g)).1, (A₁ (βψ₁ g)).2.2⟩ = ψ₂ ⟨g.1, g.2.2⟩ := by
      apply Subtype.ext
      have h := congrArg Subtype.val ((hγ2 (βψ₁ g)).trans (hγz g))
      exact h
    have hm' : (⟨(A₁ (βψ₁ g)).1, (A₁ (βψ₁ g)).2.2⟩ : ↥M2) =
        MulEquiv.symm a₂ (ψ₂ ⟨g.1, g.2.2⟩) :=
      (MulEquiv.eq_symm_apply a₂).mpr hm
    apply Subtype.ext
    exact congrArg Subtype.val hm'

end CFSG.Quasithin.F112R.St84
