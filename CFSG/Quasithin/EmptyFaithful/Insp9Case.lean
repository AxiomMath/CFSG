module

public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.EmptyFaithful.Insp9B56a
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Insp9

@[expose] def InspGoal (D : Type) [Group D] (N : Subgroup D) : Prop :=
  Nonempty (↥N ≃* Equiv.Perm (Fin 3)) ∨ (IsInspList ↥N ∧ oTwoUpper (⊤ : Subgroup D) ≤ N)

@[expose] def B56Setting (D : Type) [Group D] (N : Subgroup D) : Prop :=
  ∃ (W : Type) (_ : CommGroup W) (_ : Finite W), (∀ w : W, w ^ 2 = 1) ∧
    ∃ ρ : D →* MulAut W, Function.Injective ρ ∧ B53Hyp (N.map ρ) ∧
      (B56Case1 (N.map ρ) ∨ B56Case2 (N.map ρ) ∨ B56Case3 (N.map ρ) ∨ B56Case4 (N.map ρ) ∨
        B56Case5 (N.map ρ))

theorem b56QL_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : B56QuasisimpleList Y) : B56QuasisimpleList X := by
  rcases h with ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ |
    ⟨n, K, hK, hf, hc, ⟨e'⟩⟩ | h5 | h6 | h7 | ⟨K, hK, hf, hc, ⟨e'⟩⟩ | h9 | h10
  · exact Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨e.trans e'⟩⟩)))
  · obtain ⟨e'⟩ := h5
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩))))
  · obtain ⟨e'⟩ := h6
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv e.symm h7)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨K, hK, hf, hc, ⟨e.trans e'⟩⟩)))))))
  · obtain ⟨e'⟩ := h9
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.trans e'⟩))))))))
  · obtain ⟨e'⟩ := h10
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e.trans e'⟩))))))))

theorem B56Setting.ql_of_quasisimple {D : Type} [Group D] {N : Subgroup D}
    (h : B56Setting D N) (hq : CFSG.IsQuasisimple ↥N) : B56QuasisimpleList ↥N := by
  obtain ⟨W, _, _, _, ρ, hρ, -, hcases⟩ := h
  let e : ↥N ≃* ↥(N.map ρ) := Subgroup.equivMapOfInjective N ρ hρ
  have hq' : CFSG.IsQuasisimple ↥(N.map ρ) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact b56QL_of_mulEquiv e (b56_qs hq' hcases)

end Insp9

end CFSG.Quasithin
