module

public import CFSG.Quasithin.H13.Sp62C3Verify
public import CFSG.Quasithin.H13.GoldschmidtI51A3

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G]

theorem isDSystemIn_A3_of (Es : Fin 3 → Subgroup G)
    (hD1 : quasithinO2QuotientIso (Es 0) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hD2a : quasithinO2QuotientIso (Es 1)
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (hD2b : quasithinO2QuotientIso (Es 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hsyl : ∀ i : Fin 3, IsSylowTwoOf (Es 0 ⊓ Es 1 ⊓ Es 2) (Es i))
    (hT : ∀ i j : Fin 3, i ≠ j → Es i ⊓ Es j ≠ Es 0 ⊓ Es 1 ⊓ Es 2)
    (hX : ∀ i j : Fin 3, i ≠ j → Es i ⊓ Es j ≠ Es i)
    (hdist : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → Es i ⊓ Es j ≠ Es i ⊓ Es k)
    (hD4 : ∀ N : Subgroup G, N ≤ Es 0 ⊓ Es 1 ⊓ Es 2 →
      Es 0 ⊔ Es 1 ⊔ Es 2 ≤ Subgroup.normalizer (N : Set G) → N = ⊥) :
    IsDSystemIn .A3 Es := by
  refine ⟨fun _ => hD1, fun h => absurd h (by decide), hD2a, hD2b, hsyl, ?_, hD4,
    fun h => absurd h (by decide)⟩
  intro i j k hij hik hjk
  refine ⟨hdist i j k hij hik hjk, ?_⟩
  have hTij : Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Es i ⊓ Es j := le_inf (inf3_le Es i) (inf3_le Es j)
  have hTik : Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Es i ⊓ Es k := le_inf (inf3_le Es i) (inf3_le Es k)
  have key : ∀ {K : Type} [Group K] [Finite K], ModelData K →
      quasithinO2QuotientIso (Es i) K →
      ∀ Y : Subgroup G, (Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Y ∧ A6.IsMaxSubgroupIn Y (Es i)) ↔
        (Y = Es i ⊓ Es j ∨ Y = Es i ⊓ Es k) := fun hK hiso =>
    d3max_of_modelData hK hiso (hsyl i) hTij inf_le_left (hT i j hij) (hX i j hij) hTik
      inf_le_left (hT i k hik) (hX i k hik) (hdist i j k hij hik hjk)
  fin_cases i
  · exact key modelData_SL3 hD1
  · exact key modelData_SL22 hD2a
  · exact key modelData_SL3 hD2b

@[expose] noncomputable def slEquivGLn (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

theorem nonempty_mulEquiv_GL_of_isDSystem {G' : Type} [Group G'] [Finite G']
    {Gs : Fin 3 → Subgroup G'} (hD : IsDSystem .A3 Gs) :
    Nonempty (G' ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
  I51.exists_mulEquiv_GL (I51.pgData hD) (I51.card_Omega_A3 hD) (I51.card_G_ge_A3 hD)

theorem nonempty_mulEquiv_SL_of_isDSystemIn {Es : Fin 3 → Subgroup G} (h : IsDSystemIn .A3 Es) :
    Nonempty (↥(Es 0 ⊔ Es 1 ⊔ Es 2) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isDSystem h.isDSystem
  exact ⟨e.trans (slEquivGLn 4).symm⟩

end CFSG.Quasithin.H13.L14413
