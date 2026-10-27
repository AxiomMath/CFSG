module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinus

public section

namespace CFSG.StandardType.SympMinus

open CFSG CFSG.Assembly TableB CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem labelAll_one {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
        (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K m)), 3 ≤ m ∧ Nat.card K = 2 ∧
          p ∣ Nat.card K + 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn, hn1⟩ := h
  intro Q hQ
  have key : ∀ (_ : LargeEvenRecipeSymplectic l (2 ^ n) false Q),
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
        (∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
          (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K m)), 3 ≤ m ∧ Nat.card K = 2 ∧
            p ∣ Nat.card K + 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R)) := by
    intro hQ'
    obtain ⟨K, _, _, hK, hQK⟩ := hQ'
    have hch : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpn
    have hK2 : Nat.card K = 2 := by
      rw [hK, show n = 1 from hn1, pow_one]
    exact ⟨K, inferInstance, inferInstance, hK, hQK, l, K, inferInstance, inferInstance, hch,
      MulEquiv.refl _, hl, hK2, hpq, TableBSymp.sp_I_subset_inn⟩
  rcases htag with h | h <;> dsimp only at h <;> subst h <;> exact key hQ

theorem exists_data_of_marking_one {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hmark : GGInnerDiagOnLabel (fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ lab.n = 1) p Bs X) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSpGroup K m)),
      3 ≤ m ∧ Nat.card K = 2 ∧ p ∣ Nat.card K + 1 ∧ commutator ↥X = ⊤ ∧
        ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈
          Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
            MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
  classical
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧
      lab.n = 1)
    (fun lab _ hs => nbrC_labelAll_guard (labelAll_one hs)) (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, m, Kf, _, _, _, e, hm3, hK2, hpq, hIinn⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  refine ⟨m, Kf, inferInstance, inferInstance, inferInstance, hBsN, θ.trans e, hm3, hK2, hpq, hXc,
    fun b hb => ?_⟩
  obtain ⟨g, hg⟩ := hIinn (hBsI b hb)
  refine ⟨e g, ?_⟩
  rw [ggLAut_congr X θ (θ.trans e) ⟨b, hBsN hb⟩, ← hg]
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

end CFSG.StandardType.SympMinus

end
