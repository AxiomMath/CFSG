module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp TypeA

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem ggStdSubTwoTorus_symplectic_small [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) (hm2 : m ≤ 2) (r : ℕ) :
    GGStdSubTwoTorus p r (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have : NeZero m := ⟨by omega⟩
  have hZ := center_spProj_eq_bot (K := K) (m := m)
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) :
      Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ⊆
        Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* _) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact sp_I_subset_inn (induced_unique ψ hψ hφa hxa ▸ hφaI)
  obtain ⟨A', hA', hA'c⟩ := exists_of_subset_inn hZ hXI hX
  have hle : Nat.card A ≤ p ^ m := by
    rw [← hcard, ← hA'c]
    exact card_le_of_isElemAbelian_spProj hp hp2 hpq hA'
  have h5 : p ^ 3 ≤ p ^ m := h3.trans hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h5
  omega

end TableBSymp

theorem GGStdSubFixedJOn_symplectic_of_sp
    (h : ∀ (l n p : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → p.Prime → p ≠ 2 →
      p ∣ 2 ^ n - 1 → 3 ≤ l →
      GGStdSubTwoTorus p l (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))) :
    GGStdSubFixedJOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 := by
  refine GGStdSubFixedJOn_of_labels fun p lab hp hlab hS => ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hS
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have key : 2 ≤ l → ∀ {Q : LargeEvenRawCont}, LargeEvenRecipeSymplectic l (2 ^ n) false Q →
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
        Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I := by
    intro hl Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    refine ⟨K, inferInstance, inferInstance, hK, hQ, l,
      ggTorusLift_symplectic hp hp2 hpq (by omega), ?_⟩
    rcases (show l ≤ 2 ∨ 3 ≤ l by omega) with hl2 | hl3
    · exact ggStdSubTwoTorus_symplectic_small hp hp2 hpq (by omega) hl2 l
    · exact h l n p K hK hp hp2 hpn hl3
  intro Q hQ
  rcases htag with h' | h' <;> dsimp only at h' <;> subst h' <;> exact key hlab.2.1 hQ

theorem ggStdSubSmallInputOn_symplectic_of_sp
    (h : ∀ (l n p : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → p.Prime → p ≠ 2 →
      p ∣ 2 ^ n - 1 → 3 ≤ l →
      GGStdSubTwoTorus p l (LargeEvenProj (LargeEvenSpGroup K l))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K l)) (LargeEvenGSpSet K l))) :
    GGStdSubSmallInputOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 :=
  GGStdSubSmallInputOn_of_fixedJ (GGStdSubFixedJOn_symplectic_of_sp h)

end CFSG.StandardType

end
