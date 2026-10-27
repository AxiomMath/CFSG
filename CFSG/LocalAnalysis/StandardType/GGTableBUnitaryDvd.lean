module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGEndNodeAdmBelow (p r s : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → Nat.card A < p ^ s → GGAdmissible p L' A →
      ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
        ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

theorem ggEndNodeAdm_of_below {p r s : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hlow : GGEndNodeAdmBelow p r s R I) (hhigh : GGEndNode p s R I) : GGEndNodeAdm p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hadm
  by_cases hs : p ^ s ≤ Nat.card A
  · exact hhigh L' ψ hψ hker hperf A hA hAI hs h3
  · exact hlow L' ψ hψ hker hperf A hA hAI hr h3 (not_le.mp hs) hadm

@[expose] def GGEndNodeAdmUnitaryDvdCodimTwoInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBUnitaryLiftLabel p lab → p ∣ lab.rank + 1 → 4 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGEndNodeAdmBelow p (lab.rank + 1 - 3) (lab.rank + 1 - 2) R I

theorem ggEndNodeAdmUnitaryDvdInput_of_codimTwo (h2 : GGEndNodeAdmUnitaryDvdCodimTwoInput) :
    GGEndNodeAdmUnitaryDvdInput := by
  intro p lab hp hlab hl hpd h4
  have hlow := h2 p lab hp hlab hl hpd h4
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq⟩ := hl
  dsimp only at htag hpq hpd h4 hlow ⊢
  rcases htag with rfl | ⟨-, h3⟩
  swap
  · omega
  have hn : 1 ≤ n := hlab.1
  have hr : ggUnitaryTorusRank p (l + 1) = l + 1 - 3 := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  rw [hr]
  have hq : 2 < 2 ^ n ∨ 6 ≤ l + 1 := by
    by_cases hn1 : n = 1
    · subst hn1
      right
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
      subst hp3
      omega
    · left
      have h4' : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  intro Q hQ
  have hQ' := hlow Q hQ
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq', hbelow⟩ := hQ'
  exact ⟨K, i1, i2, hK, hq', ggEndNodeAdm_of_below hbelow
    (TableBUD.ggEndNode_unitary_sub_two (TableBU.unitaryFieldData_of_card hK hn) hK hp hpq
      (by omega) hq)⟩

end CFSG.StandardType
