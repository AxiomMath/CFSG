module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType.U63TB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

@[expose] def GGTorusNbrSCrK (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      NbrConcl p ψ.ker A

theorem nbr63_of_cover {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ 4 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    NbrConcl 3 ψ.ker A := by
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    Line63.exists_diagModel_of hK hn (by norm_num) Nat.prime_three hpq (by norm_num) hperfSU hψ
      hker hperf hA hAI hcard hcov'
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have hM : Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hA1 : Nat.card A ≠ 1 := by
    intro h1
    rw [h1] at hr
    have : 1 < 3 ^ 4 := by norm_num
    omega
  obtain ⟨W, hW1, hW2⟩ :=
    nbr_of_model hM hK Nat.prime_three (by norm_num) hpq (by norm_num) hA hA1 hsc hdiag
  exact ⟨W, hW1, fun Y _ hWA hWY hYA hYp => hW2 Y hWA hWY hYA hYp⟩

section Certificates

theorem ggTorusNbrSCrK_unitary63_big {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTorusNbrSCrK 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc
  have hcov := unitaryUniversalCover_holds n 6 K hK (by norm_num)
    (fun h => absurd (congrArg Prod.snd h) (by omega))
  exact nbr63_of_cover hK (by omega) hpq hcov.1
    (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf) hψ hker hperf hA hAI hr hsc

theorem ggTorusNbrSCrK_unitary63_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGTorusNbrSCrK 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc
  have hcov := unitaryCoverOddAt_six_two K (by norm_num [hK])
  exact nbrConcl_descent hker hψ hperf hA hAI hsc
    (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc hsc₁ =>
      nbr63_of_cover hK le_rfl (by norm_num) hcov.1
        (fun ψ'' hs'' hk'' => hcov.2 L₁ ψ'' hs'' (hk'' ▸ hk) hp (hk'' ▸ hodd)) hs hk hp hA₁ hAI₁
        (by rw [hc]; exact hr) hsc₁)

theorem ggTorusNbrSCrK_unitary63 {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTorusNbrSCrK 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact ggTorusNbrSCrK_unitary63_two hK
  · exact ggTorusNbrSCrK_unitary63_big hK h hpq

end Certificates

end CFSG.StandardType.U63TB

end
