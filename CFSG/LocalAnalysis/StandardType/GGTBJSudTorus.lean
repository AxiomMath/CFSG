module

public import CFSG.LocalAnalysis.StandardType.GGTBJSudBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJSudCore
public import CFSG.LocalAnalysis.StandardType.GGTBJSuTorus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator

theorem ggTBJ_sud_torusJNoncomm
    {K : Type} [Field K] [Finite K] {n d p r : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    {I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hI : I ⊆ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)))
    {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) I L' ψ₀ A)
    (hcard : p ^ (d / p + 2) ≤ Nat.card A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let hU : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK (by omega)
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hsc⟩ := hA
  have hAp : ∀ a ∈ A, a ^ p = 1 := hAe.2
  have hAI' : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ₀ l) = ψ₀ (a l) := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := hAI a ha
    exact ⟨x, hI hx, hxa⟩
  have hdn : (d, n) ≠ (6, 1) := by
    rintro ⟨-, h⟩
    omega
  have hcov : LineU.UnitaryCoverAt n d K :=
    LineU.unitaryUniversalCover_holds n d K hK hd hdn
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK (by omega) hd hp hpq hpd hcov hψ hker hperf hAe hAI' hcard
  obtain ⟨t, ht⟩ := hdiag y hy
  have hJ' : CFSG.Assembly.IsComponentOf J (ggFix y) := by
    rw [show ggFix y = fixSubgroup y from Subgroup.ext fun _ => Iff.rfl]
    exact (isComponentOf_iff_open).mpr hJ
  obtain ⟨I₀, -, hI₀swap, hI₀fix⟩ := ggTBJ_sud_blockData hU hn hcov.1 hφs hφker ht hJ'
  let C : Subgroup (MulAut L') := ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')
  have hC : ∀ a ∈ A, ∀ s : Fin d → K, LineU.ActsDiagU φ a s →
      (∀ i ∈ I₀, ∀ j ∈ I₀, s i = s j) → a ∈ C := by
    intro a ha s hs hconst
    rw [show C = ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L') from rfl,
      Subgroup.mem_iInf]
    intro j
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact hI₀fix a s hs hconst j j.2
  have hle : Nat.card ↥A ≤ p ^ (I₀.card - 1) * Nat.card ↥(A ⊓ C) :=
    ggTBJ_sud_count hU (by omega) hp hφker hdiag hAp I₀ hC
  have hpos : 0 < Nat.card ↥(A ⊓ C) := by
    haveI : Nonempty ↥(A ⊓ C) := ⟨1⟩
    exact Nat.card_pos
  have hpow : p ^ 2 ≤ p ^ (I₀.card - 1) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    exact hcount.trans hle
  have hI₀card : 3 ≤ I₀.card := by
    have h2 : 2 ≤ I₀.card - 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
    omega
  have hpos1 : 0 < I₀.card := Nat.lt_of_lt_of_le (by norm_num) hI₀card
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos1
  have hcard_erase_a : (I₀.erase a).card = I₀.card - 1 := Finset.card_erase_of_mem ha
  have hpos2 : 0 < (I₀.erase a).card := by
    rw [hcard_erase_a]
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num) hI₀card)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos2
  have hbI : b ∈ I₀ := Finset.mem_of_mem_erase hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hcard_erase_b : ((I₀.erase a).erase b).card = (I₀.erase a).card - 1 :=
    Finset.card_erase_of_mem hb
  have hpos3 : 0 < ((I₀.erase a).erase b).card := by
    rw [hcard_erase_b, hcard_erase_a, Nat.sub_sub]
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 2 < 3) hI₀card)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos3
  have hcI : c ∈ I₀ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcb : c ≠ b := Finset.ne_of_mem_erase hc
  have hca : c ≠ a := by
    have hc' : c ∈ I₀.erase a := Finset.mem_of_mem_erase hc
    exact Finset.ne_of_mem_erase hc'
  let n₁ : L' := φ (LineU.permSU hU (Equiv.swap a b))
  let n₂ : L' := φ (LineU.permSU hU (Equiv.swap b c))
  have hn₁J : n₁ ∈ J := hI₀swap a ha b hbI
  have hn₂J : n₂ ∈ J := hI₀swap b hbI c hcI
  have hn₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    SuDvdRootGen.conj_permSU_mem_normalizer hU hpq (by omega) hφs hφker hdiag hAp hsc
      (Equiv.swap a b)
  have hn₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    SuDvdRootGen.conj_permSU_mem_normalizer hU hpq (by omega) hφs hφker hdiag hAp hsc
      (Equiv.swap b c)
  have hW₁ : GGTorusWeylElt p A n₁ :=
    SuDvdRootGen.ggTorusWeylElt_permSU hU (by omega) hφker hdiag hAp (Equiv.swap a b)
  have hW₂ : GGTorusWeylElt p A n₂ :=
    SuDvdRootGen.ggTorusWeylElt_permSU hU (by omega) hφker hdiag hAp (Equiv.swap b c)
  have hrefl₁ : GGIsReflection p (ggConjAut A hn₁) :=
    SuDvdRootGen.isReflection_permSU_swap hU hp hpq (by omega) hφs hφker hdiag hAp hsc
      (Ne.symm hba) hn₁
  have hrefl₂ : GGIsReflection p (ggConjAut A hn₂) :=
    SuDvdRootGen.isReflection_permSU_swap hU hp hpq (by omega) hφs hφker hdiag hAp hsc
      (Ne.symm hcb) hn₂
  have hne : ggConjAut A hn₁ * ggConjAut A hn₂ ≠ ggConjAut A hn₂ * ggConjAut A hn₁ :=
    ggTBJ_sud_noncomm hU hp hpq (by omega) hφs hφker hdiag hAp hsc (Ne.symm hba) (Ne.symm hcb)
      (Ne.symm hca) hn₁ hn₂
  exact ⟨n₁, n₂, hn₁, hn₂, hn₁J, hn₂J, hW₁, hW₂, hrefl₁, hrefl₂, hne⟩

end CFSG.StandardType

end
