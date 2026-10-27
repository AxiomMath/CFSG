module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.Marking

@[expose] public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem tbGroup_false_of_card_lt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hbound : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3)
    (hTB : GGTorusTBGroup p r R I L' ψ A) : False := by
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, -⟩ := hTB
  have hAI' : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  set X : Subgroup (MulAut R) := TypeA.inducedSub ψ A
  have hXcard : Nat.card X = Nat.card A := TypeA.card_inducedSub hψ hker hperf hAI'
  have hXab : IsElemAbelian p X := TypeA.isElemAbelian_inducedSub hψ hAe
  have hXI : (X : Set (MulAut R)) ⊆ I := by
    rintro φ ⟨a, ha, hφ⟩
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hφ hφ']
    exact hφ'I
  have hlt := hbound X hXI hXab
  rw [hXcard] at hlt
  exact absurd h3 (not_le.mpr hlt)

theorem relD_D3_tbGroup_false {K : Type} [Field K] [Finite K] [CharP K 2] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {L : Type} [Group L] [Finite L]
    (ψ : L →* LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) Set.univ) L ψ A) :
    False := by
  refine tbGroup_false_of_card_lt (p := p) (r := r) ?_ hTB
  intro X hXI hX
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub hpq hd
      have e : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have h1 := Finite.one_lt_card (α := K)
        omega
      rwa [e] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hpe : ∀ j, 0 < j → 3 * j ≤ 4 → ¬ p ∣ Nat.card K ^ j - 1 := by
    intro j hj hj4
    have hj1 : j = 1 := by omega
    subst hj1
    simpa using hpK
  exact StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv 4 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun X' hX'I hX'ab =>
      TypeA.card_lt_cube_pgl_of_ord (d := 4) (by norm_num) hp hp2 hpe hX'ab hX'I) hXI hX

theorem relD_twD2_tbGroup_false {K : Type} [Field K] [Finite K] [CharP K 2] {p r n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hpq : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) {L : Type} [Group L] [Finite L]
    (ψ : L →* LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ) L ψ A) :
    False := by
  refine tbGroup_false_of_card_lt (p := p) (r := r) ?_ hTB
  intro X hXI hX
  have hsq : (2 ^ n + 1) * (2 ^ n - 1) = (2 ^ n) ^ 2 - 1 := by
    rw [← Nat.sq_sub_sq, one_pow]
  have hq : p ∣ (2 ^ n + 1) * (2 ^ n - 1) := by
    rcases hpq with h | h
    · exact dvd_mul_of_dvd_right h _
    · exact dvd_mul_of_dvd_left h _
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hK, ← hsq]
    exact hq
  refine StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv 2 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (p := p) (k := 3) ?_ hXI hX
  intro X' hX'I hX'ab
  have hle : Nat.card X' ≤ p := by
    simpa using TypeA.card_le_of_subset_conjAut_gen (d := 2) hp hp2 hpK (by norm_num) hX'ab hX'I
  exact hle.trans_lt (by simpa using Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 3))

theorem relD_twD3_tbGroup_false {K : Type} [Field K] [Finite K] [CharP K 2] {p r n : ℕ}
    (hp : p.Prime) (_hp2 : p ≠ 2) (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hpq : p ∣ 2 ^ n - 1) {L : Type} [Group L] [Finite L]
    (ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenGUSet (Fin 4) K (2 ^ n))) L ψ A) : False := by
  refine tbGroup_false_of_card_lt (p := p) (r := r) ?_ hTB
  intro X hXI hX
  have hle : Nat.card X ≤ p ^ 2 :=
    TwDThree.card_le_of_subset_unitaryConj (d := 4) (TableBU.unitaryFieldData_of_card hK hn)
      (by norm_num) (by simp) hp hpq hX hXI
  exact hle.trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3))

theorem largeEvenLabelAll_relD_D3 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.D, 3, n⟩ fun R _ I _ =>
      GGTorusTorW p (3 - 1) (ggTorMpm p ⟨.D, 3, n⟩) (3 - 1)
        (CartanMatrix.B (3 - 1)) (CoxeterMatrix.B (3 - 1)) R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n) hK
  exact ⟨K, i1, i2, hK, hQ', fun L _ _ ψ A hTB =>
    (relD_D3_tbGroup_false (p := p) (r := 3 - 1) hp hp2 (by rw [hK]; exact hpn) ψ A
      hTB).elim⟩

theorem largeEvenLabelAll_relD_twD2 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (_hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twD, 2, n⟩ fun R _ I _ =>
      GGTorusTorW p (2 - 1) (ggTorMpm p ⟨.twD, 2, n⟩) (2 - 1)
        (CartanMatrix.B (2 - 1)) (CoxeterMatrix.B (2 - 1)) R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 2 * n) (by
    rw [hK, ← pow_mul, mul_comm])
  exact ⟨K, i1, i2, hK, hQ', fun L _ _ ψ A hTB =>
    (relD_twD2_tbGroup_false (p := p) (r := 2 - 1) hp hp2 hK hpn ψ A hTB).elim⟩

theorem largeEvenLabelAll_relD_twD3 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.twD, 3, n⟩ fun R _ I _ =>
      GGTorusTorW p (3 - 1) (ggTorMpm p ⟨.twD, 3, n⟩) (3 - 1)
        (CartanMatrix.B (3 - 1)) (CoxeterMatrix.B (3 - 1)) R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 2 * n) (by
    rw [hK, ← pow_mul, mul_comm])
  exact ⟨K, i1, i2, hK, hQ', fun L _ _ ψ A hTB =>
    (relD_twD3_tbGroup_false (p := p) (r := 3 - 1) hp hp2 hK hn hpn ψ A hTB).elim⟩

end CFSG.StandardType
