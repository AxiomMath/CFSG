module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.TorusE9
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.EndNodes
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSpinMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.Blueprint CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.CentralExt CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
  CFSG.SectionRank.EvenCover

private theorem cartanB_ne_zero_iff_path {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    cartanB m i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hc
    exact h (OddCT.cartanB_of_far hij (fun h' => hc (Or.inl h')) fun h' => hc (Or.inr h'))
  · rintro (h | h)
    · simp [OddCT.cartanB_of_succ h]
    · rw [OddCT.cartanB_of_pred h]
      split_ifs <;> simp

private theorem minusDatum_endNodes_short
    {G : Type} [Group G] {m : ℕ}
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] [Finite (ShortField b c)] [CharP (ShortField b c) 2]
    (hm : 4 ≤ m) (hF2 : Nat.card F = 2)
    {π : spinGroup (quadMinus m F b c) →* G} {M : ℕ}
    (h : BorelQuotient (minusDatum m hirr) (minusWeyl m hirr) (minusTorus m hirr) π M) :
    ∃ (a s : Fin (minusDatum m hirr).rank),
      HasTorusSL2 (minusDatum m hirr) (minusTorus m hirr) s (ShortField b c) ∧
      endNodesThree (minusDatum m hirr) (minusTorus m hirr) = {a} ∧
      Nat.card (rankOne (minusDatum m hirr).rootGroup a) = 6 ∧
        ∃ x ∈ rankOne (minusDatum m hirr).rootGroup a,
          ∃ y ∈ rankOne (minusDatum m hirr).rootGroup a, x * y ≠ y * x := by
  have h4 : 4 ≤ Nat.card (ShortField b c) := by
    rw [SpinMinusClosed.card_shortField, hF2]
    norm_num
  have : Finite (spinGroup (quadMinus m F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  let a : Fin (minusDatum m hirr).rank := ⟨0, by show 0 < m - 1; omega⟩
  let s : Fin (minusDatum m hirr).rank := ⟨m - 2, by show m - 2 < m - 1; omega⟩
  have ha : a.val + 1 < m - 1 := by
    show 0 + 1 < m - 1
    omega
  have hs : ¬ s.val + 1 < m - 1 := by
    show ¬ (m - 2 + 1 < m - 1)
    omega
  have h6a : Nat.card (rankOne (minusDatum m hirr).rootGroup a) = 6 ∧
      ∃ x ∈ rankOne (minusDatum m hirr).rootGroup a,
        ∃ y ∈ rankOne (minusDatum m hirr).rootGroup a, x * y ≠ y * x :=
    ⟨spinMinus_long_card hirr hF2 (k := a) ha,
      noncomm_of_hasSL2Node (hasSL2Node_spinMinus_long hirr (k := a) ha)⟩
  have hsT : HasTorusSL2 (minusDatum m hirr) (minusTorus m hirr) s (ShortField b c) :=
    hasTorusSL2_spinMinus_short hirr h4 hs
  have hb : 2 < Nat.card ↥((minusDatum m hirr).rootGroup (Pi.single s 1)) :=
    lt_of_lt_of_le (by norm_num) (h4.trans (card_le_card_rootGroup_of_hasTorusSL2 hsT))
  have hpath : ∀ i j : Fin (minusDatum m hirr).rank, i ≠ j →
      ((minusDatum m hirr).cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
    fun _ _ hij => cartanB_ne_zero_iff_path hij
  have hset : endNodesThree (minusDatum m hirr) (minusTorus m hirr) = {a} :=
    endNodesThree_eq_of_path h (by omega) hpath (a := a) (b := s)
      (Or.inl ⟨rfl, by show m - 2 + 1 = m - 1; omega⟩) h6a hb
  exact ⟨a, s, hsT, hset, h6a⟩

theorem permWitnessOmegaMinus_holds :
    PermWitnessOmegaMinus := by
  intro G _ _ m hm hL
  obtain ⟨⟨-, -, -⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    hL.statedClassicalModel (by decide)
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hF2 : Nat.card F = 2 := by rw [hcard]; norm_num
  have : Fact (∀ r : F, r ^ 2 ≠ -c + b * r) := fact_shortField hirr
  have : Finite (ShortField b c) := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have : Finite (spinGroup (quadMinus m F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  let π : spinGroup (quadMinus m F b c) →* G :=
    e.symm.toMonoidHom.comp
      (spinToStatedProj (quadMinus m F b c) (range_spinMatrix_quadMinus hm hirr))
  have h : BorelQuotient (minusDatum m hirr) (minusWeyl m hirr) (minusTorus m hirr) π
      (Nat.card F ^ 2 - 1) :=
    borelQuotient_spinMinus hirr hm e
  have hM : Nat.card F ^ 2 - 1 = 3 := by rw [hF2]; norm_num
  have h3 : BorelQuotient (minusDatum m hirr) (minusWeyl m hirr) (minusTorus m hirr) π 3 :=
    hM ▸ h
  obtain ⟨a, s, hsT, hset, h6a⟩ := minusDatum_endNodes_short hirr hm hF2 h3
  obtain ⟨E, hEP, hE, hE9⟩ :=
    exists_E9_le_parJ_singleton h3 hsT (hasOrderThree_spinMinus hirr a) h6a
  exact permWitness_of_borelQuotient_singleton h3 (by norm_num) hset h6a hEP hE hE9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
