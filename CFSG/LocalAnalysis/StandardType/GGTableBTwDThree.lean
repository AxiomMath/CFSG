module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThreeRank
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTableBTwDThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1

theorem ggTableBTwDThreeLabel_of_unitary {p : ℕ} {lab : LargeEvenLabel}
    (hU : GGTableBUnitaryLabel lab) (hL : ¬ GGTableBUnitaryLiftLabel p lab)
    (hs : LargeEvenSplit p lab) : GGTableBTwDThreeLabel p lab := by
  have hpq : ¬ p ∣ 2 ^ lab.n + 1 := fun h => hL ⟨hU, h⟩
  rcases hU with ht | ⟨ht, hl⟩
  · exact absurd (dvd_of_largeEvenSplit_twA hs ht) hpq
  · refine ⟨ht, hl, ?_⟩
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl hpq ⊢
    subst ht
    rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, rfl⟩
    · exact absurd h id
    · exact absurd h hpq
    · exact h
    · have hn' : n = 1 := hn
      exact (hpq (by rw [hn']; norm_num)).elim

theorem largeEvenLabelAll_card_le_twDThree {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBTwDThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X ≤ p ^ 2 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq ⊢
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hdq : ((4 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro he
    have h4 : (4 : ℕ) = 3 := congrArg Prod.fst he
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  exact ⟨K, i1, i2, hK, hq', fun X hXI hX =>
    TwDThree.card_le_of_subset_unitaryConj (TableBU.unitaryFieldData_of_card hK hn) (by norm_num)
      hdq hp hpq hX hXI⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggThmIHyp_false_of_labelAll {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3)
    {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G} (hT : GGThmIHyp p B x L)
    (hM : LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    False := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, hcard⟩ := largeEvenRawDatum_exists hraw
  have hab : IsElemAbelian p (ggBeta L θ hBN).range :=
    isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hS.1.1 a.2 b.2))
      (fun a => Subtype.ext (by simpa using hS.1.1.2 a a.2)) _
  have hI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN h3 b
  have hlt := hcard _ hI hab
  have hc := card_range_ggBeta_mul L θ hp hS hL hBN
  have h4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
  have h5 : Nat.card B < p ^ 4 :=
    calc Nat.card B = Nat.card (ggBeta L θ hBN).range * p := hc.symm
      _ < p ^ 3 * p := Nat.mul_lt_mul_of_pos_right hlt hp.pos
      _ = p ^ 4 := by ring
  exact absurd h4 (not_le.mpr h5)

end Config

theorem ggBstarInputOn_of_labelAll_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) :
    GGBstarInputOn S :=
  fun _ _ _ _ _ _ _ hT hM => (ggThmIHyp_false_of_labelAll h hT hM).elim

theorem ggStdSubPreInputOn_of_labelAll_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) :
    GGStdSubPreInputOn S :=
  fun _ _ _ _ _ _ _ hT hM => (ggThmIHyp_false_of_labelAll h hT hM).elim

theorem largeEvenLabelAll_card_lt_twDThree {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBTwDThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 :=
  (largeEvenLabelAll_card_le_twDThree hp hlab h).mono fun _ _ _ _ hX X hXI hXab =>
    (hX X hXI hXab).trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))

theorem ggBstarInputOn_twDThree : GGBstarInputOn GGTableBTwDThreeLabel :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab h _ =>
    largeEvenLabelAll_card_lt_twDThree hp hlab h

theorem ggStdSubPreInputOn_twDThree : GGStdSubPreInputOn GGTableBTwDThreeLabel :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab h _ =>
    largeEvenLabelAll_card_lt_twDThree hp hlab h

theorem GGBstarInputOn.mono_split {S S' : ℕ → LargeEvenLabel → Prop} (hS : GGBstarInputOn S)
    (h : ∀ p lab, S' p lab → LargeEvenSplit p lab → S p lab) : GGBstarInputOn S' :=
  fun G _ _ p B x L hT hM => hS G p B x L hT
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨h p lab hP.1 hP.2.1, hP.2⟩) hM)

theorem GGStdSubPreInputOn.mono_split {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : GGStdSubPreInputOn S) (h : ∀ p lab, S' p lab → LargeEvenSplit p lab → S p lab) :
    GGStdSubPreInputOn S' :=
  fun G _ _ p B x L hT hM => hS G p B x L hT
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨h p lab hP.1 hP.2.1, hP.2⟩) hM)

end CFSG.StandardType
