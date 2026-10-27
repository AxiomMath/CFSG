module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGIRankLe (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
    p ^ 4 ≤ Nat.card X → Nat.card X ≤ p ^ r

section PerLabel

variable {p r : ℕ} {R R' : Type} [Group R] [Group R'] {I : Set (MulAut R)}
  {I' : Set (MulAut R')}

theorem ggIRankLe_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGIRankLe p r R' I') : GGIRankLe p r R I := by
  intro X hXI hX h4
  have hc : Nat.card (X.map (MulAut.congr e).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  rw [← hc] at h4 ⊢
  exact h _ (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hXI hφ)) (isElemAbelian_map hX _) h4

theorem ggIRankLe_of_card_le (h : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
    IsElemAbelian p X → Nat.card X ≤ p ^ r) : GGIRankLe p r R I :=
  fun X hXI hX _ => h X hXI hX

theorem ggIRankLe_zero_of_card_lt (h : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
    IsElemAbelian p X → Nat.card X < p ^ 4) : GGIRankLe p 0 R I :=
  fun X hXI hX h4 => absurd h4 (not_le.mpr (h X hXI hX))

theorem ggInnerDiagBound_of_forall_mem (h : ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) :
    GGInnerDiagBound p r R I := by
  intro Eb Eh _ _ _ _ _ hEhA _ hnot
  exact absurd (fun φ hφ => h φ (hEhA.2 φ hφ)) hnot

end PerLabel

section Config

variable {G : Type} [Group G] [Finite G]

theorem mul_card_le_card_of_lt {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hlt : B < Bs) : p * Nat.card B ≤ Nat.card Bs := by
  have := Fact.mk hp
  have hP : IsPGroup p Bs := isPGroup_of_isElemAbelian hBs
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hP.to_le hlt.le)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [ha, hb] at h1 ⊢
  have h2 : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h1
  calc p * p ^ b = p ^ (b + 1) := by rw [pow_succ, mul_comm]
    _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos h2

theorem bstar_le_normalizer_of_sstar {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) :
    Bs ≤ Subgroup.normalizer (L : Set G) := fun _ hb =>
  mem_normalizer_of_sstar hS hnc (Subgroup.mem_centralizer_singleton_iff.mpr
    (IsElemAbelian.comm hBs.2.1 hb (hBs.1 hS.2.1)))

theorem bstar_eq_of_bound_rank {p r₁ r₂ : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift₁ : GGTorusLift p r₁ R) (hbound : GGInnerDiagBound p r₁ R I)
    (hlift₂ : GGTorusLift p r₂ R) (hrank : GGIRankLe p r₂ R I) : B = Bs := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBsN := bstar_le_normalizer_of_sstar hS hBs hnc
  have hcB := card_range_ggBeta_mul L θ hp hS hL hBN
  have hcE := card_range_ggBeta_mul_of hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1
    hS.2.2.2.2 hL θ hBsN
  have hB4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
  by_contra hne
  by_cases hsub : ((ggBeta L θ hBsN).range : Set (MulAut R)) ⊆ I
  · have hpB := mul_card_le_card_of_lt hp hBs.2.1 (lt_of_le_of_ne hBs.1 hne)
    have hEh : Nat.card B ≤ Nat.card (ggBeta L θ hBsN).range := by
      refine Nat.le_of_mul_le_mul_left ?_ hp.pos
      rw [mul_comm p (Nat.card (ggBeta L θ hBsN).range), hcE]
      exact hpB
    have h1 := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1
      hL θ hlift₂
    have h2 : p ^ (r₂ + 1) ≤ Nat.card B := by
      rw [hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    have h4 := hrank _ hsub (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) (hB4.trans hEh)
    have h5 := (Nat.pow_le_pow_iff_right hp.one_lt).mp ((h2.trans hEh).trans h4)
    omega
  · have hEbI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
      rintro _ ⟨b, rfl⟩
      exact ggBeta_mem L θ hBN h3 b
    have hEb3 : p ^ 3 ≤ Nat.card (ggBeta L θ hBN).range := by
      have h := hB4
      rw [← hcB, pow_succ] at h
      exact Nat.le_of_mul_le_mul_right h hp.pos
    have hcard : Nat.card (ggBeta L θ hBsN).range ≤ p * Nat.card (ggBeta L θ hBN).range := by
      have h1 : Nat.card (ggBeta L θ hBsN).range * p ≤
          p * Nat.card (ggBeta L θ hBN).range * p := by
        rw [hcE, mul_assoc, hcB]
        exact hBs.2.2.1
      exact Nat.le_of_mul_le_mul_right h1 hp.pos
    obtain ⟨U, hU, hU2, hEU⟩ := hbound _ _ hEbI (isElemAbelian_range_ggBeta θ hS.1.1 hBN)
      (pow_le_card_range_ggBeta hp hS hL θ hBN hlift₁) hEb3 (range_ggBeta_le θ hBs.1 hBN hBsN)
      (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) hcard hsub
    obtain ⟨T, hTne, hT2, hBsT⟩ := exists_twoSubgroup_of_normalizes θ hBsN hU hU2
      (fun e he u hu => hEU _ ⟨⟨e, he⟩, rfl⟩ u hu)
    have hc := card_le_of_twoLocal hp ⟨T, hTne, hT2, rfl⟩ hBsT hBs.2.1
    rw [← hS.1.2.1] at hc
    exact hne (Subgroup.eq_of_le_of_card_ge hBs.1 hc)

theorem bstar_eq_of_inner_rank {p r : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hrank : GGIRankLe p r R I) : B = Bs := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hBsN := bstar_le_normalizer_of_sstar hS hBs hnc
  have hcE := card_range_ggBeta_mul_of hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1
    hS.2.2.2.2 hL θ hBsN
  have hB4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
  by_contra hne
  have hsub : ((ggBeta L θ hBsN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBsN h3 b
  have hpB := mul_card_le_card_of_lt hp hBs.2.1 (lt_of_le_of_ne hBs.1 hne)
  have hEh : Nat.card B ≤ Nat.card (ggBeta L θ hBsN).range := by
    refine Nat.le_of_mul_le_mul_left ?_ hp.pos
    rw [mul_comm p (Nat.card (ggBeta L θ hBsN).range), hcE]
    exact hpB
  have h1 := succ_le_twoLocalRank_of_torusLift hp hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1
    hL θ hlift
  have h2 : p ^ (r + 1) ≤ Nat.card B := by
    rw [hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos h1
  have h4 := hrank _ hsub (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) (hB4.trans hEh)
  have h5 := (Nat.pow_le_pow_iff_right hp.one_lt).mp ((h2.trans hEh).trans h4)
  omega

end Config

theorem ggStdSubIOneProperInputOn_of_bstarEq {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
          ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I) :
    GGStdSubIOneProperInputOn S := by
  intro G _ _ p B Bs x L hT hBs hne hM
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, ⟨r₁, hl₁, hb⟩, r₂, hl₂, hr⟩ :=
    largeEvenRawDatum_exists hraw
  exact absurd (bstar_eq_of_bound_rank hT hBs hnc hL θ hBN h3 hl₁ hb hl₂ hr) hne

theorem ggStdSubIOneProperInputOn_of_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) :
    GGStdSubIOneProperInputOn S :=
  fun _ _ _ _ _ _ _ _ hT _ _ hM => (ggThmIHyp_false_of_labelAll h hT hM).elim

theorem GGStdSubIOneProperInputOn.mono {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubIOneProperInputOn T) (hST : ∀ p lab, S p lab → T p lab) :
    GGStdSubIOneProperInputOn S := fun G _ _ p B Bs x L hT hBs hne hM =>
  h G p B Bs x L hT hBs hne (largeEvenMarking_mono
    (fun lab _ _ _ _ _ hP => ⟨hST p lab hP.1, hP.2⟩) hM)

end CFSG.StandardType
