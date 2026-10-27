module

public import CFSG.LocalAnalysis.StandardType.GGResJSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj
public import CFSG.LocalAnalysis.StandardType.GGTableBE6PlusThreeTB
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNCells
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNTwAMCells
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenModel
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGTBTorTwE6ThreeHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGResHyp.fix_mem_centralizer_J_of_marking_noFixSC {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r : ℕ} (hT : GGTorusNoFixSC p r R I)
    (hr : p ^ r ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := hH.Bs_le_normalizer_J
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b => by
    have := hBs.1
    exact mul_comm' a b
  have hAI : ∀ a ∈ (ggGamma J hN).range, ∃ φ ∈ I,
      ∀ l : J, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBs3 b, fun l => ggBeta_ggQuotHom J hN θ b l⟩
  exact fix_mem_centralizer_of_pointwise_noFix hp hBs hH.1.2.1.2.2.2 θ hN hBs3
    (hT J (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hJperf
      (ggGamma J hN).range (isElemAbelian_range hBc hBp (ggGamma J hN)) hAI hr h3
      hH.gamma_J_selfCent)

theorem GGResHyp.fix_mem_centralizer_J_of_noFixSC {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} {r : ℕ}
    (hH : GGResHyp p B Bs x L D J y K)
    (hS : ∀ lab, LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusNoFixSC p r R I)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hr : p ^ r ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab) (P' := fun R _ I _ => GGTorusNoFixSC p r R I)
    hS (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hact⟩, hT⟩ := largeEvenRawDatum_exists hraw
  exact hH.fix_mem_centralizer_J_of_marking_noFixSC θ hact hT hr h3

theorem GGResHyp.fix_mem_centralizer_J_of_liftNoFixSC {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} {r : ℕ} (hr3 : 3 ≤ r)
    (hH : GGResHyp p B Bs x L D J y K)
    (hS : ∀ lab, LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p r R ∧ GGTorusNoFixSC p r R I)
    (hJ : GGInnerDiagOnLabel S p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := Fact.out
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab)
    (P' := fun R _ I _ => GGTorusLift p r R ∧ GGTorusNoFixSC p r R I)
    hS (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hact⟩, hLift, hT⟩ := largeEvenRawDatum_exists hraw
  have hr := hH.pow_le_card_range_gamma_J_of_torusLift θ hLift
  exact hH.fix_mem_centralizer_J_of_marking_noFixSC θ hact hT hr
    ((Nat.pow_le_pow_right hp.pos hr3).trans hr)

theorem GGResHyp.fix_mem_centralizer_J_of_linearNs_of_card_gamma {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
  hH.fix_mem_centralizer_J_of_noFixSC (r := 0)
    (fun _ hΛ h => largeEvenLabelAll_noFixSC_linearNs Fact.out hΛ h) hJ
    (by
      rw [pow_zero]
      exact Nat.succ_le_of_lt Nat.card_pos)
    h3

theorem GGResHyp.false_of_innerDiag_J_rowPRankLeTwo_of_card_gamma {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hP : GGRowPRankLeTwo S)
    (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J) : False :=
  not_largeEvenMarking_of_labelAll_card_lt (S := S p)
    (fun lab hlab hS => hP p Fact.out hH.1.1.2.2.2.2.2.1.2.1 lab hlab hS)
    (hH.innerDiag_J_pRank_ge_three_of_card_gamma h3 hJ)

theorem GGResHyp.innerDiag_J_open (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp p B Bs x L D J y K) (hJ : GGInnerDiagOnLabel S p Bs J) :
    GGInnerDiagOnLabel (fun p lab => S p lab ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 ∨
      (lab.tag = .twD ∧ lab.rank = 2))) p Bs J := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  obtain ⟨labL, labJ, -, hsplit, -, hΛJ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj hTCJ hH.1 hH.2.2.2.2.1
  have hsq : ∀ m : ℕ, (2 ^ m) ^ 2 - 1 = (2 ^ m + 1) * (2 ^ m - 1) := fun m => by
    rw [← Nat.sq_sub_sq, one_pow]
  have hL : p ∣ (2 ^ labL.n) ^ 2 - 1 := by
    rw [hsq]
    rcases hsplit with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, rfl⟩
    · exact Dvd.dvd.mul_left h _
    · exact Dvd.dvd.mul_right h _
    · exact Dvd.dvd.mul_left h _
    · rw [hn]
      exact Dvd.dvd.mul_right (dvd_refl 3) _
  have hJ2 : p ∣ (2 ^ labJ.n) ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hdvd
    have h := Nat.sub_dvd_pow_sub_pow ((2 ^ labL.n) ^ 2) 1 k
    have he : ((2 ^ labL.n) ^ 2) ^ k = (2 ^ labJ.n) ^ 2 := by
      rw [hk]
      ring
    rw [one_pow, he] at h
    exact hL.trans h
  rw [hsq] at hJ2
  refine GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ hhas hS => ⟨hS, ?_⟩) hJ
  rcases (hRig lab labJ _ hΛ hΛJ hhas hhasJ).n_cases with hn | h2 | hn
  · rw [hn]
    rcases hp.dvd_mul.mp hJ2 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact Or.inr (Or.inr h2)
  · left
    rw [hn, mul_comm, pow_mul, hsq]
    exact hJ2

@[expose] def ggResJFixRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGTwA5PlusThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

theorem ggResJ_open_label_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab)
    (ho : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 ∨ (lab.tag = .twD ∧ lab.rank = 2)) :
    GGTBTorCov p lab ∨ ggResJPRankTwoLabel p lab ∨ GGTableBNbrInnerLinearNsLabel p lab ∨
      (((lab.tag = .A ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
        p ∣ 2 ^ lab.n + 1) ∨
      (((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
        p ∣ 2 ^ lab.n - 1) ∨
      (p = 3 ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twA ∧ 6 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨ GGE6PlusThreeLabel p lab ∨
      GGF4ThreeLabel p lab ∨ ggResJFixRestLabel p lab := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hΛ ho ⊢
  have hex : ∀ {a : ℕ}, p ∣ 2 ^ a - 1 → ¬ p ∣ 2 ^ a + 1 := by
    intro a h1 h2
    have h := Nat.dvd_sub h2 h1
    have he : 2 ^ a + 1 - (2 ^ a - 1) = 2 := by
      have : 0 < 2 ^ a := Nat.two_pow_pos a
      omega
    rw [he] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h4 : ∀ {k : ℕ}, 3 ≤ k → p ∣ k + 1 → 4 ≤ k := by
    intro k hk hd
    by_contra h
    have hk3 : k = 3 := by omega
    subst hk3
    have h22 : p ∣ 2 ^ 2 := by norm_num at hd ⊢; exact hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h22))
  cases t with
  | A =>
    have hl1 : 1 ≤ l := hΛ.2.1
    by_cases hl2 : l ≤ 2
    · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨rfl, by dsimp only; omega⟩)))
    rcases ho with hm | hpl | ⟨ht, -⟩
    · left
      by_cases hd : p ∣ l + 1
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.aDep (Or.inl rfl)
          (h4 (by dsimp only; omega) hd) hd (by simpa [ggTorM] using hm)
          (fun ⟨_, _, h⟩ => hex hm h)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inl rfl) hd (by simpa [ggTorM] using hm)⟩
    · by_cases hl3 : l = 3
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, Or.inl hl3⟩, hpl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, by dsimp only; omega, hp2, fun h => hex h hpl⟩))
    · simp at ht
  | twA =>
    have hl1 : 2 ≤ l := hΛ.2.1
    by_cases hl2 : l = 2
    · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, hl2⟩)))))
    rcases ho with hm | hpl | ⟨ht, -⟩
    · by_cases hl34 : l = 3 ∨ l = 4
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, hl34⟩, hm⟩))))
      by_cases hl5 : l = 5
      · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.relA5 hl5 (Or.inr ⟨rfl, hm⟩)⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, by omega, hm⟩))))))
    · by_cases h35 : p = 3 ∧ l = 5
      · obtain ⟨rfl, rfl⟩ := h35
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩, hpl⟩))))))))
      left
      by_cases hd : p ∣ l + 1
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.aDep (Or.inr rfl)
          (h4 (by dsimp only; omega) hd) hd (by simpa [ggTorM] using hpl)
          (fun ⟨h3, h5, _⟩ => h35 ⟨h3, h5⟩)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inr rfl) hd (by simpa [ggTorM] using hpl)⟩
    · simp at ht
  | B =>
    left
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.c (Or.inl rfl) (Dvd.dvd.mul_right hm _)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.c (Or.inl rfl) (Dvd.dvd.mul_left hpl _)⟩
    · simp at ht
  | C =>
    left
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.c (Or.inr rfl) (Dvd.dvd.mul_right hm _)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.c (Or.inr rfl) (Dvd.dvd.mul_left hpl _)⟩
    · simp at ht
  | D =>
    left
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inl hm⟩)⟩
    · rcases Nat.even_or_odd l with he | hodd
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inr ⟨hpl, he⟩⟩)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inl ⟨rfl, hpl, hodd⟩)⟩
    · simp at ht
  | twD =>
    rcases ho with hm | hpl | ⟨-, hl2⟩
    · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inl hm⟩)⟩
    · rcases Nat.even_or_odd l with he | hodd
      · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨hpl, he⟩⟩)⟩
      · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inr ⟨rfl, hpl, hodd⟩)⟩
    · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hl2⟩))))))
  | E6 =>
    by_cases hp3 : p = 3
    · subst hp3
      rcases ho with hm | hpl | ⟨ht, -⟩
      · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.e6Three rfl rfl (by simpa [ggTorM] using hm)⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨rfl, rfl, hpl⟩)))))))
      · simp at ht
    · left
      rcases ho with hm | hpl | ⟨ht, -⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind hp3 (Or.inl rfl) (by simpa [ggTorM] using hm)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.relE6 hp3 (Or.inl ⟨rfl, hpl⟩)⟩
      · simp at ht
  | E7 =>
    left
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e7 rfl (Dvd.dvd.mul_right hm _)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e7 rfl (Dvd.dvd.mul_left hpl _)⟩
    · simp at ht
  | E8 =>
    left
    by_cases hp3 : p = 3
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e8Three rfl hp3⟩
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e8Ind hp3 rfl (Dvd.dvd.mul_right hm _)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e8Ind hp3 rfl (Dvd.dvd.mul_left hpl _)⟩
    · simp at ht
  | F4 =>
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.f4 rfl (Dvd.dvd.mul_right hm _)
        (fun ⟨_, h⟩ => hex hm h)⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hpl⟩))))))))
      · exact Or.inl ⟨_, _, _, _, _, GGTBTorRowAt.f4 rfl (Dvd.dvd.mul_left hpl _)
          (fun ⟨h, _⟩ => hp3 h)⟩
    · simp at ht
  | twE6 =>
    by_cases hp3 : p = 3
    · subst hp3
      rcases ho with hm | hpl | ⟨ht, -⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl, hpl⟩))))))))
      · simp at ht
    · left
      rcases ho with hm | hpl | ⟨ht, -⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.relE6 hp3 (Or.inr ⟨rfl, hm⟩)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind hp3 (Or.inr rfl) (by simpa [ggTorM] using hpl)⟩
      · simp at ht
  | triD4 =>
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl hm⟩))))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr hpl⟩))))))
    · simp at ht
  | G2 => exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
  | twB2 => exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  | twF4 =>
    rcases ho with hm | hpl | ⟨ht, -⟩
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl hm⟩))))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr hpl⟩))))))
    · simp at ht
  | B2der => exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | G2der => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
  | twF4der => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

section UnitarySplit


open Multiplicative in
theorem ggTorusNoFixSC_unitarySplit {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 4 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusNoFixSC p 0 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI _ _ hsc a ha hfix
  obtain ⟨r, ε, U, ζ, τ, φ, -, -, hζ, -, hτ, -, -, -, hM, hτc⟩ :=
    SuSplitRootGen.exists_isCoverTorusModel hK hd hp hpq hψ hker hperf hA hAI hsc
  have hexp : ∀ z : Multiplicative (Fin r → ZMod p), z ^ p = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    have hpz : p • toAdd z = 0 := by
      funext i
      show p • toAdd z i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hpz, ofAdd_zero]
  have hcomm : ∀ v z, MulAut.conj (φ (τ v)) (φ (τ z)) = φ (τ z) := by
    intro v z
    rw [MulAut.conj_apply, ← map_inv φ, ← map_mul φ, ← map_mul φ, ← map_inv τ, ← map_mul τ,
      ← map_mul τ, mul_comm v z, mul_inv_cancel_right]
  have hinj : ∀ u v, MulAut.conj (φ (τ u)) = MulAut.conj (φ (τ v)) → u = v := by
    intro u v huv
    have h1 : MulAut.conj (φ (τ (u * v⁻¹))) = 1 := by
      rw [map_mul τ, map_inv τ, map_mul φ, map_inv φ, map_mul MulAut.conj, map_inv MulAut.conj,
        huv, mul_inv_cancel]
    refine mul_inv_eq_one.mp (hτc _ (Subgroup.mem_center_iff.mpr fun g => ?_))
    have h2 : MulAut.conj (φ (τ (u * v⁻¹))) g = g := by rw [h1]; rfl
    rw [MulAut.conj_apply] at h2
    calc g * φ (τ (u * v⁻¹))
        = φ (τ (u * v⁻¹)) * g * (φ (τ (u * v⁻¹)))⁻¹ * φ (τ (u * v⁻¹)) := by rw [h2]
      _ = φ (τ (u * v⁻¹)) * g := by group
  obtain ⟨t, rfl⟩ := (hM a).mp ha
  have hcoord : ∀ m, toAdd t m = 0 := by
    intro m
    have hw := SuSplitRootGen.lineWeyl_conj U hp hζ.pow_eq_one hτ m
    generalize SuSplitRootGen.lineWeyl U ε m = w at hw
    have hWe : GGTorusWeylElt p A (φ w) := by
      intro a' ha'
      obtain ⟨u, rfl⟩ := (hM a').mp ha'
      have hwu := hw (toAdd u)
      rw [ofAdd_toAdd] at hwu
      have hkey : φ w * (MulAut.conj (φ (τ u)) (φ w))⁻¹ =
          φ (τ (ofAdd (SlNsRootGen.negMap m (toAdd u)) * u⁻¹)) := by
        rw [MulAut.conj_apply, map_mul τ, map_inv τ, ← hwu]
        simp only [map_mul, map_inv]
        group
      refine ⟨?_, fun a'' ha'' => ?_⟩
      · rw [hkey, ← map_pow φ, ← map_pow τ, hexp, map_one τ, map_one φ]
      · obtain ⟨v, rfl⟩ := (hM a'').mp ha''
        rw [hkey]
        exact hcomm v _
    have hc := hfix (φ w) hWe
    have hwt := hw (toAdd t)
    rw [ofAdd_toAdd] at hwt
    rw [← map_inv MulAut.conj, ← map_mul MulAut.conj, ← map_mul MulAut.conj, ← map_inv φ,
      ← map_mul φ, ← map_mul φ, hwt] at hc
    have h2 : SlNsRootGen.negMap m (toAdd t) = toAdd t := by
      rw [← toAdd_ofAdd (SlNsRootGen.negMap m (toAdd t)), hinj _ _ hc]
    exact (SlNsRootGen.negMap_eq_self_iff hp2).mp h2
  have ht : t = 1 := by
    refine toAdd.injective ?_
    rw [toAdd_one]
    funext m
    exact hcoord m
  rw [ht, map_one τ, map_one φ, map_one MulAut.conj]

theorem largeEvenLabelAll_noFixSC_unitarySplit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNoFixSC p 0 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusNoFixSC_unitarySplit (d := l + 1) hK (by omega) hp hp2 hpq⟩

theorem GGResHyp.fix_mem_centralizer_J_of_unitarySplit_of_card_gamma {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
  hH.fix_mem_centralizer_J_of_noFixSC (r := 0)
    (fun _ _ h => largeEvenLabelAll_noFixSC_unitarySplit Fact.out hH.1.1.2.2.2.2.2.1.2.1 h) hJ
    (by
      rw [pow_zero]
      exact Nat.succ_le_of_lt Nat.card_pos)
    h3

end UnitarySplit

section E6PlusThree


theorem GGResHyp.fix_mem_centralizer_J_of_e6PlusThree {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJ : GGInnerDiagOnLabel GGE6PlusThreeLabel p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hJperf, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGE6PlusThreeLabel p lab)
    (P' := fun R _ I _ => GGTorusLift p 4 R ∧ GGTorusIrred p 4 R I)
    (fun _ _ h => largeEvenLabelAll_torusIrred_e6PlusThree h) (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hact⟩, hLift, hIrred⟩ := largeEvenRawDatum_exists hraw
  have h4 := hH.pow_le_card_range_gamma_J_of_torusLift θ hLift
  exact FrameRoute.fix_mem_centralizer_of_noFix hp hH.1.2.1.2.1 hH.1.2.1.2.2.2 hJperf θ
    hH.Bs_le_normalizer_J hact h4 ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4)
    (ggTorusNoFix_of_irred hp.one_lt hIrred)

end E6PlusThree

theorem ggTorusNoFixSC_of_torW_of_diag {p r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hp : p.Prime) (hp2 : p ≠ 2) (hCd : ∀ k, C k k = 2)
    {R : Type} [Group R] {I : Set (MulAut R)} (h : GGTorusTorW p r m N C M R I) :
    GGTorusNoFixSC p r R I :=
  fun L' _ _ ψ hψ hk hc A hA hAI hr h3 hSC =>
    ggTorusNoFixTB_of_torW_of_diag hp hp2 hCd h L' ψ A ⟨hψ, hk, hc, hA, hAI, hr, h3, hSC⟩

section F4Three


theorem GGResHyp.fix_mem_centralizer_J_of_f4Three {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJ : GGInnerDiagOnLabel GGF4ThreeLabel p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp3 : p = 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hJ
    obtain ⟨R, _, I, F, -, -, θ, ⟨h, -⟩⟩ := largeEvenRawDatum_exists hraw
    exact h.2.1
  subst hp3
  have hR : ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma J hN).range := fun hN =>
    ggF4Three_rank_of_marking (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hH.1 hH.2.2.2.1 hJ hN
  have hMark : LargeEvenMarking J (fun lab _ _ I _ θ =>
      lab.tag = .F4 ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : J => (l' : G) = b⁻¹ * l * b) φ) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.2⟩) hJ
  exact (ggF4NbrAutReflKGInput_holds G 3 Bs J Nat.prime_three (by decide) hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hMark (card_eq_of_F4Three_marking hH.1 hJ hR)).2.2

end F4Three

section TwA5PlusThree


theorem GGResHyp.fix_mem_centralizer_J_of_twA5PlusThree_of_card {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTwA5PlusThreeLabel p Bs J)
    (h4 : p ^ 4 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := Fact.out
  refine hH.fix_mem_centralizer_J_of_noFixSC (r := 4) (fun lab hΛ h => ?_) hJ h4
    ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4)
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, rfl, h3⟩ := h
  dsimp only at ht hl h3 hΛ
  subst ht hl
  exact (ggTorusTorW_uni_six_three_label_all hΛ.1 h3).mono fun _ _ _ _ hW =>
    ggTorusNoFixSC_of_torW_of_diag Nat.prime_three (by norm_num) (ggIntCartan_A 5).1 hW

end TwA5PlusThree

section TwE6PlusThree


theorem GGResHyp.fix_mem_centralizer_J_of_twE6PlusThree_of_card {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J)
    (h5 : p ^ 5 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := Fact.out
  refine hH.fix_mem_centralizer_J_of_noFixSC (r := 5) (fun lab hΛ h => ?_) hJ h5
    ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h5)
  obtain ⟨ht, rfl, h3⟩ := h
  have hm : ggTorM lab = 2 ^ lab.n + 1 := by simp [ggTorM, ht]
  exact (TwE6ThreeLang.ggTBTorTwE6Three_holds lab hΛ ht (by rw [hm]; exact h3)).mono
    fun _ _ _ _ hW =>
      ggTorusNoFixSC_of_torW_of_diag Nat.prime_three (by norm_num) ggIntCartan_E₆.1 hW

theorem GGResHyp.six_le_twoLocalRank_of_twE6PlusThree {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J) :
    6 ≤ LargeEvenTwoLocalRank p G := by
  have hp : p.Prime := Fact.out
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ _ _ => GGTorusLift p (TwE6Delta.liftRank p) R)
    (fun _ hΛ h => largeEvenLabelAll_torusLift_twE6Add_holds hp hΛ
      ⟨h.1, by rw [h.2.1]; exact h.2.2⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hp3, -⟩, -⟩, hLift⟩ := largeEvenRawDatum_exists hraw
  subst hp3
  have h := hH.1.torusLift_add_two_le_twoLocalRank θ hLift
  rwa [show TwE6Delta.liftRank 3 = 4 by simp [TwE6Delta.liftRank]] at h

end TwE6PlusThree

section Rest


theorem GGResHyp.fix_mem_centralizer_J_of_twE6_sub {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp3 : p = 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hJ
    obtain ⟨R, _, I, F, -, -, θ, ⟨h, -⟩⟩ := largeEvenRawDatum_exists hraw
    exact h.1
  subst hp3
  exact hH.fix_mem_centralizer_J_of_liftNoFixSC (r := 4) (by norm_num)
    (fun _ hΛ h => largeEvenLabelAll_noFixSC_twE6_sub hΛ h.2.1 h.2.2) hJ

theorem GGResHyp.fix_mem_centralizer_J_or_rest_of_tcj (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J) :
    (∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) ∨
      GGInnerDiagOnLabel (fun p lab => S p lab ∧ ggResJFixRestLabel p lab) p Bs J := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hc := GGInnerDiagOnLabel.mono_label_of_hasLabel
    (T := fun p lab => GGTBTorCov p lab ∨ ggResJPRankTwoLabel p lab ∨
      GGTableBNbrInnerLinearNsLabel p lab ∨
      ((((lab.tag = .A ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
        p ∣ 2 ^ lab.n + 1) ∨
      ((((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
        p ∣ 2 ^ lab.n - 1) ∨
      ((p = 3 ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        ((lab.tag = .twA ∧ 6 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
          (GGE6PlusThreeLabel p lab ∨
            (GGF4ThreeLabel p lab ∨ (S p lab ∧ ggResJFixRestLabel p lab))))))))
    (fun lab hΛ _ ⟨hS, ho⟩ => by
      rcases ggResJ_open_label_cases hp hp2 hΛ ho with h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨hS, h⟩)))))))))
    (hH.innerDiag_J_open hTCJ hRig hJ)
  rcases hc.elim_or with h | hc
  · exact Or.inl (hH.fix_mem_centralizer_J_of_cov hT hLift h h3)
  rcases hc.elim_or with h | hc
  · exact (hH.false_of_innerDiag_J_pRankTwo_of_card_gamma h3 h).elim
  rcases hc.elim_or with h | hc
  · exact Or.inl (hH.fix_mem_centralizer_J_of_linearNs_of_card_gamma h3 h)
  rcases hc.elim_or with h | hc
  · exact (hH.false_of_innerDiag_J_rowPRankLeTwo_of_card_gamma ggRowPRankLeTwo_smallPlus h3
      h).elim
  rcases hc.elim_or with h | hc
  · exact (hH.false_of_innerDiag_J_rowPRankLeTwo_of_card_gamma ggRowPRankLeTwo_smallMinus h3
      h).elim
  rcases hc.elim_or with h | hc
  · exact Or.inl (hH.fix_mem_centralizer_J_of_twE6_sub h)
  rcases hc.elim_or with h | hc
  · exact Or.inl (hH.fix_mem_centralizer_J_of_unitarySplit_of_card_gamma h3
      (h.mono_label fun _ ⟨ht, hl, hq⟩ => ⟨ht, by omega, hq⟩))
  rcases hc.elim_or with h | hc
  · exact Or.inl (hH.fix_mem_centralizer_J_of_e6PlusThree h)
  rcases hc.elim_or with h | hc
  · exact Or.inl (hH.fix_mem_centralizer_J_of_f4Three h)
  · exact Or.inr hc

theorem GGResHyp.fix_mem_centralizer_J_or_twE6_of_tcj_of_six (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp p B Bs x L D J y K) (hm : 6 ≤ LargeEvenTwoLocalRank p G)
    (hJ : GGInnerDiagOnLabel S p Bs J) :
    (∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) ∨
      GGInnerDiagOnLabel (fun p lab => S p lab ∧ GGTableBTwE6ThreeLabel p lab) p Bs J := by
  have hp : p.Prime := Fact.out
  rcases hH.fix_mem_centralizer_J_or_rest_of_tcj hT hLift hTCJ hRig
      (hH.pow_three_le_card_gamma_J_of_twoLocalRank (by omega)) hJ with h | hc
  · exact Or.inl h
  have hc' : GGInnerDiagOnLabel (fun p lab => GGTwA5PlusThreeLabel p lab ∨
      (S p lab ∧ GGTableBTwE6ThreeLabel p lab)) p Bs J := by
    refine hc.mono_label fun lab h => ?_
    obtain ⟨hS, hp3, hl, hq⟩ := h
    rcases hl with ⟨ht, hr⟩ | ht
    · exact Or.inl ⟨ht, hr, hp3, hq⟩
    · exact Or.inr ⟨hS, ht, hp3, hq⟩
  rcases hc'.elim_or with h | h
  · exact Or.inl (hH.fix_mem_centralizer_J_of_twA5PlusThree_of_card h
      ((Nat.pow_le_pow_right hp.pos (by omega)).trans hH.pow_le_card_gamma_J))
  · exact Or.inr h

theorem GGResHyp.fix_mem_centralizer_J_of_tcj_of_seven (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp p B Bs x L D J y K) (hm : 7 ≤ LargeEvenTwoLocalRank p G)
    (hJ : GGInnerDiagOnLabel S p Bs J) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := Fact.out
  rcases hH.fix_mem_centralizer_J_or_twE6_of_tcj_of_six hT hLift hTCJ hRig (by omega) hJ with
    h | hc
  · exact h
  · exact hH.fix_mem_centralizer_J_of_twE6PlusThree_of_card (hc.mono_label fun _ h => h.2)
      ((Nat.pow_le_pow_right hp.pos (by omega)).trans hH.pow_le_card_gamma_J)

theorem GGResHyp.fix_mem_centralizer_J_or_low_of_tcj (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp p B Bs x L D J y K) (hm : 5 ≤ LargeEvenTwoLocalRank p G)
    (hJ : GGInnerDiagOnLabel S p Bs J) :
    (∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G)) ∨
      (LargeEvenTwoLocalRank p G = 5 ∧
        GGInnerDiagOnLabel (fun p lab => S p lab ∧ GGTwA5PlusThreeLabel p lab) p Bs J) ∨
      (LargeEvenTwoLocalRank p G = 6 ∧
        GGInnerDiagOnLabel (fun p lab => S p lab ∧ GGTableBTwE6ThreeLabel p lab) p Bs J) := by
  rcases Nat.lt_or_ge (LargeEvenTwoLocalRank p G) 7 with h7 | h7
  · rcases Nat.lt_or_ge (LargeEvenTwoLocalRank p G) 6 with h6 | h6
    · rcases hH.fix_mem_centralizer_J_or_rest_of_tcj hT hLift hTCJ hRig
          (hH.pow_three_le_card_gamma_J_of_twoLocalRank hm) hJ with h | hc
      · exact Or.inl h
      have hc' : GGInnerDiagOnLabel (fun p lab => (S p lab ∧ GGTwA5PlusThreeLabel p lab) ∨
          GGTableBTwE6ThreeLabel p lab) p Bs J := by
        refine hc.mono_label fun lab h => ?_
        obtain ⟨hS, hp3, hl, hq⟩ := h
        rcases hl with ⟨ht, hr⟩ | ht
        · exact Or.inl ⟨hS, ht, hr, hp3, hq⟩
        · exact Or.inr ⟨ht, hp3, hq⟩
      rcases hc'.elim_or with h | h
      · exact Or.inr (Or.inl ⟨by omega, h⟩)
      · exact absurd (hH.six_le_twoLocalRank_of_twE6PlusThree h) (by omega)
    · rcases hH.fix_mem_centralizer_J_or_twE6_of_tcj_of_six hT hLift hTCJ hRig h6 hJ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨by omega, h⟩)
  · exact Or.inl (hH.fix_mem_centralizer_J_of_tcj_of_seven hT hLift hTCJ hRig h7 hJ)

end Rest

end CFSG.StandardType

end
