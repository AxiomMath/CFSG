module

public import CFSG.LocalAnalysis.StandardType.GGF4QTwoReduction
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdModel
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4Holds
public import CFSG.LocalAnalysis.StandardType.GGSpTwoTorusRank
public import CFSG.LocalAnalysis.StandardType.GGStdUFourExcl
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

private theorem not_ggInnerDiagOnLabel_of_torusLiftFour {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 4 R)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4) :
    ¬ GGInnerDiagOnLabel S 3 Bs L := by
  intro hq
  have hS' := largeEvenMarking_and_labelAll (S := fun lab => S 3 lab)
    (fun lab hlab hs => hS lab hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hq
  obtain ⟨hL, lab, -, hraw⟩ := hS'
  obtain ⟨R, _, I, F, -, -, θ, -, hlift⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨-, -, -, -, -, -, hSs, -⟩, hBs, -⟩ := hC
  have h5 := succ_le_twoLocalRank_of_torusLift Nat.prime_three hSs.2.2.2.1.1
    (hSs.1.1.2 x hSs.2.1) hSs.2.2.1 hL θ hlift
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  rw [hSs.1.2.1, hcard] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  omega

private theorem not_ggInnerDiagOnLabel_of_cardLt {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3)
    (hsp : ∀ lab, S 3 lab → LargeEvenSplit 3 lab)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) : ¬ GGInnerDiagOnLabel S 3 Bs L := fun hq =>
  ggThmIHyp_false_of_labelAll (S := fun p lab => p = 3 ∧ S 3 lab)
    (fun _ lab _ hlab hs _ => by
      obtain ⟨rfl, hs⟩ := hs
      exact hS lab hlab hs) hC.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨rfl, hP.1⟩, hsp lab hP.1,
      hC.2.1.1.trans hP.2.1, fun b hb => hP.2.2 b (hC.2.1.1 hb)⟩) hq)

private def GGTorusNoSC27 (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 0 R I L' ψ A → Nat.card A ≠ 3 ^ 3

private theorem not_ggInnerDiagOnLabel_of_noSC27 {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusNoSC27 R I)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4) :
    ¬ GGInnerDiagOnLabel S 3 Bs L := by
  intro hq
  have hq' := largeEvenMarking_and_labelAll (S := fun lab => S 3 lab)
    (fun lab hlab hs => hS lab hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hq
  obtain ⟨hL, lab, -, hraw⟩ := hq'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3⟩, hno⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨-, -, -, -, -, -, hSs, -⟩, ⟨hBBs, hBs, -, hSC⟩, -⟩ := hC
  have hmul := card_range_ggGamma_mul_of Nat.prime_three hBs (hBBs hSs.2.1) hSs.2.2.1
    hSs.2.2.2.1.1 hSs.2.2.2.2 hBsN
  have h27 : Nat.card (ggGamma L hBsN).range = 3 ^ 3 := by
    rw [hcard] at hmul
    omega
  exact hno L (ggQuotHom θ) _ (ggTorusTBGroup_of_marking (r := 0) Nat.prime_three hBs hSC hL θ
    hBsN (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) (by rw [h27]; norm_num) h27.ge) h27

private theorem labelAll_torusLiftFour_A {l : ℕ} (hl : 7 ≤ l) :
    LargeEvenLabelAll ⟨.A, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  exact ggTorusLift_mono Nat.prime_three (TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv _ K)
    (TwoThree.ggTorusLift_two (hK.trans (pow_one 2)) (by omega))) (by omega)

private theorem labelAll_torusLiftFour_twA
    {l : ℕ} (hlab : LargeEvenInLambda2 ⟨.twA, l, 1⟩) (hl : 6 ≤ l) :
    LargeEvenLabelAll ⟨.twA, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R :=
  (largeEvenLabelAll_torusLift_twA hlab rfl Nat.prime_three (by norm_num)).mono
    fun _ _ _ _ h => ggTorusLift_mono Nat.prime_three h (by
      show 4 ≤ ggUnitaryTorusRank 3 (l + 1)
      unfold ggUnitaryTorusRank
      split_ifs <;> omega)

private theorem labelAll_torusLiftFour_sp {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) {l : ℕ}
    (hl : 5 ≤ l) : LargeEvenLabelAll ⟨t, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  intro Q hQ
  have key : LargeEvenRecipeSymplectic l (2 ^ 1) false Q →
      LargeEvenRecipeSymplectic l (2 ^ 1) false fun R _ I F => Q R I F ∧ GGTorusLift 3 4 R := by
    rintro ⟨K, i1, i2, hK, hq⟩
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    exact ggTorusLift_mono Nat.prime_three
      (TwoThree.ggTorusLift_sp_two (k := k) (hK.trans (pow_one 2))) (by omega)
  rcases ht with rfl | rfl
  · exact key hQ
  · exact key hQ

private theorem labelAll_torusLiftFour_orth
    {t : LargeEvenLieTag} (ht : t = .D ∨ t = .twD) {l : ℕ}
    (hl : 5 ≤ l) : LargeEvenLabelAll ⟨t, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  have h : GGOrthRestLabel 3 ⟨t, l, 1⟩ := by
    refine ⟨by dsimp only; omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inr ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, by norm_num⟩
  exact (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three h).mono
    fun _ _ _ _ h => ggTorusLift_mono Nat.prime_three h.2 (by dsimp only; omega)

private theorem labelAll_torusLiftFour_E6
    {l : ℕ} :
    LargeEvenLabelAll ⟨.E6, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  exact ⟨K, i1, i2, hK, hq, TableBExc.E6Three.ggTorusLift_E6_two⟩

private theorem labelAll_torusLiftFour_E7
    {l : ℕ} :
    LargeEvenLabelAll ⟨.E7, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  exact ⟨K, i1, i2, hK, hq,
    ggTorusLift_mono Nat.prime_three TableBExcTwo.ggTorusLift_E7Two (by norm_num)⟩

private theorem labelAll_torusLiftFour_E8
    {l : ℕ} :
    LargeEvenLabelAll ⟨.E8, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  exact ⟨K, i1, i2, hK, hq,
    ggTorusLift_mono Nat.prime_three TableBExcTwo.ggTorusLift_E8Two (by norm_num)⟩

private theorem labelAll_torusLiftFour_twE6
    {l : ℕ} (hlab : LargeEvenInLambda2 ⟨.twE6, l, 1⟩) :
    LargeEvenLabelAll ⟨.twE6, l, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R :=
  (largeEvenLabelAll_twE6Three_of (p := 3) hlab ⟨rfl, rfl, by norm_num⟩ (P := fun _ _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial)).mono fun _ _ _ _ h => h.1

private theorem labelAll_noSC27_twA4 :
    LargeEvenLabelAll ⟨.twA, 4, 1⟩ fun R _ I _ => GGTorusNoSC27 R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  rintro L' _ _ ψ A ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ h27
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  obtain ⟨Θ, -⟩ := exists_permModel (d := 5) Nat.prime_three
    (TableBUE.center_proj_eq_bot hK' (by norm_num) (by decide))
    (InndiagSU.ggOutdiagPrime_unitary hK' le_rfl (by norm_num) (by decide) Nat.prime_three
      (by norm_num) (by norm_num))
    (StdSubRestU.ggCenterPrime_unitary hK' le_rfl (by norm_num) (by decide) Nat.prime_three
      (by norm_num) (by norm_num))
    (UModel.ggTorusPermEltSC_unitary hK' le_rfl (by norm_num) Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num))
    hψ hker hperf hA hAI h3 hsc
  have hc := Nat.card_congr Θ.toEquiv
  have hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3K : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; norm_num
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3K
    exact ⟨u, (IsPrimitiveRoot.coe_units_iff).mpr (hu ▸ IsPrimitiveRoot.orderOf u)⟩
  rw [ggKGTum_card_sumZero Nat.prime_three hζ (by norm_num), h27] at hc
  norm_num at hc

private theorem labelAll_noSC27_D4 :
    LargeEvenLabelAll ⟨.D, 4, 1⟩ fun R _ I _ => GGTorusNoSC27 R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [show (4 : ℕ) ≠ 3 by norm_num, ↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  rintro L' _ _ ψ A ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ h27
  have hK2 : Nat.card K = 2 := hK.trans (pow_one 2)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
  obtain ⟨hZ, hcp⟩ := ggOrthRestCenterInput_holds.2 K 4 hK2 le_rfl
  have hT := ggOrthEvenTorusInput_holds.1 K 4 3 le_rfl Nat.prime_three
    (Or.inr ⟨by decide, by rw [hK2]⟩)
  obtain ⟨k, Θ, -, hk, -⟩ := OrthExcEven.exists_evenSignedPermModelSC Nat.prime_three
    (by norm_num) subset_rfl hZ hcp hT hψ hker hperf hA hAI h3 hsc
  have hc := Nat.card_congr Θ.toEquiv
  subst hk
  rw [Nat.card_fun, Nat.card_fin, h27] at hc
  have h3' : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h3'] at hc
  norm_num at hc

private theorem labelAll_noSC27_sp8
    {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) :
    LargeEvenLabelAll ⟨t, 4, 1⟩ fun R _ I _ => GGTorusNoSC27 R I := by
  intro Q hQ
  have key : LargeEvenRecipeSymplectic 4 (2 ^ 1) false Q →
      LargeEvenRecipeSymplectic 4 (2 ^ 1) false fun R _ I F => Q R I F ∧ GGTorusNoSC27 R I := by
    rintro ⟨K, i1, i2, hK, hq⟩
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    show GGTorusNoSC27 (LargeEvenProj (LargeEvenSpGroup K 4))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 4)) (LargeEvenGSpSet K 4))
    rintro L' _ _ ψ A ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ h27
    have hK2 : Nat.card K = 2 := hK.trans (pow_one 2)
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK
    obtain ⟨k, Θ, -, hk, -⟩ := OrthExcEven.exists_evenSignedPermModelSC (kP := fun k => k = 4)
      Nat.prime_three (by norm_num)
      (fun φ _ => TwoThree.mem_range_conj_sp hK2 (by norm_num) φ)
      TableBSymp.center_spProj_eq_bot (ggCenterPrime_sp Nat.prime_three (by norm_num))
      (spTwo_scRank hK2 4 (by norm_num)) hψ hker hperf hA hAI h3 hsc
    have hc := Nat.card_congr Θ.toEquiv
    subst hk
    rw [Nat.card_fun, Nat.card_fin, h27] at hc
    have h3' : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h3'] at hc
    norm_num at hc
  rcases ht with rfl | rfl
  · exact key hQ
  · exact key hQ

private theorem not_ggInnerDiagOnLabel_u6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4) :
    ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L := by
  intro hq
  have h := Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x L D J hC
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨⟨⟨hP.1.1, by rw [hP.1.2.1]; omega,
      by rw [hP.1.2.2]; norm_num, by rw [hP.1.2.1]; norm_num⟩, hP.1.2.1, rfl⟩,
      Or.inr (Or.inr (Or.inr ⟨hP.1.2.2, rfl⟩)), hP.2⟩) hq)
  rw [hcard] at h
  norm_num at h

theorem ggQTwoEnds_of_card_bstar_of_titsExcl
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hTits : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twF4der, 0, 1⟩) 3 Bs L → False) :
    GGInnerDiagOnLabel GGLabSp6 3 Bs L ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6) ∧
        LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) ∨
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) := by
  obtain ⟨hL, lab, hlab, hraw⟩ := hq
  have hfix : ∀ S : ℕ → LargeEvenLabel → Prop, S 3 lab → GGInnerDiagOnLabel S 3 Bs L :=
    fun S hS => ⟨hL, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hP⟩ => ⟨hs, hna, θ, hS, hP⟩) hraw⟩
  have hmk : ∀ P : LargeEvenLabel → Prop, P lab →
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => P lab) :=
    fun P hP => ⟨hL, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hP⟩) hraw⟩
  have hR1 : ∀ lab₀, LargeEvenLabelAll lab₀ (fun R _ _ _ => GGTorusLift 3 4 R) → lab = lab₀ →
      False := fun lab₀ h0 he =>
    not_ggInnerDiagOnLabel_of_torusLiftFour (S := fun _ l => l = lab₀)
      (fun _ _ h => by subst h; exact h0) hC hcard (hfix _ he)
  have hR2 : ∀ lab₀ : LargeEvenLabel, lab₀.n = 1 → LargeEvenLabelAll lab₀ (fun R _ I _ =>
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X →
        Nat.card X < 3 ^ 3) → lab = lab₀ → False := fun lab₀ hn0 h0 he =>
    not_ggInnerDiagOnLabel_of_cardLt (S := fun _ l => l = lab₀)
      (fun _ _ h => by subst h; exact h0)
      (fun _ h => by subst h; exact Or.inr (Or.inr (Or.inr ⟨hn0, rfl⟩))) hC (hfix _ he)
  have hR3 : ∀ lab₀, LargeEvenLabelAll lab₀ (fun R _ I _ => GGTorusNoSC27 R I) → lab = lab₀ →
      False := fun lab₀ h0 he =>
    not_ggInnerDiagOnLabel_of_noSC27 (S := fun _ l => l = lab₀)
      (fun _ _ h => by subst h; exact h0) hC hcard (hfix _ he)
  obtain ⟨-, -, -, -, -, -, -, hn2, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  have hn : n = 1 := by
    have h1 : 1 ≤ n := hlab.1
    have h2 : n < 2 := hn2
    omega
  subst hn
  have hsp : ∀ t' l', LargeEvenSplit 3 ⟨t', l', 1⟩ := fun _ _ =>
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  cases t with
  | A =>
    have hl : 1 ≤ l ∧ (l = 1 → 2 ≤ 1) := hlab.2
    rcases (show l ≤ 4 ∨ l = 5 ∨ l = 6 ∨ 7 ≤ l by omega) with hl4 | rfl | rfl | hl7
    · exact (hR2 _ rfl (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall
        ⟨rfl, rfl, Or.inl ⟨rfl, hl4⟩⟩) rfl).elim
    · exact Or.inr (Or.inl ⟨5, Or.inl rfl, hmk _ ⟨rfl, rfl, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨6, Or.inr rfl, hmk _ ⟨rfl, rfl, rfl⟩⟩)
    · exact (hR1 _ (labelAll_torusLiftFour_A hl7) rfl).elim
  | twA =>
    have hl : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    rcases (show l = 3 ∨ l = 4 ∨ l = 5 ∨ 6 ≤ l by omega) with rfl | rfl | rfl | hl6
    · exact (not_ggInnerDiagOnLabel_u4 hC (hfix _ ⟨Or.inl rfl, rfl, rfl⟩)).elim
    · exact (hR3 _ labelAll_noSC27_twA4 rfl).elim
    · exact (not_ggInnerDiagOnLabel_u6 hC hcard (hfix _ ⟨rfl, rfl, rfl⟩)).elim
    · exact (hR1 _ (labelAll_torusLiftFour_twA hlab hl6) rfl).elim
  | B =>
    have hl : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    rcases (show l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with rfl | rfl | hl5
    · exact Or.inl (hfix GGLabSp6 ⟨Or.inl rfl, rfl, rfl⟩)
    · exact (hR3 _ (labelAll_noSC27_sp8 (Or.inl rfl)) rfl).elim
    · exact (hR1 _ (labelAll_torusLiftFour_sp (Or.inl rfl) hl5) rfl).elim
  | C =>
    have hl : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    rcases (show l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with rfl | rfl | hl5
    · exact Or.inl (hfix GGLabSp6 ⟨Or.inr rfl, rfl, rfl⟩)
    · exact (hR3 _ (labelAll_noSC27_sp8 (Or.inr rfl)) rfl).elim
    · exact (hR1 _ (labelAll_torusLiftFour_sp (Or.inr rfl) hl5) rfl).elim
  | D =>
    have hl : 3 ≤ l := hlab.2
    rcases (show l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with rfl | rfl | hl5
    · exact (hR2 _ rfl (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall
        ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩) rfl).elim
    · exact (hR3 _ labelAll_noSC27_D4 rfl).elim
    · exact (hR1 _ (labelAll_torusLiftFour_orth (Or.inl rfl) hl5) rfl).elim
  | twD =>
    have hl : 2 ≤ l := hlab.2
    rcases (show l = 2 ∨ l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with rfl | rfl | rfl | hl5
    · exact (hR2 _ rfl (largeEvenLabelAll_card_lt_linearTwo Nat.prime_three (by norm_num) hlab
        (Or.inr ⟨rfl, rfl⟩)) rfl).elim
    · exact (not_ggInnerDiagOnLabel_u4 hC (hfix _ ⟨Or.inr rfl, rfl, rfl⟩)).elim
    · exact Or.inr (Or.inr (hmk _ ⟨rfl, rfl, rfl⟩))
    · exact (hR1 _ (labelAll_torusLiftFour_orth (Or.inr rfl) hl5) rfl).elim
  | E6 => exact (hR1 _ labelAll_torusLiftFour_E6 rfl).elim
  | E7 => exact (hR1 _ labelAll_torusLiftFour_E7 rfl).elim
  | E8 => exact (hR1 _ labelAll_torusLiftFour_E8 rfl).elim
  | F4 => exact (ggL48F4TwoThreeConfigInput_holds G B Bs x L hC.1 hC.2.1 hcard
      (hmk _ ⟨rfl, rfl⟩)).elim
  | twE6 => exact (hR1 _ (labelAll_torusLiftFour_twE6 hlab) rfl).elim
  | triD4 =>
    exact (hR2 _ rfl (TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
      (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) Nat.prime_three hlab rfl
      (hsp _ _)) rfl).elim
  | G2 =>
    have h : l = 0 ∧ 2 ≤ 1 := hlab.2
    omega
  | twB2 =>
    have h : l = 0 ∧ Odd 1 ∧ 3 ≤ 1 := hlab.2
    omega
  | twF4 =>
    have h : l = 0 ∧ Odd 1 ∧ 3 ≤ 1 := hlab.2
    omega
  | B2der => exact (hR2 _ rfl (largeEvenLabelAll_card_lt_b2derThree ⟨rfl, rfl⟩) rfl).elim
  | G2der =>
    exact (hR2 _ rfl (TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der Nat.prime_three hlab rfl
      (hsp _ _)) rfl).elim
  | twF4der =>
    have hl0 : l = 0 := hlab.2.1
    subst hl0
    exact (hTits (hfix _ rfl)).elim

theorem ggQTwoEnds_of_card_bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) :
    GGInnerDiagOnLabel GGLabSp6 3 Bs L ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6) ∧
        LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) ∨
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) := by
  refine ggQTwoEnds_of_card_bstar_of_titsExcl hC hcard hq ?_
  intro hqT
  refine not_ggInnerDiagOnLabel_of_cardLt (S := fun _ lab => lab = ⟨.twF4der, 0, 1⟩)
    ?_ ?_ hC hqT
  · intro lab hlab he
    subst lab
    exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds Nat.prime_three hlab rfl
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · intro lab he
    subst lab
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem ggF4QTwoEndsLInput_of_tbFix
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGF4QTwoEndsLInput :=
  fun _ _ _ _ _ _ _ _ _ hR hW hq _ _ hN hF =>
    ggQTwoEnds_of_card_bstar hR.1 (card_bstar_F4 hTBF hWI hR hW ⟨_, _, hN, hF⟩) hq

end CFSG.StandardType

end
