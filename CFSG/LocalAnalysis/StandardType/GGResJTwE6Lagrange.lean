module

public import CFSG.LocalAnalysis.StandardType.GGResJFusion
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
import CFSG.LocalAnalysis.StandardType.GGTBJLabelJ
import CFSG.LocalAnalysis.StandardType.GGPZWeylType
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Absence
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
import CFSG.HardMathSupport.Lang.E27.TwistedE6Field
import CFSG.LocalAnalysis.StandardType.GGResJOneReflCell

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.ClassicalInvolution.RouteD

theorem padicValNat_ordF4 {p q f : ℕ} [Fact p.Prime] (hq : q = p ^ f) (hf : 0 < f) :
    padicValNat p (ordF4 q) = f * 24 := by
  have hp : p.Prime := Fact.out
  have h : ordF4 q = q ^ 24 * ((q ^ 12 - 1) * ((q ^ 8 - 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)))) / 1 :=
    by simp [ordF4, mul_assoc]
  rw [h]
  refine TWR.padicValNat_ord_form hq ?_ (one_dvd _)
  intro hd
  rcases hp.dvd_mul.mp hd with h1 | h1
  · exact TWR.not_dvd_pow_sub_one hq hf (by norm_num) h1
  rcases hp.dvd_mul.mp h1 with h1 | h1
  · exact TWR.not_dvd_pow_sub_one hq hf (by norm_num) h1
  rcases hp.dvd_mul.mp h1 with h1 | h1
  · exact TWR.not_dvd_pow_sub_one hq hf (by norm_num) h1
  · exact TWR.not_dvd_pow_sub_one hq hf (by norm_num) h1

theorem labOrd_eq_ordTwistedE6 {lab : LargeEvenLabel} (ht : lab.tag = .twE6) :
    SporadicShape.labOrd lab = ordTwistedE6 (2 ^ lab.n) := by
  obtain ⟨t, k, n⟩ := lab
  dsimp only at ht
  subst ht
  rfl

theorem padicValNat_two_labOrd_le_of_row {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt 3 lab r m N C M) (hN : N ≤ 5) :
    padicValNat 2 (SporadicShape.labOrd lab) ≤ 30 * lab.n := by
  have hs : ((lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank ≤ 5) ∨
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank ≤ 6) ∨ lab.tag = .F4 ∨ lab.tag = .G2 := by
    cases hrow with
    | aDep ht => exact Or.inl ⟨by rcases ht with h | h <;> simp [h], hN⟩
    | e6Three => omega
    | e8Three => omega
    | aInd ht => exact Or.inl ⟨by rcases ht with h | h <;> simp [h], hN⟩
    | c ht => exact Or.inl ⟨by rcases ht with h | h <;> simp [h], hN⟩
    | d ht => exact Or.inr (Or.inl ⟨by rcases ht with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h], by omega⟩)
    | e6Ind h3 => exact absurd rfl h3
    | e7 => omega
    | e8Ind h3 => exact absurd rfl h3
    | f4 ht => exact Or.inr (Or.inr (Or.inl ht))
    | g2 ht => exact Or.inr (Or.inr (Or.inr ht))
    | relD ht =>
      exact Or.inr (Or.inl ⟨by rcases ht with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h], by omega⟩)
    | relE6 h3 => exact absurd rfl h3
    | relA5 hr ht => exact Or.inl ⟨by rcases ht with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h], by omega⟩
  obtain ⟨t, k, n⟩ := lab
  obtain ⟨hn, hΛ⟩ := hΛ
  dsimp only at hs hn ⊢
  rcases hs with ⟨ht, hk⟩ | ⟨ht, hk⟩ | rfl | rfl
  · rcases ht with rfl | rfl | rfl | rfl
    · show padicValNat 2 (ordA (k + 1 - 1) (2 ^ n)) ≤ 30 * n
      rw [Nat.add_sub_cancel, TWR.padicValNat_ordA rfl hn hΛ.1]
      have h15 : k * (k + 1) / 2 ≤ 30 := by interval_cases k <;> omega
      calc n * (k * (k + 1) / 2) ≤ n * 30 := Nat.mul_le_mul_left n h15
        _ = 30 * n := Nat.mul_comm n 30
    · show padicValNat 2 (ordTwistedA (k + 1 - 1) (2 ^ n)) ≤ 30 * n
      have hk2 : 2 ≤ k := hΛ.1
      rw [Nat.add_sub_cancel, TWR.padicValNat_ordTwistedA rfl hn (by omega)]
      have h15 : k * (k + 1) / 2 ≤ 30 := by interval_cases k <;> omega
      calc n * (k * (k + 1) / 2) ≤ n * 30 := Nat.mul_le_mul_left n h15
        _ = 30 * n := Nat.mul_comm n 30
    · show padicValNat 2 (ordBC k (2 ^ n)) ≤ 30 * n
      have hk2 : 2 ≤ k := hΛ.1
      rw [TWR.padicValNat_ordBC rfl hn (by omega)]
      have h25 : k * k ≤ 30 := by interval_cases k <;> omega
      calc n * (k * k) ≤ n * 30 := Nat.mul_le_mul_left n h25
        _ = 30 * n := Nat.mul_comm n 30
    · show padicValNat 2 (ordBC k (2 ^ n)) ≤ 30 * n
      have hk2 : 2 ≤ k := hΛ.1
      rw [TWR.padicValNat_ordBC rfl hn (by omega)]
      have h25 : k * k ≤ 30 := by interval_cases k <;> omega
      calc n * (k * k) ≤ n * 30 := Nat.mul_le_mul_left n h25
        _ = 30 * n := Nat.mul_comm n 30
  · rcases ht with rfl | rfl
    · have hk3 : 3 ≤ k := hΛ
      by_cases h3 : k = 3
      · subst h3
        show padicValNat 2 (ordA (4 - 1) (2 ^ n)) ≤ 30 * n
        rw [TWR.padicValNat_ordA rfl hn (by norm_num)]
        omega
      · show padicValNat 2 (EvenSmallLie.CatalogOrders.lieOrd
          (if k = 3 then .PSL else .POmegaPlus) (if k = 3 then 4 else k) (2 ^ n)) ≤ 30 * n
        simp only [h3, if_false]
        show padicValNat 2 (ordD k (2 ^ n)) ≤ 30 * n
        rw [TWR.padicValNat_ordD rfl hn (by omega)]
        have h30 : k * (k - 1) ≤ 30 := by interval_cases k <;> omega
        calc n * (k * (k - 1)) ≤ n * 30 := Nat.mul_le_mul_left n h30
          _ = 30 * n := Nat.mul_comm n 30
    · have hk2 : 2 ≤ k := hΛ
      by_cases h2 : k = 2
      · subst h2
        show padicValNat 2 (ordA (2 - 1) (2 ^ (2 * n))) ≤ 30 * n
        rw [TWR.padicValNat_ordA rfl (by omega) (by norm_num)]
        omega
      by_cases h3 : k = 3
      · subst h3
        show padicValNat 2 (ordTwistedA (4 - 1) (2 ^ n)) ≤ 30 * n
        rw [TWR.padicValNat_ordTwistedA rfl hn (by norm_num)]
        omega
      · show padicValNat 2 (EvenSmallLie.CatalogOrders.lieOrd
          (if k = 2 then .PSL else if k = 3 then .PSU else .POmegaMinus)
          (if k = 2 then 2 else if k = 3 then 4 else k)
          (2 ^ (if k = 2 then 2 * n else n))) ≤ 30 * n
        simp only [h2, h3, if_false]
        show padicValNat 2 (ordTwistedD k (2 ^ n)) ≤ 30 * n
        rw [TWR.padicValNat_ordTwistedD rfl hn (by omega)]
        have h30 : k * (k - 1) ≤ 30 := by interval_cases k <;> omega
        calc n * (k * (k - 1)) ≤ n * 30 := Nat.mul_le_mul_left n h30
          _ = 30 * n := Nat.mul_comm n 30
  · show padicValNat 2 (ordF4 (2 ^ n)) ≤ 30 * n
    rw [padicValNat_ordF4 rfl hn]
    omega
  · show padicValNat 2 (ordG2 (2 ^ n)) ≤ 30 * n
    rw [TWR.padicValNat_ordG2 rfl hn]
    omega

theorem padicValNat_two_labOrd_le_of_iso {lab₀ lab : LargeEvenLabel}
    (h0 : LargeEvenInLambda2 lab₀) (hiso : GGLabelIso lab₀ lab)
    (hb : padicValNat 2 (SporadicShape.labOrd lab₀) ≤ 30 * lab₀.n) :
    padicValNat 2 (SporadicShape.labOrd lab₀) ≤ 30 * lab.n := by
  rcases hiso with rfl | ⟨-, -, -, hn⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
      ⟨-, rfl⟩
  · exact hb
  · rwa [← hn]
  · exact hb
  · exact hb
  · exact hb
  · exact hb
  · dsimp only
    omega
  · have hn : 1 ≤ 2 * lab.n := h0.1
    show padicValNat 2 (ordA (1 + 1 - 1) (2 ^ (2 * lab.n))) ≤ 30 * lab.n
    rw [TWR.padicValNat_ordA rfl hn le_rfl]
    omega

theorem GGResHyp.card_lt_of_twE6PlusThree_of_card_lt
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J)
    (h5 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range < p ^ 5) :
    Nat.card Bs < p ^ 7 := by
  have hp : p.Prime := Fact.out
  have hBs := hH.1.tableB_facts.2.1
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6ThreeLabel p lab)
    (P' := fun R _ _ _ => GGTorusLift p (TwE6Delta.liftRank p) R)
    (fun _ hΛ h => largeEvenLabelAll_torusLift_twE6Add_holds hp hΛ
      ⟨h.1, by rw [h.2.1]; exact h.2.2⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hp3, -⟩, -⟩, hLift⟩ := largeEvenRawDatum_exists hraw
  subst hp3
  rw [show TwE6Delta.liftRank 3 = 4 by simp [TwE6Delta.liftRank]] at hLift
  have hpre : LargeEvenStdSubPre 3 B x L D J := hH.1.2.2.1
  have hJperf : commutator ↥J = ⊤ := hpre.2.2.2.2.2.1.2.2.1
  have hC := CFSG.LocalAnalysis.GLTheoremA.S265.SF.pow_mul_card_le_of_torusLift
    (Ω := G) (K := J) (D := Bs ⊓ Subgroup.centralizer (J : Set G)) Nat.prime_three hJperf θ
    hLift (CFSG.Open.IsElemAbelian.mono hBs inf_le_left) inf_le_right
  have hrank : CFSG.Open.GLATwoLocalRank 3 G = LargeEvenTwoLocalRank 3 G := rfl
  rw [hrank] at hC
  have hm : LargeEvenTwoLocalRank 3 G ≤ 6 := by
    have hlt : 3 ^ (LargeEvenTwoLocalRank 3 G - 2) < 3 ^ 5 := hH.pow_le_card_gamma_J.trans_lt h5
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    omega
  have hC2 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 2 := by
    have h46 : 3 ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 4 * 3 ^ 2 :=
      hC.trans ((Nat.pow_le_pow_right (by norm_num) hm).trans (by norm_num))
    exact Nat.le_of_mul_le_mul_left h46 (by norm_num)
  have hker : (ggGamma J hH.Bs_le_normalizer_J).ker =
      (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcount := TableB.card_range_mul_card_ker (ggGamma J hH.Bs_le_normalizer_J)
  rw [hker, hkerCard] at hcount
  rw [← hcount]
  calc Nat.card (ggGamma J hH.Bs_le_normalizer_J).range *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G))
      ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range * 3 ^ 2 := Nat.mul_le_mul_left _ hC2
    _ < 3 ^ 5 * 3 ^ 2 := Nat.mul_lt_mul_of_pos_right h5 (by norm_num)
    _ = 3 ^ 7 := by norm_num

theorem GGResHyp.weylType_automizer_of_exact3_nonsingular_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 7) :
    ∃ r c : ℕ, r ≤ 5 ∧ GGWeylTypeData r (Nat.card ↥(ggAutomizer L Bs)) c := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, -, -, -, hWML,
    hCLL, -, -, -, hlin, -, hpairL, -, -, ⟨fL, -⟩, -, hclosL, -, -, -⟩ := id hD
  let := i1
  let := i2
  let := i5
  let := i6
  have hle := ggIntCartan_card_le_rank_add_one hWML hCLL p hp2
  have hrk := Matrix.rank_le_card_width (CL.map (Int.castRingHom (ZMod p)))
  have hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
    by_contra hne
    exact hL (ggSingularWeylOrder_of_type fL
      (ggRC_singular_typeA_or_E6_of_rank hp hp2 hWML hCLL (by omega)))
  have haxis := ggResL_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hV : Module.finrank (ZMod p) V < 7 := by
    have hc : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V]
    rw [hc] at hBs
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hBs
  refine ⟨Fintype.card Λ, Nat.card ↥(Subgroup.center ML.Group), by omega, ?_⟩
  rw [← Nat.card_congr fL.toEquiv]
  exact ggWeylTypeData_of_isWeylMatrix hWML

theorem GGResHyp.weylType_automizer_of_exact3_nonsingular_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 7) :
    ∃ r c : ℕ, r ≤ 5 ∧ GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs)) c := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, -, -, -, hWML,
    hCLL, -, -, -, hlin, -, hpairL, -, -, ⟨fL, -⟩, -, hclosL, -, -, -⟩ := id hD
  let := i1
  let := i2
  let := i5
  let := i6
  have hle := ggIntCartan_card_le_rank_add_one hWML hCLL p hp2
  have hrk := Matrix.rank_le_card_width (CL.map (Int.castRingHom (ZMod p)))
  have hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
    by_contra hne
    exact hK (ggSingularWeylOrder_of_type fL
      (ggRC_singular_typeA_or_E6_of_rank hp hp2 hWML hCLL (by omega)))
  have haxis := ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hV : Module.finrank (ZMod p) V < 7 := by
    have hc : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V]
    rw [hc] at hBs
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hBs
  refine ⟨Fintype.card Λ, Nat.card ↥(Subgroup.center ML.Group), by omega, ?_⟩
  rw [← Nat.card_congr fL.toEquiv]
  exact ggWeylTypeData_of_isWeylMatrix hWML

@[expose] def GGTwE6ThreeFreeLabel (lab₀ : LargeEvenLabel) : Prop :=
  SporadicShape.labOrd lab₀ ≠ 0 → ∀ lab : LargeEvenLabel, GGLabelIso lab₀ lab →
    ∀ μ : LargeEvenLabel, LargeEvenInLambda2 μ → μ.tag = .twE6 → 3 ∣ 2 ^ μ.n + 1 →
      lab.n ∣ μ.n → ¬ SporadicShape.labOrd μ ∣ SporadicShape.labOrd lab₀

theorem ggTwE6ThreeFreeLabel_of_two_adic {lab₀ : LargeEvenLabel}
    (h0 : LargeEvenInLambda2 lab₀)
    (hb : padicValNat 2 (SporadicShape.labOrd lab₀) ≤ 30 * lab₀.n) :
    GGTwE6ThreeFreeLabel lab₀ := by
  intro hne lab hiso μ hμ ht _ hdvd hdiv
  have hb' := padicValNat_two_labOrd_le_of_iso h0 hiso hb
  rw [labOrd_eq_ordTwistedE6 ht] at hdiv
  have h36 : 2 ^ (μ.n * 36) ∣ SporadicShape.labOrd lab₀ := by
    rw [pow_mul]
    exact (EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedE6 _).trans hdiv
  have hv := (padicValNat_dvd_iff_le hne).mp h36
  have hle : lab.n ≤ μ.n := Nat.le_of_dvd hμ.1 hdvd
  have hn1 : 1 ≤ μ.n := hμ.1
  omega

theorem ggTwE6ThreeFreeLabel_of_twA_even {lab₀ : LargeEvenLabel} (ht : lab₀.tag = .twA)
    (hn : 2 ∣ lab₀.n) : GGTwE6ThreeFreeLabel lab₀ := by
  intro _ lab hiso μ _ _ h3 hdvd _
  have hlab : lab.n = lab₀.n := by
    rcases hiso with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · rw [h]
    · rw [ht] at h
      rcases h with h | h <;> cases h
    · rw [h] at ht
      cases ht
    · rw [h] at ht
      cases ht
    · rw [h]
    · rw [h]
    · rw [h] at ht
      cases ht
    · rw [h] at ht
      cases ht
  have hn' : 2 ∣ lab.n := by
    rw [hlab]
    exact hn
  obtain ⟨m, hm⟩ := hn'.trans hdvd
  have h4 : 3 ∣ 2 ^ μ.n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 m
    rw [one_pow] at h
    have e : (2 : ℕ) ^ μ.n = 4 ^ m := by
      rw [hm, pow_mul]
      norm_num
    rw [e]
    exact h
  have h1 : 1 ≤ 2 ^ μ.n := Nat.one_le_two_pow
  omega

@[expose] def GGResNonsingAut {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer X Bs)) ∧
    (p = 3 → ∀ r c : ℕ, r ≤ 5 → GGWeylTypeData r (Nat.card ↥(ggAutomizer X Bs)) c →
      ∃ lab₀ : LargeEvenLabel, LargeEvenInLambda2 lab₀ ∧
        GGHasLabel lab₀ (↥X ⧸ Subgroup.center ↥X) ∧ GGTwE6ThreeFreeLabel lab₀)

theorem GGResHyp.nonsingAut_of_cov_L
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L) :
    GGResNonsingAut p Bs L := by
  refine ⟨hH.false_of_singular_card_nonsingular_L hT hLift hL, ?_⟩
  rintro rfl r c hr hA
  have hcov : GGInnerDiagOnLabel GGTBTorCov 3 Bs L := hL.mono_label fun _ h => h.1
  have hL' : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        (GGIsWeylMatrix M ∧ (N ≤ 5 → ∃ lab₀ : LargeEvenLabel, LargeEvenInLambda2 lab₀ ∧
          GGHasLabel lab₀ (↥L ⧸ Subgroup.center ↥L) ∧
            padicValNat 2 (SporadicShape.labOrd lab₀) ≤ 30 * lab₀.n))) 3 Bs L :=
    hcov.mono_label_of_hasLabel fun lab₀ hΛ hhas ⟨r, m, N, C, M, hrow⟩ =>
      ⟨r, m, N, C, M, hrow, (l05nPlP1_row_facts Nat.prime_three (by norm_num) hΛ hrow).2.2.1,
        fun hN => ⟨lab₀, hΛ, hhas, padicValNat_two_labOrd_le_of_row hΛ hrow hN⟩⟩
  obtain ⟨-, -, N, -, M, ⟨hWM, hbd⟩, hcard⟩ := hH.exists_row_card_automizer_L hT hLift hL'
  have hWr : GGWeylTypeData N (Nat.card M.Group) (Nat.card ↥(Subgroup.center M.Group)) := by
    simpa using ggWeylTypeData_of_isWeylMatrix hWM
  have hA' : GGWeylTypeData r (Nat.card M.Group) c := hcard ▸ hA
  obtain ⟨lab₀, hΛ, hhas, hb⟩ := hbd ((ggWeylTypeData_rank_eq hWr hA').trans_le hr)
  exact ⟨lab₀, hΛ, hhas, ggTwE6ThreeFreeLabel_of_two_adic hΛ hb⟩

theorem GGResHyp.nonsingAut_of_cov_K
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs K) :
    GGResNonsingAut p Bs K := by
  refine ⟨hH.false_of_singular_card_nonsingular_K hT hLift hK, ?_⟩
  rintro rfl r c hr hA
  have hcov : GGInnerDiagOnLabel GGTBTorCov 3 Bs K := hK.mono_label fun _ h => h.1
  have hK' : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        (GGIsWeylMatrix M ∧ (N ≤ 5 → ∃ lab₀ : LargeEvenLabel, LargeEvenInLambda2 lab₀ ∧
          GGHasLabel lab₀ (↥K ⧸ Subgroup.center ↥K) ∧
            padicValNat 2 (SporadicShape.labOrd lab₀) ≤ 30 * lab₀.n))) 3 Bs K :=
    hcov.mono_label_of_hasLabel fun lab₀ hΛ hhas ⟨r, m, N, C, M, hrow⟩ =>
      ⟨r, m, N, C, M, hrow, (l05nPlP1_row_facts Nat.prime_three (by norm_num) hΛ hrow).2.2.1,
        fun hN => ⟨lab₀, hΛ, hhas, padicValNat_two_labOrd_le_of_row hΛ hrow hN⟩⟩
  obtain ⟨-, -, N, -, M, ⟨hWM, hbd⟩, hcard⟩ := hH.exists_row_card_automizer_K hT hLift hK'
  have hWr : GGWeylTypeData N (Nat.card M.Group) (Nat.card ↥(Subgroup.center M.Group)) := by
    simpa using ggWeylTypeData_of_isWeylMatrix hWM
  have hA' : GGWeylTypeData r (Nat.card M.Group) c := hcard ▸ hA
  obtain ⟨lab₀, hΛ, hhas, hb⟩ := hbd ((ggWeylTypeData_rank_eq hWr hA').trans_le hr)
  exact ⟨lab₀, hΛ, hhas, ggTwE6ThreeFreeLabel_of_two_adic hΛ hb⟩

section Lagrange


theorem ggTwE6_false_of_labels (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {X J : Subgroup G} (hJX : J ≤ X) {lab₀ lab labJ labJ' : LargeEvenLabel}
    (h0 : LargeEvenInLambda2 lab₀) (hhas0 : GGHasLabel lab₀ (↥X ⧸ Subgroup.center ↥X))
    (hb : GGTwE6ThreeFreeLabel lab₀)
    (hl : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (hlJ : LargeEvenInLambda2 labJ) (hdvd : lab.n ∣ labJ.n)
    (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (hlJ' : LargeEvenInLambda2 labJ')
    (ht : labJ'.tag = .twE6) (h3 : 3 ∣ 2 ^ labJ'.n + 1)
    (hhasJ' : GGHasLabel labJ' (↥J ⧸ Subgroup.center ↥J)) : False := by
  have hJ : labJ = labJ' := ggLabelIso_eq_of_exceptional (by rw [ht]; decide)
    (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
    (by rw [ht]; decide) (hRig labJ' labJ _ hlJ' hlJ hhasJ' hhasJ)
  subst hJ
  have hne : SporadicShape.labOrd lab₀ ≠ 0 := by
    rw [ggKSL_labOrd_eq h0 hhas0]
    exact Nat.card_pos.ne'
  exact hb hne lab (hRig lab₀ lab _ h0 hl hhas0 hhas) labJ hlJ ht h3 hdvd
    (ggKSL_labOrd_dvd hJX h0 hhas0 hlJ hhasJ)

theorem GGResHyp.false_of_twE6PlusThree_of_weylType_L (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J)
    (hL : GGResNonsingAut p Bs L) {r c : ℕ} (hr : r ≤ 5)
    (hA : GGWeylTypeData r (Nat.card ↥(ggAutomizer L Bs)) c) : False := by
  obtain ⟨labJ', hΛJ', hhasJ', R, _, I, F, θ, ⟨htJ, hp3, h3J⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hJ
  obtain ⟨lab₀, hΛ₀, hhas₀, hb⟩ := hL.2 hp3 r c hr hA
  subst hp3
  have hLm : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hH.2.2.1.1
  obtain ⟨lab, labJ, hΛ, -, hhas, hΛJ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hH.1 hLm hH.2.2.2.2.1
  exact ggTwE6_false_of_labels hRig ((hH.1.2.2.1.2.2.2.2.2.1).1.trans inf_le_left) hΛ₀ hhas₀ hb
    hΛ hhas hΛJ hdvd hhasJ hΛJ' htJ h3J hhasJ'

theorem GGResHyp.false_of_twE6PlusThree_of_weylType_K (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J)
    (hK : GGResNonsingAut p Bs K) {r c : ℕ} (hr : r ≤ 5)
    (hA : GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs)) c) : False := by
  obtain ⟨labJ', hΛJ', hhasJ', R, _, I, F, θ, ⟨htJ, hp3, h3J⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hJ
  obtain ⟨lab₀, hΛ₀, hhas₀, hb⟩ := hK.2 hp3 r c hr hA
  subst hp3
  have hpJ : 3 ∣ Nat.card J := by
    have h27 := CFSG.HardMathSupport.Lang.E27.twentySeven_dvd_ordTwistedE6 (2 ^ labJ'.n)
      Nat.one_le_two_pow
    rw [← labOrd_eq_ordTwistedE6 htJ, ggKSL_labOrd_eq hΛJ' hhasJ'] at h27
    exact ((by norm_num : 3 ∣ 27).trans h27).trans (Subgroup.card_quotient_dvd_card _)
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hH.2.2.2.2.1
  have hKm : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) (hH.2.2.1.2 y K hH.2.2.2.2.1)
  obtain ⟨lab, labJ, hΛ, -, hhas, hΛJ, hdvd, hhasJ⟩ :=
    ggNbrK_label_J_of_tcj_onLabel_of_le hTCJ hH.1 hH.2.2.2.2.1 hJK hKm
  exact ggTwE6_false_of_labels hRig hJK hΛ₀ hhas₀ hb hΛ hhas hΛJ hdvd hhasJ hΛJ' htJ h3J
    hhasJ'

end Lagrange

section Exclusion


theorem ggResExact3_false_of_nonsingular_L_of_twE6PlusThree (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J)
    (hL : GGResNonsingAut p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False := by
  by_cases h5 : p ^ 5 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · exact ggResExact3_false_of_card_L hH
      (hH.fix_mem_centralizer_J_of_twE6PlusThree_of_card hJ h5) hL.1 hD
  · rw [not_le] at h5
    obtain ⟨r, c, hr, hA⟩ := hH.weylType_automizer_of_exact3_nonsingular_L hL.1 hD
      (hH.card_lt_of_twE6PlusThree_of_card_lt hJ h5)
    exact hH.false_of_twE6PlusThree_of_weylType_L hTCJ hRig hJ hL hr hA

theorem ggResExact3_false_of_nonsingular_K_of_twE6PlusThree (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs J)
    (hK : GGResNonsingAut p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  by_cases h5 : p ^ 5 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · exact ggResExact3_false_of_card_K hH
      (hH.fix_mem_centralizer_J_of_twE6PlusThree_of_card hJ h5) hK.1 hD
  · rw [not_le] at h5
    obtain ⟨r, c, hr, hA⟩ := hH.weylType_automizer_of_exact3_nonsingular_K hK.1 hD
      (hH.card_lt_of_twE6PlusThree_of_card_lt hJ h5)
    exact hH.false_of_twE6PlusThree_of_weylType_K hTCJ hRig hLB hJ hK hr hA

end Exclusion

section Rest


theorem ggResExact3_false_of_nonsingular_L_of_tcj (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hL : GGResNonsingAut p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False := by
  have h := ggResExact3_twE6_of_nonsingular_L_of_tcj hT hLift hTCJ hRig hH h3 hJ hL.1 hD
  exact ggResExact3_false_of_nonsingular_L_of_twE6PlusThree hTCJ hRig hH
    (h.mono_label fun _ h => h.2) hL hD

theorem ggResExact3_false_of_nonsingular_K_of_tcj (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hK : GGResNonsingAut p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  have h := ggResExact3_twE6_of_nonsingular_K_of_tcj hT hLift hTCJ hRig hH h3 hJ hK.1 hD
  exact ggResExact3_false_of_nonsingular_K_of_twE6PlusThree hTCJ hRig hLB hH
    (h.mono_label fun _ h => h.2) hK hD

theorem ggResExact3_false_of_nonsingAut_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hP : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J) (hL : GGResNonsingAut p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False := by
  by_cases h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · exact ggResExact3_false_of_nonsingular_L_of_tcj hT hLift hTCJ hRig hH h3 hJ hL hD
  push Not at h3
  obtain ⟨h5, τ, hτ, hA⟩ := hH.automizer_J_refl_of_exact3_nonsingular_L hP hL.1 hD
    (hH.card_lt_of_card_gamma_J_lt h3)
  exact hH.false_of_oneRefl hLift ggResJOneReflInput_holds h5
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hJ) hτ hA (hH.card_gamma_J_eq_sq_of_lt h3)

theorem ggResExact3_false_of_nonsingAut_K (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J) (hK : GGResNonsingAut p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  by_cases h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · exact ggResExact3_false_of_nonsingular_K_of_tcj hT hLift hTCJ hRig hLB hH h3 hJ hK hD
  push Not at h3
  obtain ⟨h5, τ, hτ, hA⟩ := hH.automizer_J_refl_of_exact3_nonsingular_K hP hK.1 hD
    (hH.card_lt_of_card_gamma_J_lt h3)
  exact hH.false_of_oneRefl hLift ggResJOneReflInput_holds h5
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hJ) hτ hA (hH.card_gamma_J_eq_sq_of_lt h3)

theorem ggResExact3_false_of_nonsingular_L_of_oneRefl (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_L hT hLift hTCJ hRig hP hH hJ
    (hH.nonsingAut_of_cov_L hT hLift hL) hD

theorem ggResExact3_false_of_nonsingular_K_of_oneRefl (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hK : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs K)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False :=
  ggResExact3_false_of_nonsingAut_K hT hLift hTCJ hRig hLB hP hH hJ
    (hH.nonsingAut_of_cov_K hT hLift hK) hD

end Rest

section Singular


theorem ggResMultiNodeRestThreeOutsideRowsInput_of_singular (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hQ1 : GGBstarInnerDiagJInput)
    (h : GGResMultiNodeRestThreeSingularInput) : GGResMultiNodeRestThreeOutsideRowsInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hD, hrest⟩
  have hJ : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩)
      (hQ1 G p B Bs x L D J hH.1 hH.2.2.1.1)
  refine h G p B Bs x L D J y K hH hF hS hE ⟨?_, hrest⟩
  rcases hD with hD | hD
  · exact Or.inl ⟨hD, fun hL =>
      ggResExact3_false_of_nonsingular_L_of_oneRefl hT hLift hTCJ hRig hP hH hJ hL hD⟩
  · exact Or.inr ⟨hD, fun hK =>
      ggResExact3_false_of_nonsingular_K_of_oneRefl hT hLift hTCJ hRig hLB hP hH hJ hK hD⟩

end Singular

end CFSG.StandardType

end
