module

public import CFSG.Quasithin.Vol2.Ch3B513NCases
public import CFSG.Quasithin.Vol2.Ch3B513NAltS
public import CFSG.Quasithin.Vol2.Ch3B513NC1SL2
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.Quasithin.Background.B5Irr
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.Quasithin.Vol2.Ch3B513NC1Nat

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def C1Sp4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G → G = quasithinGenFitting G →
      commV G ∈ IrrPlus G ⊤ → ∀ n, BinaryNaturalSp4 G (commV G) (fixV G ⊓ commV G) n →
        HasGood G

@[expose] def C1G2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), ¬ Group.IsSolvable ↥G → G ≠ ⊥ → B53Hyp G → B56Case1 G →
      G = quasithinGenFitting G → commV G ∈ IrrPlus G ⊤ →
        ∀ n, G2Natural G (commV G) (fixV G ⊓ commV G) n → HasGood G

@[expose] def C1G2Der : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G → G = quasithinGenFitting G →
      commV G ∈ IrrPlus G ⊤ → G2NaturalDerived G (commV G) (fixV G ⊓ commV G) 1 → HasGood G

@[expose] def C1Wedge5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G → G = quasithinGenFitting G →
      commV G ∈ IrrPlus G ⊤ → fixV G ⊓ commV G = ⊥ →
        SLExteriorTwo G (commV G) (fixV G ⊓ commV G) 5 → HasGood G

@[expose] def C1G2Two : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G →
      commV (quasithinGenFitting G) ∈ IrrPlus (quasithinGenFitting G) ⊤ →
      ∀ T : Subgroup (MulAut W), IsSylowTwoOf T G → G = quasithinGenFitting G ⊔ T →
        G2Natural G (commV (quasithinGenFitting G))
          (fixV (quasithinGenFitting G) ⊓ commV (quasithinGenFitting G)) 1 → HasGood G

@[expose] def C1ii : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G →
      B51Case1ii G (quasithinGenFitting G) → HasGood G

@[expose] def C1iii : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G →
      ∀ k, B51Case1iii G (quasithinGenFitting G) k → HasGood G

@[expose] def C1iv : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), G ≠ ⊥ → B53Hyp G → B56Case1 G →
      B51Case1iv G (quasithinGenFitting G) → HasGood G

variable {W : Type} [CommGroup W] [Finite W]

theorem isSolvable_statedSL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [card_statedSL_two1527d, hK]
  have h23 : Nat.primeFactors (2 * (2 ^ 2 - 1)) = {2, 3} := by
    rw [show (2 * (2 ^ 2 - 1) : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num)
      (by norm_num), Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [h23]
  decide

theorem hasGood_of_case1i_eq (hW : ∀ w : W, w ^ 2 = 1) (hI16 : H13.AsI16Cover328)
    (hA8 : AsI16CoverA8) (hSp4 : C1Sp4) (hG2 : C1G2) (hG2D : C1G2Der) (hW5 : C1Wedge5)
    {G : Subgroup (MulAut W)} (hsolv : ¬ Group.IsSolvable ↥G) (hne : G ≠ ⊥) (hB53 : B53Hyp G)
    (h1 : B56Case1 G) (hGL : G = quasithinGenFitting G) (hU : commV G ∈ IrrPlus G ⊤)
    (hpair : B42ModulePair G (commV G) (fixV G ⊓ commV G)) : HasGood G := by
  have hJ : G = ffJ G := hB53.2.1
  have hI := hI16 W hW G hU
  have hsmall : ∀ {M : FFModel}, M.Faithful → ∀ {π : M.Gam →* ↥G},
      M.RealizesVia G (commV G) (fixV G ⊓ commV G) π → Nat.card (commV G) ≤ 2 ^ 7 →
        HasGood G := fun hM _ hr hc => hasGood_of_realizes_small hW hne hJ le_rfl hM hr hc
  rcases hpair with ⟨n, hSL2⟩ | ⟨n, hSL3⟩ | ⟨n, hSp⟩ | ⟨n, hG⟩ | hGD | hA5 | hA6 | hA7 | ha7 |
    h3a6 | hL4 | hL5 | hE4 | hE5
  ·
    obtain ⟨K, _, _, hK, π, hr⟩ := hSL2
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso
      have hK2 : Nat.card K = 2 := by
        interval_cases n
        · have : 1 < Nat.card K := Finite.one_lt_card
          omega
        · simpa using hK
      have : Group.IsSolvable (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K)).Gam :=
        isSolvable_statedSL_two hK2
      exact hsolv (Group.isSolvable_of_surjective (f := π) hr.1)
    · have hC := card_fixV_le_of_sl2 hW G (commV G) (fun x hx v hv => hU.2.1 ⟨x, hx⟩ v hv)
        hU.2.2.1 hn hK ⟨π, hr⟩
      refine hasGood_of_nat_cent hW hne hJ le_rfl hr (by norm_num) ?_
      rw [hK]
      calc Nat.card ↥(fixV G ⊓ commV G) * (2 ^ n) ^ (2 - 1) ≤ 2 ^ n * (2 ^ n) ^ (2 - 1) :=
            Nat.mul_le_mul_right _ hC
        _ = (2 ^ n) ^ 2 := by ring
  ·
    obtain ⟨K, _, _, hK, π, hr⟩ := id hSL3
    rcases Nat.lt_or_ge n 2 with hn | hn
    ·
      have hn1 : n = 1 := by
        interval_cases n
        · have : 1 < Nat.card K := Finite.one_lt_card
          simp at hK
          omega
        · rfl
      subst hn1
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hC2 : Nat.card ↥(fixV G ⊓ commV G) ≤ 2 := hI.2 hSL3
      refine hsmall (FFModel.nat_faithful _) hr ?_
      rw [card_commV_of_nat hr, hK2]
      calc Nat.card ↥(fixV G ⊓ commV G) * 2 ^ 3 ≤ 2 * 2 ^ 3 := Nat.mul_le_mul_right _ hC2
        _ ≤ 2 ^ 7 := by norm_num
    · have hC : fixV G ⊓ commV G = ⊥ := hI.1 (Or.inr (Or.inr (Or.inl ⟨n, by omega, hSL3⟩)))
      refine hasGood_of_nat_cent hW hne hJ le_rfl hr (by norm_num) ?_
      rw [hC, Subgroup.card_bot, one_mul]
  · exact hSp4 W hW G hne hB53 h1 hGL hU n hSp
  · exact hG2 W hW G hsolv hne hB53 h1 hGL hU n hG
  · exact hG2D W hW G hne hB53 h1 hGL hU hGD
  · exact hasGood_of_altNatural hW le_rfl hU (Or.inl rfl) hA5
  · exact hasGood_of_altNatural hW le_rfl hU (Or.inr (Or.inl rfl)) hA6
  · exact hasGood_of_altNatural hW le_rfl hU (Or.inr (Or.inr (Or.inl rfl))) hA7
  ·
    have hC : fixV G ⊓ commV G = ⊥ :=
      hI.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha7)))))))
    obtain ⟨α, π, hr⟩ := ha7
    refine hsmall (FFC.a7Four_faithful α) hr ?_
    rw [card_commV_of_a7Four hr, hC, Subgroup.card_bot]
    norm_num
  ·
    have hC : fixV G ⊓ commV G = ⊥ :=
      hI.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3a6)))))))
    obtain ⟨K, _, _, Γ₀, hK, -, -, -, π, hr⟩ := h3a6
    refine hsmall (FFModel.nat_faithful _) hr ?_
    rw [card_commV_of_nat hr, hC, Subgroup.card_bot, hK]
    norm_num
  ·
    have hC : fixV G ⊓ commV G = ⊥ := hI.1 (Or.inr (Or.inr (Or.inr (Or.inl hL4))))
    obtain ⟨K, _, _, hK, π, hr⟩ := hL4
    refine hsmall (FFModel.nat_faithful _) hr ?_
    rw [card_commV_of_nat hr, hC, Subgroup.card_bot, hK]
    norm_num
  ·
    have hC : fixV G ⊓ commV G = ⊥ := hI.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL5)))))
    obtain ⟨K, _, _, hK, π, hr⟩ := hL5
    refine hsmall (FFModel.nat_faithful _) hr ?_
    rw [card_commV_of_nat hr, hC, Subgroup.card_bot, hK]
    norm_num
  ·
    have hC2 : Nat.card ↥(fixV G ⊓ commV G) ≤ 2 := hA8 W hW G hU hE4
    obtain ⟨π, hr⟩ := hE4
    refine hsmall (G64.extSq_faithful (by norm_num)) hr ?_
    rw [card_commV_of_wedge4 hr]
    calc Nat.card ↥(fixV G ⊓ commV G) * 2 ^ 6 ≤ 2 * 2 ^ 6 := Nat.mul_le_mul_right _ hC2
      _ = 2 ^ 7 := by norm_num
  ·
    have hC : fixV G ⊓ commV G = ⊥ :=
      hI.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE5))))))
    exact hW5 W hW G hne hB53 h1 hGL hU hC hE5

theorem case1_of (hA21 : AsA21SQTKSection) (hI16 : H13.AsI16Cover328) (hA8 : AsI16CoverA8)
    (hSp4 : C1Sp4) (hG2 : C1G2) (hG2D : C1G2Der) (hW5 : C1Wedge5) (hG2T : C1G2Two)
    (hii : C1ii) (hiii : C1iii) (hiv : C1iv) : Case1 := by
  intro W _ _ hW G hsolv hne hB53 h1
  have hB51 := b51Hyp_of_case1 hA21 hB53 h1
  obtain ⟨⟨-, hcases⟩, -⟩ := h1.2.1
  rcases hcases with ⟨hU, hpair, hGT⟩ | hii' | ⟨k, hiii'⟩ | hiv'
  · obtain ⟨T, hT⟩ := B5.exists_isSylowTwoOf G
    rcases hGT T hT with hGL | ⟨hGT', ⟨n, hn5, hn8, hS⟩ | hG2'⟩
    ·
      have hGL' : G = quasithinGenFitting G := hGL
      rw [← hGL'] at hU hpair
      exact hasGood_of_case1i_eq hW hI16 hA8 hSp4 hG2 hG2D hW5 hsolv hne hB53 h1 hGL' hU hpair
    · exact hasGood_of_symNatural hW hB51 hU hT hGT' hn5 hn8 hS
    · exact hG2T W hW G hne hB53 h1 hU T hT hGT' hG2'
  · exact hii W hW G hne hB53 h1 hii'
  · exact hiii W hW G hne hB53 h1 k hiii'
  · exact hiv W hW G hne hB53 h1 hiv'

end CFSG.Quasithin.B513N
