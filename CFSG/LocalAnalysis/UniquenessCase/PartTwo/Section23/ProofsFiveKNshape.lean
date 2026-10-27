module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
public import CFSG.GroupTheory.ComponentDirectProduct
public import CFSG.GroupTheory.ProdFactors
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Eight
public import CFSG.Timmesfeld.Orders.ClassicalLinearThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

private theorem isComponent_eq_top_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    {K : Subgroup X} (hK : CFSG.IsComponent K) : K = ⊤ := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
    (inferInstance : IsSimpleGroup X) hK.2 with h | h
  · exfalso
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
    haveI : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
      rw [h]
      infer_instance
    exact false_of_nontrivial_of_subsingleton (↥K ⧸ Subgroup.center ↥K)
  · exact h

private theorem not_isSimpleGroup_of_isL2Square {X : Type} [Group X] {j : ℕ}
    (h : IsL2Square X j) : ¬ IsSimpleGroup X := by
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := h
  letI : Group A := gA
  letI : Group B := gB
  haveI hAs : IsSimpleGroup A :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hA
  haveI hBs : IsSimpleGroup B :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hB
  haveI : Nontrivial A := hAs.toNontrivial
  haveI : Nontrivial B := hBs.toNontrivial
  intro hX
  exact CFSG.LocalAnalysis.EvenBN.U5.not_isSimpleGroup_prod (G₁ := A) (G₂ := B)
    ((MulEquiv.isSimpleGroup_congr e).mp hX)

theorem not_isQuasisimple_of_isL2Square {X : Type} [Group X] {j : ℕ}
    (h : IsL2Square X j) : ¬ CFSG.Open.IsQuasisimple X := by
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := h
  letI : Group A := gA
  letI : Group B := gB
  haveI hAs : IsSimpleGroup A :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hA
  haveI hBs : IsSimpleGroup B :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hB
  haveI : Nontrivial A := hAs.toNontrivial
  haveI : Nontrivial B := hBs.toNontrivial
  have hAnc : ¬ IsMulCommutative A := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hA
    exact fun hc => hab (hc.is_comm.comm a b)
  have hBnc : ¬ IsMulCommutative B := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hB
    exact fun hc => hab (hc.is_comm.comm a b)
  have hZA : Subgroup.center A = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hAnc
  have hZB : Subgroup.center B = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hBnc
  have hZAB : Subgroup.center (A × B) = ⊥ := by
    rw [Subgroup.center_prod, hZA, hZB, Subgroup.bot_prod_bot]
  intro hq
  have hZmap : (Subgroup.center X).map e.toMonoidHom = Subgroup.center (A × B) :=
    Subgroup.map_center_eq e
  let eQ : (X ⧸ Subgroup.center X) ≃* ((A × B) ⧸ Subgroup.center (A × B)) :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center (A × B)) e hZmap
  let eBot : ((A × B) ⧸ Subgroup.center (A × B)) ≃* A × B :=
    (QuotientGroup.quotientMulEquivOfEq hZAB).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  exact CFSG.LocalAnalysis.EvenBN.U5.not_isSimpleGroup_prod (G₁ := A) (G₂ := B)
    ((eQ.trans eBot).symm.isSimpleGroup)

private theorem not_isL2_of_isSz {X : Type} [Group X] {k j : ℕ}
    (hSz : IsSz X k) (hL2 : IsL2 X j) : False :=
  CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
    (S17.three_dvd_card_of_isL2Even hL2)

private theorem card_mul_gcd_of_isL3 {X : Type} [Group X] {k : ℕ} (h3 : IsL3 X k) :
    Nat.card X * Nat.gcd 3 (2 ^ k - 1) =
      2 ^ (3 * k) * ((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e3⟩⟩ := h3.statedClassicalModel (by decide)
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h := CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd (K := K)
  rw [← Nat.card_congr e3.toEquiv, hKcard] at h
  have hp3 : (2 ^ k) ^ 3 = 2 ^ (3 * k) := by rw [← pow_mul]; congr 1; ring
  have hp2 : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul]; congr 1; ring
  rwa [hp3, hp2] at h

private theorem card_eq_two_pow_mul_odd_of_isL3 {X : Type} [Group X] {k : ℕ}
    (h3 : IsL3 X k) :
    Nat.card X = 2 ^ (3 * k) *
        (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) / Nat.gcd 3 (2 ^ k - 1)) ∧
      Odd (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) / Nat.gcd 3 (2 ^ k - 1)) := by
  have hcard := card_mul_gcd_of_isL3 h3
  have hdiv : Nat.gcd 3 (2 ^ k - 1) ∣ (2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1) := by
    refine dvd_mul_of_dvd_left ?_ _
    calc Nat.gcd 3 (2 ^ k - 1) ∣ 2 ^ k - 1 := Nat.gcd_dvd_right 3 _
      _ ∣ (2 ^ k) ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one (2 ^ k) 2
      _ = 2 ^ (2 * k) - 1 := by rw [← pow_mul]; congr 1; ring
  have hgpos : 0 < Nat.gcd 3 (2 ^ k - 1) := by
    have h1 : Nat.gcd 3 (2 ^ k - 1) ∣ 3 := Nat.gcd_dvd_left 3 _
    exact Nat.pos_of_dvd_of_pos h1 (by norm_num)
  have hcard' : Nat.card X = 2 ^ (3 * k) *
      (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) / Nat.gcd 3 (2 ^ k - 1)) := by
    calc Nat.card X = Nat.card X * Nat.gcd 3 (2 ^ k - 1) / Nat.gcd 3 (2 ^ k - 1) := by
          rw [Nat.mul_div_cancel _ hgpos]
      _ = 2 ^ (3 * k) * ((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) /
            Nat.gcd 3 (2 ^ k - 1) := by rw [hcard]
      _ = 2 ^ (3 * k) * (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) /
            Nat.gcd 3 (2 ^ k - 1)) := by rw [Nat.mul_div_assoc _ hdiv]
  have hk : 1 ≤ k := h3.admissible.2.1
  have hoddA : Odd ((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).mul
      (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
  have hoddg : Odd (Nat.gcd 3 (2 ^ k - 1)) :=
    Odd.of_dvd_nat (by norm_num) (Nat.gcd_dvd_left 3 _)
  have hoddAg : Odd (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) /
      Nat.gcd 3 (2 ^ k - 1)) := by
    have h : (2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1) =
        Nat.gcd 3 (2 ^ k - 1) * (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) /
          Nat.gcd 3 (2 ^ k - 1)) := (Nat.mul_div_cancel' hdiv).symm
    rw [h] at hoddA
    exact Nat.Odd.of_mul_right hoddA
  exact ⟨hcard', hoddAg⟩

private theorem isL3_isL2_twoPart_eq {X : Type} [Group X] [Finite X] {k j : ℕ}
    (h3 : IsL3 X k) (h2 : IsL2 X j) :
    3 * k = j ∧
      (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) / Nat.gcd 3 (2 ^ k - 1)) =
        2 ^ (2 * j) - 1 := by
  obtain ⟨hcardR, hoddR⟩ := card_eq_two_pow_mul_odd_of_isL3 h3
  have hcard2 : Nat.card X = 2 ^ j * (2 ^ (2 * j) - 1) := S17.card_of_isL2 h2
  have hj : 1 ≤ j := h2.admissible.2.1
  have hodd2 : Odd (2 ^ (2 * j) - 1) :=
    CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hjk : 3 * k = j :=
    CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hoddR hodd2 (hcardR.symm.trans hcard2)
  refine ⟨hjk, ?_⟩
  have h := hcardR.symm.trans hcard2
  rw [← hjk] at h
  rw [← hjk]
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

private theorem l3_odd_lt_l2_square {k j : ℕ} (hk : 1 ≤ k) (hjk : 3 * k = j) :
    (((2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1)) / Nat.gcd 3 (2 ^ k - 1)) <
      2 ^ (2 * j) - 1 := by
  have hpow : 2 ^ (2 * j) = (2 ^ (3 * k)) ^ 2 := by
    rw [← hjk]
    have h : 2 * (3 * k) = (3 * k) * 2 := by ring
    rw [h, pow_mul]
  have hA3 : (2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1) < (2 ^ (3 * k)) ^ 2 - 1 := by
    have h1 : 2 ^ (2 * k) - 1 < 2 ^ (3 * k) + 1 := by
      have hle : 2 ^ (2 * k) ≤ 2 ^ (3 * k) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < 2 ^ (3 * k) := by positivity
      omega
    have h2 : 0 < 2 ^ (3 * k) - 1 := by
      have h3 : 1 < 2 ^ (3 * k) := Nat.one_lt_two_pow (by omega)
      omega
    have hsq : (2 ^ (3 * k)) ^ 2 - 1 = (2 ^ (3 * k) - 1) * (2 ^ (3 * k) + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ (3 * k)) 1
    rw [hsq]
    simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right h1 h2
  rw [hpow]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hA3

private theorem not_isL2_of_isL3 {X : Type} [Group X] [Finite X] {k j : ℕ}
    (h3 : IsL3 X k) (h2 : IsL2 X j) : False := by
  obtain ⟨hjk, hoddEq⟩ := isL3_isL2_twoPart_eq h3 h2
  exact (ne_of_lt (l3_odd_lt_l2_square h3.admissible.2.1 hjk)) hoddEq

private theorem nparamSingle_isL2_eq {X : Type} [Group X] [Finite X] {k j : ℕ}
    (h : NParamSingle X k) (hL2 : IsL2 X j) : k = j := by
  rcases h with hSz | hL2k | hSU3 | hSL3 | hSp4
  · exact (not_isL2_of_isSz hSz hL2).elim
  · exact S17.isL2_field_unique hL2k hL2
  · haveI : IsSimpleGroup X :=
      LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL2
    have hnc : ¬ IsMulCommutative X := by
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hL2
      exact fun hc => hab (hc.is_comm.comm a b)
    have hZ : Subgroup.center X = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
    have hU3 : IsU3 X k := by
      obtain ⟨-, hU3q⟩ := hSU3
      exact LieModel.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hU3q
    exact (not_isL2_of_isU3 hU3 hL2).elim
  · haveI : IsSimpleGroup X :=
      LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL2
    have hnc : ¬ IsMulCommutative X := by
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hL2
      exact fun hc => hab (hc.is_comm.comm a b)
    have hZ : Subgroup.center X = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
    have hL3 : IsL3 X k := by
      obtain ⟨-, hL3q⟩ := hSL3
      exact LieModel.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hL3q
    exact (not_isL2_of_isL3 hL3 hL2).elim
  · exact (not_isL2_of_isSp4 hSp4 hL2).elim

private theorem not_isL2Square_of_nparamSingle {X : Type} [Group X] {k j : ℕ}
    (h : NParamSingle X k) (hsq : IsL2Square X j) : False := by
  rcases h with hSz | hL2 | hSU3 | hSL3 | hSp4
  · exact not_isSimpleGroup_of_isL2Square hsq
      (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz)
  · exact not_isSimpleGroup_of_isL2Square hsq
      (LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL2)
  · exact not_isQuasisimple_of_isL2Square hsq hSU3.1
  · exact not_isQuasisimple_of_isL2Square hsq hSL3.1
  · exact not_isSimpleGroup_of_isL2Square hsq
      (LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSp) (by decide) hSp4)

private theorem prodFirstFactor_ne_prodSecondFactor {X A B : Type} [Group X] [Group A] [Group B]
    [Nontrivial A] (e : X ≃* A × B) :
    CFSG.GroupTheory.prodFirstFactor e ≠ CFSG.GroupTheory.prodSecondFactor e := by
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  intro hEq
  let x : X := e.symm (a, 1)
  have hx : e x = (a, (1 : B)) := by simp [x]
  have hx₁ : x ∈ CFSG.GroupTheory.prodFirstFactor e :=
    (CFSG.GroupTheory.mem_prodFirstFactor_iff (e := e)).mpr (by
      rw [hx]
      exact ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩)
  have hx₂ : x ∈ CFSG.GroupTheory.prodSecondFactor e := hEq ▸ hx₁
  have hcoord : (e x).1 = 1 := by
    have hmem := (CFSG.GroupTheory.mem_prodSecondFactor_iff (e := e)).mp hx₂
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).1
  rw [hx] at hcoord
  exact ha hcoord

private theorem isComponent_eq_prodFactor {X A B : Type} [Group X] [Finite X]
    [Group A] [Group B] [IsSimpleGroup A] [IsSimpleGroup B] [Nontrivial A] [Nontrivial B]
    (e : X ≃* A × B) (hAnc : ¬ IsMulCommutative A) (hBnc : ¬ IsMulCommutative B)
    {C : Subgroup X} (hC : CFSG.IsComponent C) :
    C = CFSG.GroupTheory.prodFirstFactor e ∨
      C = CFSG.GroupTheory.prodSecondFactor e := by
  let F₁ : Subgroup X := CFSG.GroupTheory.prodFirstFactor e
  let F₂ : Subgroup X := CFSG.GroupTheory.prodSecondFactor e
  let 𝒜 : Finset (Subgroup X) :=
    Finset.cons F₁ {F₂} (by simpa using prodFirstFactor_ne_prodSecondFactor e)
  have hAn : ∀ K ∈ 𝒜, K.Normal := by
    intro K hK
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl
    exacts [CFSG.GroupTheory.prodFirstFactor_normal e,
      CFSG.GroupTheory.prodSecondFactor_normal e]
  have hAs' : ∀ K ∈ 𝒜, IsSimpleGroup ↥K := by
    intro K hK
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl
    exacts [(CFSG.GroupTheory.prodFirstFactorMulEquiv e).isSimpleGroup,
      (CFSG.GroupTheory.prodSecondFactorMulEquiv e).isSimpleGroup]
  have hAnab : ∀ K ∈ 𝒜, ¬ IsMulCommutative ↥K := by
    intro K hK
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl
    exacts [fun hc => hAnc
        ((CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr
          (CFSG.GroupTheory.prodFirstFactorMulEquiv e)).mp hc),
      fun hc => hBnc
        ((CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr
          (CFSG.GroupTheory.prodSecondFactorMulEquiv e)).mp hc)]
  have hcomm : ∀ K ∈ 𝒜, ∀ K' ∈ 𝒜, K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', Commute a b := by
    intro K hK K' hK' hne a ha b hb
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl <;>
      rcases (by simpa [𝒜] using hK' : K' = F₁ ∨ K' = F₂) with rfl | rfl
    · exact absurd rfl hne
    · exact CFSG.GroupTheory.commute_prodFirstFactor_prodSecondFactor e ha hb
    · exact (CFSG.GroupTheory.commute_prodFirstFactor_prodSecondFactor e hb ha).symm
    · exact absurd rfl hne
  have hsup : 𝒜.sup id = ⊤ := by
    simpa [𝒜, Finset.sup_cons, Finset.sup_singleton]
      using CFSG.GroupTheory.prodFirstFactor_sup_prodSecondFactor e
  obtain ⟨K, hKmem, hKeq⟩ :=
    CFSG.GroupTheory.eq_of_isComponent_sup_of_direct (𝒜 := 𝒜)
      hAn hAs' hAnab hcomm hsup C hC
  rcases (by simpa [𝒜] using hKmem : K = F₁ ∨ K = F₂) with rfl | rfl
  exacts [Or.inl hKeq, Or.inr hKeq]

private theorem isL2_of_isL2_of_mem_calC {G : Type} [Group G] [Finite G]
    {L L₁ : Subgroup G} {j : ℕ} (hL₁ : L₁ ∈ calC L)
    (h : IsL2 (Bar2 L) j) : IsL2 (Bar2 L₁) j := by
  haveI : IsSimpleGroup (Bar2 L) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h
  have htop : barImage L L₁ = ⊤ :=
    isComponent_eq_top_of_isSimpleGroup (uc22p22l_barImage_isComponent hL₁)
  have hbar : IsL2 (barImage L L₁) j := by
    rw [htop]
    exact LieModel.of_mulEquiv Subgroup.topEquiv.symm h
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hL₁
  exact LieModel.of_mulEquiv e₁.symm hbar

private theorem isL2_of_isL2Square_of_mem_calC {G : Type} [Group G] [Finite G]
    {L L₁ : Subgroup G} {j : ℕ} (hL₁ : L₁ ∈ calC L)
    (h : IsL2Square (Bar2 L) j) : IsL2 (Bar2 L₁) j := by
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := h
  letI : Group A := gA
  letI : Group B := gB
  haveI hAs : IsSimpleGroup A :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hA
  haveI hBs : IsSimpleGroup B :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hB
  haveI : Nontrivial A := hAs.toNontrivial
  haveI : Nontrivial B := hBs.toNontrivial
  have hAnc : ¬ IsMulCommutative A := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hA
    exact fun hc => hab (hc.is_comm.comm a b)
  have hBnc : ¬ IsMulCommutative B := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hB
    exact fun hc => hab (hc.is_comm.comm a b)
  have hcomp := isComponent_eq_prodFactor e hAnc hBnc
    (uc22p22l_barImage_isComponent hL₁)
  have hbar : IsL2 (barImage L L₁) j := by
    rcases hcomp with hEq | hEq
    · rw [hEq]
      exact LieModel.of_mulEquiv
        (CFSG.GroupTheory.prodFirstFactorMulEquiv e).symm hA
    · rw [hEq]
      exact LieModel.of_mulEquiv
        (CFSG.GroupTheory.prodSecondFactorMulEquiv e).symm hB
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hL₁
  exact LieModel.of_mulEquiv e₁.symm hbar

theorem kNshape_holds : KNshape := by
  intro G _ _ L k j hNP hshape
  rcases hNP with hSingle | hProd
  · rcases hshape with hL2 | hsq
    · exact nparamSingle_isL2_eq hSingle hL2
    · exact (not_isL2Square_of_nparamSingle hSingle hsq).elim
  · obtain ⟨L₁, L₂, hL₁, hL₂, hsup, hne, hshapes⟩ := hProd
    have hsingle : NParamSingle (Bar2 L₁) k := by
      rcases hshapes L₁ (by simp) with h | h | ⟨hk3, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · subst hk3
        exact Or.inr (Or.inr (Or.inl h))
    rcases hshape with hL2 | hsq
    · exact nparamSingle_isL2_eq hsingle (isL2_of_isL2_of_mem_calC hL₁ hL2)
    · exact nparamSingle_isL2_eq hsingle (isL2_of_isL2Square_of_mem_calC hL₁ hsq)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
