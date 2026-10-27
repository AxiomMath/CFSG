module

public import CFSG.Quasithin.Background.WreathedCentralizerGeneration
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GU
public import CFSG.LocalAnalysis.WeakClosure81.PSLThreeInvolutionCentralizer
public import CFSG.LocalAnalysis.WeakClosure81.PSUThreeInvolutionCentralizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11 CFSG.Wreathed
open CFSG.Quasithin.Vol2.Ch11.SecU1
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.Q3.TL4
open CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

section General

variable {G : Type} [Group G]

theorem sup_inf_centralizer_eq_of_sup_centralizer_eq_top {L : Subgroup G} {x y : G}
    (hx : x ∈ L) (hy : y ∈ L)
    (h : Subgroup.centralizer ({(⟨x, hx⟩ : ↥L)} : Set ↥L) ⊔
      Subgroup.centralizer ({(⟨y, hy⟩ : ↥L)} : Set ↥L) = ⊤) :
    (L ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
      (L ⊓ Subgroup.centralizer ({y} : Set G)) = L := by
  have hCx : (Subgroup.centralizer ({(⟨x, hx⟩ : ↥L)} : Set ↥L)).map L.subtype ≤
      L ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf ?_ ?_
    · rintro _ ⟨z, -, rfl⟩
      exact z.2
    · simpa using Subgroup.map_centralizer_le_centralizer_image
        ({(⟨x, hx⟩ : ↥L)} : Set ↥L) L.subtype
  have hCy : (Subgroup.centralizer ({(⟨y, hy⟩ : ↥L)} : Set ↥L)).map L.subtype ≤
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    refine le_inf ?_ ?_
    · rintro _ ⟨z, -, rfl⟩
      exact z.2
    · simpa using Subgroup.map_centralizer_le_centralizer_image
        ({(⟨y, hy⟩ : ↥L)} : Set ↥L) L.subtype
  have hmap := congrArg (Subgroup.map L.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  exact hmap.symm.trans_le (sup_le_sup hCx hCy)

end General

theorem two_dvd_card_of_wreathed {L : Type} [Group L] [Finite L]
    (hwr : ∀ S : Sylow 2 L, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup L) ≃* CFSG.Open.WreathedTwoGroup m)) :
    2 ∣ Nat.card L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 L := Classical.choice (Sylow.nonempty (p := 2) (G := L))
  obtain ⟨m, hm, ⟨e⟩⟩ := hwr S
  have hcard : Nat.card ↥(S : Subgroup L) = 2 * (2 ^ m) ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact (wreath_center_involution_and_quaternion_coordinates m hm).card
  have h2S : 2 ∣ Nat.card ↥(S : Subgroup L) := by
    rw [hcard]
    exact dvd_mul_right 2 _
  exact dvd_trans h2S (Subgroup.card_subgroup_dvd_card (S : Subgroup L))

section ProjectiveThree

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  {X : Type} [Group X] [Finite X]

theorem wreathed_sylow_of_projectiveSL_three
    (hodd : Odd (Nat.card K)) (hq4 : Nat.card K % 4 = 1) (hq5 : 5 < Nat.card K)
    (e : X ≃* projectiveSL 3 K) :
    ∀ S : Sylow 2 X, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.WreathedTwoGroup m) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hcardNat : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  have hp2 : ringChar K ≠ 2 := by
    intro h2
    have hEven : Fintype.card K % 2 = 0 :=
      (FiniteField.even_card_iff_char_two (F := K)).mp h2
    have hOdd : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
    rw [Nat.card_eq_fintype_card] at hOdd
    omega
  have hLn : IsLnEps 3 X 1 (ringChar K ^ (n : ℕ)) :=
    Or.inl ⟨rfl, K, inferInstance, inferInstance, hcardNat,
      ⟨e.trans (Lemma41dL3.projEquiv K)⟩⟩
  intro S
  exact Lemma44b.sylow_L3_wr hp hp2 hLn (by rw [← hcardNat]; exact hq4)
    (by rw [← hcardNat]; omega) S

theorem sup_inf_centralizer_eq_top_of_projectiveSL_three
    (hodd : Odd (Nat.card K)) (e : ↥L ≃* projectiveSL 3 K) :
    ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
      (L ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
        (L ⊓ Subgroup.centralizer ({y} : Set G)) = L := by
  intro x hx y hy hx2 hy2 hne hcomm
  have hmodel : Subgroup.centralizer ({e ⟨x, hx⟩} : Set (projectiveSL 3 K)) ⊔
      Subgroup.centralizer ({e ⟨y, hy⟩} : Set (projectiveSL 3 K)) = ⊤ := by
    have hcommL : (⟨x, hx⟩ : ↥L) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      apply Subtype.ext
      simpa using hcomm
    have hneL : (⟨x, hx⟩ : ↥L) ≠ ⟨y, hy⟩ := by
      intro h
      exact hne (by simpa using congrArg Subtype.val h)
    refine E3C269G.sup_centralizer_eq_top_psl3 hodd ?_ ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
    · rw [← map_mul, ← map_mul]
      exact congrArg e hcommL
    · exact fun h => hneL (e.injective h)
  exact sup_inf_centralizer_eq_of_sup_centralizer_eq_top hx hy
    (E3C269G.sup_centralizer_eq_top_of_equiv e hmodel)

end ProjectiveThree

section UnitaryThree

variable {G : Type} [Group G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]
  {X : Type} [Group X] [Finite X]

theorem wreathed_sylow_of_psu_three (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hq4 : p ^ f % 4 = 3) (e : X ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    ∀ S : Sylow 2 X, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.WreathedTwoGroup m) := by
  have hKU : IsLnEps 3 X (-1) (p ^ f) :=
    Or.inr ⟨rfl, K, inferInstance, hU.finite,
      by rw [hU.card, mul_comm 2 f, pow_mul], ⟨e⟩⟩
  intro S
  exact Lemma44b.sylow_U3_wr hU.prime hp2 hKU hq4 S

theorem sup_inf_centralizer_eq_top_of_psu_three (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (e : ↥L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
      (L ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
        (L ⊓ Subgroup.centralizer ({y} : Set G)) = L := by
  intro x hx y hy hx2 hy2 hne hcomm
  have hmodel : Subgroup.centralizer ({e ⟨x, hx⟩} :
        Set (StatedProj (StatedSU 3 (p ^ f) K))) ⊔
      Subgroup.centralizer ({e ⟨y, hy⟩} :
        Set (StatedProj (StatedSU 3 (p ^ f) K))) = ⊤ := by
    have hcommL : (⟨x, hx⟩ : ↥L) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      apply Subtype.ext
      simpa using hcomm
    have hneL : (⟨x, hx⟩ : ↥L) ≠ ⟨y, hy⟩ := by
      intro h
      exact hne (by simpa using congrArg Subtype.val h)
    refine E3C269G.sup_centralizer_eq_top_psu3 hU hp2 ?_ ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
    · rw [← map_mul, ← map_mul]
      exact congrArg e hcommL
    · exact fun h => hneL (e.injective h)
  exact sup_inf_centralizer_eq_of_sup_centralizer_eq_top hx hy
    (E3C269G.sup_centralizer_eq_top_of_equiv e hmodel)

end UnitaryThree

section ProjectiveModel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem nParam_le_one_of_wreathed_projectiveSL_three
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hodd : Odd (Nat.card K)) (hq4 : Nat.card K % 4 = 1) (hq5 : 5 < Nat.card K)
    (e : ↥L ≃* projectiveSL 3 K)
    (hn1 : ∀ x ∈ L, orderOf x = 2 →
      E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwr := wreathed_sylow_of_projectiveSL_three hodd hq4 hq5 e
  have h2 := two_dvd_card_of_wreathed hwr
  have hgen := sup_inf_centralizer_eq_top_of_projectiveSL_three hodd e
  exact RonanE114.Seven.nParam_le_one_of_wreathed_of_sup_centralizer_eq hAS hT h2 hwr hgen hn1

end ProjectiveModel

section UnitaryModel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]

theorem nParam_le_one_of_wreathed_psu_three
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 3)
    (e : ↥L ≃* StatedProj (StatedSU 3 (p ^ f) K))
    (hn1 : ∀ x ∈ L, orderOf x = 2 →
      E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwr := wreathed_sylow_of_psu_three hU hp2 hq4 e
  have h2 := two_dvd_card_of_wreathed hwr
  have hgen := sup_inf_centralizer_eq_top_of_psu_three hU hp2 e
  exact RonanE114.Seven.nParam_le_one_of_wreathed_of_sup_centralizer_eq hAS hT h2 hwr hgen hn1

end UnitaryModel

section ProjectiveUnconditional

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  {p f : ℕ}

theorem nParam_le_one_of_wreathed_projectiveSL_three_of_three_le
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (hcardK : Nat.card K = p ^ f) (hq4 : p ^ f % 4 = 1)
    (e : ↥L ≃* projectiveSL 3 K) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq5 : 5 < p ^ f := by
    have h3f : 3 ^ 3 ≤ p ^ f := by
      calc 3 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega : 0 < p) hf
    norm_num at h3f
    omega
  have hn1 : ∀ x ∈ L, orderOf x = 2 →
      E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
    intro x hx hx2
    exact nParam_centralizer_le_one_of_psl3 hp hp2 hf hcardK hAS hx hx2 e
  exact nParam_le_one_of_wreathed_projectiveSL_three hAS hT
    (by rw [hcardK]; exact (hp.odd_of_ne_two hp2).pow)
    (by rw [hcardK]; exact hq4) (by rw [hcardK]; exact hq5) e hn1

theorem nParam_le_one_of_wreathed_projectiveSL_three_of_five_lt
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (hcardK : Nat.card K = p ^ f) (hq4 : p ^ f % 4 = 1)
    (e : ↥L ≃* projectiveSL 3 K) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have hn1 : ∀ x ∈ L, orderOf x = 2 →
      E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
    intro x hx hx2
    exact nParam_centralizer_le_one_of_psl3_of_five_lt hp hp2 h5 hcardK hAS hx hx2 e
  exact nParam_le_one_of_wreathed_projectiveSL_three hAS hT
    (by rw [hcardK]; exact (hp.odd_of_ne_two hp2).pow)
    (by rw [hcardK]; exact hq4) (by rw [hcardK]; exact h5) e hn1

end ProjectiveUnconditional

section UnitaryUnconditional

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {p f : ℕ} {K : Type} [Field K]

theorem nParam_le_one_of_wreathed_psu_three_of_two_le
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hq4 : p ^ f % 4 = 3)
    (e : ↥L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have hf3 : 3 ≤ f := by
    by_contra h
    have hf2 : f = 2 := by omega
    subst hf2
    have hpodd : Odd p := hU.prime.odd_of_ne_two hp2
    have h8 : 8 ∣ p ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hpodd
    have h4dvd : 4 ∣ p ^ 2 - 1 := dvd_trans (by norm_num : 4 ∣ 8) h8
    obtain ⟨k, hk⟩ := h4dvd
    have hpk : p ^ 2 = 4 * k + 1 := by omega
    have hsq : p ^ 2 % 4 = 1 := by
      rw [hpk]
      simp
    omega
  have hn1 : ∀ x ∈ L, orderOf x = 2 →
      E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
    intro x hx hx2
    exact nParam_centralizer_le_one_of_psu3 hU hp2 hf3 hAS hx hx2 e
  exact nParam_le_one_of_wreathed_psu_three hAS hT hU hp2 hq4 e hn1

theorem nParam_le_one_of_wreathed_psu_three_of_five_lt
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h5 : 5 < p ^ f)
    (hq4 : p ^ f % 4 = 3)
    (e : ↥L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have hn1 : ∀ x ∈ L, orderOf x = 2 →
      E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
    intro x hx hx2
    exact nParam_centralizer_le_one_of_psu3_of_five_lt hU hp2 h5 hAS hx hx2 e
  exact nParam_le_one_of_wreathed_psu_three hAS hT hU hp2 hq4 e hn1

end UnitaryUnconditional

theorem nParam_le_one_of_lieModel_PSL_three_of_three_le
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f) (hq4 : p ^ f % 4 = 1)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hLie : CFSG.Blueprint.LieModel ↥(CFSG.generalizedFitting Q) .PSL 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  letI : Field K := hK
  letI : Finite K := hKfin
  exact nParam_le_one_of_wreathed_projectiveSL_three_of_three_le hAS hT hp hp2 hf hcard hq4 e

theorem nParam_le_one_of_lieModel_PSL_three_of_five_lt
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f) (hq4 : p ^ f % 4 = 1)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hLie : CFSG.Blueprint.LieModel ↥(CFSG.generalizedFitting Q) .PSL 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  letI : Field K := hK
  letI : Finite K := hKfin
  exact nParam_le_one_of_wreathed_projectiveSL_three_of_five_lt hAS hT hp hp2 h5 hcard hq4 e

theorem nParam_le_one_of_lieModel_PSU_three_of_two_le
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f) (hq4 : p ^ f % 4 = 3)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hLie : CFSG.Blueprint.LieModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  have hc : StatedClassicalModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f :=
    hLie.statedClassicalModel (by decide)
  simp only [StatedClassicalModel] at hc
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hc
  letI : Field K := hK
  letI : Finite K := hKfin
  have hU : UnitaryFieldData p f K :=
    ⟨hp, by omega, by rw [hcard, ← pow_mul, mul_comm f 2]⟩
  exact nParam_le_one_of_wreathed_psu_three_of_two_le hAS hT hU hp2 hf hq4 e

theorem nParam_le_one_of_lieModel_PSU_three_of_five_lt
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 < p ^ f) (hq4 : p ^ f % 4 = 3)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hLie : CFSG.Blueprint.LieModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  have hc : StatedClassicalModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f :=
    hLie.statedClassicalModel (by decide)
  simp only [StatedClassicalModel] at hc
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hc
  letI : Field K := hK
  letI : Finite K := hKfin
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0] at h5
    simp at h5
  have hU : UnitaryFieldData p f K :=
    ⟨hp, hf1, by rw [hcard, ← pow_mul, mul_comm f 2]⟩
  exact nParam_le_one_of_wreathed_psu_three_of_five_lt hAS hT hU hp2 h5 hq4 e

end CFSG.LocalAnalysis.WeakClosure81
