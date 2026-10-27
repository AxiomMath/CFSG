module

public import CFSG.RankThree.GF2n.Parrott.Section5Theorem5
public import CFSG.RankThree.GF2n.Parrott.Section5LocalWOrbits
public import CFSG.RankThree.GF2n.Parrott.Section5LocalK
public import CFSG.RankThree.GF2n.Parrott.Section5LocalSigma
public import CFSG.RankThree.GF2n.Parrott.Section5CenterT1
public import CFSG.RankThree.GF2n.Parrott.Section5LocalSpin
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT23
public import CFSG.RankThree.GF2n.Parrott.Section5NoE16T1
public import CFSG.RankThree.GF2n.Parrott.Section5SqrtT1
public import CFSG.RankThree.GF2n.Parrott.Section5Choice
public import CFSG.RankThree.GF2n.Parrott.E27LineCount
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality
public import CFSG.RankThree.GF2n.Parrott.Section5KL
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntStandard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma37Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma38
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.Sporadic.Fi22.FischerOpen

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem exists_conj_actionQA45_eq_rhoA (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2),
      ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := by
  obtain ⟨P, -, hP'⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  exact ⟨P, fun a => by simpa [rhoA, toQAct] using hP' a⟩

private theorem parrott_theorem5_of_choice [DecidableEq G] (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z))
    (hHO : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2)
    (hT2 : (∃ g ∈ centralizer ({z₁} : Set G),
        g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z) →
      ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
        (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
            (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X))
    {T₁ S₀ : Subgroup G} {σ₂ τ : ↥(H z)}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    (hS₀ : IsSylowOf 2 S₀
      (H z ⊓ normalizer (zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) : Set G)))
    (hTS : T₁ ≤ S₀) (htT : (τ : G) ∈ centerIn T₁) (htJ : (τ : G) ∉ J z)
    (hZS : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = (τ : G) * z₁ ∨ e = (τ : G) * z₁ * z)
    (hy : ∃ y ∈ S₀, y ∉ centralizer ({z₁} : Set G)) (htz₁ : (τ : G) * z₁ ∈ centerIn S₀)
    (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (hbad : ∀ y ∈ H z, orderOf y = 2 → y ≠ z →
      (∀ c ∈ H z,
        c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y)
    {T₃ : Subgroup G} (hT₃ : IsSylowOf 2 T₃
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G)))
    (hT₃c : Nat.card T₃ = 2 ^ 5) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  obtain ⟨w, hwH, hw⟩ := exists_inv_sigma1Nine_mul_inv D h hσ₂ hq₂ hc₂
  obtain ⟨w₁, hw₁H, hw₁⟩ := exists_inv_sigma1Nine D h
  have hT₂ := isSylowOf_lemma54T₂ D h P hP hσ₂ hq₂ hc₂
  have hT₂c := card_lemma54T₂ D h P hP hσ₂ hq₂ hc₂
  have hJx := (card_J_inf_centralizer_sigma1Nine_mul_inv_of_spin D h P hP hσ₂ hq₂ hc₂).ge
  obtain ⟨O, hOW, hcover, hdisj, horb, hinv, hcard, hO0, hO1, hJ, hnJ, hO2z, hO3z, hgen,
    hO56, hT₁O⟩ :=
    exists_lemma54_orbits (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (hS₀.le.trans inf_le_left) htz₁ hZS hy
  exact parrott_theorem5
    (z₁ := z₁) (σ₁ := ((sigma1Nine (z := z) D : ↥(H z)) : G))
    (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (σ₃ := ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)) (w := w) (w₁ := w₁) (T₁ := T₁)
    (T₂ := (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))) (T₃ := T₃)
    (W := lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
    (t := (τ : G)) (S₀ := S₀) (O := O) h hZ hHO hz₁ hz₁z hord hT2
    (card_and_centerIn_isSylowOf_centralizer_of_spin D h hZ hz₁ hz₁z hord P hP)
    ((Subgroup.orderOf_coe (sigma1Nine (z := z) D)).trans (sigma1Nine_order D))
    (sigma1Nine (z := z) D).2 (orderOf_sigma1Nine_mul_inv D h hσ₂ hq₂ hc₂)
    (sigma1Nine (z := z) D * σ₂⁻¹).2 (orderThree_subgroup_classes_H D h hσ₂ hq₂ hc₂)
    hwH hw hw₁H hw₁ hT₁ (card_isSylowOf_centralizer_sigma1Nine D h hT₁)
    (card_centerIn_isSylowOf_centralizer_sigma1Nine D h hT₁)
    (mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine D h hT₁) hT₂ hT₂c
    (centerIn_isSylowOf_centralizer_sigma1Nine_mul_inv_eq_zpowers D h hZ P hP hσ₂ hq₂ hc₂ hT₂)
    hT₃ (z_mem_commutator_of_isSylowOf_centralizer_sigma1Nine_mul D h hZ hσ₂ hq₂ hc₂ hT₃)
    (fun y hy => hT₃c.trans_lt
      (two_pow_five_lt_card_inf_centralizer_of_mem_commutator h hT₂ hT₂c hJx hy))
    (exists_conj_mem_isSylowOf_centralizer_sigma1Nine_mul_inv D h P hP hσ₂ hq₂ hc₂ hT₂) hbad
    (lemma54W_le_lemma54T₂ (z := z) D (σ₂ := σ₂) (τ := τ) hqτ hτ₁ hτ₂)
    (lemma54W_comm D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
    (lemma54W_mul_self D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
    (card_lemma54W D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
    (eq_lemma54W_of_le_lemma54T₂ D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
    (fun j hj hj2 _ => exists_conj_mem_lemma54W D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ j hj hj2)
    (lemma54_kl_of_not_equalityBranch D h hZ hIII hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
    hOW hcover hdisj horb hinv hcard hO0 hO1 hJ hnJ hO2z hO3z hgen hO56
    (exists_elementaryAbelian_or_isSylowOf_centralizer_sigma1Nine_mul D h hZ hIII hσ₂ hq₂ hc₂)
    (not_elementaryAbelian_of_le_isSylowOf_centralizer_sigma1Nine D h hIII hT₁) hS₀ hTS
    (centerIn_J_le_centerIn_of_isSylowOf_centralizer_sigma1Nine D h hT₁ hz₁) htT hT₁O
    (mem_commutator_or_ncard_sqrt_ne_of_isSylowOf_centralizer_sigma1Nine D h hT₁ hz₁ hz₁z htJ)

theorem parrott_theorem5_of_quotientData [DecidableEq G] (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z))
    (hHO : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (hT2 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G),
          g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z) →
        ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
          (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
              (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X))
    (hbad : ∀ P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2),
      (∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) →
      ∀ σ₂ : ↥(H z), orderOf σ₂ = 3 → qH (z := z) D σ₂ = s2A →
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ →
      ∀ y ∈ H z, orderOf y = 2 → y ≠ z →
        (∀ c ∈ H z,
          c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
        ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
          (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
          IsPGroup 2 B → y ∈ B → z ∉ B →
          Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
          ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  classical
  obtain ⟨P, hP⟩ := exists_conj_actionQA45_eq_rhoA (z := z) (D := D) h hIII
  obtain ⟨z₁, hZeq, hz₁z, hord⟩ := exists_z1 (z := z) h
  have hz₁ : z₁ ∈ centerIn (J z) :=
    hZeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  obtain ⟨T₁, S₀, t, σ₂, hT₁, hS₀, hTS, htT, htJ, hZS, hy, hσ₂, hq₂, hc₂, hσ₂t,
    ⟨ht, hqt⟩, htz₁⟩ := exists_parrott_T1_choice D h hZ hz₁ hz₁z hord
  let τ : ↥(H z) := ⟨t, ht⟩
  have hτ : τ * τ = 1 :=
    Subtype.ext (mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine D h hT₁ t htT)
  have hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hT₁.le htT.1)).2)
  have hτ₂ : τ * σ₂ = σ₂ * τ := Subtype.ext hσ₂t.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₃, hT₃⟩ := exists_isSylowOf 2
    (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))
  exact parrott_theorem5_of_choice D h hZ hHO hIII P hP hz₁ hz₁z hord (hT2 z₁ hz₁ hz₁z hord)
    (τ := τ) hT₁ hS₀ hTS htT htJ hZS hy htz₁ hσ₂ hq₂ hc₂ hqt hτ hτ₁ hτ₂
    (hbad P hP σ₂ hσ₂ hq₂ hc₂) hT₃
    (card_isSylowOf_centralizer_sigma1Nine_mul D h hIII hσ₂ hq₂ hc₂
      (e27LineCountData_of_not_equalityBranch D h hIII hσ₂ hq₂ hc₂) hT₃)

end Certified

end CFSG.RankThree.GF2n.Parrott
