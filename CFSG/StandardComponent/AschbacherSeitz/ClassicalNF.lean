module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOpen
public import CFSG.StandardComponent.AschbacherSeitz.Main
public import CFSG.StandardComponent.AschbacherSeitz.L3NF
public import CFSG.StandardComponent.AschbacherSeitz.Cfg76NF

public noncomputable section

namespace CFSG.StandardComponent.AschbacherSeitz

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoL3Even
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

theorem hyp31_ofNF {G : Type} [Group G] [Finite G] {A : Subgroup G} (hII : ClassicalHypII)
    (hH : RankTwoHypNF G A) (hO : standardComponentOddCore G = ⊥)
    (hT : RankTwoClassicalEvenType (rankTwoQuot A)) : Hyp31 A :=
  ⟨hH.standard, hII _ hH.standard.1.1 hT, hO, lt_of_lt_of_le one_lt_two hH.rank, hH.not_normal⟩

theorem false_of_benderNF
    (h2 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → RankTwoBenderType (rankTwoQuot A) →
        SuzukiModel (rankTwoQuot A) 2 3 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru)
    {H : Type} [Group H] [Finite H] {B : Subgroup H} (hB : RankTwoHypNF H B)
    (hO : standardComponentOddCore H = ⊥) {n : ℕ} (hn : 3 ≤ n)
    (hT : StatedClassicalModel (rankTwoQuot B) .PSL 2 2 n) : False := by
  obtain ⟨hSz, -⟩ := h2 H B hB hO (Or.inl ⟨n, hn, hT⟩)
  exact RankTwoL3Even.not_three_dvd_card_of_suzukiModel_three hSz
    (three_dvd_card_of_psl_two (by omega) hT)

theorem false_of_psu_threeNF
    (h2 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → RankTwoBenderType (rankTwoQuot A) →
        SuzukiModel (rankTwoQuot A) 2 3 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru)
    {H : Type} [Group H] [Finite H] {B : Subgroup H} (hB : RankTwoHypNF H B)
    (hO : standardComponentOddCore H = ⊥) {m : ℕ} (hm : 2 ≤ m)
    (hT : StatedClassicalModel (rankTwoQuot B) .PSU 3 2 m) : False := by
  obtain ⟨hSz, -⟩ := h2 H B hB hO (Or.inr (Or.inl ⟨m, hm, hT⟩))
  exact RankTwoL3Even.not_three_dvd_card_of_suzukiModel_three hSz
    (three_dvd_card_of_psu_three hT)

theorem false_of_triality_fourNF (hSuz : SuzL34DiagInput) (h32 : AS76b.Lemma32)
    (h4 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        (standardComponentOddCore G = ⊥ → m = 2) ∧
        (m = 2 →
          (NativeSporadic.IsSporadic (rankTwoX A ⧸ Subgroup.center (rankTwoX A)) .Suz ∧
            Nat.card (Subgroup.center (rankTwoX A)) ∣ 3) ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
        (standardComponentOddCore G = ⊥ →
          NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
            (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX A) .He)))
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : Hyp31 A) (hH : RankTwoHypNF G A)
    {R Q : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hQA : Q ≤ A)
    (hstd : standardComponentIsStandard
      ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))))
    (hnn : ¬ ((AS76b.layerCentralizer A Q).subgroupOf (centralizer (Q : Set G))).Normal)
    (hZ : Odd (Nat.card (center ↥(AS76b.layerCentralizer A Q))))
    (hT : StatedClassicalModel (rankTwoQuot (AS76b.layerCentralizer A Q)) .PSL 3 2 2)
    (hy : ∃ y ∈ A ⊓ centralizer (Q : Set G), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
      ¬ InducesInner y (AS76b.layerCentralizer A Q)) : False := by
  set W := centralizer (Q : Set G) with hW
  set L := AS76b.layerCentralizer A Q with hLdef
  have hLAW : L ≤ A ⊓ W := AS76b.layerCentralizer_le A Q
  have hLW : L ≤ W := hLAW.trans inf_le_right
  have hLA : L ≤ A := hLAW.trans inf_le_left
  have hH' : RankTwoHypNF ↥W (L.subgroupOf W) :=
    ⟨hstd, hnn, RankTwoL3Even.two_le_pRank_centralizer_subgroupOf hQA hLA hH.rank⟩
  let eLL : ↥(L.subgroupOf W) ≃* ↥L := subgroupOfEquivOfLe hLW
  have hTL' : StatedClassicalModel (rankTwoQuot (L.subgroupOf W)) .PSL 3 2 2 :=
    SectionRank.statedClassicalModel_of_mulEquiv (quotCenterCongr eLL) hT
  obtain ⟨-, hii, -⟩ := h4 ↥W (L.subgroupOf W) hH' 2 le_rfl hTL'
  rcases hii rfl with ⟨hSz, -⟩ | ⟨⟨eE⟩, -⟩
  swap
  · have hcardE : Nat.card (center ↥(L.subgroupOf W)) = 4 := by
      rw [Nat.card_congr eE.toEquiv, Nat.card_prod]
      simp
    have hcardZ : Nat.card (center ↥(L.subgroupOf W)) = Nat.card (center ↥L) :=
      Nat.card_congr ((MulEquiv.subgroupMap eLL (center _)).toEquiv.trans
        (MulEquiv.subgroupCongr (Subgroup.map_center_eq eLL)).toEquiv)
    rw [hcardZ] at hcardE
    rw [hcardE] at hZ
    exact absurd hZ (by decide)
  obtain ⟨e⟩ := hSz
  obtain ⟨y, ⟨hyA, hyQ⟩, ⟨k, hk⟩, hyn⟩ := hy
  apply hyn
  have hyW : y ∈ W := hyQ
  have hRW : R ≤ W := hR.le.trans (centralizer_le hQA)
  have hRL : R ≤ centralizer (L : Set G) := hR.le.trans (centralizer_le hLA)
  have hRe : IsElemAbelian 2 R := h32 G A hA R hR
  have hyL : y ∈ normalizer (L : Set G) :=
    AS76b.normalizer_inf_le_normalizer_layerCentralizer A Q ⟨le_normalizer hyA, hyQ⟩
  refine inducesInner_subgroupOf hLW (y := ⟨y, hyW⟩) ?_
  refine inducesInner_of_l34DiagFact (X₀ := NativeSporadic.Carrier .Suz) hSuz
    (X := rankTwoX (L.subgroupOf W)) (R := R.subgroupOf W)
    (commutator_rankTwoX hstd.1.1) e Subgroup.le_normalClosure hstd.1 hTL' ?_ ?_ ?_ ?_ ?_ ?_
    ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro r hr
    rw [mem_centralizer_iff]
    intro l hl
    exact Subtype.ext (mem_centralizer_iff.mp (hRL (mem_subgroupOf.mp hr)) l
      (mem_subgroupOf.mp hl))
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun r hr => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, mem_subgroupOf.mp a.2⟩
        ⟨b, mem_subgroupOf.mp b.2⟩)
      simpa using this
    · simpa using hRe.2 _ (mem_subgroupOf.mp hr)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hRW).toEquiv]
    exact four_le_card_of_isSylowOf hR hH.rank
  · refine AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ _ ?_
      (odd_card_centralizer_rankTwoX hstd hnn) inf_le_right
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hRe.2 _ (mem_subgroupOf.mp (mem_inf.mp x.2).1)
  · rw [mem_normalizer_iff]
    intro l
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp hyL l
  · rw [mem_centralizer_iff]
    intro r hr
    exact Subtype.ext (mem_centralizer_iff.mp (hR.le (mem_subgroupOf.mp hr)) y hyA).symm

theorem step76L3NF (hSuz : SuzL34DiagInput) (h32 : AS76b.Lemma32)
    (h4 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        (standardComponentOddCore G = ⊥ → m = 2) ∧
        (m = 2 →
          (NativeSporadic.IsSporadic (rankTwoX A ⧸ Subgroup.center (rankTwoX A)) .Suz ∧
            Nat.card (Subgroup.center (rankTwoX A)) ∣ 3) ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
        (standardComponentOddCore G = ⊥ →
          NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
            (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX A) .He))) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
      (R T Y W L : Subgroup G) (g : G), RankTwoHypNF G A → Hyp31 A →
      RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75Y D T Y W L →
      D.IsLinearFiveFour → False := by
  intro G _ _ A D R T Y W L g hH hA hTy hch hl hD
  have hy := hl.diag hD
  have hZ := hl.oddCenter
  have hlevi := hl.levi
  have hstd := hl.standard
  have hnn := hl.not_normal
  obtain rfl := hl.L_eq
  have hT : StatedClassicalModel (rankTwoQuot (AS76b.layerCentralizer A Y)) .PSL 3 2 2 := by
    cases D with
    | linear n m hn hm hnm K hK e =>
      obtain ⟨rfl, rfl⟩ := hD
      exact hlevi
    | unitary => exact hD.elim
    | symplectic => exact hD.elim
    | orthPlus => exact hD.elim
    | orthMinus => exact hD.elim
  exact false_of_triality_fourNF hSuz h32 h4 hA hH hch.sylowR hl.Y_le hstd hnn hZ hT hy

theorem step76L2NF
    (h4 : Asc75Theorem4)
    (h32 : AS76b.Lemma32) (h34 : Asc08Lemma34) (h5 : Asc08Lemma310NF) (hJ : J2Std.J2StdFacts)
    (hSp44 : Sp44EndgameNF) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
      (R T Y W L : Subgroup G) (g : G), RankTwoHypNF G A → Hyp31 A →
      RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75Y D T Y W L →
      D.IsLTwoFour → False := by
  intro G _ _ A D R T Y W L g hH hA hTy hch hl hD
  have hc := NF.Levi75Y.cfg76NF hH hA hch hl hD
  by_cases hfam : D.family = .symplectic
  · obtain ⟨y, s, y₃, rfl, hsp⟩ := hl.spFour hD hfam
    exact hSp44 G A R W L y s y₃ hc hsp
  obtain ⟨D', s, x, hY, hs, hWs, hLs, hDs, hxL, hx5, hlay, hnoZ⟩ := hl.sym hD hfam
  have hc' : NF.Cfg76 A R (rightConjugate Y s) W := hLs ▸ hc.conj hs
  have hYs : rightConjugate Y s = D' ⊔ L := by
    rw [hY]
    change (D' ⊔ W).map (MulAut.conj s⁻¹).toMonoidHom = D' ⊔ L
    rw [Subgroup.map_sup]
    change rightConjugate D' s ⊔ rightConjugate W s = D' ⊔ L
    rw [hDs, hWs]
  set Z := D' ⊔ zpowers x with hZdef
  have hZYs : Z ≤ rightConjugate Y s := by
    rw [hYs]
    exact sup_le_sup_left (zpowers_le.mpr hxL) D'
  have hZA : Z ≤ A := hZYs.trans hc'.Y_le
  have hLYs : L ≤ rightConjugate Y s := by
    rw [hYs]
    exact le_sup_right
  obtain ⟨c, hcYx, r, hr, hcr⟩ := hc.exists_conj h5 h32 hJ hxL hx5
  have hcZ : c ∈ centralizer (Z : Set G) := by
    obtain ⟨hcY, hcx⟩ := mem_inf.mp hcYx
    refine mem_centralizer_sup ?_ ?_
    · exact centralizer_le (show D' ≤ Y by rw [hY]; exact le_sup_left) hcY
    · rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp hcx).symm k).eq
  have hxW : s⁻¹ * x * s ∈ W := by
    rw [← hLs, mem_rightConjugate_iff]
    simpa [mul_assoc] using hxL
  have hxW5 : orderOf (s⁻¹ * x * s) = 5 := by
    have := orderOf_injective (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective x
    simpa [MulAut.conj_apply, hx5] using this
  have hRE := hc'.R_le_E h5 h32 hxW hxW5
  have hr2 : r ^ 2 = 1 := (h32 G A hA R hch.sylowR).2 r hr
  have hmem := hc'.conj_mem_E h4 h32 h34 h5 hZYs hZA hlay hnoZ c hcZ r (hRE hr) hr2
  exact hcr (((NF.Cfg76.E76_le_centralizer).trans (centralizer_le hLYs)) hmem)

theorem step76NF_of_inputs
    (h2 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → RankTwoBenderType (rankTwoQuot A) →
        SuzukiModel (rankTwoQuot A) 2 3 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru)
    (h4 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        (standardComponentOddCore G = ⊥ → m = 2) ∧
        (m = 2 →
          (NativeSporadic.IsSporadic (rankTwoX A ⧸ Subgroup.center (rankTwoX A)) .Suz ∧
            Nat.card (Subgroup.center (rankTwoX A)) ∣ 3) ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
        (standardComponentOddCore G = ⊥ →
          NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
            (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX A) .He)))
    (hSuz : SuzL34DiagInput) (h75 : Asc75Theorem4) (h32 : AS76b.Lemma32)
    (h34 : Asc08Lemma34) (h5 : Asc08Lemma310NF) (hJ : J2Std.J2StdFacts) (hSp44 : Sp44EndgameNF) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
      (R T Y W L : Subgroup G) (g : G), RankTwoHypNF G A → Hyp31 A →
      RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75Y D T Y W L →
      (∀ (G' : Type) [Group G'] [Finite G'] (A' : Subgroup G'), Nat.card G' < Nat.card G →
        RankTwoHypNF G' A' → standardComponentOddCore G' = ⊥ →
          ¬ RankTwoClassicalEvenType (rankTwoQuot A')) → False := by
  intro G _ _ A D R T Y W L g hH hA hTy hch hl ih
  obtain ⟨H, _, _, B, hlt, hB, hO, ⟨eB⟩⟩ := levi75Y_exists_quotientNF hH hA hl
  have hq := hch.four_le
  have hlevi := hl.levi
  have hm2 : ∀ m : ℕ, 4 ≤ 2 ^ m → 2 ≤ m := by
    intro m hm
    by_contra h
    interval_cases m <;> norm_num at hm
  have hclass : ∀ {t : StatedLieTag} {n m : ℕ}, StatedClassicalModel (rankTwoQuot L) t n 2 m →
      ((t = .PSL ∧ 4 ≤ n) ∨ (t = .PSU ∧ 4 ≤ n) ∨ (t = .PSp ∧ 2 ≤ n) ∨
        ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n)) →
      EvenSmallLie.CatalogOrders.lieMin t ≤ n →
      7 ≤ m * EvenSmallLie.CatalogOrders.lieExp t n → False := by
    intro t n m hT ht hn he
    have hT' := SectionRank.statedClassicalModel_of_mulEquiv eB hT
    exact ih H B hlt hB hO
      (classicalEvenType_of_model hT' ht (two_pow_seven_dvd_of_model hn he hT'))
  have hbender : ∀ {m : ℕ}, 3 ≤ m → StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m → False :=
    fun hm hT => false_of_benderNF h2 hB hO hm (SectionRank.statedClassicalModel_of_mulEquiv eB hT)
  have hL2' : D.IsLTwoFour → False :=
    step76L2NF h75 h32 h34 h5 hJ hSp44 G A D R T Y W L g hH hA hTy hch hl
  have hL3' : D.IsLinearFiveFour → False :=
    step76L3NF hSuz h32 h4 G A D R T Y W L g hH hA hTy hch hl
  cases D with
  | linear n m hn hm hnm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · rcases Nat.lt_or_ge n 5 with h5 | h5
      ·
        obtain rfl : n = 4 := by omega
        rcases Nat.lt_or_ge m 3 with h3 | h3
        · obtain rfl : m = 2 := by omega
          exact hL2' ⟨rfl, rfl⟩
        · exact hbender h3 hlevi
      ·
        obtain rfl : n = 5 := by omega
        have hT' := SectionRank.statedClassicalModel_of_mulEquiv eB hlevi
        have hm2' : m = 2 := (h4 H B hB m hm' hT').1 hO
        subst hm2'
        exact hL3' ⟨rfl, rfl⟩
    · exact hclass hlevi (Or.inl ⟨rfl, by omega⟩)
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 3 * 4 ≤ (n - 2 - 1) * (n - 2) := Nat.mul_le_mul (by omega) (by omega)
          have hP2 : 6 ≤ (n - 2 - 1) * (n - 2) / 2 := by omega
          calc 7 ≤ 2 * 6 := by norm_num
            _ ≤ m * ((n - 2 - 1) * (n - 2) / 2) := Nat.mul_le_mul hm' hP2)
  | unitary n m hn hm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h5, hT⟩ | ⟨rfl, hT⟩
    · rcases Nat.lt_or_ge n 6 with h6 | h6
      · obtain rfl : n = 5 := by omega
        exact false_of_psu_threeNF h2 hB hO hm'
          (SectionRank.statedClassicalModel_of_mulEquiv eB hT)
      · exact hclass hT (Or.inr (Or.inl ⟨rfl, by omega⟩))
          (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
          (by
            simp only [EvenSmallLie.CatalogOrders.lieExp]
            have hP : 3 * 4 ≤ (n - 2 - 1) * (n - 2) := Nat.mul_le_mul (by omega) (by omega)
            have hP2 : 6 ≤ (n - 2 - 1) * (n - 2) / 2 := by omega
            calc 7 ≤ 2 * 6 := by norm_num
              _ ≤ m * ((n - 2 - 1) * (n - 2) / 2) := Nat.mul_le_mul hm' hP2)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT
  | symplectic n m hn hm hnm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h3, hT⟩ | ⟨rfl, hT⟩
    · exact hclass hT (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 2 * 2 ≤ (n - 1) * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
          calc 7 ≤ 2 * (2 * 2) := by norm_num
            _ ≤ m * ((n - 1) * (n - 1)) := Nat.mul_le_mul hm' hP)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT
  | orthPlus n m hn hm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h6, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩
    · exact hclass hT (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 4 * 3 ≤ (n - 2) * (n - 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
          calc 7 ≤ 2 * (4 * 3) := by norm_num
            _ ≤ m * ((n - 2) * (n - 2 - 1)) := Nat.mul_le_mul hm' hP)
    · exact hclass hT (Or.inl ⟨rfl, le_rfl⟩) (by simp [EvenSmallLie.CatalogOrders.lieMin])
        (by simp only [EvenSmallLie.CatalogOrders.lieExp]; omega)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT
  | orthMinus n m hn hm K hK b c hbc e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h6, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩
    · exact hclass hT (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)))
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 4 * 3 ≤ (n - 2) * (n - 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
          calc 7 ≤ 2 * (4 * 3) := by norm_num
            _ ≤ m * ((n - 2) * (n - 2 - 1)) := Nat.mul_le_mul hm' hP)
    · exact hclass hT (Or.inr (Or.inl ⟨rfl, le_rfl⟩)) (by simp [EvenSmallLie.CatalogOrders.lieMin])
        (by simp only [EvenSmallLie.CatalogOrders.lieExp]; omega)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT

theorem step76NF_of_certs
    (h2 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → RankTwoBenderType (rankTwoQuot A) →
        SuzukiModel (rankTwoQuot A) 2 3 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru)
    (h4 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        (standardComponentOddCore G = ⊥ → m = 2) ∧
        (m = 2 →
          (NativeSporadic.IsSporadic (rankTwoX A ⧸ Subgroup.center (rankTwoX A)) .Suz ∧
            Nat.card (Subgroup.center (rankTwoX A)) ∣ 3) ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
        (standardComponentOddCore G = ⊥ →
          NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
            (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX A) .He)))
    (hSuz : SuzL34DiagInput) (h75 : Asc75Theorem4) (h32 : AS76b.Lemma32)
    (h34 : Asc08Lemma34) (h5 : Asc08Lemma310NF) (hSp44 : Sp44EndgameNF) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
      (R T Y W L : Subgroup G) (g : G), RankTwoHypNF G A → Hyp31 A →
      RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75Y D T Y W L →
      (∀ (G' : Type) [Group G'] [Finite G'] (A' : Subgroup G'), Nat.card G' < Nat.card G →
        RankTwoHypNF G' A' → standardComponentOddCore G' = ⊥ →
          ¬ RankTwoClassicalEvenType (rankTwoQuot A')) → False :=
  step76NF_of_inputs h2 h4 hSuz h75 h32 h34 h5
    (J2Std.j2StdFacts_of_check J2Std.j2_stdCheck) hSp44

theorem rankTwoClassicalEvenStandardNF_of_steps (hII : ClassicalHypII) (h74 : Step74)
    (h75 : Step75Y)
    (h76 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
      (R T Y W L : Subgroup G) (g : G), RankTwoHypNF G A → Hyp31 A →
      RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75Y D T Y W L →
      (∀ (G' : Type) [Group G'] [Finite G'] (A' : Subgroup G'), Nat.card G' < Nat.card G →
        RankTwoHypNF G' A' → standardComponentOddCore G' = ⊥ →
          ¬ RankTwoClassicalEvenType (rankTwoQuot A')) → False) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → ¬ RankTwoClassicalEvenType (rankTwoQuot A) := by
  suffices h : ∀ (N : ℕ) (G : Type) [Group G] [Finite G] (A : Subgroup G), Nat.card G = N →
      RankTwoHypNF G A → standardComponentOddCore G = ⊥ →
        ¬ RankTwoClassicalEvenType (rankTwoQuot A) by
    intro G _ _ A hH hO
    exact h _ G A rfl hH hO
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ _ A hN hH hO hT
    obtain ⟨D⟩ := nonempty_classicalModel hT
    have hA := hyp31_ofNF hII hH hO hT
    obtain ⟨R, T, g, hc⟩ := h74 G A D hA hT
    obtain ⟨Y, W, L, hl⟩ := h75 G A D R T g hA hT hc
    exact h76 G A D R T Y W L g hH hA hT hc hl fun G' _ _ A' hlt hH' hO' =>
      ih _ (hN ▸ hlt) G' A' rfl hH' hO'

theorem rankTwoClassicalEvenStandardNF
    : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      standardComponentOddCore G = ⊥ → ¬ RankTwoClassicalEvenType (rankTwoQuot A) := by
  have hBender := rankTwoBenderStandardNF
  have hL3 := rankTwoL3EvenStandardNF
  have h32 := RankTwoFoundation.lemma32
  have h33 := RankTwoFoundation.lemma33Three
  have h4 := RankTwoFoundation.asc75Theorem4
  have h2 := RankTwoFoundation.asc76Theorem2
  have h34 := AS76b.asc08Lemma34
  have h310 : Asc08Lemma310NF := CFSG.RankThree.GF2n.Tim79a.asc08Lemma310NF_holds
  have hF : Classical222Facts := by
    refine ⟨fun fam => ?_, fun fam => ?_, fun fam => ?_, symplecticJ23, orthJ4⟩
    · cases fam
      exacts [deltaAlpha_linear, deltaAlpha_unitary, deltaAlpha_symplectic, deltaAlpha_orthPlus,
        deltaAlpha_orthMinus]
    · cases fam
      exacts [autAlpha_linear, autAlpha_unitary, autAlpha_symplectic, autAlpha_orthPlus,
        autAlpha_orthMinus]
    · cases fam
      exacts [pairOrbitFree_linear, pairOrbitFree_unitary, pairOrbitFree_symplectic,
        pairOrbitFree_orthPlus, pairOrbitFree_orthMinus]
  have h222 := classical222Large_of hF
  have I : Inputs74 := ⟨h32, h4, h34, h2, classicalOutCommOdd, classicalCentralizerCharTwo,
    h222, classicalJSylow_of hF⟩
  have hExc := classical222TwoExcCenter_of exc213_PSU_four exc213_PSU_six exc213_PSp_three
    exc213_POmegaPlus_four
  have hTwo := classical222Two_of hExc deltaAlphaTwo_symplectic deltaAlphaTwo_orthPlus
    deltaAlphaTwo_orthMinus symplecticJ23Two orthJ4Two
    (classical222TwoB_of linearCaseIITwo unitaryCaseIITwo orthCaseIITwo)
  have h73 := step73_of I h33 hTwo linearTwoResidual symplecticTwoOut
  have h74 := step74_of I classicalSplit classicalPrimaryPerfect h33 h73 symplecticTypeAPerfect
    symplecticCase1Type symplecticSplitA symplecticPairA2
  have hRC : ClassicalRigidChoice := ⟨rigidLeviChoice_linear, rigidLeviChoice_unitary,
    rigidLeviChoice_orthPlus, rigidLeviChoice_orthMinus⟩
  have h75 := step75Y_of h32 h4 h34 h2 classicalOutCommOdd classicalCentralizerCharTwo h222
    hRC symplecticYChoice symplecticOddCentralizerO2
  have hSp44 := sp44EndgameNF_of h32 h310 J2Std.j2A4Facts m12AutThreeFive
  have h76 := step76NF_of_certs hBender hL3 RankTwoExceptional.suzL34DiagInput h4 h32 h34 h310
    hSp44
  exact rankTwoClassicalEvenStandardNF_of_steps
    (classicalHypII_of_multiplier classicalEvenMultiplier) h74 h75 h76

end CFSG.StandardComponent.AschbacherSeitz
