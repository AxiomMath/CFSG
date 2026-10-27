module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem delta_mono {Y Z : Subgroup G} (h : Y ≤ Z) : delta A LB Y ≤ delta A LB Z :=
  sSup_le fun _ hQ => le_delta hQ.1 (hQ.2.trans h)

omit [Finite G] in
theorem deltaZero_mono {Y Z : Subgroup G} (h : Y ≤ Z) : deltaZero A LB Y ≤ deltaZero A LB Z :=
  sSup_le fun _ hQ => le_deltaZero hQ.1 (hQ.2.trans h)

omit [Finite G] in
theorem card_sup_dvd_card_mul {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) ∣ Nat.card H * Nat.card K := by
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK
  have hq : Nat.card (↥(H ⊔ K) ⧸ K.subgroupOf (H ⊔ K)) ∣ Nat.card H := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hs : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K)), hs]
  exact mul_dvd_mul_right hq _

omit [Finite G] in
theorem isPiSubgroup_piCompl_sup {H K : Subgroup G} (hH : IsPiSubgroup (piCompl 3) H)
    (hK : IsPiSubgroup (piCompl 3) K) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    IsPiSubgroup (piCompl 3) (H ⊔ K) := by
  have hH3 := (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hH
  have hK3 := (isPiSubgroup_piCompl_iff Nat.prime_three K).mp hK
  refine (isPiSubgroup_piCompl_iff Nat.prime_three (H ⊔ K)).mpr fun h3 => ?_
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans (card_sup_dvd_card_mul hHK)) with h | h
  exacts [hH3 h, hK3 h]

omit [Finite G] in
theorem le_normalizer_sup {H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := fun x hx =>
  mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_sup, Late.map_conj_eq_of_mem_normalizer (hH hx),
      Late.map_conj_eq_of_mem_normalizer (hK hx)])

omit [Finite G] in
@[expose] def commutatorInSubgroup (Q N : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ Subgroup.normalizer (N : Set G) ∧ ∀ q ∈ Q, ⁅q, k⁆ ∈ N}
  mul_mem' := by
    intro k l hk hl
    refine ⟨mul_mem hk.1 hl.1, fun q hq => ?_⟩
    have h : ⁅q, k * l⁆ = ⁅q, k⁆ * (k * ⁅q, l⁆ * k⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact mul_mem (hk.2 q hq) ((Subgroup.mem_normalizer_iff.mp hk.1 _).mp (hl.2 q hq))
  one_mem' := ⟨one_mem _, fun q _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
  inv_mem' := by
    intro k hk
    refine ⟨inv_mem hk.1, fun q hq => ?_⟩
    have h : ⁅q, k⁻¹⁆ = k⁻¹ * ⁅q, k⁆⁻¹ * k⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem hk.1) _).mp (inv_mem (hk.2 q hq))

omit [Finite G] in
theorem mem_commutatorInSubgroup {Q N : Subgroup G} {k : G} :
    k ∈ commutatorInSubgroup Q N ↔ k ∈ Subgroup.normalizer (N : Set G) ∧ ∀ q ∈ Q, ⁅q, k⁆ ∈ N :=
  Iff.rfl

omit [Finite G] in
theorem le_normalizer_inf_centralizer (hAab : IsMulCommutative A) {Q B : Subgroup G}
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hB : B ≤ A) :
    A ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf hAQ (((Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
    (Subgroup.centralizer_le hB)).trans Subgroup.le_normalizer)

omit [Finite G] in
theorem commutator_inf_centralizer_le (hAab : IsMulCommutative A) {Q B : Subgroup G}
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hB : B ≤ A) :
    ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤ Q ⊓ Subgroup.centralizer (B : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_inf_centralizer hAab hAQ hB)

theorem commutator_inf_centralizer_mem_scriptQZero (hA : IsE27 A) {Q B : Subgroup G}
    (hQ : Q ∈ scriptQ A LB) (hB : B ≤ A) :
    ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ ∈ scriptQZero A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Q ⊓ Subgroup.centralizer (B : Set G) with hR
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := le_normalizer_inf_centralizer hA.1.1 hQ.1.2.2 hB
  have hR3 : ¬ 3 ∣ Nat.card R := fun h =>
    (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.2.1
      (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcomm : ⁅R, A⁆ ≤ R := commutator_inf_centralizer_le hA.1.1 hQ.1.2.2 hB
  have hAcomm : A ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.normalizer_commutator_ge_left A R
  exact ⟨mem_scriptQ_of_le hQ (hcomm.trans inf_le_left) hAcomm,
    (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A R
      hA.isPGroup hR3 hAR).symm⟩

theorem le_iSup_commutator_centralizer (hA : IsE27 A) {Q : Subgroup G}
    (hQ3 : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQA : Q = ⁅Q, A⁆) :
    Q ≤ ⨆ (B : Subgroup G) (_ : IsHyperplane A B),
      ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := ⨆ (B : Subgroup G) (_ : IsHyperplane A B),
    ⁅Q ⊓ Subgroup.centralizer (B : Set G), A⁆ with hJ
  set C := Q ⊓ Subgroup.centralizer (A : Set G) with hC
  have hAQB : ∀ B : Subgroup G, B ≤ A →
      A ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    fun B hB => le_normalizer_inf_centralizer hA.1.1 hAQ hB
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := by
    intro x hx
    refine mem_normalizer_of_map_conj_eq ?_
    rw [hJ, Subgroup.map_iSup]
    refine iSup_congr fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun hB => ?_
    rw [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hAQB B hB.1 hx),
      Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)]
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := by
    intro c hc
    have hcA : c ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp hc).2
    refine mem_normalizer_of_map_conj_eq ?_
    rw [hJ, Subgroup.map_iSup]
    refine iSup_congr fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun hB => ?_
    have hcB : c ∈ Subgroup.normalizer
        ((Q ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans ((Subgroup.centralizer_le hB.1).trans Subgroup.le_normalizer)) hc
    rw [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer hcB,
      Late.map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (A : Set G) hcA)]
  have hQJC : Q ≤ J ⊔ C := by
    refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
      (by rw [hA.2]; norm_num) hAQ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
      fun B hBA hB9 => ?_
    have hB : IsHyperplane A B := ⟨hBA, by rw [hA.2, hB9]; norm_num⟩
    have hR3 : ¬ 3 ∣ Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) := fun h =>
      hQ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three A (Q ⊓ Subgroup.centralizer (B : Set G)) hA.isPGroup hR3 (hAQB B hBA)]
    exact sup_le_sup (le_iSup₂_of_le B hB le_rfl) (inf_le_inf_right _ inf_le_left)
  rw [hQA, Subgroup.commutator_le]
  intro x hx α hα
  have hx' : x ∈ ((J : Set G) * (C : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left J C hCJ]
    exact hQJC hx
  obtain ⟨j, hj, c, hc, rfl⟩ := hx'
  have hcα : c * α = α * c :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 α hα).symm
  have hkey : ⁅j * c, α⁆ = j * (α * j⁻¹ * α⁻¹) := by
    rw [commutatorElement_def]
    calc j * c * α * (j * c)⁻¹ * α⁻¹ = j * (c * α) * c⁻¹ * j⁻¹ * α⁻¹ := by group
      _ = j * (α * c) * c⁻¹ * j⁻¹ * α⁻¹ := by rw [hcα]
      _ = j * (α * j⁻¹ * α⁻¹) := by group
  rw [hkey]
  exact mul_mem hj ((Subgroup.mem_normalizer_iff.mp (hAJ hα) j⁻¹).mp (inv_mem hj))

theorem deltaZero_eq_iSup (hA : IsE27 A) (Y : Subgroup G) :
    deltaZero A LB Y = ⨆ (B : Subgroup G) (_ : IsHyperplane A B),
      deltaZero A LB (Y ⊓ Subgroup.centralizer (B : Set G)) := by
  refine le_antisymm (sSup_le fun Q hQ => ?_) (iSup₂_le fun B _ => deltaZero_mono inf_le_left)
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.1.2.1
  refine (le_iSup_commutator_centralizer hA hQ3 hQ.1.1.1.2.2 hQ.1.2).trans
    (iSup₂_mono fun B hB => ?_)
  exact le_deltaZero (commutator_inf_centralizer_mem_scriptQZero hA hQ.1.1 hB.1)
    ((commutator_inf_centralizer_le hA.1.1 hQ.1.1.1.2.2 hB.1).trans (inf_le_inf_right _ hQ.2))

theorem commutator_inf_centralizer_le_delta (h444 : Item1444 A LB) (hAab : IsMulCommutative A)
    {Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {Q : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a})) (hQY : Q ≤ Y) :
    ⁅Q, pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer {a}⁆ ≤ delta A LB (pPrimeCoreOf 3 Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := pPrimeCoreOf 3 Y with hK
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    hY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQY.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hAa : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    le_trans (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))) Subgroup.le_normalizer
  have hK3 : IsPiSubgroup (piCompl 3) K :=
    (isPiSubgroup_piCompl_iff Nat.prime_three K).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y))
  have hS : K ⊓ Subgroup.centralizer {a} ∈
      invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3) :=
    ⟨inf_le_right, isPiSubgroup_piCompl_of_le hK3 inf_le_left,
      sup_le (le_normalizer_inf hAK hAa)
        (le_normalizer_inf hQK (hQ.2.trans Subgroup.le_normalizer))⟩
  obtain ⟨hle, -⟩ := commutator_mem_invariantPiSubgroups ⟨hQ.1.1, hQ.2⟩ hS
  exact le_delta (h444 a ha ha1 Q hQ _ hS).1 (hle.trans inf_le_left)

theorem commutator_le_of_le_centralizer (hA : IsE27 A) (h444 : Item1444 A LB)
    {Y N : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hIN : delta A LB (pPrimeCoreOf 3 Y) ≤ N)
    (hKN : pPrimeCoreOf 3 Y ≤ Subgroup.normalizer (N : Set G)) {B Q : Subgroup G}
    (hB : IsHyperplane A B) (hQ : Q ∈ scriptQZero A LB)
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅Q, pPrimeCoreOf 3 Y⁆ ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAK : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    hY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hB9 : 3 ^ 2 ≤ Nat.card B := by
    have h := hB.2
    rw [hA.2] at h
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h9]
    omega
  have hKT : pPrimeCoreOf 3 Y ≤ commutatorInSubgroup Q N := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three (Sec5.isElemAbelian_of_le hA.1 hB.1)
      hB9 (hB.1.trans hAK) (coprime_card_pPrimeCoreOf 3 Y) fun v hv hv1 k hk => ?_
    refine mem_commutatorInSubgroup.mpr ⟨hKN (Subgroup.mem_inf.mp hk).1, fun q hq => ?_⟩
    have hQv : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {v}) :=
      ⟨hQ, hQY.trans (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)))⟩
    exact hIN (commutator_inf_centralizer_le_delta h444 hA.1.1 hY (hB.1 hv) hv1 hQv
      (hQY.trans inf_le_left) (Subgroup.commutator_mem_commutator hq hk))
  rw [Subgroup.commutator_le]
  intro q hq k hk
  exact (mem_commutatorInSubgroup.mp (hKT hk)).2 q hq

theorem rank3II_14_7_le (hA : IsE27 A) (h444 : Item1444 A LB) {Y N : Subgroup G}
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) (hIN : delta A LB (pPrimeCoreOf 3 Y) ≤ N)
    (hKN : pPrimeCoreOf 3 Y ≤ Subgroup.normalizer (N : Set G))
    (hXN : deltaZero A LB Y ≤ Subgroup.normalizer (N : Set G)) :
    ⁅deltaZero A LB Y, pPrimeCoreOf 3 Y⁆ ≤ N := by
  have hXT : deltaZero A LB Y ≤ commutatorInSubgroup (pPrimeCoreOf 3 Y) N := by
    rw [deltaZero_eq_iSup hA Y]
    refine iSup₂_le fun B hB => sSup_le fun Q hQ x hx => ?_
    have hxX : x ∈ deltaZero A LB Y := deltaZero_mono inf_le_left (le_deltaZero hQ.1 hQ.2 hx)
    refine mem_commutatorInSubgroup.mpr ⟨hXN hxX, fun k hk => ?_⟩
    have h := Subgroup.commutator_le.mp
      (commutator_le_of_le_centralizer hA h444 hY hIN hKN hB hQ.1 hQ.2) x hx k hk
    rw [← commutatorElement_inv]
    exact inv_mem h
  rw [Subgroup.commutator_le]
  intro x hx k hk
  rw [← commutatorElement_inv]
  exact inv_mem ((mem_commutatorInSubgroup.mp (hXT hx)).2 k hk)

omit [Finite G] in
theorem delta_mem_scriptQ (hA : IsE27 A) (h146 : Item146 A LB) {Z : Subgroup G}
    (hZ : Z ∈ invariantPiSubgroups ⊤ A (piCompl 3)) : delta A LB Z ∈ scriptQ A LB := by
  set D := delta A LB Z with hD
  have hDD : D = delta A LB D :=
    le_antisymm (sSup_le fun Q hQ => le_delta hQ.1 (le_delta hQ.1 hQ.2)) (delta_mono (delta_le Z))
  have hDinv : D ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_of_le hZ.2.1 (delta_le Z),
      le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩
  refine ⟨hDinv, fun B hB => ?_⟩
  have hBbot : B ≠ ⊥ := by
    intro h
    have h2 := hB.2
    rw [h, Subgroup.card_bot, hA.2] at h2
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBbot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨hDb, hDbQ⟩ := h146 D hDinv hDD b (hB.1 hbB) hb1'
  have hmem : D ⊓ Subgroup.centralizer {b} ∈ scriptQ A LB := by
    rw [hDb]
    exact hDbQ.1
  have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer {b} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
  calc D ⊓ Subgroup.centralizer (B : Set G)
      = (D ⊓ Subgroup.centralizer {b}) ⊓ Subgroup.centralizer (B : Set G) := by
        rw [inf_assoc, inf_eq_right.mpr hCB]
    _ ≤ qBound A LB B := hmem.2 B hB

omit [Finite G] in
theorem delta_le_normalizer_delta
    (hΔ : ∀ Z ∈ invariantPiSubgroups ⊤ A (piCompl 3), delta A LB Z ∈ scriptQ A LB)
    {Y K : Subgroup G} (hK : K ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) :
    delta A LB Y ≤ Subgroup.normalizer (delta A LB K : Set G) := by
  refine sSup_le fun Q hQ => ?_
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.2.trans hYK
  have hZ : Q ⊔ K ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_sup hQ.1.1.2.1 hK.2.1 hQK,
      le_normalizer_sup hQ.1.1.2.2 hK.2.2⟩
  have hDZ := hΔ _ hZ
  have hDK : delta A LB K = delta A LB (Q ⊔ K) ⊓ K := by
    refine le_antisymm (le_inf (delta_mono le_sup_right) (delta_le K)) ?_
    exact le_delta (mem_scriptQ_of_le hDZ inf_le_left (le_normalizer_inf hDZ.1.2.2 hK.2.2))
      inf_le_right
  rw [hDK]
  exact le_normalizer_inf ((le_delta hQ.1 le_sup_left).trans Subgroup.le_normalizer) hQK

theorem rank3II_14_7_reduction (hA : IsE27 A) (h444 : Item1444 A LB) (h146 : Item146 A LB)
    {Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hKN : pPrimeCoreOf 3 Y ≤ Subgroup.normalizer (delta A LB (pPrimeCoreOf 3 Y) : Set G)) :
    ⁅deltaZero A LB Y, pPrimeCoreOf 3 Y⁆ ≤ delta A LB (pPrimeCoreOf 3 Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : pPrimeCoreOf 3 Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)),
      hY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)⟩
  refine rank3II_14_7_le hA h444 hY le_rfl hKN ?_
  exact (deltaZero_le_delta Y).trans (delta_le_normalizer_delta
    (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hK (le_normalizer_pPrimeCoreOf 3 Y))

end CFSG.RankThree.PartTwo.Sec14
