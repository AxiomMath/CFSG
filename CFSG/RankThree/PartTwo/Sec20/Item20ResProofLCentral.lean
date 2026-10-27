module

import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec20.OneBasics
public import CFSG.RankThree.PartTwo.Sec20.OneContraMax
public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofL
public import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step209XAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    IsBlock M (kTwenty M c) → vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) →
    ∀ n : ℕ, Odd n → IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n →
    ∀ y : G, (n = 1 ∧ y ^ 7 = 1 ∨ 1 < n ∧ y ^ 5 = 1) →
      y ∈ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) →
      (∀ x ∈ normalClosureIn (kTwenty M c ⊓ N) c, y * x * y⁻¹ * x⁻¹ ∈
        CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c)) →
        y ∈ Subgroup.normalizer (vTwenty M c T : Set G)

theorem isSimpleGroup_projSL_three_galois_four :
    IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 2) (n := 3)
    (by norm_num) (Or.inl le_rfl)).2.1
  set e : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
        (GaloisField 2 2)).symm).trans
      (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm
  exact e.symm.isSimpleGroup

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_pCoreOf_normalClosureIn_core {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyL : y ∈ L)
    (hyX : y ∈ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G)) :
    ∀ x ∈ normalClosureIn (kTwenty M c ⊓ N) c, y * x * y⁻¹ * x⁻¹ ∈
      CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL (mem_of_hyp201 hT.toHyp201)
  have hXN : normalClosureIn (kTwenty M c ⊓ N) c ≤ N :=
    (normalClosureIn_le (show c ∈ kTwenty M c ⊓ N from ⟨hcK, hcN⟩)).trans inf_le_right
  have hNO : N ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hN ▸ CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hle : normalClosureIn (kTwenty M c ⊓ N) c ⊓ CFSG.Open.pCoreOf 2 L ≤
      CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) (hNO (hXN hx)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right)
  intro x hx
  refine hle ⟨?_, ?_⟩
  · have h1 : y * x * y⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c :=
      (Subgroup.mem_normalizer_iff.mp hyX x).mp hx
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx)
  · have h1 := commutator_mem_pCoreOf_of_mem_normalClosureIn_core hT hN hAL hx y hyL
    have : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ h1

omit [Finite G] in
theorem conj_mem_closure_pow_eq_one {L : Subgroup G} {r : ℕ} {l : G} (hl : l ∈ L) {y : G}
    (hy : y ∈ Subgroup.closure {z : G | z ∈ L ∧ z ^ r = 1}) :
    l * y * l⁻¹ ∈ Subgroup.closure {z : G | z ∈ L ∧ z ^ r = 1} := by
  have hmap : (Subgroup.closure {z : G | z ∈ L ∧ z ^ r = 1}).map (MulAut.conj l).toMonoidHom ≤
      Subgroup.closure {z : G | z ∈ L ∧ z ^ r = 1} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, ⟨hzL, hzr⟩, rfl⟩
    refine Subgroup.subset_closure ⟨L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hzr]
    group
  exact hmap ⟨y, hy, rfl⟩

theorem closure_pow_eq_one_eq {L : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrL : r ∣ Nat.card L) : Subgroup.closure {z : G | z ∈ L ∧ z ^ r = 1} = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  set Y := Subgroup.closure {z : G | z ∈ L ∧ z ^ r = 1} with hY
  have hYL : Y ≤ L := by
    rw [hY, Subgroup.closure_le]
    rintro z ⟨hz, -⟩
    exact hz
  refine le_antisymm hYL ?_
  set Y' : Subgroup ↥L := Y.subgroupOf L with hY'
  have hY'n : Y'.Normal := ⟨fun a ha b => by
    rw [hY', Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_closure_pow_eq_one b.2 ha⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrL
  have hyY' : y ∈ Y' := by
    rw [hY', Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨y.2, ?_⟩
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using congrArg Subtype.val this
  have hyO : y ∉ CFSG.pCore 2 ↥L := by
    intro hyO
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y, hyO⟩
    have hk' : y ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : r ∣ 2 ^ k := hy ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  have hmapn : (Y'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hY'n.map _ (QuotientGroup.mk'_surjective _)
  have hmap : Y'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    have := hs
    have := hmapn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Y'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
    · exfalso
      have hm : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈
          Y'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := Subgroup.mem_map_of_mem _ hyY'
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
      exact hyO hm
    · exact h
  have hsup : Y' ⊔ CFSG.pCore 2 ↥L = ⊤ := by
    have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) Y'
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hY'top := eq_top_of_sup_pCore_eq_top hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥L) ∈ Y' := hY'top ▸ Subgroup.mem_top _
  exact this

theorem step209LCentral_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Assembly.RankThreeEven.projSL 3
      (GaloisField 2 2)))
    (hLp : ⁅L, L⁆ = L) (hLM : ¬ L ≤ M) (hTN : T ≤ N)
    (h7 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (h8 : IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n)
    (hAut : ∀ n : ℕ, Odd n → IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n →
      ∀ y : G, (n = 1 ∧ y ^ 7 = 1 ∨ 1 < n ∧ y ^ 5 = 1) →
        y ∈ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) →
        (∀ x ∈ normalClosureIn (kTwenty M c ⊓ N) c, y * x * y⁻¹ * x⁻¹ ∈
          CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c)) →
          y ∈ Subgroup.normalizer (vTwenty M c T : Set G))
    (hLX : L ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G)) : False := by
  obtain ⟨hblock, hVO, n, hn, hnat⟩ := h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, hr2, hrn, hr20160⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      (n = 1 ∧ r = 7 ∨ 1 < n ∧ r = 5) ∧ r ∣ 20160 := by
    rcases Nat.lt_or_ge 1 n with h | h
    · exact ⟨5, by norm_num, by norm_num, Or.inr ⟨h, rfl⟩, by norm_num⟩
    · have h1 : n = 1 := by
        obtain ⟨k, rfl⟩ := hn
        omega
      exact ⟨7, by norm_num, by norm_num, Or.inl ⟨h1, rfl⟩, by norm_num⟩
  have hyV : ∀ y ∈ L, y ^ r = 1 → y ∈ Subgroup.normalizer (vTwenty M c T : Set G) := by
    intro y hy hyr
    refine hAut n hn hnat y ?_ (hLX hy)
      (commutator_mem_pCoreOf_normalClosureIn_core hT hN hAL hy (hLX hy))
    rcases hrn with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · exact Or.inl ⟨h1, hyr⟩
    · exact Or.inr ⟨h1, hyr⟩
  obtain ⟨e⟩ := hLq
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := isSimpleGroup_projSL_three_galois_four
    exact e.isSimpleGroup
  have hrL : r ∣ Nat.card L := by
    rw [card_eq_of_nonempty_quotient e]
    exact hr20160.mul_right _
  have hgen := closure_pow_eq_one_eq hLp hs hr hr2 hrL
  have hLV : L ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    rw [← hgen, Subgroup.closure_le]
    rintro y ⟨hy, hyr⟩
    exact hyV y hy hyr
  have hV2 : IsPGroup 2 (vTwenty M c T) :=
    hVO ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  have hV1 : vTwenty M c T ≠ ⊥ := by
    obtain ⟨-, F, _, _, hF, -, -, -, β, -⟩ := hnat
    intro hbot
    have hcard : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (vTwenty M c T) :=
      Nat.card_congr β.symm.toEquiv
    rw [hbot, Subgroup.card_bot] at hcard
    have h3 : Nat.card (Multiplicative (Fin 3 → F)) = (2 ^ n) ^ 3 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card,
        Fintype.card_fun, Fintype.card_fin, hF]
    rw [h3] at hcard
    have h1 : 1 < (2 ^ n) ^ 3 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow_iff.mpr (by
        rintro rfl
        have : Fintype.card F = 1 := by rw [hF, pow_zero]
        exact absurd this (Fintype.one_lt_card).ne'))
    omega
  have hMV : M ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    rw [hVO]
    exact (le_normalizer_normalClosureIn M c).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hNV := normalizer_eq_of_le hT.mem_scriptM.1 hV1 hV2 hMV
  exact hLM (hNV ▸ hLV)

theorem step209LCentral_of_xAut (h184 : Sec18.Item184_1) (hAut : Step209XAut) :
    Step209LCentral := by
  intro G _ _ A M L N c T hT hTN h7 h8 hLX
  exfalso
  obtain ⟨H, hH18, -, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  have hLp : ⁅L, L⁆ = L := by
    rw [hL]
    exact Sec18.commutator_eq_of_mem_oTwoComponentsIn
      (mem_scriptH_iff.mp hH18.mem_scriptH).2.2.1
  exact step209LCentral_core hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One)
    (nonempty_quotient_of_hyp201One h184 hT.hyp201One) hLp (not_le_of_hyp201One hT.hyp201One)
    hTN h7 h8 (fun n hn hnat y hyr hyX hyc => hAut G A M L N c T hT hTN h7 h8.1 h8.2.1 n hn hnat
      y hyr hyX hyc) hLX

end CFSG.RankThree.PartTwo.Sec20
