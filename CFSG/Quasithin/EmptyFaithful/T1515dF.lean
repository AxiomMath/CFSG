module

public import CFSG.Quasithin.EmptyFaithful.T1515dStruct
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_of_perfect_of_isSimple1521d {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup Q) : CFSG.IsQuasisimple Q := by
  have := hs
  have hnt : Nontrivial Q := hs.toNontrivial
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.2 fun y _ => hcon y x
    have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
      have := hperf.commutator_eq_top
      rwa [_root_.commutator_def] at this
    rw [h1] at hc
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    exact hx (Subgroup.mem_bot.1 (hc ▸ Subgroup.mem_top x))
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : (Q ⧸ Subgroup.center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      simpa using this)⟩

omit [Finite G] in
theorem isQuasisimple_pCoreQuot_of_block1521d {L : Subgroup G} (hsh : IsShort2 L)
    (hty : IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rcases hsh.2.2.2.1 with h | h3
  · exact h
  · exfalso
    rcases hty with ⟨α, hα, hker, -⟩ | ⟨n, hn, F, _, _, hF, α, hα, hker, -⟩
    · have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hα)
      have h1 := Nat.card_congr e.toEquiv
      rw [h3, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h1
      norm_num [Nat.factorial] at h1
    · have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hα)
      have h1 := Nat.card_congr e.toEquiv
      have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
      have hfin : Finite F := inferInstance
      rw [h3, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF'] at h1
      have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hI : Finset.Icc 2 2 = {2} := by decide
      rw [hI, Finset.prod_singleton] at h1
      norm_num at h1
      have h2 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
      have h3' := Nat.mul_le_mul hq h2
      omega

theorem isQuasisimple_pCoreQuot_of_component1521d {L H : Subgroup G} (hc : IsComponentOf L H)
    (hO : oddCoreIn H = ⊥) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hc.2.2
  have h2 : IsPGroup 2 ↥(Subgroup.center ↥L) := isPGroup_two_center_of_isComponentOf1515c hc hO
  have hcenter_le : Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, h2⟩
  have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have hpc_le : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (CFSG.pCore 2 ↥L) with h | h
    · exact h
    · exfalso
      have hpg : IsPGroup 2 ↥L := fun x => by
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
          ⟨x, by rw [h]; exact Subgroup.mem_top x⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnil : Group.IsNilpotent ↥L := hpg.isNilpotent
      have hnt : Nontrivial ↥L := by
        have := hq.2.toNontrivial
        exact (QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial
      exact Group.IsPerfect.not_isSolvable ↥L (inferInstance : Group.IsSolvable _)
  have hZ : CFSG.pCore 2 ↥L = Subgroup.center ↥L := le_antisymm hpc_le hcenter_le
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hZ.symm)).1 hq.2
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact isQuasisimple_of_perfect_of_isSimple1521d hperf hs

theorem lemma15121InputU_of (hSt : Struct15121) (hI20 : Lemma15120InputU)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) : Lemma15121InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hx18 hLc hant
  by_contra hnot
  have hq := hC.qtfe
  have hM := hC.mf
  have hS := hC.setting
  have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hant with ⟨-, hbl, hty⟩ | ⟨hco, -⟩
    · exact isQuasisimple_pCoreQuot_of_block1521d hbl.1 hty
    · exact isQuasisimple_pCoreQuot_of_component1521d hco h19.one
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hqs, hnot⟩
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18.four hpc
  have h15' := h15 G T Mc M hq hM hC.ce
  have h20 : Lemma15120Concl T Mc M Z₁ L := by
    obtain ⟨h2, h3⟩ := hI20 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL hx18
    exact ⟨lemma_15_1_20_sylow h18.four hL20,
      lemma_15_1_20_one (h1416 G T Mc hq).1 hM h15' hL20, h2,
      fun hc => ⟨isPGroup_two_center_of_isComponentOf1515c hc h19.one, h3 hc⟩⟩
  have hS1 : s1516 T Z₁ ≠ ⊥ := fun h =>
    hpc (le_bot_iff.1 (h ▸ pCoreOf_le_of_isSylowTwoOf h18.four))
  have hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS h18.four.2.1 hS1).trans h17.cgs
  have h197 := h19.seven L hLc hqs hnot
  have hV2V : V₂ ≤ V154 T Mc M := hS.v2_le
  rcases hSt G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 hant with
    ⟨B₀, hBZ, hBN, hB2, hBS⟩ | hb
  ·
    have hBM : B₀ ≤ M := hBN.trans hNJ
    have hB1 : B₀ ≤ M ⊓ Mc ⊓ g1_1516 Z₁ := fun b hb => ⟨⟨hBM hb, (hBZ hb).2⟩, (hBZ hb).1⟩
    have hBC : B₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
      have h1 : oTwoUpper B₀ ≤ oTwoUpper (M ⊓ Mc ⊓ g1_1516 Z₁) := oTwoUpper_mono hB1
      rw [hB2, hx18.two_eq] at h1
      exact h1.trans (oTwoUpper_le _)
    apply h197.2
    have hc : L ≤ Subgroup.centralizer (V₂ : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hBS v hv (fun b hb => Subgroup.mem_centralizer_iff.mp (hBC hb).2 v (hV2V hv)) l hl
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hc
  ·
    obtain ⟨p, hp, Y, hYMG, hYJ, hYp, hSY, hVY⟩ := hS.p_sub
    have hYJ' : Y ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) := by
      rw [h17.jS]
      exact hYJ
    have hLY : ⁅L, Y⁆ = ⊥ := hb p Y hp hYMG hYJ' hYp hSY hVY
    have hV2N : V₂ ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans h197.1
    have h1 : ⁅⁅Y, L⁆, V₂⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Y L, hLY, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅L, V₂⁆, Y⁆ = ⊥ := by
      have hle : ⁅L, V₂⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hV2N
      exact le_bot_iff.1 ((Subgroup.commutator_mono hle le_rfl).trans hLY.le)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hVY] at h3
    exact h197.2 (by rw [Subgroup.commutator_comm]; exact h3)

end CFSG.Quasithin
