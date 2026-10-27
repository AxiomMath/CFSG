module

public import CFSG.Quasithin.EmptyFaithful.T1521SAux
public import CFSG.Quasithin.EmptyFaithful.T1521SCutDefs
public import CFSG.Quasithin.EmptyFaithful.T1515dF
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithful.T1521SDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_ne_three_of_isQuasisimple1521 {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    Nat.card Q ≠ 3 := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : IsCyclic Q := isCyclic_of_prime_card (p := 3) h3
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Group.IsPerfect Q := h.1
  let _ : CommGroup Q := IsCyclic.commGroup
  exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem s1516_le_mZ1516' {T Mc M Z₁ : Subgroup G} (h18 : Lemma15118Concl T Mc M Z₁) :
    s1516 T Z₁ ≤ mZ1516 Mc Z₁ :=
  le_inf (s1516_le_g1 T Z₁) ((s1516_le T Z₁).trans (le_sup_right.trans h18.seven.1.1.2))

theorem oTwoUpper_eq_of_perfect1521 {K : Subgroup G} (hK : ⁅K, K⁆ = K) : oTwoUpper K = K := by
  refine le_antisymm (oTwoUpper_le K) ?_
  let N : Subgroup ↥K := (oTwoUpper K).subgroupOf K
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := CFSG.Quasithin.conj_mem_oTwoUpper (X := K) (g := (g : G))
      (Subgroup.le_normalizer g.2) hn
    simpa using this⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have hP : IsPGroup 2 (↥K ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := CFSG.Quasithin.exists_pow_mem_oTwoUpper K g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Finite (↥K ⧸ N) := inferInstance
  have : Group.IsNilpotent (↥K ⧸ N) := hP.isNilpotent
  have : Subsingleton (↥K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) ‹_›
  intro g hg
  have : (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at this
  exact this

theorem centralMoving1521_of_ctx {T Mc M Z₁ L : Subgroup G} (h18 : Lemma15118Concl T Mc M Z₁)
    (hLP : ⁅L, L⁆ = L) (hnot : ¬ L ≤ mZ1516 Mc Z₁) (hZ₁T : Z₁ ≤ T) :
    CentralMoving1521 (s1516 T Z₁) L := by
  by_contra hno
  refine hnot ?_
  have hgen : ∀ z : G, z ∈ T ⊓ Subgroup.centralizer (T : Set G) → z ^ 2 = 1 →
      ∀ l ∈ L, z * l = l * z := by
    intro z hzT _ l hl
    by_contra hne
    refine hno ⟨z, ?_, ?_, l, hl, hne⟩
    · show z ∈ T ⊓ Subgroup.centralizer (Z₁ : Set G)
      refine Subgroup.mem_inf.mpr ⟨hzT.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hzT.2 y (hZ₁T hy)
    · intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hzT.2 y (s1516_le T Z₁ hy)).symm
  have hC : L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact hgen z hz.1 hz.2 l hl
    | one => simp
    | mul a b _ _ ha hb =>
      rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_assoc, mul_inv_cancel, mul_one]
  calc L = oTwoUpper L := (oTwoUpper_eq_of_perfect1521 hLP).symm
    _ ≤ oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
        oTwoUpper_mono hC
    _ ≤ mZ1516 Mc Z₁ := h18.one.2

theorem borelOver_le_of_isBorelIn1521 {L P Q : Subgroup G} (hQ : IsSylowTwoOf Q L)
    (hB : IsBorelIn L P) (hQP : Q ≤ P) : L ⊓ Subgroup.normalizer (Q : Set G) ≤ P := by
  obtain ⟨S', hS', hPeq⟩ := hB
  have hPL : P ≤ L := by rw [hPeq]; exact inf_le_left
  exact borelOver_le_of_parabolic hQ hS' hPL (by rw [hPeq]) hQP

theorem borelOver_le_of_isParabolic1521 {L P Q : Subgroup G} (hQ : IsSylowTwoOf Q L)
    (hP : IsParabolic2 L P) (hQP : Q ≤ P) : L ⊓ Subgroup.normalizer (Q : Set G) ≤ P := by
  obtain ⟨hPL, S', hS', hle⟩ := hP
  exact borelOver_le_of_parabolic hQ hS' hPL hle hQP

theorem borelOver_le_of_isBorelOfBlock1521 {L P Q : Subgroup G} (hQ : IsSylowTwoOf Q L)
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 3) (hB : IsBorelOfBlock L P) (hQP : Q ≤ P)
    (hPL : P ≤ L) : L ⊓ Subgroup.normalizer (Q : Set G) ≤ P := by
  unfold IsBorelOfBlock at hB
  split_ifs at hB with hc
  · exact absurd hc hcard
  obtain ⟨S', hS', hPeq⟩ := hB
  have hO2 : pCoreOf 2 L ≤ Q := pCoreOf_le_of_isSylowTwoOf hQ
  have hO2P : pCoreOf 2 L ≤ P := hO2.trans hQP
  refine borelOver_le_of_parabolic hQ hS' hPL ?_ hQP
  rw [← hPeq]
  exact sup_le le_rfl hO2P

theorem struct15121_conclusion {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h18 : Lemma15118Concl T Mc M Z₁)
    (h19 : Lemma15119Used T Mc M Z₁ V₂) (hL : IsL1519 Mc Z₁ L)
    (horb : conjSubgroupsBy (g1_1516 Z₁) L = conjSubgroupsBy (s1516 T Z₁) L)
    (hBL : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ mZ1516 Mc Z₁)
    (hd : Nrm1521 (s1516 T Z₁) L ∨ Exc1521 (g1_1516 Z₁) (s1516 T Z₁) L) :
    (∃ B₀ : Subgroup G, B₀ ≤ mZ1516 Mc Z₁ ∧
        B₀ ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ∧ oTwoUpper B₀ = B₀ ∧
        ∀ v ∈ V₂, (∀ b ∈ B₀, v * b = b * v) → ∀ l ∈ L, v * l = l * v) ∨
    (∀ (p : ℕ) (Y : Subgroup G), (p = 3 ∨ p = 5) → Y ≤ M ⊓ g1_1516 Z₁ →
        Y ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) → IsPGroup p ↥Y →
        ((s1516 T Z₁ : Set G) * (Y : Set G) = (Y : Set G) * (s1516 T Z₁ : Set G)) →
        ⁅V₂, Y⁆ = V₂ → ⁅L, Y⁆ = ⊥) := by
  have hq := hC.qtfe
  have hMf := hC.mf
  have hSet := hC.setting
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516' h18
  rcases hd with ⟨B₀, hB₀J, hB₀N, hB₀O, hB₀v⟩ | hE
  · left
    have hB₀M : B₀ ≤ mZ1516 Mc Z₁ := hB₀J.trans (conjJoin_le_of_le hBL hSM)
    have hV2V : V₂ ≤ V154 T Mc M := hSet.v2_le
    have hV2T : V₂ ≤ T := hV2V.trans (hSet.V_le_T hq hMf)
    have hV2C : V₂ ≤ Subgroup.centralizer (Z₁ : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hab := (hSet.V_isElemAbelian hq hMf).1
      have := hab.is_comm.comm (⟨z, hSet.z1_le_V hz⟩ : ↥(V154 T Mc M)) ⟨v, hV2V hv⟩
      exact congrArg Subtype.val this
    have hV2S : V₂ ≤ s1516 T Z₁ := le_inf hV2T hV2C
    have hV2N : V₂ ≤ Subgroup.normalizer (L : Set G) :=
      le_sup_right.trans (h19.seven L hL.comp hL.quasi hL.not_le).1
    exact ⟨B₀, hB₀M, hB₀N, hB₀O, fun v hv hc l hl => hB₀v v (hV2S hv) (hV2N hv) hc l hl⟩
  · right
    intro p Y hp hYMG hYJ hYp hSY _
    have hYX : Y ≤ g1_1516 Z₁ := hYMG.trans inf_le_right
    have hYK : Y ≤ Subgroup.normalizer (conjJoin (s1516 T Z₁) L : Set G) := fun y hy =>
      mem_normalizer_conjJoin_of_orbits (s1516_le_g1 T Z₁) horb (hYX hy)
    exact hE p Y hp hYX hYJ hYK hYp hSY

theorem struct15121_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcutB : TypeCutBlock1521)
    (hcutC : TypeCutComp1521) (hBlkL2 : Dich1521BlockL2) (hBlkA5 : Dich1521BlockA5)
    (hL2 : Dich1521L2) (hSz : Dich1521Sz) (hU3 : Dich1521U3) (hL3 : Dich1521L3)
    (hSp4 : Dich1521Sp4) : Struct15121 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 hant
  have hq := hC.qtfe
  have hM := hC.mf
  have hS := hC.setting
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hS1 : s1516 T Z₁ ≠ ⊥ := fun h =>
    hpc (le_bot_iff.1 (h ▸ pCoreOf_le_of_isSylowTwoOf h18.four))
  have hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS h18.four.2.1 hS1).trans h17.cgs
  have hLN : ¬ L ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) := fun h =>
    h20.one (h.trans hNJ)
  have hSQ : IsSQTKIn (g1_1516 Z₁) := h18.five.2.2.sqtk
  have hStd : Std1521 (g1_1516 Z₁) (s1516 T Z₁) L := ⟨hSQ, h18.four, hL.comp, h20.sylow, hLN⟩
  have horb := (a3Orbits_of_a37_a38 h37 h38 (g1_1516 Z₁) (s1516 T Z₁) L hSQ h18.four hL.comp).1
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516' h18
  have hMLS : s1516 T Z₁ ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right L hSM
  have key : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ mZ1516 Mc Z₁ ∧
      (Nrm1521 (s1516 T Z₁) L ∨ Exc1521 (g1_1516 Z₁) (s1516 T Z₁) L) := by
    rcases hant with ⟨hchar, hbl, hty⟩ | ⟨hco, hcty⟩
    · have hshort : IsShort2 L := hbl.1
      have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
        isQuasisimple_pCoreQuot_of_block1521d hshort hty
      obtain ⟨hLJ, h2⟩ := h20.two hchar
      rcases h2 with h2A | h2B | h2C
      · have hBor := borelOver_le_of_isBorelOfBlock1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
          (Q := s1516 T Z₁ ⊓ L) h20.sylow (card_ne_three_of_isQuasisimple1521 hqs) h2A.2.2 hMLS
          inf_le_right
        refine ⟨hBor.trans inf_le_left, ?_⟩
        rcases hty with h5 | ⟨n, hn, hn'⟩
        · exact hBlkA5 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hLJ hchar hbl h5
        · exact hBlkL2 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hLJ hchar hbl ⟨n, hn, hn'⟩
      · exact absurd h2B.1 (hcutB G L hshort hty).1
      · exact absurd h2C.1 (hcutB G L hshort hty).2
    · obtain ⟨hZ, h3⟩ := h20.three hco
      have hZ₁T : Z₁ ≤ T := fun z hz => hS.V_le_T hq hM (hS.z1_le_V hz)
      have hz : CentralMoving1521 (s1516 T Z₁) L :=
        centralMoving1521_of_ctx h18
          (Subgroup.isPerfect_iff.1 (Group.IsPerfect.mk hco.2.2.1)) hL.not_le hZ₁T
      rcases h3 with h3A | h3B | h3C | h3D | h3E
      · obtain ⟨hty3, hBor3⟩ := h3A
        have hBor := borelOver_le_of_isBorelIn1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
          (Q := s1516 T Z₁ ⊓ L) h20.sylow hBor3 hMLS
        refine ⟨hBor.trans inf_le_left, ?_⟩
        rcases hty3 with hB | hSz'
        · rcases hB with ⟨n, hn, h⟩ | ⟨e, h⟩ | ⟨n, hn, h⟩
          · exact hL2 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hco hZ ⟨n, hn, h⟩
          · exact hSz G (g1_1516 Z₁) (s1516 T Z₁) L hStd hco hZ (Or.inl ⟨e, h⟩)
          · exact hU3 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hco hZ ⟨n, hn, h⟩
        · exact hSz G (g1_1516 Z₁) (s1516 T Z₁) L hStd hco hZ (Or.inr hSz')
      · obtain ⟨hty3, hBP⟩ := h3B
        have hBor : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤
            mZ1516 Mc Z₁ ⊓ L := by
          rcases hBP with hB | hP
          · exact borelOver_le_of_isBorelIn1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
              (Q := s1516 T Z₁ ⊓ L) h20.sylow hB hMLS
          · exact borelOver_le_of_isParabolic1521 (L := L) (P := mZ1516 Mc Z₁ ⊓ L)
              (Q := s1516 T Z₁ ⊓ L) h20.sylow hP.1 hMLS
        refine ⟨hBor.trans inf_le_left, ?_⟩
        rcases hty3 with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
        · exact hL3 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hz hco hZ (Or.inl ⟨n, hn, h⟩)
        · exact hSp4 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hco hZ ⟨n, hn, h⟩
        · exact hL3 G (g1_1516 Z₁) (s1516 T Z₁) L hStd hz hco hZ (Or.inr h)
      · exact absurd (Or.inl h3C.1) (hcutC G L hco.2.2 hcty)
      · exact absurd (Or.inr (Or.inl h3D.1)) (hcutC G L hco.2.2 hcty)
      · exact absurd (Or.inr (Or.inr h3E.1)) (hcutC G L hco.2.2 hcty)
  exact struct15121_conclusion hC h18 h19 hL horb key.1 key.2

end CFSG.Quasithin
