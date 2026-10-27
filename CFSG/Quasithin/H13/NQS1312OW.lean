module

public import CFSG.Quasithin.H13.NQS1312O
public import CFSG.Quasithin.MS93.Burnside.C134Big
public import CFSG.Quasithin.H13.NQS1312N

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G]

theorem false_of_c27SL3_even_lineW [Finite G]
    (h1332 : Stmt13_3_2) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hA3 : A3Orbits G) (h134 : MS93.burnsideC134w_AS_C_1_34_corrBig) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G))
    (hC1 : (K ⊔ pCoreOf 2 (L ⊔ T)) ⊓
      centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))) : Set G) ≤
        pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)) ⊔ oTwoZIn K)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : Even n) (hn1 : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (e : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hMS : IsMSPair (K ⊔ pCoreOf 2 (L ⊔ T)) (pCoreOf 2 (L ⊔ T))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, hVQ, -, hLV, -, -, -, hTC, -, -⟩ := id hF
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hKH : K ≤ lineH Φ := le_of_mem_cComp hK
  have hyp : HypC23 (lineH Φ) Q (lineH Φ ⊓ normalizer (L : Set G)) :=
    hypC23_line h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  have hKQc : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hKc hQp hQK
  have hO : pCoreOf 2 (K ⊔ Q) ≤ Q :=
    c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hyp.radical hK hq hQK)
  have hVV : V ≤ VK := le_omegaOneCenterOf_line hKQc hO hVQ hQC
  set α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    e.toMonoidHom.comp (SBc17.actOn hKV) with hα
  have hαs : Function.Surjective α := e.surjective.comp (SBc17.actOn_surjective hKV)
  obtain ⟨g, hg⟩ := exists_orderOf_three_sl3 F
  have hg' : orderOf (specialLinearGroupEquivStatedSL 3 F g) = 3 :=
    (orderOf_injective (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
      (specialLinearGroupEquivStatedSL 3 F).injective g).trans hg
  have hK3 : 3 ∣ Nat.card K := three_dvd_card_of_surjective α hαs hg'
  have hle := inf_centralizer_le_pCoreOf_line h36 hA3 h38 hH hU3 hF hΦLs hK hq hK3 hC1 hVV
  have hker : α.ker = CFSG.pCore 2 ↥K := by
    rw [hα, MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact ker_actOn_line hQK hle
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  have hxN := mem_lineN_of_tau_k2 (hLV hxL) hxτ
  have hxH := not_mem_lineH_of_tau_k2 (hLV hxL) hxτ
  have hSQ : SQTKGroup ↥(lineN Φ) := isSQTKIn_lineN hH
  have hKN : K ∈ cComp (lineN Φ) := cComp_mem_of_subnormal isSubnormal_lineH hK
  obtain ⟨-, hNK⟩ := le_normalizer_of_commute_three hA3 h38 hSQ lineH_le_lineN
    lineN_le_normalizer_lineH hKN hKH hK3 hxN (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H hxH
  have hxK : x ∈ normalizer (K : Set G) := hNK hxN
  have hxQ : x ∈ normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (mem_sup_left hxL)
  have hxP : x ∈ normalizer (pCoreOf 2 (K ⊔ Q) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_sup_line hxK hxQ)
  have hxQc : x ∈ normalizer (c134Q (K ⊔ Q) K : Set G) :=
    mem_normalizer_commutator_line hxP hxK
  have hxZ : x ∈ normalizer (centerOf (c134Q (K ⊔ Q) K) : Set G) :=
    A4.normalizer_le_normalizer_centerOf _ hxQc
  have hxU : x ∈ normalizer ((⁅centerOf (c134Q (K ⊔ Q) K), K⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator_line hxZ hxK
  have hPK : pCoreOf 2 (K ⊔ Q) ≤ normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer hQK)
  have hQcK : c134Q (K ⊔ Q) K ≤ K := commutator_le_of_le_normalizer_line hPK
  have hZK : centerOf (c134Q (K ⊔ Q) K) ≤ K := inf_le_left.trans hQcK
  have hUK : ⁅centerOf (c134Q (K ⊔ Q) K), K⁆ ≤ K :=
    commutator_le_of_le_normalizer_line (hZK.trans Subgroup.le_normalizer)
  have hQH : Q ≤ lineH Φ :=
    hQC.trans (Subgroup.centralizer_le (by
      intro y hy
      rcases hy with rfl | rfl
      · exact ptOf_mem _
      · exact ptOf_mem _))
  have hKc' : K ∈ cComp (K ⊔ Q) := cComp_mem_of_le hK le_sup_left (sup_le hKH hQH)
  have hprod : ((K ⊔ Q : Subgroup G) : Set G) = (K : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K Q hQK
  have hchar : CharP F 2 := charP_two_of_card_line hn1 hcard
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  obtain ⟨i, hi⟩ := h134 G (K ⊔ Q) Q K hMS hKc' hprod ⟨n, F, inferInstance, inferInstance, α, hn2,
    hcard, hαs, hker⟩
  have hfin : ∀ {W : Subgroup G}, W ≤ K → K ≤ normalizer (W : Set G) →
      x ∈ normalizer (W : Set G) → IsElemAbelian 2 W →
      (∀ H : Subgroup G, K ≤ H → W ≤ H → A319Hyp (K.subgroupOf H) (W.subgroupOf H)) → False :=
    fun hWK hKW hxW hW hHyp =>
      hxH (hKH (mem_of_a319_line hF318 h36 h38 hSQ hKN hxN hx3 hWK hKW hxW hW hHyp))
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  ·
    obtain ⟨-, n', F', _, _, hcard', hKW, α', hα's, hα'ker, β, hβs, hβker, hβeq⟩ := hi
    have hn'1 : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · have h1 : 1 < Fintype.card F' := Fintype.one_lt_card
        rw [hcard', h, pow_zero] at h1
        omega
      · exact h
    have := charP_two_of_card_line hn'1 hcard'
    have hn' := even_of_quot_statedSL3 hn hn1 hcard hcard' hαs hker hα's hα'ker
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    exact hfin hQcK hKW hxQc (isElemAbelian_of_injective_line add_self_eq_zero_line' β hβi)
      fun H hKH' hWH => Vol2.Ch11.SecA.a319Hyp_one hKH' hWH hKW hn'
        (by rw [Nat.card_eq_fintype_card, hcard'])
        (natOn_of_isNaturalSection hα's hα'ker hβs hβker hβeq)
  ·
    obtain ⟨⟨n', F', _, _, α', hcard', ⟨hα's, hα'ker⟩, hsum⟩, -⟩ := hi
    have hn'1 : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · have h1 : 1 < Fintype.card F' := Fintype.one_lt_card
        rw [hcard', h, pow_zero] at h1
        omega
      · exact h
    have := charP_two_of_card_line hn'1 hcard'
    have hn' := even_of_quot_statedSL3 hn hn1 hcard hcard' hαs hker hα's hα'ker
    obtain ⟨W₀, W₁, hK0, hK1, hsup, hinf, hN0, hN1⟩ := natOn_of_isSumVia_two hα's hα'ker hsum
    obtain ⟨hKW, -, β, -, hβker, -⟩ := hsum
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    exact hfin hQcK hKW hxQc (isElemAbelian_of_injective_line add_self_eq_zero_line β hβi)
      fun H hKH' hWH => Vol2.Ch11.SecA.a319Hyp_two hKH' hWH hK0 hK1 hsup hinf hn'
        (by rw [Nat.card_eq_fintype_card, hcard']) hN0 hN1
  ·
    obtain ⟨⟨n', F', _, _, α', hcard', ⟨hα's, hα'ker⟩, hZ, -⟩, -⟩ := hi
    have hn'1 : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · have h1 : 1 < Fintype.card F' := Fintype.one_lt_card
        rw [hcard', h, pow_zero] at h1
        omega
      · exact h
    have := charP_two_of_card_line hn'1 hcard'
    have hn' := even_of_quot_statedSL3 hn hn1 hcard hcard' hαs hker hα's hα'ker
    obtain ⟨hKW, -, β, -, hβker, -⟩ := id hZ
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    exact hfin hZK hKW hxZ (isElemAbelian_of_injective_line add_self_eq_zero_line β hβi)
      fun H hKH' hWH => Vol2.Ch11.SecA.a319Hyp_one hKH' hWH hKW hn'
        (by rw [Nat.card_eq_fintype_card, hcard']) (natOn_of_isSumVia_one hα's hα'ker hZ)
  ·
    obtain ⟨⟨n', F', _, _, α', hcard', ⟨hα's, hα'ker⟩, -, -, -, hU, -⟩, -⟩ := hi
    have hn'1 : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · have h1 : 1 < Fintype.card F' := Fintype.one_lt_card
        rw [hcard', h, pow_zero] at h1
        omega
      · exact h
    have := charP_two_of_card_line hn'1 hcard'
    have hn' := even_of_quot_statedSL3 hn hn1 hcard hcard' hαs hker hα's hα'ker
    obtain ⟨hKW, -, β, -, hβker, -⟩ := id hU
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    exact hfin hUK hKW hxU (isElemAbelian_of_injective_line add_self_eq_zero_line β hβi)
      fun H hKH' hWH => Vol2.Ch11.SecA.a319Hyp_one hKH' hWH hKW hn'
        (by rw [Nat.card_eq_fintype_card, hcard']) (natOn_of_isSumVia_one hα's hα'ker hU)
  ·
    obtain ⟨⟨α', ⟨hα's, hα'ker⟩, -⟩, -⟩ := hi
    have hc := Nat.card_congr ((quotEquivOf hα's hα'ker).symm.trans (quotEquivOf hαs hker)).toEquiv
    have h1 := eq_of_card_statedSL3_eq (F := ZMod 2) (m := 1) le_rfl hn1 (by simp) hcard hc
    rw [← h1] at hn
    exact Nat.not_even_one hn
  · exact hi.elim

end CFSG.Quasithin.H13.U3.NLine
