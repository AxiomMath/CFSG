module

public import CFSG.Quasithin.H13.NQS1312A
public import CFSG.Quasithin.Background.C134L32CorrM
public import CFSG.Quasithin.H13.NQS1312N
public import CFSG.Quasithin.H13.NQS1312O
public import CFSG.Quasithin.H13.NQS1312V

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem false_of_c27SL3_two_lineW
    (h1332 : Stmt13_3_2) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hA3 : A3Orbits G)
    (h134 : C134L32CorrM) (hU33 : U33CommDimFact)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦL : ∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
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
    {F : Type} [Field F] [Fintype F] (hcard : Fintype.card F = 2)
    (e : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)))))
      (autOn ((lineH Φ ⊓ normalizer (L : Set G)) ⊓ K)
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))))
    (hMS : IsMSPair (K ⊔ pCoreOf 2 (L ⊔ T)) (pCoreOf 2 (L ⊔ T))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hTL, -, -, hV64, hVQ, -, hLV, -, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, -, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  set Mh := lineH Φ ⊓ normalizer (L : Set G) with hMh
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hKH : K ≤ lineH Φ := le_of_mem_cComp hK
  have hyp : HypC23 (lineH Φ) Q Mh := hypC23_line h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  have hKQc : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hKc hQp hQK
  have hO : pCoreOf 2 (K ⊔ Q) ≤ Q :=
    c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hyp.radical hK hq hQK)
  have hVV : V ≤ VK := le_omegaOneCenterOf_line hKQc hO hVQ hQC
  have hVO : V ⊓ K ≤ pCoreOf 2 K := inf_le_pCoreOf_of_pCoreOf_le hKQc hO hVQ hQC
  set α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    e.toMonoidHom.comp (SBc17.actOn hKV) with hα
  have hαs : Function.Surjective α := e.surjective.comp (SBc17.actOn_surjective hKV)
  obtain ⟨g, hg⟩ := exists_orderOf_three_sl3 F
  have hg' : orderOf (specialLinearGroupEquivStatedSL 3 F g) = 3 :=
    (orderOf_injective (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
      (specialLinearGroupEquivStatedSL 3 F).injective g).trans hg
  have hK3 : 3 ∣ Nat.card K := three_dvd_card_of_surjective α hαs hg'
  have hle := inf_centralizer_le_pCoreOf_line h36 hA3 h38 hH hU3 hF hΦLs hK hq hK3 hC1 hVV
  have hkerA := ker_actOn_line hQK hle
  have hker : α.ker = CFSG.pCore 2 ↥K := by
    rw [hα, MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact hkerA
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  have hxN := mem_lineN_of_tau_k2 (hLV hxL) hxτ
  have hxH := not_mem_lineH_of_tau_k2 (hLV hxL) hxτ
  have hSQ : SQTKGroup ↥(lineN Φ) := isSQTKIn_lineN hH
  have hKN : K ∈ cComp (lineN Φ) := cComp_mem_of_subnormal isSubnormal_lineH hK
  obtain ⟨hk₁K, hNK⟩ := le_normalizer_of_commute_three hA3 h38 hSQ lineH_le_lineN
    lineN_le_normalizer_lineH hKN hKH hK3 hxN (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H hxH
  have hcard1 : Fintype.card F = 2 ^ 1 := by rw [hcard, pow_one]
  have hF'2 : ∀ {F' : Type} [Field F'] [Fintype F'] {n' : ℕ}
      {α' : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F')}, Fintype.card F' = 2 ^ n' →
      Function.Surjective α' → α'.ker = CFSG.pCore 2 ↥K → Fintype.card F' = 2 := by
    intro F' _ _ n' α' hcard' hα's hα'ker
    have hn'1 : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · have h1 : 1 < Fintype.card F' := Fintype.one_lt_card
        rw [hcard', h, pow_zero] at h1
        omega
      · exact h
    have hc := Nat.card_congr ((quotEquivOf hα's hα'ker).symm.trans (quotEquivOf hαs hker)).toEquiv
    rw [hcard', eq_of_card_statedSL3_eq hn'1 le_rfl hcard' hcard1 hc, pow_one]
  have hPK : pCoreOf 2 (K ⊔ Q) ≤ normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer hQK)
  have hQcK : c134Q (K ⊔ Q) K ≤ K := commutator_le_of_le_normalizer_line hPK
  have hQcP : c134Q (K ⊔ Q) K ≤ pCoreOf 2 (K ⊔ Q) :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 ((le_sup_left : K ≤ K ⊔ Q).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ Q)))
  have hQH : Q ≤ lineH Φ :=
    hQC.trans (Subgroup.centralizer_le (by
      intro y hy
      rcases hy with rfl | rfl
      · exact ptOf_mem _
      · exact ptOf_mem _))
  have hKc' : K ∈ cComp (K ⊔ Q) := cComp_mem_of_le hK le_sup_left (sup_le hKH hQH)
  have hprod : ((K ⊔ Q : Subgroup G) : Set G) = (K : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K Q hQK
  have hU : ∀ c ∈ lperpList, ptOf Φ (vecOf c) ∈ blockU K := fun c hc =>
    ptOf_lperp_mem_blockU hk₁K (hLV hk₁L) hk₁τ (hVQ.trans hQK) hVO hc
  have hlQc : ∀ c ∈ lperpList, ptOf Φ (vecOf c) ∈ c134Q (K ⊔ Q) K := fun c hc =>
    Subgroup.commutator_mono (SBc17.pCoreOf_le_pCoreOf_sup hQK) le_rfl (hU c hc)
  have hlZ : ∀ c ∈ lperpList, ptOf Φ (vecOf c) ∈ centerOf (c134Q (K ⊔ Q) K) := by
    intro c hc
    refine ⟨hlQc c hc, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact (mem_centralizer_iff.1 (hQC (hO (hQcP hy))) _ (ptOf_mem _)).symm
  obtain ⟨i, hi⟩ := h134 G (K ⊔ Q) Q K hMS hKc' hprod ⟨F, inferInstance, inferInstance, α,
    hcard, hαs, hker⟩
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  ·
    obtain ⟨-, n', F', _, _, hcard', -, α', hα's, hα'ker, β, hβs, hβker, -⟩ := hi
    have hF' := hF'2 hcard' hα's hα'ker
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    have hc8 : Nat.card (c134Q (K ⊔ Q) K) = 8 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβi, hβs⟩).toEquiv, card_mult_fin3 hF']
    have h16 := sixteen_le_relIndex_of_lperp hk₁K (hLV hk₁L) hk₁τ hlQc
      (bot_le : (⊥ : Subgroup G) ≤ centralizer (K : Set G))
    rw [Subgroup.relIndex_bot_left, hc8] at h16
    omega
  ·
    obtain ⟨⟨n', F', _, _, α', hcard', ⟨hα's, hα'ker⟩, hKQc', -, β', hβ's, hβ'ker, hβ'eq⟩, -⟩ := hi
    have hF' := hF'2 hcard' hα's hα'ker
    have hβ'i : Function.Injective β' := by
      rw [← MonoidHom.ker_eq_bot_iff, hβ'ker, Subgroup.bot_subgroupOf]
    have hk₁3' : k₁ ^ 3 = 1 := by
      have h := pow_orderOf_eq_one k₁
      rwa [hk₁3] at h
    have h3 : ∀ X : Subgroup G, X ≤ Q → ¬ 3 ∣ Nat.card X := by
      intro X hXQ h3
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (hQp.to_le hXQ)
      rw [hm] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hO168 : (pCoreOf 2 K).relIndex K = 168 := by
      have h1 : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
        ext y
        rw [Subgroup.mem_subgroupOf, coe_mem_pCoreOf_iff_line]
      rw [Subgroup.relIndex, h1, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hαs,
        Subgroup.card_top, card_statedSL3, hcard]
      norm_num
    set P := K ⊓ Q with hPdef
    set P₀ := P ⊓ pCoreOf 2 K with hP₀def
    have hPQ : P ≤ Q := inf_le_right
    have hPK : P ≤ K := inf_le_left
    have hPp : IsPGroup 2 P := hQp.to_le hPQ
    have hLQ : L ≤ normalizer (Q : Set G) :=
      (le_sup_left : L ≤ L ⊔ T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
    have hk₁Q : k₁ ∈ normalizer (Q : Set G) := hLQ hk₁L
    have hKO2 : K ≤ normalizer (pCoreOf 2 K : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
    have hk₁P : k₁ ∈ normalizer (P : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk₁K, hk₁Q⟩
    have hQP : Q ≤ normalizer (P : Set G) := fun q hq =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hQK hq, Subgroup.le_normalizer hq⟩
    have hPP₀ : P ≤ normalizer (P₀ : Set G) := fun p hp =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hp, hKO2 (hPK hp)⟩
    have hk₁P₀ : k₁ ∈ normalizer (P₀ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hk₁P, hKO2 hk₁K⟩
    have hfQ : ∀ a ∈ Q, a⁻¹ * (k₁ * a * k₁⁻¹) ∈ P := by
      intro a ha
      refine ⟨?_, Q.mul_mem (Q.inv_mem ha) ((mem_normalizer_iff.1 hk₁Q a).1 ha)⟩
      have h1 : a⁻¹ * k₁ * a⁻¹⁻¹ ∈ K := (mem_normalizer_iff.1 (hQK (Q.inv_mem ha)) k₁).1 hk₁K
      have e1 : a⁻¹ * (k₁ * a * k₁⁻¹) = (a⁻¹ * k₁ * a⁻¹⁻¹) * k₁⁻¹ := by group
      rw [e1]
      exact K.mul_mem h1 (K.inv_mem hk₁K)
    have hιQ : (fixSub Q ⊥ k₁ (le_normalizer_bot_line Q)).relIndex Q =
        (fixSub P ⊥ k₁ (le_normalizer_bot_line P)).relIndex P := by
      rw [relIndex_fixSub_mul hk₁3' bot_le hPQ (le_normalizer_bot_line Q) hQP hk₁P (h3 P hPQ),
        relIndex_fixSub_eq_one hQP hfQ, one_mul]
    have hιP : (fixSub P ⊥ k₁ (le_normalizer_bot_line P)).relIndex P ≤
        4 * (fixSub P₀ ⊥ k₁ (le_normalizer_bot_line P₀)).relIndex P₀ := by
      rw [relIndex_fixSub_mul hk₁3' bot_le inf_le_left (le_normalizer_bot_line P) hPP₀ hk₁P₀
        (h3 P₀ (inf_le_left.trans hPQ))]
      exact Nat.mul_le_mul_right _ (relIndex_fixSub_le_four hk₁3' inf_le_left hPP₀ hk₁P hk₁P₀
        hPp (relIndex_inf_pCoreOf_le_eight hPK hPp hO168))
    have hP₀O : P₀ ≤ pCoreOf 2 (K ⊔ Q) := inf_le_right.trans (SBc17.pCoreOf_le_pCoreOf_sup hQK)
    have hOQc : pCoreOf 2 (K ⊔ Q) ≤ normalizer (c134Q (K ⊔ Q) K : Set G) :=
      Subgroup.normalizer_commutator_ge_left _ _
    have hk₁Qc : k₁ ∈ normalizer (c134Q (K ⊔ Q) K : Set G) :=
      Subgroup.normalizer_commutator_ge_right _ _ hk₁K
    have hfO : ∀ a ∈ pCoreOf 2 (K ⊔ Q), a⁻¹ * (k₁ * a * k₁⁻¹) ∈ c134Q (K ⊔ Q) K := by
      intro a ha
      have h1 := Subgroup.commutator_mem_commutator ((pCoreOf 2 (K ⊔ Q)).inv_mem ha) hk₁K
      rw [commutatorElement_def, inv_inv] at h1
      have h2 : a⁻¹ * (k₁ * a * k₁⁻¹) ∈ ⁅pCoreOf 2 (K ⊔ Q), K⁆ := by simpa only [mul_assoc] using h1
      exact h2
    have hιO : (fixSub (pCoreOf 2 (K ⊔ Q)) ⊥ k₁
          (le_normalizer_bot_line (pCoreOf 2 (K ⊔ Q)))).relIndex (pCoreOf 2 (K ⊔ Q)) =
        (fixSub (c134Q (K ⊔ Q) K) ⊥ k₁
          (le_normalizer_bot_line (c134Q (K ⊔ Q) K))).relIndex (c134Q (K ⊔ Q) K) := by
      rw [relIndex_fixSub_mul hk₁3' bot_le hQcP (le_normalizer_bot_line _) hOQc hk₁Qc
        (h3 _ (hQcP.trans hO)), relIndex_fixSub_eq_one hOQc hfO, one_mul]
    have hιQc := relIndex_fixSub_le_sixteen_of_sum hF' hKQc' β' hβ's hβ'i hβ'eq hk₁K hk₁3'
    have hι64 : (fixSub Q ⊥ k₁ (le_normalizer_bot_line Q)).relIndex Q ≤ 64 := by
      rw [hιQ]
      calc _ ≤ 4 * (fixSub P₀ ⊥ k₁ (le_normalizer_bot_line P₀)).relIndex P₀ := hιP
        _ ≤ 4 * (fixSub (pCoreOf 2 (K ⊔ Q)) ⊥ k₁
          (le_normalizer_bot_line (pCoreOf 2 (K ⊔ Q)))).relIndex (pCoreOf 2 (K ⊔ Q)) :=
          Nat.mul_le_mul_left _ (relIndex_fixSub_bot_mono hP₀O)
        _ ≤ 4 * 16 := by rw [hιO]; exact Nat.mul_le_mul_left _ hιQc
        _ = 64 := by norm_num
    have hQV : Q ≤ normalizer (V : Set G) := hQC.trans (Subgroup.centralizer_le_normalizer _)
    have hιQV := relIndex_fixSub_mul hk₁3' (bot_le : (⊥ : Subgroup G) ≤ V) hVQ
      (le_normalizer_bot_line Q) hQV (hLV hk₁L) (h3 V hVQ)
    have hιV : 16 ≤ (fixSub V ⊥ k₁ (hVQ.trans (le_normalizer_bot_line Q))).relIndex V :=
      sixteen_le_relIndex_fixSub_V hV64 (hLV hk₁L) hk₁τ
    have hle4 : (fixSub Q V k₁ hQV).relIndex Q ≤ 4 := by
      rw [hιQV] at hι64
      nlinarith
    have hΦL' : ∀ (l : G) (hl : l ∈ L), tau Φ ⟨l, hLV hl⟩ ∈ J6 := fun l hl => by
      obtain ⟨j, hj, hlj⟩ := hΦL l hl
      rw [tau_eq_iff.2 hlj]
      exact hj
    have hΦLs' : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), tau Φ ⟨l, hLV hl⟩ = j := fun j hj => by
      obtain ⟨l, hl, hlj⟩ := hΦLs j hj
      exact ⟨l, hl, tau_eq_iff.2 hlj⟩
    have hCL : L ⊓ centralizer (V : Set G) = pCoreOf 2 L := (u3_internal_frame_kernel hLV hU3 hF).1
    have hgood := fixSub_good hk₁L hk₁3'
      (chief_good_line hU33 hLV hCL hΦL' hΦLs' hk₁L hk₁3' hk₁τ) _ Q V hQV le_rfl hVQ hQp hLQ hLV
    have h1 : (fixSub Q V k₁ hQV).relIndex Q = 1 := by omega
    have hHu : lineH Φ ≤ centralizer ({ptOf Φ (vecOf 15)} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
    have hMhV : Mh ≤ normalizer (V : Set G) := fun y hy =>
      hTI _ (ptOf_mem _) ptOf_fifteen_ne_one ⟨hy.2, hHu hy.1⟩
    obtain ⟨u, huQ, hu⟩ := exists_mem_not_fixSub_line hTL hLV hCL hΦN hMhV hKV hkerA hVO hcard e
      hmax hk₁L hk₁K hk₁H hk₁3 hk₁τ
    exact hu (Subgroup.relIndex_eq_one.1 h1 huQ).2
  ·
    obtain ⟨⟨n', F', _, _, α', hcard', ⟨hα's, hα'ker⟩, hZ, -⟩, -⟩ := hi
    have hF' := hF'2 hcard' hα's hα'ker
    obtain ⟨-, -, β, hβs, hβker, -⟩ := hZ
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    have hc8 : Nat.card (centerOf (c134Q (K ⊔ Q) K)) = 8 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβi, hβs⟩).toEquiv, card_mult_fin1_fin3 hF']
    have h16 := sixteen_le_relIndex_of_lperp hk₁K (hLV hk₁L) hk₁τ hlZ
      (bot_le : (⊥ : Subgroup G) ≤ centralizer (K : Set G))
    rw [Subgroup.relIndex_bot_left, hc8] at h16
    omega
  ·
    obtain ⟨⟨n', F', _, _, α', hcard', ⟨hα's, hα'ker⟩, hZeq, hinf, hU', -, -⟩, -⟩ := hi
    have hF' := hF'2 hcard' hα's hα'ker
    obtain ⟨-, -, β, hβs, hβker, -⟩ := hU'
    have hβi : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    have hcU : Nat.card (⁅centerOf (c134Q (K ⊔ Q) K), K⁆ : Subgroup G) = 8 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβi, hβs⟩).toEquiv, card_mult_fin1_fin3 hF']
    set Z := centerOf (c134Q (K ⊔ Q) K) with hZdef
    set C := c134CQ (K ⊔ Q) K with hCdef
    set U := ⁅Z, K⁆ with hUdef
    have hCZ : C ≤ Z := by
      rw [hZeq]
      exact le_sup_left
    have hUN : U ≤ normalizer (C : Set G) := by
      intro u hu
      have huZ : u ∈ Z := by
        rw [hZeq]
        exact (le_sup_right : U ≤ C ⊔ U) hu
      rw [mem_normalizer_iff]
      intro c
      have hc : ∀ c ∈ c134Q (K ⊔ Q) K, u * c * u⁻¹ = c := fun c hc => by
        rw [← (mem_centralizer_iff.1 huZ.2) c hc]
        group
      constructor
      · intro h
        rw [hc c h.1]
        exact h
      · intro h
        have hc' : u * c * u⁻¹ ∈ c134Q (K ⊔ Q) K := h.1
        have e1 : c = u⁻¹ * (u * c * u⁻¹) * u := by group
        rw [e1]
        have hc'' := hc _ hc'
        have e2 : u⁻¹ * (u * c * u⁻¹) * u = u * c * u⁻¹ := by
          calc u⁻¹ * (u * c * u⁻¹) * u = u⁻¹ * (u * (u * c * u⁻¹) * u⁻¹) * u := by rw [hc'']
            _ = u * c * u⁻¹ := by group
        rw [e2]
        exact h
    have hprodZ := card_sup_mul_card_inf_line hUN
    rw [← hZeq, hinf, Subgroup.card_bot, mul_one, hcU] at hprodZ
    have hrel : C.relIndex Z * Nat.card C = Nat.card Z := by
      rw [← Subgroup.relIndex_mul_card (H := C) (K := Z), inf_of_le_left hCZ]
    have hC8 : C.relIndex Z = 8 := by
      have hpos : 0 < Nat.card C := Nat.card_pos
      rw [hprodZ] at hrel
      nlinarith
    have h16 := sixteen_le_relIndex_of_lperp (C := C) hk₁K (hLV hk₁L) hk₁τ hlZ inf_le_right
    rw [hC8] at h16
    omega
  ·
    obtain ⟨⟨α', ⟨hα's, hα'ker⟩, -, hsum⟩, -⟩ := hi
    obtain ⟨-, -, β, hβs, hβker, -⟩ := hsum
    have hidx : (c134CQ (K ⊔ Q) K).relIndex (c134Q (K ⊔ Q) K) = 8 := by
      rw [Subgroup.relIndex, ← hβker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hβs,
        Subgroup.card_top, card_mult_fin1_fin3 (ZMod.card 2)]
    have h16 := sixteen_le_relIndex_of_lperp (C := c134CQ (K ⊔ Q) K) hk₁K (hLV hk₁L) hk₁τ hlQc
      inf_le_right
    rw [hidx] at h16
    omega
  · exact hi.elim

end CFSG.Quasithin.H13.U3.NLine
