module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTwoSub
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProof
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof
public import CFSG.RankThree.PartTwo.Sec18.Rem187

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item18ResProof

variable {G : Type} [Group G] [Finite G]

theorem mem_of_isPGroup_three_quotient {Y : Type*} [Group Y] {X : Subgroup Y} [X.Normal]
    (hq : IsPGroup 3 (Y ⧸ X)) {y : Y} {k : ℕ} (hy : y ^ 2 ^ k = 1) : y ∈ X := by
  obtain ⟨j, hj⟩ := hq (y : Y ⧸ X)
  have h3 : orderOf (y : Y ⧸ X) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj
  have h2 : orderOf (y : Y ⧸ X) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hy]
    rfl
  have hcop : Nat.Coprime (3 ^ j) (2 ^ k) := Nat.Coprime.pow j k (by norm_num)
  have h1 := Nat.eq_one_of_dvd_coprimes hcop h3 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem false_of_mem_scriptH
    (h1812 : Item181_2)
    {A M N L S : Subgroup G} (h : Sec18Std G A M) (hN : IsMaximalTwoLocal N) (hAN : A ≤ N)
    (hMN : CFSG.Open.pCoreOf 2 (M ⊓ N) = CFSG.Open.pCoreOf 2 M) (hL : L ∈ oTwoComponentsIn N)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (inSubgroup (CFSG.pPrimeCore 3) (N ⊓ M)))
    (hH : L ⊔ A ⊔ S ∈ scriptH A M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hAM : A ≤ M := sec18Std_le h
  have h1813 := rank3II_18_1_3_of h1812
  set H := L ⊔ A ⊔ S with hHdef
  have hLN : L ≤ N := le_of_mem_oTwoComponentsIn hL
  have hHN : H ≤ N :=
    sup_le (sup_le hLN hAN) (hS.le.trans ((Subgroup.map_subtype_le _).trans inf_le_left))
  have hLH : L ≤ H := le_sup_left.trans le_sup_left
  have hAH : A ≤ H := le_sup_right.trans le_sup_left
  obtain ⟨-, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hL
  have hLeq : L = inSubgroup perfectResidual H :=
    eq_of_mem_oTwoComponentsIn_of_mem_scriptH hH
      (mem_oTwoComponentsIn_of_le hL hLH (isSubnormal_subgroupOf_of_le hsn hHN))
  have hLp : ⁅L, L⁆ = L := commutator_eq_of_mem_oTwoComponentsIn hL
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLeq]
    exact le_normalizer_inSubgroup_perfectResidual H
  have hLM : ¬ L ≤ M := by
    rw [hLeq]
    exact perfectResidual_not_le_of_mem_scriptH h hH
  set T := CFSG.Open.pCoreOf 2 (M ⊓ N) with hTdef
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hNM' : N ⊓ M = M ⊓ N := inf_comm N M
  have hNMT : N ⊓ M ≤ Subgroup.normalizer (T : Set G) := by
    rw [hNM']
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hTNM : T ≤ N ⊓ M := by
    rw [hNM']
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hTY : T ≤ inSubgroup (CFSG.pPrimeCore 3) (N ⊓ M) :=
    le_inSubgroup_pPrimeCore_of hcop hTNM hNMT
  have hTS : T ≤ S := le_of_isSylowOf_of_normal hT2 hTY (Subgroup.map_subtype_le _) hNMT hS
  have hTH : T ≤ H := hTS.trans le_sup_right
  have hTM : T ≤ M := hTNM.trans inf_le_right
  have hMT : Subgroup.normalizer (T : Set G) = M := by
    rw [hMN]
    exact normalizer_pCoreOf_of_isMaximalTwoLocal h.mem_scriptM.1
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (le_inf hAN hAM).trans hNMT
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTH.trans hHL
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAH.trans hHL
  have hle := pCoreOf_le_pCoreOf_inf h hAN
  have hOL : CFSG.Open.pCoreOf 2 L ≤ T :=
    (pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hL).trans (hle.trans (by rw [hNM']))
  set H₀ := L ⊔ A ⊔ T with hH₀def
  have hLH₀ : L ≤ H₀ := le_sup_left.trans le_sup_left
  have hAH₀ : A ≤ H₀ := le_sup_right.trans le_sup_left
  have hTH₀ : T ≤ H₀ := le_sup_right
  have hH₀H : H₀ ≤ H := sup_le (sup_le hLH hAH) hTH
  have hH₀N : H₀ ≤ N := hH₀H.trans hHN
  have hres : inSubgroup perfectResidual H₀ = L :=
    le_antisymm ((inSubgroup_perfectResidual_mono hH₀H).trans hLeq.ge)
      (le_inSubgroup_perfectResidual hLp hLH₀)
  have hLH₀c : L ∈ oTwoComponentsIn H₀ :=
    mem_oTwoComponentsIn_of_le hL hLH₀ (isSubnormal_subgroupOf_of_le hsn hH₀N)
  set R := CFSG.Open.pCoreOf 2 (H₀ ⊓ M) with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRH₀ : R ≤ H₀ := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    (le_inf hAH₀ hAM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hTR : T ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hTH₀ hTM)
      (inf_le_right.trans hMT.ge) hT2
  set P := L ⊔ T with hPdef
  have hPH₀ : P ≤ H₀ := sup_le hLH₀ hTH₀
  have hH₀P : H₀ ≤ Subgroup.normalizer (P : Set G) := by
    refine sup_le (sup_le ((le_sup_left : L ≤ P).trans Subgroup.le_normalizer) ?_)
      ((le_sup_right : T ≤ P).trans Subgroup.le_normalizer)
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hAL ha, hAT ha⟩
  have hRP : R ≤ P := by
    have hPn : (P.subgroupOf H₀).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPH₀).mpr hH₀P
    have hq3 : IsPGroup 3 (H₀ ⧸ P.subgroupOf H₀) := by
      have hA3 : IsPGroup 3 (A.subgroupOf H₀) := by
        intro a
        refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
        simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp a.2)
      have h1 := hA3.map (QuotientGroup.mk' (P.subgroupOf H₀))
      have hsup : P.subgroupOf H₀ ⊔ A.subgroupOf H₀ = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hPH₀ hAH₀]
        have hPA : P ⊔ A = H₀ := by rw [hPdef, hH₀def, sup_right_comm]
        rw [hPA, Subgroup.subgroupOf_self]
      have h2 : (A.subgroupOf H₀).map (QuotientGroup.mk' (P.subgroupOf H₀)) = ⊤ := by
        rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' (P.subgroupOf H₀))
          (QuotientGroup.mk'_surjective _), ← hsup, Subgroup.map_sup,
          QuotientGroup.map_mk'_self, bot_sup_eq]
      rw [h2] at h1
      exact h1.of_equiv Subgroup.topEquiv
    intro x hx
    obtain ⟨k, hk⟩ := hR2 ⟨x, hx⟩
    have hx' : (⟨x, hRH₀ hx⟩ : H₀) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact Subgroup.mem_subgroupOf.mp (mem_of_isPGroup_three_quotient hq3 hx')
  have hRL : R ⊓ L ≤ T := by
    have hQ : R ⊓ L ≤ inSubgroup perfectResidual H := hLeq ▸ inf_le_right
    have h1 := le_pCoreOf_of_le_normalizer h1812 h hH hQ (hR2.to_le inf_le_left)
      (fun a ha => Subgroup.inf_normalizer_le_normalizer_inf ⟨hAR ha, hAL ha⟩)
    rw [← hLeq] at h1
    exact h1.trans hOL
  have hRT : R = T := by
    refine le_antisymm (fun x hx => ?_) hTR
    have hxP : x ∈ ((L ⊔ T : Subgroup G) : Set G) := hRP hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTL] at hxP
    obtain ⟨l, hl, t, ht, rfl⟩ := hxP
    have hlR : l ∈ R := by
      have := R.mul_mem hx (R.inv_mem (hTR ht))
      simpa using this
    exact T.mul_mem (hRL ⟨hlR, hl⟩) ht
  have hne : CFSG.Open.pCoreOf 2 H₀ ≠ R := by
    intro heq
    apply hLM
    rw [← hMT]
    refine hLH₀.trans ?_
    have h1 := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀
    rwa [heq, hRT] at h1
  have hH₀mem : H₀ ∈ scriptH A M := by
    refine mem_scriptH_iff.mpr ⟨fun htop => ne_top_of_mem_scriptH hH ?_, ?_, ?_, hne⟩
    · exact eq_top_iff.mpr (htop ▸ hH₀H)
    · rw [hres, ← hRdef, hRT]
    · rw [hres]
      exact hLH₀c
  have hON : CFSG.Open.pCoreOf 2 N ≤ H₀ := hle.trans (by rw [hNM']; exact hTH₀)
  obtain ⟨Q, hQ1, hQ2, hNQ⟩ := hN.1
  have hF : CFSG.generalizedFitting H₀ = CFSG.pCore 2 H₀ :=
    Item183NMProof.generalizedFitting_eq_of_pCoreOf_le h.charTwoType ⟨Q, hQ1, hQ2, hNQ⟩ hH₀N
      hON
  obtain ⟨⟨C, hCchar, hC1, hH₀C⟩, -⟩ := h1813 G A M h H₀ hH₀mem hF
  set C' := C.map (CFSG.Open.pCoreOf 2 (H₀ ⊓ M)).subtype with hC'
  have hMC : M ≤ Subgroup.normalizer (C' : Set G) := by
    have : C.Characteristic := hCchar
    have hMO : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H₀ ⊓ M) : Set G) := by
      rw [← hRdef, hRT]
      exact hMT.ge
    exact hMO.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic C)
  have hC'1 : C' ≠ ⊥ := fun hb =>
    hC1 ((Subgroup.map_eq_bot_iff_of_injective C (Subgroup.subtype_injective _)).mp hb)
  have hC'2 : IsPGroup 2 C' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H₀ ⊓ M)).to_le (Subgroup.map_subtype_le C)
  have hloc : IsPLocal 2 (Subgroup.normalizer (C' : Set G)) := ⟨C', hC'1, hC'2, rfl⟩
  have hMeq : Subgroup.normalizer (C' : Set G) = M := by
    by_contra hne'
    exact h.mem_scriptM.1.2 _ (lt_of_le_of_ne hMC (Ne.symm hne')) hloc
  exact perfectResidual_not_le_of_mem_scriptH h hH₀mem
    ((Subgroup.map_subtype_le _).trans (hH₀C.trans hMeq.le))

end Item18ResProof

open Item18ResProof

theorem step183S_of_item181_2
    (h1812 : Item181_2) :
    Step183S := by
  intro G _ _ A M N L S h hN hAN _ _ hMN hL hS hH
  exact (false_of_mem_scriptH h1812 h hN hAN hMN hL hS hH).elim

theorem noSharedCore_of_item181
    (h1811 : Item181_1)
    (h1812 : Item181_2) : Step183SNoSharedCore :=
  noSharedCore_of_step183S h1811 (rank3II_18_1_3_of h1812) (step183S_of_item181_2 h1812)

theorem step183Hyp191_of_item181
    (h45 : Sec4.Item4_5)
    (h1811 : Item181_1) (h1812 : Item181_2) : Step183Hyp191 :=
  step183Hyp191_of_noSharedCore h45 h1811 h1812 (noSharedCore_of_item181 h1811 h1812)

theorem item183One_of_item181
    (h45 : Sec4.Item4_5)
    (h1811 : Item181_1) (h1812 : Item181_2) (hET : Item183ET) : Item183One :=
  item183One_of h45 h1811 h1812 hET (step183Hyp191_of_item181 h45 h1811 h1812)

end CFSG.RankThree.PartTwo.Sec18
