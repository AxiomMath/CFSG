module

public import CFSG.Quasithin.H13.L32A1410a
public import CFSG.Quasithin.H13.L32A1410h
public import CFSG.Quasithin.EmptyFaithful.S1422Quot
public import CFSG.Quasithin.H13.L32A1410f

public section

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B Mat8Cert G5ACert
  L1442M L128P

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {b : Bool}

section CanonicalList

variable {K I S : Subgroup G}

theorem not_f112ListC (hSz : Nat.card ↥(Sz 0) = 20) (hK : Nat.card (oTwoQuot ↥K) = 60)
    (hI : Nat.card (oTwoQuot ↥I) = 6)
    (hKO : 2 ^ 9 ≤ Nat.card (pCoreOf 2 (K ⊔ bigB K I S)))
    (hK48 : 48 < Nat.card K) : ¬ F112List K I S := by
  intro h
  unfold F112List at h
  rcases h with ⟨f, hf, -, h⟩ | ⟨f, hf, -, h⟩ | ⟨f, hf, -, hqK, hqI, -⟩ |
      ⟨f, hf, -, hqK, -, hqI, -⟩ | ⟨a, -, hsz, -, hqI, -⟩ | ⟨f, hf, -, -, -, -, hqI, -⟩ |
      ⟨-, -, -, hqI, -⟩ | ⟨-, hqK, -⟩ | ⟨-, hK9, -⟩ | ⟨-, -, hQ, -⟩ | ⟨-, -, hQ, -⟩ |
      ⟨-, hqK, -⟩ | ⟨-, hqK, -⟩
  ·
    rcases h with ⟨hf2, -, -, -, hI'⟩ | ⟨-, ⟨eK⟩, -⟩
    · have hc := isLin2Type_card_quot hI'
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6 : Nat.card (OTwoQuot I) = 6 := hI
      omega
    · have hc := Nat.card_congr eK.toEquiv
      rw [card_perm_four] at hc
      have := Subgroup.card_le_of_le (le_sup_left : K ≤ K ⊔ S)
      omega
  ·
    rcases h with ⟨hf2, -, -, -, hI'⟩ | ⟨-, ⟨eK⟩, -⟩
    · have hc := isLin2Type_card_quot hI'
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6 : Nat.card (OTwoQuot I) = 6 := hI
      omega
    · have hc := Nat.card_congr eK.toEquiv
      rw [card_z2_perm_four] at hc
      have := Subgroup.card_le_of_le (le_sup_left : K ≤ K ⊔ S)
      omega
  ·
    have := hqI.eq_one_of_card_eq_six hf hI
    subst this
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := hqI.eq_one_of_card_eq_six hf hI
    subst this
    have := hqK.card (by norm_num)
    norm_num at this
    omega
  ·
    have ha : 2 * a + 1 = 1 := hqI.eq_one_of_card_eq_six (by omega) hI
    have ha0 : a = 0 := by omega
    subst ha0
    rcases hsz with ⟨⟨eK⟩⟩ | ⟨-, ⟨eK⟩⟩
    · have := Nat.card_congr eK.toEquiv
      omega
    · have := Nat.card_congr eK.toEquiv
      rw [DihedralGroup.nat_card] at this
      omega
  ·
    have := hqI.eq_one_of_card_eq_six (by omega) hI
    omega
  ·
    have := hqI.eq_one_of_card_eq_six (by omega) hI
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    rcases hK9 with h | h
    · obtain ⟨eK⟩ := h
      have := Nat.card_congr eK.toEquiv
      rw [DihedralGroup.nat_card] at this
      omega
    · obtain ⟨eK⟩ := h
      have := Nat.card_congr eK.toEquiv
      omega
  ·
    have := hQ.1
    omega
  ·
    have := hQ.1
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega

theorem not_f112List_swapC (hK : Nat.card (oTwoQuot ↥K) = 60)
    (hI : Nat.card (oTwoQuot ↥I) = 6) (hK48 : 48 < Nat.card K) (hKs : ¬ IsShort2 K) :
    ¬ F112List I K S := by
  intro h
  unfold F112List at h
  rcases h with ⟨f, hf, -, h⟩ | ⟨f, hf, -, h⟩ | ⟨f, hf, -, hqI, hqK, -⟩ |
      ⟨f, hf, -, hqI, -⟩ | ⟨a, -, -, -, hqK, -⟩ | ⟨f, hf, -, -, -, hB, -⟩ |
      ⟨-, -, -, hqK, -⟩ | ⟨-, -, hqK, -⟩ | ⟨-, -, -, hqK, -⟩ | ⟨-, -, -, hqK, -⟩ |
      ⟨-, -, -, ⟨eK⟩, -⟩ | ⟨-, -, -, hqK, -⟩ | ⟨-, -, -, hqK, -⟩
  ·
    rcases h with ⟨hf2, -, hI', -⟩ | ⟨-, -, ⟨eK⟩⟩
    · have hc := isLin2Type_card_quot hI'
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6 : Nat.card (OTwoQuot I) = 6 := hI
      omega
    · have hc := Nat.card_congr eK.toEquiv
      rw [card_perm_four] at hc
      have := Subgroup.card_le_of_le (le_sup_left : K ≤ K ⊔ S)
      omega
  ·
    rcases h with ⟨hf2, -, hI', -⟩ | ⟨-, -, ⟨eK⟩⟩
    · have hc := isLin2Type_card_quot hI'
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6 : Nat.card (OTwoQuot I) = 6 := hI
      omega
    · have hc := Nat.card_congr eK.toEquiv
      rw [card_z2_perm_four] at hc
      have := Subgroup.card_le_of_le (le_sup_left : K ≤ K ⊔ S)
      omega
  ·
    have := hqI.eq_one_of_card_eq_six hf hI
    subst this
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := hqI.eq_one_of_card_eq_six (by omega) hI
    omega
  ·
    have := eq_two_of_card_sixty (by omega) hqK hK
    omega
  ·
    exact hKs hB.1
  ·
    have := eq_two_of_card_sixty (by norm_num) hqK hK
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := Nat.card_congr eK.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at this
    have h6 : Nat.factorial 3 = 6 := rfl
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega
  ·
    have := card_oTwoQuot_of_isL2Quot_one hqK
    omega

end CanonicalList

namespace CtxA

variable (C : CtxA G T L V V₂ g D e b)
include C

theorem charTwo_K0 (h12213 : Stmt12_2_13) :
    CharTwo (preM D e KA5 ⊔ T ⊔ borelOf (i128 T L V (fsuV1 T V)) T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := C.base.hyp.fsu.sylow
  have hB₂ := borelOf_I2_le h12213 C.base
  have hX : preM D e KA5 ⊔ T ⊔ borelOf (i128 T L V (fsuV1 T V)) T = preM D e KA5 ⊔ T :=
    sup_eq_left.mpr (hB₂.trans le_sup_right)
  have hU2 : IsPGroup 2 ↥(fsuU T V) := hT.1.to_le C.base.UT
  have hUX : fsuU T V ≤ preM D e KA5 ⊔ T := C.base.UT.trans le_sup_right
  have hXN : preM D e KA5 ⊔ T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    (sup_le (preM_le_H e KA5) C.base.TH).trans HN
  have hUO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUX hXN hU2
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  have hU1 : fsuU T V ≠ ⊥ := fun h => by
    have haU := C.base.V2U ha
    rw [h, Subgroup.mem_bot] at haU
    exact haV (by rw [haU]; exact one_mem _)
  rw [hX]
  exact charTwo_of_inH C.base.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
    ⟨le_sup_right, fun h => hU1 (le_bot_iff.mp (h ▸ hUO))⟩

theorem charTwo_I2 (h12213 : Stmt12_2_13) :
    CharTwo (i128 T L V (fsuV1 T V) ⊔ T ⊔ borelOf (preM D e KA5) T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := C.base.hyp.fsu.sylow
  have hs := C.base.s1282
  have hV2T : V₂ ≤ T := C.base.V2U.trans C.base.UT
  have hV22 : IsPGroup 2 ↥V₂ := hT.1.to_le hV2T
  have hVX : V₂ ≤ i128 T L V (fsuV1 T V) ⊔ T ⊔ borelOf (preM D e KA5) T :=
    hV2T.trans (le_sup_right.trans le_sup_left)
  have hXN : i128 T L V (fsuV1 T V) ⊔ T ⊔ borelOf (preM D e KA5) T ≤
      Subgroup.normalizer (V₂ : Set G) :=
    sup_le (sup_le (I2_le_normalizer_V2 h12213 C.base) hs.v2.2.2) C.borelOf_K0_le
  have hVO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVX hXN hV22
  have hV1 : V₂ ≠ ⊥ := fun h => by
    have h4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
    rw [h, Subgroup.card_bot] at h4
    omega
  exact charTwo_of_inH C.base.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
    ⟨le_sup_right.trans le_sup_left, fun h => hV1 (le_bot_iff.mp (h ▸ hVO))⟩

theorem hyp111 (h12213 : Stmt12_2_13)
    (h0 : pCoreOf 2 (preM D e KA5 ⊔ i128 T L V (fsuV1 T V) ⊔ T) = ⊥) :
    Hyp111 (preM D e KA5) (i128 T L V (fsuV1 T V)) T := by
  have hT := C.base.hyp.fsu.sylow
  obtain ⟨e₃⟩ := nonempty_oTwoQuot_I2 h12213 C.base
  exact ⟨⟨inferInstance, hT.1, C.T_le_normalizer_K0, C.isSylowTwoOf_K0, C.isRankOneListed_K0,
      (borelOf_I2_le h12213 C.base).trans C.T_le_normalizer_K0, C.charTwo_K0 h12213⟩,
    ⟨inferInstance, hT.1, T_le_normalizer_I2, isSylowTwoOf_I2 C.base,
      isRankOneListed_perm_three e₃,
      C.borelOf_K0_le.trans (normalizer_le_normalizer_i128 C.base.h1222 C.base.s1282),
      C.charTwo_I2 h12213⟩, h0⟩

end CtxA

end CFSG.Quasithin.H13.Q1410

end
