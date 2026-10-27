module

public import CFSG.Quasithin.Vol2.Ch12Sec5Cfg
public import CFSG.Quasithin.Vol2.Ch12Sec5K1List
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.EmptyFaithful.S1421QA15N1
public import CFSG.Quasithin.H13.J4Core

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125O2P

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_P (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Nat.card F.P = 3 * Nat.card T := by
  have h := Subgroup.relIndex_mul_card (H := T) (K := F.P)
  rw [inf_eq_left.2 (S125Cfg.T_le_P h1222 F hH), S125Pm.relIndex_P h1222 F hH] at h
  exact h.symm

theorem orderOf_dvd_three (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {x : G} (hx : x ∈ F.P) (ho : Odd (orderOf x)) : orderOf x ∣ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hH.hyp.sylow.1
  have hdvd : orderOf x ∣ 3 * 2 ^ n := by
    rw [← hn, ← card_P h1222 F hH]
    exact Subgroup.orderOf_dvd_natCard F.P hx
  refine Nat.Coprime.dvd_of_dvd_mul_right ?_ hdvd
  exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 ho)

theorem oTwoUpper_P_le_of_three (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K : Subgroup G}
    (hK : ∀ x ∈ Subgroup.normalizer (F.V1 : Set G), orderOf x = 3 → x ∈ K) :
    oTwoUpper F.P ≤ K := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  have hPM : F.P ≤ mi T L F.V1 := inf_le_left.trans inf_le_left
  have hMG : mi T L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) := inf_le_right
  have hG₁ : x ∈ Subgroup.normalizer (F.V1 : Set G) := hMG (hPM hx)
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_three h1222 F hH hx ho) with h1 | h3
  · rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact K.one_mem
  · exact hK x hG₁ h3

omit [Finite G] in
theorem mem_oPrimeResidualOf_of_orderOf {X : Subgroup G} {x : G} (hx : x ∈ X)
    (h3 : orderOf x = 3) : x ∈ oPrimeResidualOf 3 X := by
  exact Subgroup.subset_closure ⟨hx, 1, by rw [h3, pow_one]⟩

theorem pCoreOf_G1_ne_bot (F : Frame125 T L V) :
    pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := S125L9a.card_V1 F
  intro hb
  have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 F.V1 (IsPGroup.of_card (n := 1)
    (by rw [hcard, pow_one]))
  rw [hb, le_bot_iff] at h1
  rw [h1, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem oTwoUpper_P_le_of_exclusion (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G))) {S : Type} [Group S]
    [Finite S] (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* S) (hS : A318Exclusion S) :
    oTwoUpper F.P ≤ K₁ := by
  have hyp := hH.hyp
  have hSQ : SQTKGroup ↥(Subgroup.normalizer (F.V1 : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian (pCoreOf_G1_ne_bot F)
  have hn : ¬ (Nat.card S).Prime := by
    intro hp
    have h9 := hS.nine_dvd_card
    rcases (Nat.dvd_prime hp).1 ((by norm_num : 3 ∣ 9).trans h9) with h | h
    · omega
    · rw [← h] at h9
      omega
  have hQ : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (S153L.comp_quasisimple_of_simple hS.simple hn)
  have heq := eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hSQ hK hQ e hS
  refine oTwoUpper_P_le_of_three h1222 F hH fun x hx h3 => ?_
  rw [heq]
  exact mem_oPrimeResidualOf_of_orderOf hx h3

theorem oTwoUpper_P_le_of_list2
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h1222 : Stmt12_2_2)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hl : IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) : oTwoUpper F.P ≤ K₁ := by
  rcases hl with h | h | h <;> obtain ⟨e⟩ := h
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK e
      (a318Exclusion_psl52 (isPSL_sl_zmod_two (by norm_num)))
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK (MulEquiv.refl _)
      (a318Exclusion_m24 ⟨e⟩)
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK (MulEquiv.refl _)
      (a318Exclusion_j4 ⟨e⟩)

theorem oTwoUpper_P_le_of_list3
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h1222 : Stmt12_2_2)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) {K₁ : Subgroup G}
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hl : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.M23) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.HS) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.He) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* NativeSporadic.Ru)) :
    oTwoUpper F.P ≤ K₁ := by
  rcases hl with h | h | h | h | h | h <;> obtain ⟨e⟩ := h
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK e
      (a318Exclusion_psl42 l34NotL42Fact1515e_of_cert (isPSL_sl_zmod_two (by norm_num)))
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK e a318Exclusion_alt7
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK (MulEquiv.refl _)
      (a318Exclusion_m23 ⟨e⟩)
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK (MulEquiv.refl _)
      (a318Exclusion_hs ⟨e⟩)
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK (MulEquiv.refl _)
      (a318Exclusion_he ⟨e⟩)
  · exact oTwoUpper_P_le_of_exclusion hF h36 h38 h1222 F hH hK (MulEquiv.refl _)
      (a318Exclusion_ru ⟨e⟩)

end S125O2P

end CFSG.Quasithin.H13
