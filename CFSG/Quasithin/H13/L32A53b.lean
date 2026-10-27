module

public import CFSG.Quasithin.H13.L32A53a
public import CFSG.Quasithin.H13.U3S1349B
public import CFSG.Quasithin.H13.L32ASk1

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_open_of_quasithinO2QuotientIso {K : Subgroup G} {X : Type*} [Group X]
    (h : quasithinO2QuotientIso K X) : Nonempty (↥K ⧸ CFSG.Open.pCore 2 ↥K ≃* X) := by
  obtain ⟨φ, hφ, hker⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem isSylowTwoOf_T {K : Subgroup G} (hTK : T ≤ K) : IsSylowTwoOf T K :=
  isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow hTK

theorem pCoreOf_g1_le_T : pCoreOf 2 (A6.g1 T V) ≤ T :=
  pCoreOf_le_of_le C.hyp (C.hyp.isTSub_V1 (stmtL32NModule_of_inputs C.h1332 C.h1334)).2.2

theorem i2_facts (h4 : Lemma14_7_4_two_three) :
    Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (i2 T V V₂ : Set G) ∧
      i2 T V V₂ = xL L V₂ ⊔ pCoreOf 2 (A6.g1 T V) ∧
      quasithinO2QuotientIso (i2 T V V₂) (Equiv.Perm (Fin 3)) ∧
      xL L V₂ = oTwoRes (i2 T V V₂) := by
  obtain ⟨⟨-, hN⟩, hI, hS3, hO2, -⟩ := h4 G T L V V₂ C.hyp C.hV2
  exact ⟨hN, hI, (quasithinO2QuotientIso_iff _ _).mpr hS3, hO2⟩

theorem xT_eq (h4 : Lemma14_7_4_two_three) : xL L V₂ ⊔ T = i2 T V V₂ ⊔ T := by
  obtain ⟨-, hI, -, -⟩ := C.i2_facts h4
  rw [hI]
  refine le_antisymm (sup_le_sup_right le_sup_left T) (sup_le (sup_le le_sup_left ?_) le_sup_right)
  exact C.pCoreOf_g1_le_T.trans le_sup_right

theorem T_le_normalizer_i2 (h4 : Lemma14_7_4_two_three) :
    T ≤ Subgroup.normalizer (i2 T V V₂ : Set G) :=
  C.hV2.2.2.1.trans (C.i2_facts h4).1

theorem quot_xT (h4 : Lemma14_7_4_two_three) :
    quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)) ∧ T.relIndex (xL L V₂ ⊔ T) = 3 := by
  rw [C.xT_eq h4]
  exact U3.quot_S3_sup (C.T_le_normalizer_i2 h4) (C.isSylowTwoOf_T le_sup_right)
    (C.i2_facts h4).2.2.1

theorem relIndex_yT : T.relIndex (Y ⊔ T) = 3 :=
  U3.relIndex_eq_three_of_quot C.hS3 (C.isSylowTwoOf_T le_sup_right)

theorem T_le_normalizer_xL : T ≤ Subgroup.normalizer (xL L V₂ : Set G) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    C.hyp.normalizes (stmt13_3_2_two_of C.h1332)
  have hT : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₂ : Set G) : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTL ht,
      Subgroup.le_normalizer (C.hV2.2.2.1 ht)⟩
  have h := hT.trans (normalizer_le_normalizer_oTwoUpper _)
  rw [← oTwoRes_eq_oTwoUpper] at h
  exact h

theorem oTwoUpper_sup_T {K : Subgroup G} (hK : oTwoUpper K = K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : oTwoUpper (K ⊔ T) = K := by
  have hT : IsPGroup 2 T := C.hyp.fsu.sylow.1
  apply le_antisymm
  · refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTK).1 hx
    obtain ⟨k, hk⟩ := hT ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hTK hp) (2 ^ k)
    exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩
  · calc K = oTwoUpper K := hK.symm
      _ ≤ oTwoUpper (K ⊔ T) := oTwoUpper_mono le_sup_left

theorem oTwoUpper_xT : oTwoUpper (xL L V₂ ⊔ T) = xL L V₂ := by
  refine C.oTwoUpper_sup_T ?_ C.T_le_normalizer_xL
  have h := L32NSet14.oTwoUpper_oTwoRes (L ⊓ Subgroup.normalizer (V₂ : Set G))
  exact h

theorem oTwoUpper_yT : oTwoUpper (Y ⊔ T) = Y := C.oTwoUpper_sup_T C.hYo C.hTY

theorem inf_eq (h4 : Lemma14_7_4_two_three) : (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T := by
  set D := (xL L V₂ ⊔ T) ⊓ (Y ⊔ T)
  have hTD : T ≤ D := le_inf le_sup_right le_sup_right
  have h3 := (C.quot_xT h4).2
  have hmul := Subgroup.relIndex_mul_relIndex T D (xL L V₂ ⊔ T) hTD inf_le_left
  rw [h3] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hmul) with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.1 h) hTD
  · exfalso
    rw [h] at hmul
    have h1 : D.relIndex (xL L V₂ ⊔ T) = 1 := by omega
    have hXY : xL L V₂ ⊔ T ≤ Y ⊔ T := (Subgroup.relIndex_eq_one.1 h1).trans inf_le_right
    have hc1 := Subgroup.relIndex_mul_relIndex T (xL L V₂ ⊔ T) (Y ⊔ T) le_sup_right hXY
    rw [h3, C.relIndex_yT] at hc1
    have h2 : (xL L V₂ ⊔ T).relIndex (Y ⊔ T) = 1 := by omega
    have heq : xL L V₂ ⊔ T = Y ⊔ T := le_antisymm hXY (Subgroup.relIndex_eq_one.1 h2)
    have hXY' : xL L V₂ = Y := by rw [← C.oTwoUpper_xT, heq, C.oTwoUpper_yT]
    apply C.not_le_M
    rw [← hXY']
    exact ((oTwoRes_le _).trans inf_le_left).trans Subgroup.le_normalizer

theorem goldschmidt (h4 : Lemma14_7_4_two_three) :
    F6.IsGoldschmidtTripleIn (hY T L V₂ Y) (xL L V₂ ⊔ T) (Y ⊔ T) := by
  refine ⟨?_, nonempty_open_of_quasithinO2QuotientIso (C.quot_xT h4).1,
    nonempty_open_of_quasithinO2QuotientIso C.hS3, ?_⟩
  · apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_right)
  · rw [C.inf_eq h4]
    exact C.isSylowTwoOf_T le_sup_right

end Ctx

end CFSG.Quasithin.H13.L32A.T53
