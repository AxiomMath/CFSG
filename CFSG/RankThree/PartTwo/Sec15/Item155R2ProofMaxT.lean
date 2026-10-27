module

import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof155R2

variable {G : Type} [Group G] [Finite G]

theorem isoQuot_of_le_sup {L R N : Subgroup G} (hLN : L ≤ N) (hNLR : N ≤ L ⊔ R)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup 2 R) : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥N ⧸ CFSG.pCore 2 ↥N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : L →* N ⧸ CFSG.pCore 2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 N)).comp (Subgroup.inclusion hLN) with hφ
  have hker : ∀ l : L, φ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 N := by
    intro l
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Sec18.mem_pCore_iff_mem_pCoreOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨l, hl, hln⟩ := Sec18.exists_mem_mul_of_le_sup hLN hNLR hLR hNR hR n.2
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_eq_mk']
    refine ⟨⟨l⁻¹ * n, N.mul_mem (N.inv_mem (hLN hl)) n.2⟩,
      (Sec18.mem_pCore_iff_mem_pCoreOf _).mpr hln, ?_⟩
    apply Subtype.ext
    simp
  have hkerle : φ.ker ≤ CFSG.pCore 2 L := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have himg : (φ.ker).map L.subtype ≤ CFSG.Open.pCoreOf 2 N := by
      rintro _ ⟨l, hl, rfl⟩
      exact (hker l).mp hl
    have hp := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le himg
    exact hp.of_equiv ((φ.ker).equivMapOfInjective _ L.subtype_injective).symm
  have hle : CFSG.pCore 2 L ≤ φ.ker := by
    have hn : ((CFSG.pCore 2 L).map φ).Normal :=
      (CFSG.pCore_normal (p := 2) (G := L)).map φ hsurj
    have hp : IsPGroup 2 ((CFSG.pCore 2 L).map φ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := L)).map φ
    have hbot : (CFSG.pCore 2 L).map φ ≤ CFSG.pCore 2 (N ⧸ CFSG.pCore 2 N) :=
      le_sSup ⟨hn, hp⟩
    rw [Sec18.pCore_quotient_pCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hbot
    exact hbot
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hle hkerle)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

omit [Finite G] in
theorem mem_oPrimeResidualOf {p : ℕ} {Y : Subgroup G} {y : G} (hy : y ∈ Y) {k : ℕ}
    (hk : y ^ p ^ k = 1) : y ∈ oPrimeResidualOf p Y := by
  rw [oPrimeResidualOf_eq_closure]
  exact Subgroup.subset_closure ⟨hy, k, hk⟩

omit [Finite G] in
theorem oPrimeResidualOf_idem (p : ℕ) (Y : Subgroup G) :
    oPrimeResidualOf p (oPrimeResidualOf p Y) = oPrimeResidualOf p Y :=
  oPrimeResidualOf_eq_of_le (oPrimeResidualOf_le_self p Y)
    fun _ hy _ hk => mem_oPrimeResidualOf hy hk

theorem oPrimeResidualOf_sup_le {X S : Subgroup G} (hS : IsPGroup 2 S) :
    oPrimeResidualOf 3 (X ⊔ S) ≤ X ⊔ ⁅X, S⁆ := by
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  have hy' : y ∈ (X ⊔ ⁅X, S⁆) ⊔ S := sup_le_sup_right le_sup_left S hy
  exact mem_left_of_pow_prime_pow Nat.prime_three (le_normalizer_sup_commutator X S) hcop hy' hk

theorem oPrimeResidualOf_le_of_le_sup {H K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hH : H ≤ K ⊔ S) :
    oPrimeResidualOf 3 H ≤ K := by
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  exact mem_left_of_pow_prime_pow Nat.prime_three hSK hcop (hH hy) hk

variable {A : Subgroup G} {c : G} {L : Subgroup G}

end Proof155R2

end CFSG.RankThree.PartTwo.Sec15
