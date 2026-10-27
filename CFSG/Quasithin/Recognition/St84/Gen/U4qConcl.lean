module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qModel
import CFSG.Quasithin.Recognition.GoldschmidtF112RY9Group
import CFSG.Quasithin.Background.SimsD1TransBlock
import CFSG.Quasithin.Recognition.St84.Gen.G2q
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverA
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open scoped commutatorElement

theorem perfectCore_sup_eq_of_isL2Quot {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hB : Group.IsSolvable ↥B) {f : ℕ} (hf : 2 ≤ f)
    (hq : IsL2Quot f (oTwoQuot ↥L)) (ho : pCoreOf 2 (L ⊔ B) ≤ perfectCore (L ⊔ B)) :
    perfectCore (L ⊔ B) = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLP : L ≤ L ⊔ B := le_sup_left
  have hn : (L.subgroupOf (L ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).mpr (sup_le Subgroup.le_normalizer hBL)
  have hC_le : perfectCore (L ⊔ B) ≤ L :=
    perfectCore_le_of_sup_solvable hLP hn rfl hB
  have hO : pCoreOf 2 L = L ⊓ pCoreOf 2 (L ⊔ B) :=
    pCoreOf_eq_inf_pCoreOf hLP (sup_le Subgroup.le_normalizer hBL)
  have hO_le : pCoreOf 2 L ≤ perfectCore (L ⊔ B) := by
    rw [hO]
    exact inf_le_right.trans ho
  have hcomm : pCoreOf 2 L ≤ ⁅L, L⁆ := by
    have hperf : ⁅perfectCore (L ⊔ B), perfectCore (L ⊔ B)⁆ = perfectCore (L ⊔ B) :=
      perfectCore_perfect (L ⊔ B)
    calc pCoreOf 2 L ≤ perfectCore (L ⊔ B) := hO_le
      _ = ⁅perfectCore (L ⊔ B), perfectCore (L ⊔ B)⁆ := hperf.symm
      _ ≤ ⁅L, L⁆ := Subgroup.commutator_mono hC_le hC_le
  have hLperf : ⁅L, L⁆ = L := perfect_of_isL2Quot hf hq hcomm
  exact le_antisymm hC_le (le_perfectCore_of_perfect le_sup_left hLperf)

theorem not_nonempty_perfectCore_sup_mulEquiv_parP {G : Type} [Group G] [Finite G]
    {L B : Subgroup G} (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hB : Group.IsSolvable ↥B)
    {f : ℕ} (hf : 2 ≤ f) (hq : IsL2Quot (2 * f) (oTwoQuot ↥L))
    (ho : pCoreOf 2 (L ⊔ B) ≤ perfectCore (L ⊔ B)) {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) :
    ¬ Nonempty (↥(perfectCore (L ⊔ B)) ≃* ↥(perfectCore (parP h))) := by
  rintro ⟨e⟩
  have hC : perfectCore (L ⊔ B) = L :=
    perfectCore_sup_eq_of_isL2Quot hBL hB (by omega : 2 ≤ 2 * f) hq ho
  let e' : ↥L ≃* ↥(perfectCore (parP h)) := (MulEquiv.subgroupCongr hC).symm.trans e
  have hcard : Nat.card (oTwoQuot ↥L) = Nat.card (oTwoQuot ↥(perfectCore (parP h))) :=
    Nat.card_congr (CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv e').toEquiv
  have hleft : Nat.card (oTwoQuot ↥L) = 2 ^ (2 * f) * (4 ^ (2 * f) - 1) :=
    IsL2Quot.card (by omega : 1 ≤ 2 * f) hq
  have hright : Nat.card (oTwoQuot ↥(perfectCore (parP h))) = 2 ^ f * (4 ^ f - 1) := by
    haveI := h.finite
    refine (Nat.card_congr (U4qModel.quotPerfectCoreParP h hf).toEquiv).trans ?_
    refine (Nat.card_congr (CFSG.Quasithin.F146Field.Cover.slTwoCongr
      (CFSG.Quasithin.F146Field.Cover.ringEquivGalois (by omega)
        h.card_fixedField)).toEquiv).trans ?_
    exact CFSG.Quasithin.card_sl_two_gf2 f (by omega)
  have heq : 2 ^ (2 * f) * (4 ^ (2 * f) - 1) = 2 ^ f * (4 ^ f - 1) :=
    hleft.symm.trans (hcard.trans hright)
  set q : ℕ := 2 ^ f with hqdef
  have hpow2 : 2 ^ (2 * f) = q ^ 2 := by
    rw [hqdef, Nat.mul_comm 2 f, pow_mul]
  have hpow4 : 4 ^ (2 * f) = q ^ 4 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    calc 4 ^ (2 * f) = (2 ^ 2) ^ (2 * f) := by rw [h4]
      _ = 2 ^ (2 * (2 * f)) := (pow_mul 2 2 (2 * f)).symm
      _ = 2 ^ (f * 4) := by
        congr 1
        ring
      _ = (2 ^ f) ^ 4 := pow_mul 2 f 4
      _ = q ^ 4 := by rw [hqdef]
  have h4f : 4 ^ f = q ^ 2 := by
    have h : 4 ^ f = 2 ^ (2 * f) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h, hpow2]
  rw [hpow2, hpow4, h4f] at heq
  have hq4 : 4 ≤ q := by
    rw [hqdef]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq2pos : 0 < q ^ 2 := pow_pos (by omega : 0 < q) 2
  have hq2lt4 : q ^ 2 < q ^ 4 :=
    pow_lt_pow_right₀ (by omega : 1 < q) (by norm_num : 2 < 4)
  have hsub : q ^ 2 - 1 < q ^ 4 - 1 := by omega
  have hlt : q ^ 2 * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) :=
    mul_lt_mul_of_pos_left hsub hq2pos
  have hqle : q ≤ q ^ 2 := by
    calc q = q * 1 := (mul_one q).symm
      _ ≤ q * q := mul_le_mul_of_nonneg_left (by omega : 1 ≤ q) (Nat.zero_le q)
      _ = q ^ 2 := by ring
  have hle : q * (q ^ 2 - 1) ≤ q ^ 2 * (q ^ 2 - 1) := by
    calc q * (q ^ 2 - 1) = (q ^ 2 - 1) * q := mul_comm _ _
      _ ≤ (q ^ 2 - 1) * q ^ 2 := mul_le_mul_of_nonneg_left hqle (by positivity)
      _ = q ^ 2 * (q ^ 2 - 1) := mul_comm _ _
  rw [heq] at hlt
  exact absurd hle (not_le.mpr hlt)

theorem _root_.CFSG.QuasithinUnique.IsShort2.of_mulEquiv {G H : Type*} [Group G] [Group H]
    {L : Subgroup G} {N : Subgroup H} (e : ↥L ≃* ↥N) (hN : IsShort2 N) : IsShort2 L := by
  let g : ↥L →* H := N.subtype.comp e.toMonoidHom
  have hg : Function.Injective g := N.subtype_injective.comp e.injective
  have hmap : (⊤ : Subgroup ↥L).map g = N := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have htop : IsShort2 (⊤ : Subgroup ↥L) := by
    rw [← CFSG.Quasithin.SimsD1.TransBlock.isShort2_map_iff g hg ⊤, hmap]
    exact hN
  have hmapL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := (CFSG.Quasithin.SimsD1.TransBlock.isShort2_map_iff L.subtype
    L.subtype_injective ⊤).mpr htop
  rwa [hmapL] at h

theorem y9U4q_concl {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}
    (hF : F112Hyp L1 L2 S) (hf : 2 ≤ f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot (2 * f) (oTwoQuot ↥L2)) (hB : Group.IsSolvable ↥(bigB L1 L2 S))
    (ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ perfectCore (L1 ⊔ bigB L1 L2 S))
    (ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ perfectCore (L2 ⊔ bigB L1 L2 S))
    (hsp : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)))
    {H : Type} [Group H] {N : Subgroup H} (hN : IsShort2 N) (hNO : IsOmega4MinusType N f)
    (e2 : ↥(perfectCore (L2 ⊔ bigB L1 L2 S)) ≃* ↥N) :
    (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
      IsBlock2 L2 L2 ∧ IsOmega4MinusType L2 f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_sup_eq_of_isL2Quot hB1 hB hf h1 ho1
  have hc2 := perfectCore_sup_eq_of_isL2Quot hB2 hB (by omega : 2 ≤ 2 * f) h2 ho2
  have eL : ↥L2 ≃* ↥N := (MulEquiv.subgroupCongr hc2).symm.trans e2
  have hshort : IsShort2 L2 := IsShort2.of_mulEquiv eL hN
  have hb : IsBlock2 L2 L2 :=
    ⟨hshort, le_rfl, ((Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).mpr
      Subgroup.le_normalizer).isSubnormal⟩
  have ho : IsOmega4MinusType L2 f := IsOmega4MinusType.of_mulEquiv eL hNO
  refine ⟨?_, hb, ho⟩
  have hct1 : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hF.1.h1.charTwo
  have hp1 : ⁅L1, L1⁆ = L1 := by
    have h := perfectCore_perfect (L1 ⊔ bigB L1 L2 S)
    rwa [hc1] at h
  have hQS1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := by
    have hle := hF.1.h1.sylow.le_of_normalizes (ho1.trans (le_of_eq hc1))
      (le_sup_left.trans (le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S)))
      (pCoreOf_isPGroup 2 (L1 ⊔ bigB L1 L2 S))
    exact hle.trans inf_le_left
  have hSP : S ≤ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S).trans le_sup_right
  have hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) ≤ 2 ^ f := by
    rw [hsp.2.2]
  have hZpow : ∀ z ∈ Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)), z ^ 2 = 1 := by
    intro z hz
    obtain ⟨-, h | h⟩ := hsp.1
    · exact h.2 z
    · exact h.2.2 z hz
  intro _
  exact centerOf_le_centralizer_of_card hp1 le_sup_left hct1 hSP hQS1 hf h1 hZ hZpow

end CFSG.Quasithin.F112R
