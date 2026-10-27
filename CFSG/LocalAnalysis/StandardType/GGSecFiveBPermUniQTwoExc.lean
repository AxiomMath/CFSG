module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

theorem UnitTB.Model.twoCenter_eq_bot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {f d : ℕ} {φ : ↥(unitarySU 2 f K d) →* ↥L} (hφ : UnitTB.Model φ)
    (hd : 4 ≤ d) : Line63.H5.twoCenter L = ⊥ := by
  have := hφ.field.finite
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [hφ.field.card, ← pow_mul, mul_comm]
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨hzL, hzc, hz2⟩ := hz
  obtain ⟨s, hs⟩ := hφ.surj ⟨z, hzL⟩
  have hconj : ∀ y, φ (s * y * s⁻¹) = φ y := fun y => by
    refine Subtype.ext ?_
    have h := hzc _ (φ y).2
    simp only [map_mul, map_inv, hs, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := UnitTB.scalar_of_map_conj_eq hφ hK hd hconj
  have : Fintype K := Fintype.ofFinite K
  have hsK : s ^ Nat.card K = s := by
    refine Subtype.ext (Units.ext_iff.2 ?_)
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hc, Matrix.diagonal_pow]
    congr 1
    funext i
    rw [Pi.pow_apply, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  have hs1 : s ^ (Nat.card K - 1) = 1 := by
    have h := hsK
    rw [← Nat.sub_add_cancel h1, pow_succ] at h
    exact mul_right_cancel (h.trans (one_mul s).symm)
  have hz1 : z ^ (Nat.card K - 1) = 1 := by
    have h := congrArg (fun t : ↥L => (t : G)) (congrArg φ hs1)
    simpa [map_pow, hs] using h
  have hodd : Odd (Nat.card K - 1) := by
    have hf0 : f ≠ 0 := by have := hφ.field.one_le; omega
    obtain ⟨k, hk⟩ : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 hf0) two_ne_zero
    have hpos : 0 < (2 ^ f) ^ 2 := by positivity
    exact ⟨k - 1, by rw [hK]; omega⟩
  have hcop : Nat.Coprime (Nat.card K - 1) (2 ^ Nat.card G) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have h := pow_gcd_eq_one.2 ⟨hz1, hz2⟩
  rw [hcop.gcd_eq_one, pow_one] at h
  exact Subgroup.mem_bot.2 h

theorem twoCenter_eq_bot_of_uniLabel_two
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≠ 6)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) p Bs L) :
    Line63.H5.twoCenter L = ⊥ := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hIDA : GGInnerDiagAll p B Bs x L D J := hR.1.2.2.1
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => GGSecFiveBPermUniLabel (r + 1) p lab ∧ lab.n ≤ 1) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨hUni, hm⟩ := hP
  obtain ⟨tag, rank, m⟩ := lab
  have hUni' : tag = .twA ∧ rank = (r + 1) - 1 ∧ p ∣ 2 ^ m + 1 := hUni
  obtain ⟨htag, hrank, hpq⟩ := hUni'
  have hm1 : m ≤ 1 := hm
  subst tag
  have hrankr : rank = r := by omega
  subst rank
  have hm0 : 1 ≤ m := hlab.1
  obtain rfl : m = 1 := by omega
  have hr4 : 4 ≤ r := by omega
  have hr5 : r ≠ 5 := by omega
  by_cases hpd : p ∣ r + 1
  · obtain ⟨F, _, _, _, _, _, _, hM, _⟩ := exists_diagonal_cover_of_large_unitary_side_of_cfg hRig
      hcfg hIDA (Or.inl rfl) hr4 hr5 hpq hpd hhas hlab
    exact hM.twoCenter_eq_bot (by omega)
  · obtain ⟨F, _, _, _, _, _, _, hM, _⟩ := exists_diagonal_cover_of_large_unitary_coprime_of_inner
      hRig hcfg.2.1.2.1 hIDA.1 hr4 (Or.inl hr5) hpq hpd hhas hlab
    exact hM.twoCenter_eq_bot (by omega)

section Inputs


theorem ggSecFiveBPermUniQTwoExcInput_of_six (h6 : GGSecFiveBPermUniQTwoExcSixInput) :
    GGSecFiveBPermUniQTwoExcInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hP hn5 eta hJ hA hNb hG0 hSp hB hU hz
  rcases eq_or_ne n 6 with rfl | hn6
  · exact h6 G p B Bs x L D J 𝒦 hR hT e hP eta hJ hA hNb hG0 hSp hB hU hz
  · exact absurd (twoCenter_eq_bot_of_uniLabel_two ggLabelRigidInput_holds hR hn5 hn6 hU) hz

end Inputs

end CFSG.StandardType

end
