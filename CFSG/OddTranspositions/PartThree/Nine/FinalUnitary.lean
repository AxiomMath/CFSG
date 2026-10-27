module

public import CFSG.OddTranspositions.PartThree.Nine.FinalLocal
public import CFSG.OddTranspositions.PartThree.Nine.SevenCore
public import CFSG.CGT.T75E.RootOrders
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.CGT.T75E.Reduce
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem card_sylow_le_mul_card_regularCore {hC : HypothesisC D}
    {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q) {k : ℕ} (hk : Nat.card U = 2 ^ k) :
    Nat.card (S : Subgroup G) ≤ k * Nat.card Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.isElementaryAbelian
  obtain ⟨-, -, ⟨φ, -, hφ⟩, -⟩ := hU.affine h3
  have hQ' : IsRegularCore ((fun v : G => hC.d * v) '' (U : Set G)) Q := hU.sylow_inter ▸ hQ
  obtain ⟨-, -, -, d, hdk, hcard⟩ :=
    hU.exists_semilinear_coordinates_of_isRegularCore h3 hQ' φ hφ hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hk, pow_zero])) hU.ne_bot
    · exact h
  set ℓ := AffineEquiv.linearHom.comp φ with hℓ
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) := by
    rw [← hU.sylow_inter]
    exact h4.2.1
  set SN := (S : Subgroup G).subgroupOf
    (Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) with hSNdef
  have hSNcard : Nat.card SN = Nat.card (S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hsplit := Subgroup.relIndex_mul_card (H := ℓ.ker) (K := SN)
  rw [Subgroup.relIndex_ker] at hsplit
  have himg : Nat.card (SN.map ℓ) ≤ k := by
    have h2 : IsPGroup 2 (SN.map ℓ) := (S.isPGroup'.comap_subtype).map ℓ
    have : Finite (SN.map ℓ) := Finite.of_surjective _ (ℓ.subgroupMap_surjective SN)
    obtain ⟨j, hj⟩ := h2.exists_card_eq
    have hdvd : Nat.card (SN.map ℓ) ∣ (2 ^ k - 1) * d := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (Subgroup.map_le_range ℓ SN)
    have hodd : Odd (2 ^ k - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      refine ⟨2 ^ m - 1, ?_⟩
      have := Nat.one_le_two_pow (n := m)
      rw [pow_succ]
      omega
    have hcop : Nat.Coprime (2 ^ j) (2 ^ k - 1) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
    rw [hj] at hdvd ⊢
    have hd : 2 ^ j ∣ d := hcop.dvd_of_dvd_mul_left hdvd
    exact (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hdk hk1) hd).trans (Nat.le_of_dvd hk1 hdk)
  have hker : Nat.card (ℓ.ker ⊓ SN :) ≤ Nat.card Q := by
    let f : (ℓ.ker ⊓ SN :) → Q := fun x =>
      ⟨((x : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) : G),
        hU.mem_regularCore_of_linear_eq_one h3 hQ' φ hφ (MonoidHom.mem_ker.mp x.2.1)⟩
    refine Nat.card_le_card_of_injective f fun a b h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  rw [← hSNcard, ← hsplit]
  exact Nat.mul_le_mul himg hker

theorem card_sylow_map_le_of_psl2 {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC) (h5 : Conclusion9_5 D hC T S)
    (hU : DeltaSetup hC T S U) {n : ℕ} (hn : 1 ≤ n)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model n) :
    Nat.card ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) ≤ 2 * 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZcard : Nat.card (Subgroup.center (Halpha D hC.alpha)) = 2 := by
    rw [← Subgroup.card_map_of_injective (Halpha D hC.alpha).subtype_injective,
      center_Halpha_eq_zpowers h3 hU h5.1, Nat.card_zpowers, hC.setup.oddT.orderOf_eq_two hC.hd]
  have hHcard : Nat.card (Halpha D hC.alpha) = 2 ^ (n + 1) * ((2 ^ n) ^ 2 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Halpha D hC.alpha)),
      hZcard, Nat.card_congr eH.toEquiv, CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model hn,
      pow_succ]
    ring
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
    have h2 : Even ((2 ^ n) ^ 2) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  rw [Subgroup.card_map_of_injective (Halpha D hC.alpha).subtype_injective]
  obtain ⟨a, ha⟩ := (T.isPGroup').exists_card_eq
  have hdvd : 2 ^ a ∣ 2 ^ (n + 1) * ((2 ^ n) ^ 2 - 1) := by
    rw [← ha, ← hHcard]
    exact Subgroup.card_subgroup_dvd_card _
  rw [ha, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (CFSG.CGT.T75E.le_of_two_pow_dvd_mul_odd hodd hdvd)

theorem false_of_commutator_mulEquiv_psu3 {hC : HypothesisC D}
    {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G} {U : Subgroup G} (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q) {n : ℕ} (hn : 1 ≤ n)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model n)
    (eK : ↥(commutator G) ≃* PSU3Model n) (huK : hC.d ∉ commutator G) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := card_sylow_map_le_of_psl2 h3 h5 hU hn eH
  obtain ⟨k, -, hk⟩ := hU.exists_card
  have hqT := two_mul_card_le_card_sylow_map h3 hU
  have h2k : 2 ^ k ≤ 2 ^ n := by omega
  have hkn : k ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2k
  have huD : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
  have hΔcard : ((S : Set G) ∩ D).ncard = Nat.card U := by
    rw [hU.sylow_inter, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h),
      ← Nat.card_coe_set_eq]
    rfl
  have hQcard := card_regularCore_eq hQ huD
  rw [hΔcard, h5.1, hk] at hQcard
  have hS := card_sylow_le_mul_card_regularCore h3 h4 hU hQ hk
  obtain ⟨P, hP⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 (commutator G) S
  obtain ⟨r, -, hKcard⟩ := CFSG.CGT.T75E.exists_odd_card_psu3Model hn
  have hP3 : 2 ^ (3 * n) ≤ Nat.card (commutator G ⊓ (S : Subgroup G) : Subgroup G) := by
    have hdvd : 2 ^ (3 * n) ∣ Nat.card (commutator G) := by
      rw [Nat.card_congr eK.toEquiv, hKcard]
      exact Dvd.intro r rfl
    have hPeq : Nat.card (P : Subgroup (commutator G)) =
        Nat.card (commutator G ⊓ (S : Subgroup G) : Subgroup G) := by
      rw [hP, ← Subgroup.card_map_of_injective (commutator G).subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [← hPeq]
    exact Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card hdvd)
  have hrel := Subgroup.relIndex_mul_card (H := commutator G) (K := (S : Subgroup G))
  have hrel2 : 2 ≤ (commutator G).relIndex (S : Subgroup G) := by
    have h0 : (commutator G).relIndex (S : Subgroup G) ≠ 0 := fun h => by
      rw [h, zero_mul] at hrel
      exact (Nat.card_pos (α := (S : Subgroup G))).ne hrel
    have h1 : (commutator G).relIndex (S : Subgroup G) ≠ 1 := fun h =>
      huK (Subgroup.relIndex_eq_one.mp h huD.1)
    omega
  set a := 2 ^ n with ha
  have h3n : 2 ^ (3 * n) = a * a * a := by rw [pow_mul', ← ha]; ring
  have hle : 2 * (a * a * a) ≤ n * (a * (2 * a)) :=
    calc 2 * (a * a * a) ≤ (commutator G).relIndex (S : Subgroup G) *
          Nat.card (commutator G ⊓ (S : Subgroup G) : Subgroup G) :=
          Nat.mul_le_mul hrel2 (h3n ▸ hP3)
      _ = Nat.card (S : Subgroup G) := hrel
      _ ≤ k * Nat.card Q := hS
      _ = k * (2 ^ k * Nat.card ((T : Subgroup (Halpha D hC.alpha)).map
          (Halpha D hC.alpha).subtype)) := by rw [hQcard]
      _ ≤ n * (a * (2 * a)) := Nat.mul_le_mul hkn (Nat.mul_le_mul h2k hT)
  have hapos : 0 < a * a := Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n)
  have han : a ≤ n := by
    have h' : (a * a) * a ≤ (a * a) * n := by nlinarith
    exact Nat.le_of_mul_le_mul_left h' hapos
  exact absurd han (not_le.mpr Nat.lt_two_pow_self)

end CFSG.OddTranspositions.PartThree.Nine
