module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FO
public import CFSG.Quasithin.H13.NQCatBNExc
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Timmesfeld.Transvection.PresSp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

section Borel


theorem borelFacts_of_lie_ch615 {Γ : Type} [Group Γ] [Finite Γ] {F : Subgroup Γ}
    (hs : IsSimpleGroup ↥F) (hnab : ∃ a b : ↥F, a * b ≠ b * a) (hlie : IsLieChar2Big ↥F) :
    BorelFacts_ch615 F := by
  have hns : ¬ Group.IsSolvable ↥F := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr h a b)
  refine borelFacts_of_mulEquiv_ch615 (MulEquiv.refl ↥F) hns fun S₀ hS₀ R₀ hSR hR r hr s hs' => ?_
  have := NQCat.lieOvergroupFact_holds ↥F hs hlie S₀ hS₀ R₀ hSR hR hr
  exact (Subgroup.mem_normalizer_iff.mp this s).mp hs'

end Borel

theorem isSimpleGroup_of_isQuasisimple_ch615 {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  have := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem center_eq_bot_of_mulEquiv_ch615 {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']
  rw [hY, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr (e.injective (hex.trans (map_one e).symm))

section Lie


variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_sp4_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H)))) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K)) : False := by
  have : CharP K 2 := charTwo_facts_ch615 hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hcenSp := CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (n := 2) (K := K) (by norm_num)
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) :=
    isSimpleGroup_of_isQuasisimple_ch615 h1.1 (center_eq_bot_of_mulEquiv_ch615 e hcenSp)
  have hproj : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenSp).trans QuotientGroup.quotientBot).symm.trans
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 K)
  have hlie : IsLieChar2Big ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) :=
    ⟨m, hm, Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => by
      have h' := congrArg Prod.snd h
      simp only at h'
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega⟩, K, inferInstance, inferInstance, hK, ⟨e.trans hproj⟩⟩)))⟩
  have hB := borelFacts_of_lie_ch615 hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple h1.1) hlie
  have hcard : 40320 < Nat.card (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      show Finset.Icc 1 2 = {1, 2} from by decide, Finset.prod_pair (by norm_num)]
    set q := Nat.card K
    have h256 : 256 ≤ q ^ 2 ^ 2 := by
      calc 256 = 4 ^ 2 ^ 2 := by norm_num
        _ ≤ q ^ 2 ^ 2 := Nat.pow_le_pow_left h4 _
    have h15 : 15 ≤ q ^ (2 * 1) - 1 := by
      have : 16 ≤ q ^ (2 * 1) := by
        calc 16 = 4 ^ (2 * 1) := by norm_num
          _ ≤ q ^ (2 * 1) := Nat.pow_le_pow_left h4 _
      omega
    have h255 : 255 ≤ q ^ (2 * 2) - 1 := by
      have : 256 ≤ q ^ (2 * 2) := by
        calc 256 = 4 ^ (2 * 2) := by norm_num
          _ ≤ q ^ (2 * 2) := Nat.pow_le_pow_left h4 _
      omega
    calc 40320 < 256 * (15 * 255) := by norm_num
      _ ≤ q ^ 2 ^ 2 * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) :=
        Nat.mul_le_mul h256 (Nat.mul_le_mul h15 h255)
  have hJ := genFitting_eq_ch615 h1 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  exact c.false_of_case1_borel_ch615 hU hJ hB.2


theorem false_of_case1_g2_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H)))) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(quasithinG2 K)) : False := by
  classical
  have : CharP K 2 := charTwo_facts_ch615 hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hG2 : quasithinG2 K = CFSG.Quasithin.Explicit.cayleyGroup K :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  set e' := e.trans (MulEquiv.subgroupCongr hG2)
  obtain ⟨c0, hc0, hc1⟩ : ∃ c0 : K, c0 ≠ 0 ∧ c0 ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_finset_four_ch615 h4
    by_contra hno
    push Not at hno
    have hsub : s ⊆ {0, 1} := fun x _ => by
      by_cases h0 : x = 0
      · simp [h0]
      · simp [hno x h0]
    have := Finset.card_le_card hsub
    rw [hs] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  have hcen : Subgroup.center ↥(CFSG.Quasithin.Explicit.cayleyGroup K) = ⊥ :=
    CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) :=
    isSimpleGroup_of_isQuasisimple_ch615 h1.1 (center_eq_bot_of_mulEquiv_ch615 e' hcen)
  obtain ⟨ψ⟩ := CFSG.Quasithin.B42G2Id.nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hm
  have hlie : IsLieChar2Big ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) :=
    ⟨m, hm, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨Nat.prime_two, by omega, rfl, by
      rw [← hK]
      omega⟩, K, inferInstance, inferInstance, hK, ⟨e'.trans ψ⟩⟩))))⟩
  have hB := borelFacts_of_lie_ch615 hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple h1.1) hlie
  have hcard : 40320 < Nat.card (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK]
    set q := Nat.card K
    have h4096 : 4096 ≤ q ^ 6 := by
      calc 4096 = 4 ^ 6 := by norm_num
        _ ≤ q ^ 6 := Nat.pow_le_pow_left h4 _
    have h15 : 15 ≤ q ^ 2 - 1 := by
      have : 16 ≤ q ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left h4 _
      omega
    have h4095 : 4095 ≤ q ^ 6 - 1 := by omega
    calc 40320 < 4096 * (4095 * 15) := by norm_num
      _ ≤ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
        Nat.mul_le_mul h4096 (Nat.mul_le_mul h4095 h15)
  have hJ := genFitting_eq_ch615 h1 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  exact c.false_of_case1_borel_ch615 hU hJ hB.2

end Cx615C

end Lie

end CFSG.Quasithin.H13
