module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Local
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import Certificates.Certificate9570
public import Certificates.Certificate9571
public import Certificates.Certificate9572
public import Certificates.Certificate9573
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
import CFSG.Adapters.TauCetiExceptional.BridgeG2
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree46
import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
import Certificates.Certificate2022
import Certificates.Certificate2022Base
import Certificates.Certificate2121
import Certificates.Certificate2122
import Certificates.Certificate2123
import Certificates.Certificate2202
import Certificates.Certificate2214
import Certificates.Certificate2215
import Certificates.Certificate2217
import Certificates.Certificate2283
import Certificates.Certificate2288

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three
open CFSG.RankThree.PartTwo.Sec4.Item434Cover

namespace Item434RemG23

theorem sylCheck_true : sylCheck = true :=
  Certificates.certificate9570

theorem k2Check_true : k2Check = true :=
  Certificates.certificate9571

theorem coverCheck_true : coverCheck = true :=
  Certificates.certificate9572

theorem liftCheck_true : liftCheck = true :=
  Certificates.certificate9573

theorem exists_E27 {Y : Type*} [Group Y] [Finite Y] {W : Subgroup Y}
    (hW : CFSG.Assembly.IsElemAbelian 3 W) (h27 : 27 ≤ Nat.card W) :
    ∃ D : Subgroup Y, D ≤ W ∧ CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hW).exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := W) (n := 3)
    (by rw [hk]; exact pow_dvd_pow 3 hk3)
  refine ⟨K.map W.subtype, Subgroup.map_subtype_le K,
    Sec5.isElemAbelian_of_le hW (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective W.subtype_injective, hK]
  norm_num

theorem factorization_three_card : (4245696 : ℕ).factorization 3 = 6 := by
  have h : (4245696 : ℕ) = 3 ^ 6 * 5824 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 5824 by norm_num)]

theorem liftData_R3 :
    ∃ d : LiftData R3, ∀ i, ((d.x i : R3) : GL (Fin 14) (ZMod 3)) ∈ sylow :=
  exists_liftData sylCheck_true liftCheck_true
    (wordsOK_of_coverCheck coverCheck_true) sylWord_lt

theorem exists_E27_R3 :
    ∃ D : Subgroup R3, CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 27 := by
  obtain ⟨d, -⟩ := liftData_R3
  have hW : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure (Set.range d.x)) :=
    Item434SporE81.isElemAbelian_closure_of_comm
      (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact d.hxc a b) (by rintro _ ⟨a, rfl⟩; exact d.hx3 a)
  obtain ⟨D, -, hD, hD27⟩ := exists_E27 hW d.hx27
  exact ⟨D, hD, hD27⟩

theorem conj_eq_of_coe {h t z : R3} {h' t' z' : GL (Fin 14) (ZMod 3)}
    (hh : (h : GL (Fin 14) (ZMod 3)) = h') (ht : (t : GL (Fin 14) (ZMod 3)) = t')
    (hz : (z : GL (Fin 14) (ZMod 3)) = z') (e : h' * t' * h'⁻¹ = z') : h * t * h⁻¹ = z := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hh, ht, hz, e]

section R3


theorem center_R3 : Subgroup.center R3 = ⊥ := by
  have h0 : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 3)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have h := @Subgroup.map_center_eq _ _ _ R3.toGroup _ _ _ adjointEquivR3
  rw [h0, Subgroup.map_bot] at h
  exact h.symm

theorem card_sylow_eq :
    Nat.card sylow = 3 ^ (Nat.card R3).factorization 3 := by
  rw [card_sylow sylCheck_true sylWord_lt, card_R3, factorization_three_card]
  norm_num

theorem hE_R3 :
    ∀ P : Subgroup R3, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 27 →
      ∃ B E : Subgroup R3, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
        81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  intro P hP hP27
  obtain ⟨z, hzS, hz3, hz1, hzc, hgood⟩ := exists_hgood sylCheck_true k2Check_true sylWord_lt
  exact Item434SporE81.exists_e81_of_e27_ambient (J := R3) (Q := sylow) (R := sylow) (z := z)
    (sylow_le_R3 sylWord_lt) card_sylow_eq hz3 hz1 hzS hzc le_rfl
    (Nat.le_mul_of_pos_right _ (by norm_num)) hgood hP hP27

theorem hX_R3 :
    ∀ U : Subgroup R3, CFSG.Assembly.IsElemAbelian 3 U → Nat.card U = 9 →
      ∃ u ∈ U, u ≠ 1 ∧ ∃ d : LiftData R3, ∀ i, d.x i ∈ Subgroup.centralizer ({u} : Set R3) := by
  obtain ⟨d₀, hd₀⟩ := liftData_R3
  refine exists_lift_of_cover (sylow.subgroupOf R3) ?_ ?_ d₀ (fun i => ?_)
  · rw [Item434SporE81.card_subgroupOf_of_le (sylow_le_R3 sylWord_lt)]
    exact card_sylow_eq
  · intro a ha b hb ha1 ha3 hb3 hab hbz
    have ha' : (a : GL (Fin 14) (ZMod 3)) ∈ sylow := Subgroup.mem_subgroupOf.mp ha
    have hb' : (b : GL (Fin 14) (ZMod 3)) ∈ sylow := Subgroup.mem_subgroupOf.mp hb
    have ha3' : (a : GL (Fin 14) (ZMod 3)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one]
    have hb3' : (b : GL (Fin 14) (ZMod 3)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hb3, Subgroup.coe_one]
    have hab' : (a : GL (Fin 14) (ZMod 3)) * b = b * a := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hab]
    have hbz' : (b : GL (Fin 14) (ZMod 3)) ∉ Subgroup.zpowers (a : GL (Fin 14) (ZMod 3)) := by
      intro hmem
      apply hbz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow]
      exact hk
    obtain ⟨t, ht, h, hh, z', hz'S, hz'c, htz⟩ := exists_isT sylCheck_true
      (zOK_of_k2Check k2Check_true) coverCheck_true sylWord_lt _ ha' _ hb'
      (fun h1 => ha1 (Subtype.ext h1)) ha3' hb3' hab' hbz'
    have hz'' : (⟨z', sylow_le_R3 sylWord_lt hz'S⟩ : R3) ∈ sylow.subgroupOf R3 :=
      Subgroup.mem_subgroupOf.mpr hz'S
    have hcen : ∀ q ∈ sylow.subgroupOf R3,
        q * (⟨z', sylow_le_R3 sylWord_lt hz'S⟩ : R3) = ⟨z', sylow_le_R3 sylWord_lt hz'S⟩ * q :=
      fun q hq => Subtype.ext (hz'c q (Subgroup.mem_subgroupOf.mp hq))
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨a, by simp, ⟨h, hh⟩, _, hz'', hcen, conj_eq_of_coe rfl rfl rfl htz⟩
    · exact ⟨b, by simp, ⟨h, hh⟩, _, hz'', hcen, conj_eq_of_coe rfl rfl rfl htz⟩
    · exact ⟨a * b, by simp, ⟨h, hh⟩, _, hz'', hcen,
        conj_eq_of_coe rfl (Subgroup.coe_mul _ _ _) rfl htz⟩
    · exact ⟨a * b ^ 2, by simp, ⟨h, hh⟩, _, hz'', hcen,
        conj_eq_of_coe rfl (by rw [Subgroup.coe_mul, Subgroup.coe_pow]) rfl htz⟩
  · exact Subgroup.mem_subgroupOf.mpr (hd₀ i)

theorem false_of_R3
    {G : Type} [Group G] [Finite G]
    {A M Q : Subgroup G} (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* R3) (hout : ¬ 3 ∣ Nat.card (Outer R3)) :
    False := by
  have hcen : Subgroup.center R3 = ⊥ := center_R3
  by_cases hZ : Subgroup.center (layer G) = ⊥
  · rcases h.card_layerStar with h9 | ⟨h27, -⟩
    · obtain ⟨D, hD, hD27⟩ := exists_E27_R3
      exact @Item434Spor.false_of_card_nine G _ _ A M Q R3 R3.toGroup h hZ e D hD hD27 h9
    · exact @Item434SporE81.false_of_e27 G _ _ A M Q (GL (Fin 14) (ZMod 3)) _ R3 _ h e hcen hout
        hE_R3 hZ h27
  · exact @false_of_cover G _ _ A M Q R3 R3.toGroup _ h e hcen hout hZ hX_R3

theorem not_three_dvd_outer_R3 {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 3 1) (ψ : Y ≃* R3) :
    ¬ 3 ∣ Nat.card (Outer R3) := by
  have h2 := CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.card_outer_G2_three Y hY
  rw [← Nat.card_congr
    (@CFSG.ComponentClassification.OuterAutomorphisms.equivalence _ _ _ R3.toGroup ψ).toEquiv, h2]
  norm_num

end R3

end Item434RemG23

section Families


theorem item434CharThreeG2 :
    Item434CharThreeG2 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have hK : Nat.card (ZMod 3) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def]
    rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q g2ThreeIndex.2 (by decide) (ZMod 3) hK
  let ψ : (TauCeti.CFSGIndex.lie g2ThreeIndex).Group ≃* R3 :=
    b.symm.trans adjointQuotientEquivR3
  have hY := Census.chevalleyExceptionalModel_G2_three q g2ThreeIndex.2 rfl rfl
  exact (Item434RemG23.false_of_R3 hc (e₀.trans ψ)
    (Item434RemG23.not_three_dvd_outer_R3 hY ψ)).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
