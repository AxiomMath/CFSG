module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTits
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofFix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section NR

variable {Ω : Type} [Field Ω]

theorem torusGroup_le_adjointGroup_D4 :
    torusGroup TwistTag.D4.tag Ω ≤ adjointGroup TwistTag.D4.tag Ω :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem nw_inv_021 [CharP Ω 2] : (nw Ω [0, 2, 1])⁻¹ = nw Ω [1, 2, 0] := nw_inv _

theorem noRefl_alg [IsAlgClosed Ω] [CharP Ω 2] {ζ : Ωˣ} (hζ : orderOf ζ = 3)
    {m : ModGL TwistTag.D4.tag Ω} (hmG : m ∈ adjointGroup TwistTag.D4.tag Ω)
    (hmc : m * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * m⁻¹ =
      rootDiagUnit TwistTag.D4.tag (tup ζ gT))
    (hmb : m * rootDiagUnit TwistTag.D4.tag (tup ζ gT2) * m⁻¹ =
      (rootDiagUnit TwistTag.D4.tag (tup ζ gT2))⁻¹) : False := by
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hpK : ringChar Ω ≠ 3 := by
    rw [ringChar.eq Ω 2]
    decide
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  obtain ⟨-, -, hQM, -, -, -, hMder, hinf, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer Ω 3 Nat.prime_three (by decide) hpK
      (tup ζ gT) hord vT hv.symm
  set c := rootDiagUnit TwistTag.D4.tag (tup ζ gT) with hc
  set b := rootDiagUnit TwistTag.D4.tag (tup ζ gT2) with hb
  have hbT : b ∈ torusGroup TwistTag.D4.tag Ω := rootDiagUnit_mem_torusGroup _
  have hcT : c ∈ torusGroup TwistTag.D4.tag Ω := rootDiagUnit_mem_torusGroup _
  have hmc' : m * c = c * m := by
    calc m * c = (m * c * m⁻¹) * m := by group
      _ = c * m := by rw [hmc]
  have hmM : m ∈ toralCentralizer TwistTag.D4.tag Ω (tup ζ gT) :=
    mem_toralCentralizer.2 ⟨hmG, by rw [← hc, mul_inv_eq_iff_eq_mul]; exact hmc'.symm⟩
  have hbM : b ∈ toralCentralizer TwistTag.D4.tag Ω (tup ζ gT) :=
    mem_toralCentralizer.2 ⟨torusGroup_le_adjointGroup_D4 hbT, by
      rw [← hc, mul_inv_eq_iff_eq_mul]
      exact CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.torusGroup_mul_comm hcT hbT⟩
  have hb3 : b ^ 3 = 1 := by
    rw [hb, ← rootDiagUnit_pow', tup_pow_three hζ3, rootDiagUnit_one]
  have hcomm : m * b * m⁻¹ * b⁻¹ = b := by
    rw [hmb]
    have : b⁻¹ * b⁻¹ = b := by
      calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * b ^ 3 := by rw [hb3, mul_one]
        _ = b := by group
    exact this
  have hQ : b ∈ d4A2Qv Ω vT := by
    rw [← hMder, ← hcomm]
    exact Subgroup.commutator_mem_commutator hmM hbM
  have hT : b ∈ d4A2Tv Ω vT := by
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨hQ, hbT⟩
  obtain ⟨s0, hsTQ, hsb⟩ := Subgroup.mem_map.1 hT
  let s : ModGL TwistTag.D4.tag Ω := s0
  have hnv : canonicalRep (coxeterSystem Tag.D4) Ω vT = nw Ω [0, 2, 1] :=
    (nw_eq_canonicalRep [0, 2, 1]).symm
  have hsb' : nw Ω [0, 2, 1] * s * (nw Ω [0, 2, 1])⁻¹ = b := by
    rw [← hnv]
    exact hsb
  have h1 : nw Ω [0, 2, 1] * s = b * nw Ω [0, 2, 1] := mul_inv_eq_iff_eq_mul.1 hsb'
  have h2 : s = (nw Ω [0, 2, 1])⁻¹ * (b * nw Ω [0, 2, 1]) := eq_inv_mul_iff_mul_eq.2 h1
  have hs : s = rootDiagUnit TwistTag.D4.tag (tup ζ (wordExp [1, 2, 0] gT2)) := by
    rw [← nw_conj_rootDiagUnit hζ3, h2, ← nw_inv_021, inv_inv, mul_assoc]
  obtain ⟨t, u, htu⟩ := mem_subsystemTorus_d4A2.1 hsTQ
  unfold d4A2TorusElt at htu
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul] at htu
  have htup := rootDiagUnit_injective (hs.symm.trans htu)
  have h1' := congrFun htup 1
  have h3' := congrFun htup 3
  obtain ⟨⟨-, a01, -, a03⟩, ⟨-, a21, -, a23⟩⟩ := cartan_D4_values
  have c01 : Tag.D4.cartan 0 1 = 0 := a01
  have c03 : Tag.D4.cartan 0 3 = 0 := a03
  have c21 : Tag.D4.cartan 2 1 = -1 := a21
  have c23 : Tag.D4.cartan 2 3 = -1 := a23
  have e : tup ζ (wordExp [1, 2, 0] gT2) 1 = tup ζ (wordExp [1, 2, 0] gT2) 3 := by
    rw [h1', h3']
    show t ^ Tag.D4.cartan 0 1 * u ^ Tag.D4.cartan 2 1 =
      t ^ Tag.D4.cartan 0 3 * u ^ Tag.D4.cartan 2 3
    rw [c01, c03, c21, c23]
  have w1 : (wordExp [1, 2, 0] gT2) 1 = 1 := by decide
  have w3 : (wordExp [1, 2, 0] gT2) 3 = 0 := by decide
  have e1 : tup ζ (wordExp [1, 2, 0] gT2) 1 = ζ := by
    show ζ ^ ((wordExp [1, 2, 0] gT2) 1).val = ζ
    rw [w1]
    exact pow_one ζ
  have e3 : tup ζ (wordExp [1, 2, 0] gT2) 3 = 1 := by
    show ζ ^ ((wordExp [1, 2, 0] gT2) 3).val = 1
    rw [w3]
    exact pow_zero ζ
  rw [e1, e3] at e
  rw [e, orderOf_one] at hζ
  exact absurd hζ (by norm_num)

end NR

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
