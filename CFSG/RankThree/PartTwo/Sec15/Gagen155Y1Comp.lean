module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155T51
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155T52Lem
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec13.Item135CritProofTrans
import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofTools
public import CFSG.Sporadic.Suz.Simple
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y1

private theorem exists_mem_normalizer_not_commute_of_le {A B C : Subgroup G}
    (hCdef : C = Subgroup.centralizer (B : Set G))
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) (hAC : A ≤ C)
    (hAmax : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E →
      A.subgroupOf C ≤ E → E = A.subgroupOf C)
    {Y : Subgroup (↥C ⧸ CFSG.pPrimeCore 3 ↥C)} (hY : CFSG.IsComponent Y)
    (hYaut : ∀ ψ : (↥C ⧸ CFSG.pPrimeCore 3 ↥C) ≃* (↥C ⧸ CFSG.pPrimeCore 3 ↥C),
      Y.map ψ.toMonoidHom = Y)
    (hKle : ∀ e ∈ A.subgroupOf C, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e ∈ Y →
      (e : G) ∈ B) :
    ∃ d ∈ Subgroup.centralizer (B : Set G), d ∈ Subgroup.normalizer (A : Set G) ∧
      (∃ k : ℕ, d ^ 3 ^ k = 1) ∧ ∃ e ∈ A, d * e * d⁻¹ ≠ e := by
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hO : CFSG.pPrimeCore 3 (↥C ⧸ CFSG.pPrimeCore 3 ↥C) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  obtain ⟨u, huY, hu3, y, hyY, huy⟩ :=
    Sylow155T51.exists_pow_three_not_commute_of_isComponent hO hY
  have hYn : ∀ q : ↥C ⧸ CFSG.pPrimeCore 3 ↥C,
      q ∈ Subgroup.normalizer (Y : Set (↥C ⧸ CFSG.pPrimeCore 3 ↥C)) := fun q =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hYaut (MulAut.conj q))
  have hA'ab : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf C) := hAab.subgroupOf C
  have hEY : ∀ e ∈ A.subgroupOf C, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e ∈ Y →
      ∀ z ∈ Y, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e * z =
        z * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e := by
    intro e he heY z _
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C) z
    have hm : (m : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [← hCdef]
      exact m.2
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hm (e : G) (hKle e he heY))
  obtain ⟨d, hdN, ⟨k, hk⟩, e, he, hde⟩ :=
    Sylow155T52.exists_mem_normalizer_not_commute (CFSG.pPrimeCore 3 ↥C) hN3 hA'ab hAmax hYn
      huY hu3 hyY huy hEY
  refine ⟨(d : G), ?_, ?_, ⟨k, by simpa using congrArg Subtype.val hk⟩, (e : G), he, ?_⟩
  · rw [← hCdef]
    exact d.2
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (Subgroup.mem_normalizer_iff.mp hdN ⟨x, hAC hx⟩).mp hx
    · intro hx
      have hxC : x ∈ C := by
        have hx' : x = (d : G)⁻¹ * ((d : G) * x * (d : G)⁻¹) * (d : G) := by group
        rw [hx']
        exact C.mul_mem (C.mul_mem (C.inv_mem d.2) (hAC hx)) d.2
      exact (Subgroup.mem_normalizer_iff.mp hdN ⟨x, hxC⟩).mpr hx
  · intro h
    exact hde (Subtype.ext (by simpa using h))

theorem exists_component_mem_not_mem (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (hT : TheoremFourHyp G) (hS : partTwoS G = ∅) {A : Subgroup G} (hA : A ∈ partTwoF G)
    {B : Subgroup G} (hBA : IsHyperplane A B) {c : G} (hcA : c ∈ A) (hcB : c ∉ B)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))) :
    ∃ Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))),
      CFSG.IsComponent Yc ∧ ∃ a ∈ A, a ∉ B ∧
        a ∈ (Yc.comap (QuotientGroup.mk'
          (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
            (Subgroup.centralizer (B : Set G)).subtype := by
  classical
  have hAE : A ∈ partTwoE G := (hT.partTwoF_eq_partTwoE hS).1 ▸ hA
  have hA27 : Nat.card A = 27 := hAE.2.1
  have hB9 : Nat.card B = 9 := by
    have h := hBA.2
    rw [hA27] at h
    omega
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hCdef
  have hAC : A ≤ C := by
    intro a ha
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA.1 hb⟩ ⟨a, ha⟩)
  obtain ⟨Y, hY, hYaut, _, _⟩ :=
    Sylow155T51.exists_centralizer_component_data h1 h2 h43 hin hT hS hA hBA.1 hB9 hcon
  have hAmax : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E →
      A.subgroupOf C ≤ E → E = A.subgroupOf C := by
    intro E hE hAE'
    have hAEm : A ≤ E.map C.subtype := fun x hx =>
      ⟨⟨x, hAC hx⟩, hAE' (show (⟨x, hAC hx⟩ : C) ∈ A.subgroupOf C from hx), rfl⟩
    have hEq : E.map C.subtype = A := hA.2.1 _ (hE.map _) hAEm
    rw [← hEq]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective E).symm
  refine ⟨Y, hY, ?_⟩
  by_contra hno
  have hKle : ∀ e ∈ A.subgroupOf C, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e ∈ Y →
      (e : G) ∈ B := by
    intro e he heY
    by_contra heB
    exact hno ⟨(e : G), he, heB, ⟨e, heY, rfl⟩⟩
  obtain ⟨d, hdB, hdA, ⟨k, hdk⟩, e, heA, hde⟩ :=
    exists_mem_normalizer_not_commute_of_le hCdef hAab hAC hAmax hY hYaut hKle
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hdc : d * c = c * d :=
    Sec8.Item812Res4.commute_of_mem_normalizer_zpowers hc3 hdk (hW hdA)
  have hsup : Subgroup.zpowers c ⊔ (A ⊓ B) = A :=
    TransProof.sup_eq_of_card hA27 (by rw [inf_eq_right.mpr hBA.1]; exact hB9) hcA hcB
  have hACd : A ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [← hsup]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) fun x hx => ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hdc.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hdB x hx.2)
  exact hde (by rw [← Subgroup.mem_centralizer_singleton_iff.mp (hACd heA), mul_inv_cancel_right])

end Gagen155Y1

end CFSG.RankThree.PartTwo.Sec15
